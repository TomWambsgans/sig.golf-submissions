import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Extract
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OneTime
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierOracleMask
import SigGolfCandidate.SphincsSecurity.Proof.Ots.SecretProbe
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] chainWalk
noncomputable local instance instDecidableEqQueryImplHashInputHashSpecId : DecidableEq (QueryImpl HashSpec Id) := Classical.decEq _

noncomputable def otsChainFunctions (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin steps → Digest → Digest :=
  fun step value => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + step.val) 1 value)

theorem otsChainFunctions_tail (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) :
    Fin.tail (otsChainFunctions parameter lay tree leaf chainIdx start (steps + 1) f) =
      otsChainFunctions parameter lay tree leaf chainIdx (start + 1) steps f := by
  funext step value
  simp only [Fin.tail, otsChainFunctions, Fin.val_succ, Nat.add_right_comm start 1 step.val,
    Nat.add_assoc]

theorem otsChainFunctions_apply (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id)
    (step : Fin steps) (hstep : start + step.val < chainLength - 1) (value : Digest) :
    otsChainFunctions parameter lay tree leaf chainIdx start steps f step value =
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx ⟨start + step.val, hstep⟩)
        (digestBytes value))) := by
  simp only [otsChainFunctions, chainWalk, Nat.add_zero, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    dif_pos hstep, eval_tweakableHash]

theorem otsChainFunctions_evaluate (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (f : QueryImpl HashSpec Id) (value : Digest) :
    PartialChainEndpoint.evaluate (otsChainFunctions parameter lay tree leaf chainIdx start steps f) value =
      evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps generalizing start value with
  | zero => simp only [PartialChainEndpoint.evaluate, chainWalk, evalWithAnswerFn_pure]
  | succ steps ih =>
      rw [PartialChainEndpoint.evaluate, otsChainFunctions_tail, ih]
      change evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + 1) steps
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start 1 value))) = _
      simpa only [Nat.add_comm 1 steps] using
        (eval_chainWalk_add f parameter lay tree leaf chainIdx start 1 steps value).symm

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

structure OtsPrefix where
  parameter : PublicParameter
  lay : Layer
  tree : TreeIndex
  leaf : LeafIndex
  chainIdx : ChainIndex
  digit : Digit

namespace OtsPrefix

abbrev Query (segment : OtsPrefix) := Fin segment.digit.val × Digest
abbrev High := BitVec (hashOutputBits - digestBits)

def step (segment : OtsPrefix) (index : Fin segment.digit.val) : ChainStep :=
  ⟨index.val, by have := index.isLt; have := segment.digit.isLt; omega⟩

def input (segment : OtsPrefix) (query : segment.Query) : HashInput :=
  tweakableHashInput segment.parameter (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1))
    (digestBytes query.2)

theorem input_injective (segment : OtsPrefix) : Function.Injective segment.input := by
  intro left right heq
  have hparts := tweakableHashInput_injective segment.parameter (by trivial) (by trivial) heq
  have hstep : segment.step left.1 = segment.step right.1 := by
    simpa only [HashDomain.chain.injEq, true_and] using hparts.1
  have hindex : left.1.val = right.1.val := congrArg (fun position : ChainStep => position.val) hstep
  exact Prod.ext (Fin.ext hindex) (digestBytes_injective hparts.2)

noncomputable def parse (segment : OtsPrefix) (bytes : HashInput) : Option segment.Query :=
  if h : ∃ query, segment.input query = bytes then some h.choose else none

theorem parse_some_iff (segment : OtsPrefix) (bytes : HashInput) (query : segment.Query) :
    segment.parse bytes = some query ↔ bytes = segment.input query := by
  unfold parse
  split
  · rename_i hex
    rw [Option.some.injEq]
    constructor
    · intro heq
      rw [← heq]
      exact hex.choose_spec.symm
    · intro heq
      exact segment.input_injective (hex.choose_spec.trans heq)
  · rename_i hnone
    constructor
    · intro h
      cases h
    · intro heq
      exact False.elim (hnone ⟨query, heq.symm⟩)

theorem parse_input (segment : OtsPrefix) (query : segment.Query) : segment.parse (segment.input query) = some query :=
  (segment.parse_some_iff _ query).mpr rfl

noncomputable def combine (low : Digest) (high : High) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem split_combine (low : Digest) (high : High) : splitHashOutput digestBits (combine low high) = (low, high) := by
  exact (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)

theorem truncate_combine (low : Digest) (high : High) : truncateHash (combine low high) = low :=
  congrArg Prod.fst (split_combine low high)

theorem combine_split (output : HashOutput) :
    combine (truncateHash output) (splitHashOutput digestBits output).2 = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

noncomputable def answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun bytes => match segment.parse bytes with
    | none => outside bytes
    | some query => combine (tables query.1 query.2) (high query)

theorem answer_input (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (query : segment.Query) :
    segment.answer tables high outside (segment.input query) = combine (tables query.1 query.2) (high query) := by
  simp only [answer, parse_input]

def lows (segment : OtsPrefix) (f : QueryImpl HashSpec Id) : Fin segment.digit.val → Digest → Digest :=
  fun index value => truncateHash (f (segment.input (index, value)))

def highs (segment : OtsPrefix) (f : QueryImpl HashSpec Id) : segment.Query → High :=
  fun query => (splitHashOutput digestBits (f (segment.input query))).2

theorem answer_original (segment : OtsPrefix) (f : QueryImpl HashSpec Id) :
    segment.answer (segment.lows f) (segment.highs f) f = f := by
  funext bytes
  cases hparse : segment.parse bytes with
  | none => simp only [answer, hparse]
  | some query =>
      have hinput := (segment.parse_some_iff bytes query).mp hparse
      rw [hinput, answer_input]
      exact combine_split (f (segment.input query))

theorem lows_eq_chainFunctions (segment : OtsPrefix) (f : QueryImpl HashSpec Id) :
    segment.lows f = otsChainFunctions segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val f := by
  funext index value
  rw [otsChainFunctions_apply segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val f
    index (by have := (segment.step index).isLt; simpa only [step, Nat.zero_add] using this) value]
  simp only [lows, input, step]
  congr 4
  exact Fin.ext (Nat.zero_add index.val).symm

theorem evaluate_lows (segment : OtsPrefix) (f : QueryImpl HashSpec Id) (secret : Digest) :
    PartialChainEndpoint.evaluate (segment.lows f) secret =
      evalWithAnswerFn f (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val secret) := by
  rw [lows_eq_chainFunctions, otsChainFunctions_evaluate]

theorem input_private (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val) (query : segment.Query) :
    PrivateOtsPrefixInput segment.parameter words (segment.input query) := by
  rw [input, privateOtsPrefixInput_chain_iff]
  exact query.1.isLt.trans_le hword

theorem answer_agrees_outside (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    AgreeOutsideOtsPrefixes segment.parameter words (segment.answer tables high outside) outside := by
  intro bytes hnot
  cases hparse : segment.parse bytes with
  | none => simp only [answer, hparse]
  | some query =>
      have hinput := (segment.parse_some_iff bytes query).mp hparse
      exact False.elim (hnot (hinput ▸ segment.input_private words hword query))

theorem mask_answer (segment : OtsPrefix) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    maskOtsPrefixes segment.parameter words (segment.answer tables high outside) = maskOtsPrefixes segment.parameter words outside :=
  maskOtsPrefixes_congr (segment.answer_agrees_outside words hword tables high outside)

end OtsPrefix
end SphincsSecurity.Concrete
