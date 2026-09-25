import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCap
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedRun
import SigGolfCandidate.SphincsSecurity.Proof.Reference.CausalFrontierProgram
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State AuxIndex ExtraIndex : Type} {auxSpec : OracleSpec AuxIndex} {extraSpec : OracleSpec ExtraIndex} {n : Nat} {Result : Type}

noncomputable def extendAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id) : QueryImpl (auxSpec + extraSpec) PMF
  | .inl input => auxiliary input
  | .inr input => PMF.pure (extra input)

noncomputable def eraseAux (extra : QueryImpl extraSpec Id) :
    QueryImpl ((auxSpec + extraSpec) + PrefixSpec n State) (OracleComp (auxSpec + PrefixSpec n State))
  | .inl (.inl input) => liftM ((auxSpec + PrefixSpec n State).query (.inl input))
  | .inl (.inr input) => pure (extra input)
  | .inr query => liftM ((auxSpec + PrefixSpec n State).query (.inr query))

variable [Fintype State] [DecidableEq State] [Nonempty State]

omit [Fintype State] [Nonempty State] in
theorem observedRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (tables : Fin n → State → State) (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (simulateQ (eraseAux extra) computation) observed = observedRun (extendAux auxiliary extra) tables computation observed := by
  have himpl : (observedImpl auxiliary tables).compose (eraseAux extra) = observedImpl (extendAux auxiliary extra) tables := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, observedImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [observedRun, ← QueryImpl.simulateQ_compose, himpl]

theorem realRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      realRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [realRun, observedRun_eraseAux]

end SphincsSecurity.Concrete.PartialChainEndpoint

namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

abbrev VisibleWorld (segment : OtsPrefix) := OracleWorld + PartialChainEndpoint.PrefixSpec segment.digit.val Digest

noncomputable def visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl HashSpec (OracleComp segment.VisibleWorld) := fun bytes =>
  match segment.parse bytes with
  | none => liftM (segment.VisibleWorld.query (.inl (.inr bytes)))
  | some query => (combine · (high query)) <$> liftM (segment.VisibleWorld.query (.inr query))

noncomputable def visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl OracleWorld (OracleComp segment.VisibleWorld)
  | .inl input => liftM (segment.VisibleWorld.query (.inl (.inl input)))
  | .inr bytes => segment.visibleHashImpl high bytes

theorem erase_visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleHashImpl high bytes) = segment.hashImpl high outside bytes := by
  cases hparse : segment.parse bytes <;>
    simp only [visibleHashImpl, hashImpl, hparse, simulateQ_spec_query, simulateQ_map, PartialChainEndpoint.eraseAux]

theorem erase_visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    (PartialChainEndpoint.eraseAux outside).compose (segment.visibleWorldImpl high) = segment.worldImpl high outside := by
  funext input
  cases input with
  | inl input => simp only [QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query, PartialChainEndpoint.eraseAux, worldImpl]
  | inr bytes => exact segment.erase_visibleHashImpl high outside bytes

noncomputable def visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  simulateQ (segment.visibleWorldImpl high) (CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary)

theorem erase_visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleGame high outside ftsSecret words frontier adversary) =
      segment.game high outside ftsSecret words frontier adversary := by
  rw [visibleGame, ← QueryImpl.simulateQ_compose, erase_visibleWorldImpl, CausalFrontierProgram.prefix_game]

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

noncomputable def visibleSeedGame (endpoint : Digest) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  segment.visibleGame auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary

theorem erase_visibleSeedGame (endpoint : Digest) :
    simulateQ (PartialChainEndpoint.eraseAux (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) =
        segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [visibleSeedGame, erase_visibleGame]
  rfl

theorem visibleSeedGame_real :
    PartialChainEndpoint.realRun (fun endpoint => PartialChainEndpoint.extendAux uniformImpl
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none) =
    PartialChainEndpoint.realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none) := by
  simpa only [erase_visibleSeedGame] using
    (PartialChainEndpoint.realRun_eraseAux (fun _ => uniformImpl)
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words)
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none)).symm

end SphincsSecurity.Concrete.OtsPrefix
