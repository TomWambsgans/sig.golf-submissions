import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingOracleSplit
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

abbrev ReferenceSelection := Option (Fin encodingAttemptLimit × Encoding)

noncomputable def referenceTableSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) : ReferenceSelection :=
  FirstSuccessTable.select decodeEncodingOutput (fun counter =>
    readCanonicalEncodingRows key.parameter (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      f (position, counter))

def referenceSelectionResult (selection : ReferenceSelection) : Option (Counter × Encoding) × Nat :=
  (selection.map (fun result => (BitVec.ofNat counterBits result.1.val, result.2)),
    selection.elim encodingAttemptLimit (fun result => result.1.val + 1))

theorem referenceSelectionResult_eq_search (key : SecretKey) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) :
    referenceSelectionResult (referenceTableSelection key f position) =
      canonicalEncodingSearch key f position.lay position.tree position.leafIdx := by
  rw [← congrFun (canonicalEncodingResults_eq key f) position]
  simp only [canonicalEncodingResults, referenceSelectionResult, referenceTableSelection, encodingTableResult, Nat.zero_add]

theorem referenceTableSelection_joinEncodingTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      position = FirstSuccessTable.select decodeEncodingOutput
        (encoding ∘ referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position)) := by
  rw [referenceTableSelection, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  apply congrArg (FirstSuccessTable.select decodeEncodingOutput)
  funext counter
  change finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    (encodingRetryInput key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter.val) = _
  rw [finiteHashAnswer_none ∅ inputs _ _
    (hencoding (encodingRetryInput_mem_canonicalEncodingInputs _ _ _ counter)) (by simp)]
  exact UniformTableSplit.join_embed _ _ encoding outside
    (referenceCounterCell key.parameter position (outsideGraphMessage key inputs hencoding outside position) counter)

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_3 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

namespace UniformTableSplit

theorem uniform_bind_firstSuccessFamily {Index Cell Answer Value Result : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Cell] [DecidableEq Cell]
    [Fintype Answer] [DecidableEq Answer] [Nonempty Answer] [Fintype Value] {n : Nat}
    (embed : Index × Fin n → Cell) (hinj : Function.Injective embed) (decode : Answer → Option Value)
    (next : (Index → Option (Fin n × Value)) → (Cell → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Cell → Answer)).bind (fun table =>
        next (fun index => FirstSuccessTable.select decode (fun counter => table (embed (index, counter)))) table) =
      (FirstSuccessFamily.selected decode n).bind (fun results =>
        (FirstSuccessFamily.afterSelect decode n results).bind (fun rows =>
          (PMF.uniformOfFintype (Outside embed → Answer)).bind
            (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))) := by
  rw [uniform_bind_split embed hinj]
  simp only [join_embed]
  have huncurry := PMF.uniformOfFintype_map_of_bijective (Equiv.curry Index (Fin n) Answer).symm
    (Equiv.curry Index (Fin n) Answer).symm.bijective
  rw [← huncurry, PMF.bind_map]
  exact FirstSuccessFamily.uniform_bind_eq_selected decode n
    (fun results rows => (PMF.uniformOfFintype (Outside embed → Answer)).bind
      (fun outside => next results (join embed hinj (Function.uncurry rows) outside)))

end UniformTableSplit

abbrev ReferenceFamily := EncodingPosition → ReferenceSelection

noncomputable def referenceFamilyCell (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (row : EncodingRow) : canonicalEncodingInputs parameter :=
  referenceCounterCell parameter row.1 (messages row.1) row.2

theorem referenceFamilyCell_injective (parameter : PublicParameter) (messages : EncodingPosition → Digest) :
    Function.Injective (referenceFamilyCell parameter messages) := by
  rintro ⟨left, first⟩ ⟨right, second⟩ heq
  have hbytes := congrArg Subtype.val heq
  have hposition : left = right := atEncodingPosition_unique
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) left from ⟨_, rfl⟩)
    (show AtEncodingPosition parameter (encodingRetryInput parameter left (messages left) first.val) right from ⟨_, hbytes⟩)
  subst right
  exact Prod.ext rfl (referenceCounterCell_injective parameter left (messages left) heq)

noncomputable def referenceFamilyOracleTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (remaining : UniformTableSplit.Outside
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput) :
    inputs → HashOutput :=
  joinEncodingTable key.parameter inputs hencoding
    (UniformTableSplit.join
      (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside))
      (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding outside))
      (Function.uncurry rows) remaining) outside

end SphincsSecurity.Concrete
