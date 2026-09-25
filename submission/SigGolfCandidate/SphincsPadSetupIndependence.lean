import SigGolfCandidate.SphincsFiniteTableMasking
import SigGolfCandidate.SphincsSecurity.Completeness.Fresh
import SigGolfCandidate.SphincsMaskedKeygenRefinement

/-! The plaintext keygen values never query tag-14 pad coordinates. -/

namespace SigGolfCandidate.SphincsPadSetupIndependence
open SigGolf OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

theorem eval_eq_of_agree_on_path {α : Type} (computation : OracleComp SphincsSecurity.HashSpec α)
    (f g : QueryImpl SphincsSecurity.HashSpec Id)
    (hagree : ∀ input, input ∈ queriedInputs f computation → f input = g input) :
    evalWithAnswerFn f computation = evalWithAnswerFn g computation := by
  induction computation using OracleComp.inductionOn generalizing f g with
  | pure value => rfl
  | query_bind input next ih =>
      have hinput : f input = g input :=
        hagree input (by simp [queriedInputs_query_bind])
      have hf : evalWithAnswerFn f (liftM (SphincsSecurity.HashSpec.query input)) =
          f input := simulateQ_spec_query f input
      have hg : evalWithAnswerFn g (liftM (SphincsSecurity.HashSpec.query input)) =
          g input := simulateQ_spec_query g input
      simp only [evalWithAnswerFn_bind, hf, hg]
      rw [hinput]
      apply ih (g input) f g
      intro row hrow
      apply hagree row
      simp only [queriedInputs_query_bind]
      exact List.mem_cons_of_mem _ (hinput ▸ hrow)

def PadAgree (first second : SigGolf.Hash) (parameter : PublicParameter)
    (seed : MasterSeed) : Prop :=
  ∀ input : HashInput,
    (∀ i : Fin 4095, input ≠ padInput parameter seed (BitVec.ofNat 32 i.val)) →
    first (SphincsBridge.toQuery input) = second (SphincsBridge.toQuery input)

theorem eval_eq_of_avoids_pads {α : Type} (computation : OracleComp SphincsSecurity.HashSpec α)
    (first second : SigGolf.Hash) (parameter : PublicParameter)
    (seed : MasterSeed) (hagree : PadAgree first second parameter seed)
    (havoid : ∀ i : Fin 4095,
      SphincsSecurity.Completeness.Avoids (SphincsBridge.adaptOracle first)
        (padInput parameter seed (BitVec.ofNat 32 i.val)) computation) :
    evalWithAnswerFn (SphincsBridge.adaptOracle first) computation =
      evalWithAnswerFn (SphincsBridge.adaptOracle second) computation := by
  apply eval_eq_of_agree_on_path
  intro input hquery
  apply hagree input
  intro i heq
  exact havoid i (heq ▸ hquery)

theorem treeNode_avoids_pad (hash : SigGolf.Hash)
    (actualParameter padParameter : PublicParameter)
    (actualSeed padSeed : MasterSeed) (index : Fin 4095)
    (level node : Nat) :
    SphincsSecurity.Completeness.Avoids (SphincsBridge.adaptOracle hash)
      (padInput padParameter padSeed (BitVec.ofNat 32 index.val))
      (Seeded.treeNode actualParameter topLayer Concrete.rootTree actualSeed level node) := by
  apply SphincsSecurity.Completeness.Avoids.treeNode
  · intro leaf chain step payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.chain topLayer Concrete.rootTree leaf chain step) payload).symm
  · intro leaf payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.leaf topLayer Concrete.rootTree leaf) payload).symm
  · intro level node payload
    exact (padInput_ne_tweakableHashInput padParameter actualParameter padSeed
      (BitVec.ofNat 32 index.val) (.node topLayer Concrete.rootTree level node) payload).symm
  · intro leaf chain
    exact (padInput_ne_keygenHashInput padParameter actualParameter padSeed actualSeed
      (BitVec.ofNat 32 index.val) (.ots topLayer Concrete.rootTree leaf chain)).symm

theorem treeValue_eq_of_padAgree (first second : SigGolf.Hash)
    (actualParameter padParameter : PublicParameter)
    (actualSeed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed)
    (level node : Nat) :
    SphincsMaskedParentLevels.treeValue first actualParameter actualSeed level node =
      SphincsMaskedParentLevels.treeValue second actualParameter actualSeed level node := by
  unfold SphincsMaskedParentLevels.treeValue
  apply eval_eq_of_avoids_pads _ first second padParameter padSeed hagree
  intro index
  exact treeNode_avoids_pad first actualParameter padParameter actualSeed padSeed index level node

theorem parameter_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.parameter first seed =
      SphincsMaskedKeygenRefinement.parameter second seed := by
  unfold SphincsMaskedKeygenRefinement.parameter
  congr 1
  apply hagree
  intro index heq
  exact padInput_ne_keygenHashInput padParameter 0 padSeed seed
    (BitVec.ofNat 32 index.val) .parameter heq.symm

theorem root_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.root first seed =
      SphincsMaskedKeygenRefinement.root second seed := by
  have hparameter := parameter_eq_of_padAgree first second padParameter seed padSeed hagree
  calc
    SphincsMaskedKeygenRefinement.root first seed =
        SphincsMaskedParentLevels.treeValue first
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 := rfl
    _ = SphincsMaskedParentLevels.treeValue second
          (SphincsMaskedKeygenRefinement.parameter first seed) seed
          (layerHeight topLayer) 0 :=
      treeValue_eq_of_padAgree first second _ padParameter seed padSeed hagree _ _
    _ = SphincsMaskedKeygenRefinement.root second seed := by rw [hparameter]; rfl

theorem publicKey_eq_of_padAgree (first second : SigGolf.Hash)
    (padParameter : PublicParameter) (seed padSeed : MasterSeed)
    (hagree : PadAgree first second padParameter padSeed) :
    SphincsMaskedKeygenRefinement.publicKey first seed =
      SphincsMaskedKeygenRefinement.publicKey second seed := by
  have hparameter := parameter_eq_of_padAgree first second padParameter seed padSeed hagree
  have hroot := root_eq_of_padAgree first second padParameter seed padSeed hagree
  unfold SphincsMaskedKeygenRefinement.publicKey
  rw [hroot, hparameter]
  have hhash : first (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) =
      second (SphincsBridge.toQuery (SphincsWire.commitmentInput
        ⟨SphincsMaskedKeygenRefinement.root second seed,
          SphincsMaskedKeygenRefinement.parameter second seed⟩)) := by
    apply hagree
    intro index heq
    exact padInput_ne_commitmentInput padParameter padSeed
      (BitVec.ofNat 32 index.val)
      ⟨SphincsMaskedKeygenRefinement.root second seed,
        SphincsMaskedKeygenRefinement.parameter second seed⟩ heq.symm
  exact congrArg (fun output : BitVec 256 => output.extractLsb' 0 128) hhash

theorem finiteHashAnswer_padAgree (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256) :
    PadAgree
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table)
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
        (SphincsFiniteTableMasking.xorTable
          (SphincsFiniteTableMasking.nodeMask
            (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table))
      parameter seed := by
  intro input hnot
  by_cases hin : SphincsBridge.toQuery input ∈ inputs
  · rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _ hin (by rfl)]
    rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs _ _ hin (by rfl)]
    symm
    apply SphincsFiniteTableMasking.xorTable_away
    intro i heq
    have hhash := SphincsBridge.toQuery_injective (congrArg Subtype.val heq)
    exact hnot i hhash.symm
  · simp [SphincsOrganizerFiniteHash.finiteHashAnswer, hin]

noncomputable def plaintextSetup (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (table : inputs → BitVec 256) :
    Digest × SigGolf.PublicKey × (Nat → Nat → Digest) :=
  let hash := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  (SphincsMaskedKeygenRefinement.parameter hash seed,
    SphincsMaskedKeygenRefinement.publicKey hash seed,
    fun level node =>
      SphincsMaskedParentLevels.treeValue hash
        (SphincsMaskedKeygenRefinement.parameter hash seed) seed level node)

theorem plaintextSetup_stable (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256) :
    plaintextSetup inputs seed
      (SphincsFiniteTableMasking.xorTable
        (SphincsFiniteTableMasking.nodeMask
          (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table) =
      plaintextSetup inputs seed table := by
  let first := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  let second := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
    (SphincsFiniteTableMasking.xorTable
      (SphincsFiniteTableMasking.nodeMask
        (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem) nodes) table)
  have hagree : PadAgree first second parameter seed :=
    finiteHashAnswer_padAgree inputs parameter seed hmem nodes table
  have hparameter := parameter_eq_of_padAgree first second parameter seed seed hagree
  have hpublic := publicKey_eq_of_padAgree first second parameter seed seed hagree
  dsimp only [plaintextSetup]
  apply Prod.ext
  · exact hparameter.symm
  · apply Prod.ext
    · exact hpublic.symm
    · funext level node
      rw [hparameter]
      exact (treeValue_eq_of_padAgree first second
        (SphincsMaskedKeygenRefinement.parameter second seed)
        parameter seed seed hagree level node).symm

end SigGolfCandidate.SphincsPadSetupIndependence

/-- info: 'SigGolfCandidate.SphincsPadSetupIndependence.eval_eq_of_avoids_pads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsPadSetupIndependence.eval_eq_of_avoids_pads
