import SigGolfCandidate.SphincsDynamicPadSetup
import SigGolfCandidate.SphincsMacUniformExtract

/-! Extract a whole block of adaptively located oracle answers. -/

namespace SigGolfCandidate.SphincsPadBlockUniform
open SigGolfCandidate.SphincsMacUniformExtract

noncomputable def blockUpdate {D : Type} [DecidableEq D] {n : Nat}
    (addresses : Fin n → D) (values : Fin n → BitVec 256)
    (table : D → BitVec 256) (d : D) : BitVec 256 :=
  if h : ∃ i, addresses i = d then values (Classical.choose h) else table d

theorem blockUpdate_at {D : Type} [DecidableEq D] {n : Nat}
    (addresses : Fin n → D) (hinj : Function.Injective addresses)
    (values : Fin n → BitVec 256) (table : D → BitVec 256) (i : Fin n) :
    blockUpdate addresses values table (addresses i) = values i := by
  classical
  unfold blockUpdate
  split_ifs with h
  · rw [hinj (Classical.choose_spec h)]
  · exact False.elim (h ⟨i, rfl⟩)

theorem blockUpdate_away {D : Type} [DecidableEq D] {n : Nat}
    (addresses : Fin n → D) (values : Fin n → BitVec 256)
    (table : D → BitVec 256) (d : D)
    (h : ∀ i, addresses i ≠ d) :
    blockUpdate addresses values table d = table d := by
  simp only [blockUpdate]
  split_ifs with h'
  · rcases h' with ⟨i, hi⟩
    exact False.elim (h i hi)
  · rfl

theorem blockUpdate_restore {D : Type} [DecidableEq D] {n : Nat}
    (addresses : Fin n → D) (hinj : Function.Injective addresses)
    (values : Fin n → BitVec 256)
    (table : D → BitVec 256) :
    blockUpdate addresses (fun i => table (addresses i))
      (blockUpdate addresses values table) = table := by
  funext d
  by_cases h : ∃ i, addresses i = d
  · obtain ⟨i, rfl⟩ := h
    exact blockUpdate_at addresses hinj _ _ i
  · have haway : ∀ i, addresses i ≠ d := by
      intro i hi
      exact h ⟨i, hi⟩
    rw [blockUpdate_away addresses _ _ d haway,
      blockUpdate_away addresses _ _ d haway]

noncomputable def swapBlock {D : Type} [DecidableEq D] {n : Nat}
    (addresses : (D → BitVec 256) → Fin n → D)
    (pair : (D → BitVec 256) × (Fin n → BitVec 256)) :
    (D → BitVec 256) × (Fin n → BitVec 256) :=
  (blockUpdate (addresses pair.1) pair.2 pair.1,
    fun i => pair.1 (addresses pair.1 i))

theorem swapBlock_involutive {D : Type} [DecidableEq D] {n : Nat}
    (addresses : (D → BitVec 256) → Fin n → D)
    (hinj : ∀ table, Function.Injective (addresses table))
    (hstable : ∀ table values,
      addresses (blockUpdate (addresses table) values table) = addresses table)
    (pair : (D → BitVec 256) × (Fin n → BitVec 256)) :
    swapBlock addresses (swapBlock addresses pair) = pair := by
  rcases pair with ⟨table, values⟩
  simp only [swapBlock, hstable]
  apply Prod.ext
  · exact blockUpdate_restore (addresses table) (hinj table) values table
  · funext i
    exact blockUpdate_at (addresses table) (hinj table) values table i

/-- Under stable adaptive locations, the full block of random-oracle answers
is a fresh independent uniform vector, with the programmed table retained. -/
theorem dynamic_block_answer_extraction {D State : Type} [Fintype D] [DecidableEq D]
    {n : Nat}
    (addresses : (D → BitVec 256) → Fin n → D)
    (observation : (D → BitVec 256) → State)
    (hinj : ∀ table, Function.Injective (addresses table))
    (haddresses : ∀ table values,
      addresses (blockUpdate (addresses table) values table) = addresses table)
    (hobs : ∀ table values,
      observation (blockUpdate (addresses table) values table) = observation table) :
    (PMF.uniformOfFintype (D → BitVec 256)).map
      (fun table => (observation table,
        (fun i => table (addresses table i)), table)) =
    (PMF.uniformOfFintype (D → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (Fin n → BitVec 256)).map (fun values =>
        (observation table, values, blockUpdate (addresses table) values table))) := by
  let pairLaw := PMF.uniformOfFintype ((D → BitVec 256) × (Fin n → BitVec 256))
  let encoded := fun pair : (D → BitVec 256) × (Fin n → BitVec 256) =>
    (observation pair.1, pair.2, blockUpdate (addresses pair.1) pair.2 pair.1)
  have hpoint : ∀ pair : (D → BitVec 256) × (Fin n → BitVec 256),
      encoded (swapBlock addresses pair) =
        (observation pair.1, (fun i => pair.1 (addresses pair.1 i)), pair.1) := by
    intro ⟨table, values⟩
    simp only [encoded, swapBlock, haddresses, hobs]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact blockUpdate_restore (addresses table) (hinj table) values table
  have hu : (PMF.uniformOfFintype ((D → BitVec 256) × (Fin n → BitVec 256))).map
      (swapBlock addresses) = pairLaw := by
    apply PMF.uniformOfFintype_map_of_bijective
    constructor
    · intro left right heq
      have := congrArg (swapBlock addresses) heq
      simpa only [swapBlock_involutive addresses hinj haddresses] using this
    · intro pair
      exact ⟨swapBlock addresses pair,
        swapBlock_involutive addresses hinj haddresses pair⟩
  symm
  calc
    _ = pairLaw.map encoded := by
      dsimp only [pairLaw]
      rw [← uniformPair (A := D → BitVec 256) (B := Fin n → BitVec 256)]
      rw [PMF.map_bind]
      apply congrArg ((PMF.uniformOfFintype (D → BitVec 256)).bind ·)
      funext table
      rw [PMF.map_comp]
      rfl
    _ = pairLaw.map (fun pair => encoded (swapBlock addresses pair)) := by
      calc
        _ = ((PMF.uniformOfFintype ((D → BitVec 256) × (Fin n → BitVec 256))).map
            (swapBlock addresses)).map encoded := by simpa only [pairLaw] using
              (congrArg (fun law : PMF ((D → BitVec 256) × (Fin n → BitVec 256)) =>
                law.map encoded) hu.symm)
        _ = _ := by rw [PMF.map_comp]; rfl
    _ = pairLaw.map (fun pair =>
        (observation pair.1, (fun i => pair.1 (addresses pair.1 i)), pair.1)) := by
      congr 1
      funext pair
      exact hpoint pair
    _ = _ := by
      dsimp only [pairLaw]
      rw [← uniformPair (A := D → BitVec 256) (B := Fin n → BitVec 256), PMF.map_bind]
      simp only [PMF.map_comp]
      apply congrArg ((PMF.uniformOfFintype (D → BitVec 256)).bind ·)
      funext table
      change (PMF.uniformOfFintype (Fin n → BitVec 256)).map
        (Function.const (Fin n → BitVec 256)
          (observation table, (fun i => table (addresses table i)), table)) =
            PMF.pure (observation table, (fun i => table (addresses table i)), table)
      exact PMF.map_const _ _

/-- info: 'SigGolfCandidate.SphincsPadBlockUniform.dynamic_block_answer_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dynamic_block_answer_extraction

open SigGolf SphincsSecurity
open SigGolfCandidate.SphincsPadSetupIndependence
open SigGolfCandidate.SphincsCacheSecretDomains
open SigGolfCandidate.SphincsDynamicPadSetup

theorem finiteHashAnswer_padAgree_block (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (values : Fin 4095 → BitVec 256) (table : inputs → BitVec 256) :
    PadAgree
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table)
      (SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
        (blockUpdate (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem)
          values table)) parameter seed := by
  intro input hnot
  by_cases hin : SphincsBridge.toQuery input ∈ inputs
  · rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs table _ hin (by rfl)]
    rw [SphincsOrganizerFiniteHash.finiteHashAnswer_none ∅ inputs _ _ hin (by rfl)]
    symm
    apply blockUpdate_away
    intro i heq
    have hhash := SphincsBridge.toQuery_injective (congrArg Subtype.val heq)
    exact hnot i hhash.symm
  · simp [SphincsOrganizerFiniteHash.finiteHashAnswer, hin]

theorem plaintextSetup_stable_block (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (values : Fin 4095 → BitVec 256) (table : inputs → BitVec 256) :
    plaintextSetup inputs seed
      (blockUpdate (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem)
        values table) = plaintextSetup inputs seed table := by
  let first := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs table
  let second := SphincsOrganizerFiniteHash.finiteHashAnswer ∅ inputs
    (blockUpdate (SphincsFiniteTableMasking.padAddresses inputs parameter seed hmem)
      values table)
  have hagree : PadAgree first second parameter seed :=
    finiteHashAnswer_padAgree_block inputs parameter seed hmem values table
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

theorem actual_pad_answers_fresh_joint
    (inputs : Finset SigGolf.Query) (seed : MasterSeed)
    (hpad : ∀ parameter : PublicParameter, ∀ i : Fin 4095,
      SphincsBridge.toQuery
        (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs) :
    let setup := plaintextSetup inputs seed
    let addresses := keygenPadAddresses inputs seed hpad
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table => (setup table,
        (fun i => table (addresses table i)), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (Fin 4095 → BitVec 256)).map (fun values =>
        (setup table, values, blockUpdate (addresses table) values table))) := by
  let setup := plaintextSetup inputs seed
  let addresses := keygenPadAddresses inputs seed hpad
  have hinj : ∀ table, Function.Injective (addresses table) := by
    intro table
    exact SphincsFiniteTableMasking.padAddresses_injective inputs
      (setup table).1 seed (hpad _)
  have hsetup : ∀ table values,
      setup (blockUpdate (addresses table) values table) = setup table := by
    intro table values
    exact plaintextSetup_stable_block inputs (setup table).1 seed
      (hpad _) values table
  have haddr : ∀ table values,
      addresses (blockUpdate (addresses table) values table) = addresses table := by
    intro table values
    have hp := congrArg Prod.fst (hsetup table values)
    exact padAddresses_congr_parameter inputs seed hpad _ _ hp
  exact dynamic_block_answer_extraction addresses setup hinj haddr hsetup

/-- info: 'SigGolfCandidate.SphincsPadBlockUniform.plaintextSetup_stable_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms plaintextSetup_stable_block
/-- info: 'SigGolfCandidate.SphincsPadBlockUniform.actual_pad_answers_fresh_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_pad_answers_fresh_joint
end SigGolfCandidate.SphincsPadBlockUniform
