import SigGolfCandidate.SphincsPadSetupIndependence

/-! A dynamic, but stable, oracle coordinate is uniformly fresh. -/

namespace SigGolfCandidate.SphincsMacUniformExtract
open SigGolf OracleComp
open SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

set_option linter.style.haveILetI false in
theorem uniformPair {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (PMF.uniformOfFintype A).bind (fun a =>
      (PMF.uniformOfFintype B).map (fun b => (a, b))) =
      PMF.uniformOfFintype (A × B) := by
  classical
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq B := Classical.decEq B
  apply PMF.ext
  intro pair
  rw [PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply, PMF.map_apply]
  rcases pair with ⟨pa, pb⟩
  simp only [tsum_fintype, Prod.mk.injEq, Fintype.card_prod]
  have hinner (a : A) :
      (∑ b : B, if pa = a ∧ pb = b then ((Fintype.card B : ENNReal)⁻¹) else 0) =
        if pa = a then ((Fintype.card B : ENNReal)⁻¹) else 0 := by
    by_cases h : pa = a
    · subst a
      simp
    · simp [h]
  simp_rw [hinner]
  simp [Nat.cast_mul, ENNReal.mul_inv]

def swapDynamic {D : Type} [DecidableEq D]
    (index : (D → BitVec 256) → D)
    (pair : (D → BitVec 256) × BitVec 256) :
    (D → BitVec 256) × BitVec 256 :=
  (Function.update pair.1 (index pair.1) pair.2,
    pair.1 (index pair.1))

theorem swapDynamic_involutive {D : Type} [DecidableEq D]
    (index : (D → BitVec 256) → D)
    (hstable : ∀ table answer,
      index (Function.update table (index table) answer) = index table)
    (pair : (D → BitVec 256) × BitVec 256) :
    swapDynamic index (swapDynamic index pair) = pair := by
  rcases pair with ⟨table, answer⟩
  have hindex := hstable table answer
  simp only [swapDynamic, hindex, Function.update_self]
  congr 1
  funext row
  by_cases hrow : row = index table
  · subst row
    simp
  · simp [hrow]

theorem uniform_swapDynamic {D : Type} [Fintype D] [DecidableEq D]
    (index : (D → BitVec 256) → D)
    (hstable : ∀ table answer,
      index (Function.update table (index table) answer) = index table) :
    (PMF.uniformOfFintype ((D → BitVec 256) × BitVec 256)).map
      (swapDynamic index) =
        PMF.uniformOfFintype ((D → BitVec 256) × BitVec 256) := by
  apply PMF.uniformOfFintype_map_of_bijective
  constructor
  · intro left right heq
    have := congrArg (swapDynamic index) heq
    simpa only [swapDynamic_involutive index hstable] using this
  · intro pair
    exact ⟨swapDynamic index pair, swapDynamic_involutive index hstable pair⟩

/-- Expose one adaptively selected MAC answer as an independent uniform word,
while returning a full oracle table programmed at that selected address. -/
theorem dynamic_answer_extraction {D State : Type}
    [Fintype D] [DecidableEq D]
    (index : (D → BitVec 256) → D)
    (observation : (D → BitVec 256) → State)
    (hindex : ∀ table answer,
      index (Function.update table (index table) answer) = index table)
    (hobs : ∀ table answer,
      observation (Function.update table (index table) answer) = observation table) :
    (PMF.uniformOfFintype (D → BitVec 256)).map
      (fun table => (observation table, table (index table), table)) =
    (PMF.uniformOfFintype (D → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        (observation table, answer, Function.update table (index table) answer))) := by
  let pairLaw := PMF.uniformOfFintype ((D → BitVec 256) × BitVec 256)
  let encoded := fun pair : (D → BitVec 256) × BitVec 256 =>
    (observation pair.1, pair.2,
      Function.update pair.1 (index pair.1) pair.2)
  have hpoint : ∀ pair : (D → BitVec 256) × BitVec 256,
      encoded (swapDynamic index pair) =
        (observation pair.1, pair.1 (index pair.1), pair.1) := by
    intro ⟨table, answer⟩
    simp only [encoded, swapDynamic, hindex, hobs]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext row
        by_cases hrow : row = index table
        · subst row
          simp
        · simp [hrow]
  symm
  calc
    _ = pairLaw.map encoded := by
      dsimp only [pairLaw]
      rw [← uniformPair (A := D → BitVec 256) (B := BitVec 256)]
      rw [PMF.map_bind]
      apply congrArg ((PMF.uniformOfFintype (D → BitVec 256)).bind ·)
      funext table
      rw [PMF.map_comp]
      rfl
    _ = pairLaw.map (fun pair => encoded (swapDynamic index pair)) := by
      have hu := congrArg
        (fun law : PMF ((D → BitVec 256) × BitVec 256) => law.map encoded)
        (uniform_swapDynamic index hindex).symm
      calc
        _ = ((PMF.uniformOfFintype ((D → BitVec 256) × BitVec 256)).map
            (swapDynamic index)).map encoded := by
              simpa only [pairLaw] using hu
        _ = _ := by rw [PMF.map_comp]; rfl
    _ = pairLaw.map (fun pair =>
        (observation pair.1, pair.1 (index pair.1), pair.1)) := by
      congr 1
      funext pair
      exact hpoint pair
    _ = _ := by
      dsimp only [pairLaw]
      rw [← uniformPair (A := D → BitVec 256) (B := BitVec 256), PMF.map_bind]
      simp only [PMF.map_comp]
      apply congrArg ((PMF.uniformOfFintype (D → BitVec 256)).bind ·)
      funext table
      change (PMF.uniformOfFintype (BitVec 256)).map
        (Function.const (BitVec 256) (observation table, table (index table), table)) =
          PMF.pure (observation table, table (index table), table)
      exact PMF.map_const _ _

noncomputable def ciphertextNodes (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (table : inputs → BitVec 256) : Fin 4095 → Digest :=
  fun i =>
    truncateHash (table (SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad i)) ^^^
      SphincsPadSetupIndependence.plaintextNodes coordinates
        (SphincsPadSetupIndependence.plaintextSetup inputs seed table) i

noncomputable def chosenMacAddress (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (encode : (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery (macInput parameter seed (encode cipher)) ∈ inputs)
    (table : inputs → BitVec 256) : inputs :=
  ⟨SphincsBridge.toQuery
    (macInput parameter seed (encode (ciphertextNodes inputs parameter seed hpad coordinates table))),
    hmac _⟩

theorem plaintext_and_ciphertext_stable_at_mac
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter) (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (encode : (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery (macInput parameter seed (encode cipher)) ∈ inputs)
    (table : inputs → BitVec 256) (answer : BitVec 256) :
    let updated := Function.update table
      (chosenMacAddress inputs parameter seed hpad coordinates encode hmac table) answer
    SphincsPadSetupIndependence.plaintextSetup inputs seed updated =
      SphincsPadSetupIndependence.plaintextSetup inputs seed table ∧
    ciphertextNodes inputs parameter seed hpad coordinates updated =
      ciphertextNodes inputs parameter seed hpad coordinates table := by
  let cipher := ciphertextNodes inputs parameter seed hpad coordinates table
  let mac := chosenMacAddress inputs parameter seed hpad coordinates encode hmac table
  have hsetup : SphincsPadSetupIndependence.plaintextSetup inputs seed
      (Function.update table mac answer) =
      SphincsPadSetupIndependence.plaintextSetup inputs seed table := by
    exact SphincsPadSetupIndependence.plaintextSetup_stable_mac_update
      inputs parameter seed (encode cipher) (hmac cipher) table answer
  constructor
  · exact hsetup
  · funext i
    have hne : SphincsFiniteTableMasking.padAddresses inputs parameter seed hpad i ≠ mac := by
      exact SphincsFiniteTableMasking.padAddresses_ne_mac
        inputs parameter parameter seed seed (encode cipher) hpad (hmac cipher) i
    simp only [ciphertextNodes]
    rw [Function.update_of_ne hne, hsetup]

theorem plaintext_mac_fresh_joint
    (inputs : Finset SigGolf.Query) (parameter : PublicParameter) (seed : MasterSeed)
    (hpad : ∀ i : Fin 4095,
      SphincsBridge.toQuery (padInput parameter seed (BitVec.ofNat 32 i.val)) ∈ inputs)
    (coordinates : Fin 4095 → Nat × Nat)
    (encode : (Fin 4095 → Digest) → HashInput)
    (hmac : ∀ cipher : Fin 4095 → Digest,
      SphincsBridge.toQuery (macInput parameter seed (encode cipher)) ∈ inputs) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map (fun table =>
      (SphincsPadSetupIndependence.plaintextSetup inputs seed table,
        ciphertextNodes inputs parameter seed hpad coordinates table,
        table (chosenMacAddress inputs parameter seed hpad coordinates encode hmac table), table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).bind (fun table =>
      (PMF.uniformOfFintype (BitVec 256)).map (fun answer =>
        (SphincsPadSetupIndependence.plaintextSetup inputs seed table,
          ciphertextNodes inputs parameter seed hpad coordinates table,
          answer,
          Function.update table
            (chosenMacAddress inputs parameter seed hpad coordinates encode hmac table) answer))) := by
  let index := chosenMacAddress inputs parameter seed hpad coordinates encode hmac
  let observation := fun table : inputs → BitVec 256 =>
    (SphincsPadSetupIndependence.plaintextSetup inputs seed table,
      ciphertextNodes inputs parameter seed hpad coordinates table)
  have hstable : ∀ table answer,
      observation (Function.update table (index table) answer) = observation table := by
    intro table answer
    exact Prod.ext
      (plaintext_and_ciphertext_stable_at_mac inputs parameter seed hpad
        coordinates encode hmac table answer).1
      (plaintext_and_ciphertext_stable_at_mac inputs parameter seed hpad
        coordinates encode hmac table answer).2
  have hindex : ∀ table answer,
      index (Function.update table (index table) answer) = index table := by
    intro table answer
    apply Subtype.ext
    exact congrArg (fun cipher => SphincsBridge.toQuery
      (macInput parameter seed (encode cipher)))
      (plaintext_and_ciphertext_stable_at_mac inputs parameter seed hpad
        coordinates encode hmac table answer).2
  let flatten : ((Digest × SigGolf.PublicKey × (Nat → Nat → Digest)) ×
        (Fin 4095 → Digest)) × BitVec 256 × (inputs → BitVec 256) →
      (Digest × SigGolf.PublicKey × (Nat → Nat → Digest)) ×
        (Fin 4095 → Digest) × BitVec 256 × (inputs → BitVec 256) :=
    fun result => (result.1.1, result.1.2, result.2.1, result.2.2)
  have h := congrArg (PMF.map flatten)
    (dynamic_answer_extraction index observation hindex hstable)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at h
  simpa only [flatten, observation, index] using h

end SigGolfCandidate.SphincsMacUniformExtract

/-- info: 'SigGolfCandidate.SphincsMacUniformExtract.dynamic_answer_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsMacUniformExtract.dynamic_answer_extraction

/-- info: 'SigGolfCandidate.SphincsMacUniformExtract.plaintext_mac_fresh_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsMacUniformExtract.plaintext_mac_fresh_joint
