import SigGolfCandidate.SphincsOrganizerFiniteHash
import SigGolfCandidate.SphincsCacheSecretDomains
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.TableSampling
import SigGolfCandidate.SphincsBridge

/-! Reparameterize a complete finite random-oracle table by an XOR mask.
The whole table is preserved in the distributional identity, so later oracle
queries can be coupled to the transformed setup. -/

namespace SigGolfCandidate.SphincsFiniteTableMasking
open SigGolf OracleComp
open SphincsSecurity
open SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false

def xorTable {inputs : Finset SigGolf.Query}
    (mask table : inputs → BitVec 256) : inputs → BitVec 256 :=
  fun input => table input ^^^ mask input

theorem xorTable_involutive {inputs : Finset SigGolf.Query}
    (mask table : inputs → BitVec 256) :
    xorTable mask (xorTable mask table) = table := by
  funext input
  simp [xorTable, BitVec.xor_assoc]

theorem xorTable_bijective {inputs : Finset SigGolf.Query}
    (mask : inputs → BitVec 256) :
    Function.Bijective (xorTable mask) := by
  constructor
  · intro left right heq
    have := congrArg (xorTable mask) heq
    simpa only [xorTable_involutive] using this
  · intro table
    exact ⟨xorTable mask table, xorTable_involutive mask table⟩

/-- Full 256-bit answer words and every unrelated oracle coordinate retain
their joint uniform law after a setup-dependent mask. -/
theorem uniform_xorTable {inputs : Finset SigGolf.Query}
    (mask : inputs → BitVec 256) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map (xorTable mask) =
      PMF.uniformOfFintype (inputs → BitVec 256) :=
  PMF.uniformOfFintype_map_of_bijective _ (xorTable_bijective mask)

theorem state_dependent_xorTable {State : Type}
    (inputs : Finset SigGolf.Query) (prior : PMF State)
    (mask : State → inputs → BitVec 256) :
    prior.bind (fun state =>
      (PMF.uniformOfFintype (inputs → BitVec 256)).map
        (fun table => (state, xorTable (mask state) table))) =
    prior.bind (fun state =>
      (PMF.uniformOfFintype (inputs → BitVec 256)).map
        (fun table => (state, table))) := by
  apply congrArg (prior.bind ·)
  funext state
  have h := uniform_xorTable (mask state)
  calc
    _ = ((PMF.uniformOfFintype (inputs → BitVec 256)).map
          (xorTable (mask state))).map (fun table => (state, table)) := by
        rw [PMF.map_comp]
        rfl
    _ = _ := congrArg
      (fun law : PMF (inputs → BitVec 256) =>
        law.map (fun table => (state, table))) h

/-- A mask changes the low 160 bits at selected, pairwise distinct oracle
coordinates. It keeps all high bits and every other answer unchanged. -/
noncomputable def nodeMask {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : Fin n → inputs) (nodes : Fin n → Digest)
    (input : inputs) : BitVec 256 :=
  if h : ∃ i, addresses i = input then
    outputHalves.symm (nodes (Classical.choose h), 0)
  else 0

theorem nodeMask_at {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : Fin n → inputs) (nodes : Fin n → Digest)
    (hinj : Function.Injective addresses) (i : Fin n) :
    nodeMask addresses nodes (addresses i) = outputHalves.symm (nodes i, 0) := by
  classical
  unfold nodeMask
  have h : ∃ j, addresses j = addresses i := ⟨i, rfl⟩
  simp only [dif_pos h]
  have hchosen : Classical.choose h = i := hinj (Classical.choose_spec h)
  rw [hchosen]

theorem nodeMask_away {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : Fin n → inputs) (nodes : Fin n → Digest)
    (input : inputs) (h : ∀ i, addresses i ≠ input) :
    nodeMask addresses nodes input = 0 := by
  unfold nodeMask
  simp only [dif_neg (not_exists.mpr h)]

theorem xorTable_away {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : Fin n → inputs) (nodes : Fin n → Digest)
    (table : inputs → BitVec 256) (input : inputs)
    (h : ∀ i, addresses i ≠ input) :
    xorTable (nodeMask addresses nodes) table input = table input := by
  simp [xorTable, nodeMask_away addresses nodes input h]

theorem truncated_xorTable_at {n : Nat} {inputs : Finset SigGolf.Query}
    (addresses : Fin n → inputs) (nodes : Fin n → Digest)
    (hinj : Function.Injective addresses) (table : inputs → BitVec 256)
    (i : Fin n) :
    truncateHash (xorTable (nodeMask addresses nodes) table (addresses i)) =
      truncateHash (table (addresses i)) ^^^ nodes i := by
  simp only [xorTable, nodeMask_at addresses nodes hinj i]
  rw [truncateHash, BitVec.extractLsb'_xor]
  exact congrArg (fun value : Digest => truncateHash (table (addresses i)) ^^^ value)
    (truncate_from_halves (nodes i) 0)

def padAddresses (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
          (BitVec.ofNat 32 i.val)) ∈ inputs) : Fin 4095 → inputs :=
  fun i => ⟨SigGolfCandidate.SphincsBridge.toQuery
    (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
      (BitVec.ofNat 32 i.val)), hmem i⟩

theorem padAddresses_injective (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
          (BitVec.ofNat 32 i.val)) ∈ inputs) :
    Function.Injective (padAddresses inputs parameter seed hmem) := by
  intro i j h
  have hinput := congrArg Subtype.val h
  have hpad := SigGolfCandidate.SphincsBridge.toQuery_injective hinput
  have hindex := SigGolfCandidate.SphincsCacheSecretDomains.padInput_injective_node
    parameter seed hpad
  apply Fin.ext
  have hnat := congrArg BitVec.toNat hindex
  simp only [BitVec.toNat_ofNat] at hnat
  have hi : i.val < 2 ^ 32 := by omega
  have hj : j.val < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hnat
  exact hnat

theorem padAddresses_ne_mac (inputs : Finset SigGolf.Query)
    (parameter p : PublicParameter) (seed s : MasterSeed)
    (ciphertext : HashInput)
    (hmem : ∀ i : Fin 4095,
      SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
          (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : SigGolfCandidate.SphincsBridge.toQuery
      (SigGolfCandidate.SphincsCacheSecretDomains.macInput p s ciphertext) ∈ inputs)
    (i : Fin 4095) :
    padAddresses inputs parameter seed hmem i ≠
      ⟨SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.macInput p s ciphertext), hmac⟩ := by
  intro h
  have hinput := congrArg Subtype.val h
  have hhash := SigGolfCandidate.SphincsBridge.toQuery_injective hinput
  exact SigGolfCandidate.SphincsCacheSecretDomains.padInput_ne_macInput
    parameter p seed s (BitVec.ofNat 32 i.val) ciphertext hhash

theorem pad_table_mac_unchanged (inputs : Finset SigGolf.Query)
    (parameter p : PublicParameter) (seed s : MasterSeed)
    (ciphertext : HashInput)
    (hmem : ∀ i : Fin 4095,
      SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
          (BitVec.ofNat 32 i.val)) ∈ inputs)
    (hmac : SigGolfCandidate.SphincsBridge.toQuery
      (SigGolfCandidate.SphincsCacheSecretDomains.macInput p s ciphertext) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256) :
    xorTable (nodeMask (padAddresses inputs parameter seed hmem) nodes) table
      ⟨SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.macInput p s ciphertext), hmac⟩ =
      table ⟨SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.macInput p s ciphertext), hmac⟩ := by
  apply xorTable_away
  intro i
  exact padAddresses_ne_mac inputs parameter p seed s ciphertext hmem hmac i

theorem pad_table_cipher_identity (inputs : Finset SigGolf.Query)
    (parameter : PublicParameter) (seed : MasterSeed)
    (hmem : ∀ i : Fin 4095,
      SigGolfCandidate.SphincsBridge.toQuery
        (SigGolfCandidate.SphincsCacheSecretDomains.padInput parameter seed
          (BitVec.ofNat 32 i.val)) ∈ inputs)
    (nodes : Fin 4095 → Digest) (table : inputs → BitVec 256)
    (i : Fin 4095) :
    truncateHash
      (xorTable (nodeMask (padAddresses inputs parameter seed hmem) nodes) table
        (padAddresses inputs parameter seed hmem i)) =
      truncateHash (table (padAddresses inputs parameter seed hmem i)) ^^^ nodes i :=
  truncated_xorTable_at (padAddresses inputs parameter seed hmem) nodes
    (padAddresses_injective inputs parameter seed hmem) table i

/-- This transform is valid even when the plaintext nodes depend on the
random oracle, provided they depend only on answers outside the pad slots. -/
noncomputable def setupMaskTransform {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query} (addresses : Fin n → inputs)
    (setup : (inputs → BitVec 256) → State)
    (nodes : State → Fin n → Digest) (table : inputs → BitVec 256) :
    inputs → BitVec 256 :=
  xorTable (nodeMask addresses (nodes (setup table))) table

theorem setupMaskTransform_involutive {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query} (addresses : Fin n → inputs)
    (setup : (inputs → BitVec 256) → State)
    (nodes : State → Fin n → Digest)
    (hstable : ∀ table,
      setup (setupMaskTransform addresses setup nodes table) = setup table)
    (table : inputs → BitVec 256) :
    setupMaskTransform addresses setup nodes
      (setupMaskTransform addresses setup nodes table) = table := by
  have hs : setup (xorTable (nodeMask addresses (nodes (setup table))) table) =
      setup table := by
    simpa only [setupMaskTransform] using hstable table
  simp only [setupMaskTransform]
  rw [hs]
  exact xorTable_involutive (nodeMask addresses (nodes (setup table))) table

theorem uniform_setupMaskTransform {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query} (addresses : Fin n → inputs)
    (setup : (inputs → BitVec 256) → State)
    (nodes : State → Fin n → Digest)
    (hstable : ∀ table,
      setup (setupMaskTransform addresses setup nodes table) = setup table) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (setupMaskTransform addresses setup nodes) =
        PMF.uniformOfFintype (inputs → BitVec 256) := by
  apply PMF.uniformOfFintype_map_of_bijective
  constructor
  · intro left right heq
    have := congrArg (setupMaskTransform addresses setup nodes) heq
    simpa only [setupMaskTransform_involutive addresses setup nodes hstable] using this
  · intro table
    exact ⟨setupMaskTransform addresses setup nodes table,
      setupMaskTransform_involutive addresses setup nodes hstable table⟩

/-- Joint law of the public setup, ciphertext pad words, and the complete
oracle table. The table in the right-hand game is programmed at precisely the
pad slots; all other coordinates, including MAC, remain available unchanged. -/
theorem joint_setup_cipher_table {State : Type} {n : Nat}
    {inputs : Finset SigGolf.Query} (addresses : Fin n → inputs)
    (hinj : Function.Injective addresses)
    (setup : (inputs → BitVec 256) → State)
    (nodes : State → Fin n → Digest)
    (hstable : ∀ table,
      setup (setupMaskTransform addresses setup nodes table) = setup table) :
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        (setup table,
          (fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i),
          table)) =
    (PMF.uniformOfFintype (inputs → BitVec 256)).map
      (fun table =>
        (setup table,
          (fun i => truncateHash (table (addresses i))),
          setupMaskTransform addresses setup nodes table)) := by
  let transform := setupMaskTransform addresses setup nodes
  let target := fun table : inputs → BitVec 256 =>
    (setup table, (fun i => truncateHash (table (addresses i))), transform table)
  have hpoint : ∀ table : inputs → BitVec 256,
      (setup table,
        (fun i => truncateHash (table (addresses i)) ^^^ nodes (setup table) i),
        table) = target (transform table) := by
    intro table
    dsimp only [target, transform]
    apply Prod.ext
    · exact (hstable table).symm
    · apply Prod.ext
      · funext i
        exact (truncated_xorTable_at addresses (nodes (setup table)) hinj table i).symm
      · exact (setupMaskTransform_involutive addresses setup nodes hstable table).symm
  calc
    _ = (PMF.uniformOfFintype (inputs → BitVec 256)).map
        (fun table => target (transform table)) := by
          congr 1
          funext table
          exact hpoint table
    _ = ((PMF.uniformOfFintype (inputs → BitVec 256)).map transform).map target := by
          rw [PMF.map_comp]
          rfl
    _ = _ := by
          rw [uniform_setupMaskTransform addresses setup nodes hstable]

end SigGolfCandidate.SphincsFiniteTableMasking

/-- info: 'SigGolfCandidate.SphincsFiniteTableMasking.uniform_xorTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsFiniteTableMasking.uniform_xorTable

/-- info: 'SigGolfCandidate.SphincsFiniteTableMasking.state_dependent_xorTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsFiniteTableMasking.state_dependent_xorTable

/-- info: 'SigGolfCandidate.SphincsFiniteTableMasking.pad_table_mac_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsFiniteTableMasking.pad_table_mac_unchanged

/-- info: 'SigGolfCandidate.SphincsFiniteTableMasking.pad_table_cipher_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsFiniteTableMasking.pad_table_cipher_identity

/-- info: 'SigGolfCandidate.SphincsFiniteTableMasking.joint_setup_cipher_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsFiniteTableMasking.joint_setup_cipher_table
