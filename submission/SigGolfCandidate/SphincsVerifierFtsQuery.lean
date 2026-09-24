import SigGolfCandidate.SphincsVerifierFtsPayload

/-! The exact byte query issued by the first FORS leaf HASH instruction. -/

namespace SigGolfCandidate.SphincsVerifierFtsQuery
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsPayload
open SigGolfCandidate.SphincsVerifierHashBytes

def firstFtsInput (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest) : HashInput :=
  tweakableHashInput pk.parameter (.ftsLeaf index ⟨0, by decide⟩ leaf)
    (bytesLE 20 secret)

theorem firstFtsInput_eq (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest) :
    firstFtsInput pk index leaf secret =
      fieldBytes (tweakFields 9 0 index.val 0 leaf.val) ++
        bytesLE 20 pk.parameter ++ bytesLE 20 secret := by
  rfl

theorem firstFtsInput_length (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest) :
    (firstFtsInput pk index leaf secret).length = 60 := by
  simp [firstFtsInput, tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, bytesLE]

theorem firstFtsInput_header (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
    ((fieldBytes (tweakFields 9 0 index.val 0 leaf.val)).map
      UInt8.toBitVec)[i]'(by simp [fieldBytes, bytesLE]; omega) := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega)]

theorem firstFtsInput_parameter (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[20 + i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [
    List.getElem_append_left (by simp [fieldBytes, bytesLE]; omega),
    List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, fieldBytes, bytesLE]
  rfl

theorem firstFtsInput_secret (pk : SphincsSecurity.PublicKey)
    (index : Index) (leaf : FtsLeaf) (secret : Digest)
    (i : Nat) (hi : i < 20) :
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)[40 + i]'(by
      rw [List.length_map, firstFtsInput_length]; omega) =
      secret.extractLsb' (8 * i) 8 := by
  simp only [firstFtsInput_eq, List.map_append]
  rw [List.getElem_append_right (by simp [fieldBytes, bytesLE])]
  simp only [List.getElem_map, bytesLE, List.getElem_ofFn,
    UInt8.toBitVec_ofBitVec]
  simp [List.length_map, List.length_append, fieldBytes, bytesLE]
  rfl

theorem readyFirstFts_hashInput (pointers : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (witnessPrefix : WitnessPrefix pointers pk)
    (secretEncoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (layerZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43000 = 0)
    (positionZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43010 = 0)
    (treeIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43008 =
      BitVec.ofNat 64 index.val)
    (leafIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43018 =
      BitVec.ofNat 64 leaf.val) :
    hashInput (ftsHashReadyState (ftsAdvanceState (copyRootState pointers))) =
      toQuery (firstFtsInput pk index leaf secret) := by
  let advanced := ftsAdvanceState (copyRootState pointers)
  let ready := ftsHashReadyState advanced
  apply Serialization.hashInput_of_list ready 0x40000
    ((firstFtsInput pk index leaf secret).map UInt8.toBitVec)
  · exact (ftsHashReady_regs advanced).1
  · rw [(ftsHashReady_regs advanced).2.1,
      List.length_map, firstFtsInput_length]
    rfl
  · intro i hi
    have hi60 : i < 60 := by
      simpa [firstFtsInput_length] using hi
    by_cases header : i < 20
    · let byte : Fin 20 := ⟨i, header⟩
      have actual := readyHeader_bytes advanced index leaf
        layerZero positionZero treeIndex leafIndex byte
      have expected := firstFtsInput_header pk index leaf secret i header
      simpa [ready, advanced, byte] using actual.trans expected.symm
    · by_cases parameter : i < 40
      · have lower : 20 ≤ i := by omega
        have smaller : i - 20 < 20 := by omega
        have split : 20 + (i - 20) = i := by omega
        have actual := readyParameter_bytes pointers destination pk witnessPrefix
          (i - 20) smaller
        have expected := firstFtsInput_parameter pk index leaf secret
          (i - 20) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40014 + (i - 20) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined
      · have lower : 40 ≤ i := by omega
        have smaller : i - 40 < 20 := by omega
        have split : 40 + (i - 40) = i := by omega
        have actual := readySecret_bytes pointers source destination secret
          secretEncoded (i - 40) smaller
        have expected := firstFtsInput_secret pk index leaf secret
          (i - 40) smaller
        have joined := actual.trans expected.symm
        simp only [split] at joined
        have address : 0x40028 + (i - 40) = 0x40000 + i := by omega
        rw [address] at joined
        simpa only [ready, advanced] using joined

theorem readyFirstFts_hashStep (hash : Hash) (pointers : MachineState)
    (pk : SphincsSecurity.PublicKey) (index : Index)
    (leaf : FtsLeaf) (secret : Digest)
    (pc : pointers.pc = 0x17c4)
    (source : pointers.getReg .x6 = 0x22cdc)
    (destination : pointers.getReg .x7 = 0x40028)
    (witnessPrefix : WitnessPrefix pointers pk)
    (secretEncoded : ∀ i, (hi : i < 20) →
      pointers.getByte (BitVec.ofNat 64 (0x22cdc + i)) =
        secret.extractLsb' (8 * i) 8)
    (layerZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43000 = 0)
    (positionZero : (ftsAdvanceState (copyRootState pointers)).getMem 0x43010 = 0)
    (treeIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43008 =
      BitVec.ofNat 64 index.val)
    (leafIndex : (ftsAdvanceState (copyRootState pointers)).getMem 0x43018 =
      BitVec.ofNat 64 leaf.val)
    (steps : Nat) (result : Execution)
    (tail : Executes hash SphincsImages.verify
      (writeHash (ftsHashReadyState (ftsAdvanceState (copyRootState pointers)))
        (hash (toQuery (firstFtsInput pk index leaf secret)))) steps result) :
    Executes hash SphincsImages.verify
      (ftsHashReadyState (ftsAdvanceState (copyRootState pointers)))
      (steps + 1) (result.charge 8 1 1) := by
  let copied := copyRootState pointers
  let advanced := ftsAdvanceState copied
  let ready := ftsHashReadyState advanced
  have copiedPc := SphincsVerifierFtsLeafCopy.ftsLeafCopy_pc pointers pc
  have advancedPc := ftsAdvance_pc copied copiedPc
  have readyPc := ftsHashReady_pc advanced advancedPc
  have regs := ftsHashReady_regs advanced
  have query := readyFirstFts_hashInput pointers pk index leaf secret
    source destination witnessPrefix secretEncoded layerZero positionZero
    treeIndex leafIndex
  have tail' : Executes hash SphincsImages.verify
      (writeHash ready (hash (hashInput ready))) steps result := by
    rw [query]
    exact tail
  exact SphincsVerifierFtsHash.hash_step hash ready readyPc
    regs.1 regs.2.1 regs.2.2.1 regs.2.2.2 steps result tail'

/-- info: 'SigGolfCandidate.SphincsVerifierFtsQuery.readyFirstFts_hashInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyFirstFts_hashInput

/-- info: 'SigGolfCandidate.SphincsVerifierFtsQuery.readyFirstFts_hashStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms readyFirstFts_hashStep

end SigGolfCandidate.SphincsVerifierFtsQuery
