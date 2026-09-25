import SigGolfCandidate.SphincsMaskedSignRootDecrypt
import SigGolfCandidate.SphincsMaskedMaskSemantics
import SigGolfCandidate.SphincsVerifierFtsGenericBytes
import SigGolfCandidate.SphincsMaskedKeygenRefinement

namespace SigGolfCandidate.SphincsMaskedSignRootValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsMaskedSignRootPad SphincsMaskedSignRootPadDomain
open SphincsMaskedSignRootDecrypt
open SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsSecurity SphincsMaskedMaskSemantics
open SphincsVerifierFtsGenericBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Selecting the pad's top-tree address leaves the masked root untouched. -/
theorem init_root_word (s : MachineState) (i : Fin 5) :
    (init s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  fin_cases i <;>
    simp [init,runSchedule,initSchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.getWord32,alignToDword,byteOffset]

/-- The root-pad query preparation does not modify the masked root in the cache. -/
theorem padPrepare_root_word (s : MachineState) (i : Fin 5) :
    (padPrepare s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  fin_cases i <;>
    simp [padPrepare,runSchedule,padSchedule,
      SphincsMaskedMaskCode.prepareSchedule,execInstrBr,signExtend12,
      signExtend13,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

theorem padAnswer_root_word (hash : Hash) (s : MachineState) (i : Fin 5) :
    (padAnswer hash s).getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  have dst := (pad_registers s).2.2.1
  have frame := padPrepare_root_word s i
  fin_cases i <;>
    simpa [padAnswer,writeHash,dst,MachineState.writeWords,
      MachineState.getWord32,alignToDword,byteOffset] using frame

theorem root_pad_masked_word (hash : Hash) (s : MachineState) (i : Fin 5) :
    (padAnswer hash (init s)).getWord32
      (BitVec.ofNat 64 (0x60 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x60 + 4 * i.val)) := by
  rw [padAnswer_root_word,init_root_word]

/-- Honest root ciphertext decrypts back to the keygen top-tree root. -/
theorem decrypted_root_words (hash : Hash) (s : MachineState)
    (parameter : BitVec 160) (seed : MasterSeed) (root : Digest)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (masked : Words20 s 0x60
      (root ^^^ padValue hash parameter seed 4094)) (i : Fin 5) :
    (decrypted (padAnswer hash (init s))).getWord32
      (BitVec.ofNat 64 (0x53020 + 4 * i.val)) =
      root.extractLsb' (32 * i.val) 32 := by
  rw [decrypted_words,root_pad_masked_word,masked i,
    pad_answer_words32 hash s parameter seed par key i]
  have padEq :
      (padValue hash parameter seed 4094).extractLsb' (32 * i.val) 32 =
      (hash (SphincsBridge.toQuery
        (SphincsCacheSecretDomains.padInput parameter seed 4094))).extractLsb'
          (32 * i.val) 32 := by
    unfold padValue truncateHash
    exact BitVec.extractLsb'_extractLsb'_of_le (by simp [digestBits]; omega)
  rw [BitVec.extractLsb'_xor, padEq]
  simp only [BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]

/-- Copy the decrypted top root and public parameter to the compact signature. -/
def signaturePrefixSchedule : List (Word × Instr) := [
  (0x14a4, .LUI .x6 83),
  (0x14a8, .ADDI .x6 .x6 32),
  (0x14ac, .LUI .x7 32),
  (0x14b0, .ADDI .x7 .x7 96),
  (0x14b4, .LWU .x13 .x6 0),
  (0x14b8, .SW .x7 .x13 0),
  (0x14bc, .LWU .x13 .x6 4),
  (0x14c0, .SW .x7 .x13 4),
  (0x14c4, .LWU .x13 .x6 8),
  (0x14c8, .SW .x7 .x13 8),
  (0x14cc, .LWU .x13 .x6 12),
  (0x14d0, .SW .x7 .x13 12),
  (0x14d4, .LWU .x13 .x6 16),
  (0x14d8, .SW .x7 .x13 16),
  (0x14dc, .ADDI .x6 .x0 116),
  (0x14e0, .LUI .x7 32),
  (0x14e4, .ADDI .x7 .x7 116),
  (0x14e8, .LWU .x13 .x6 0),
  (0x14ec, .SW .x7 .x13 0),
  (0x14f0, .LWU .x13 .x6 4),
  (0x14f4, .SW .x7 .x13 4),
  (0x14f8, .LWU .x13 .x6 8),
  (0x14fc, .SW .x7 .x13 8),
  (0x1500, .LWU .x13 .x6 12),
  (0x1504, .SW .x7 .x13 12),
  (0x1508, .LWU .x13 .x6 16),
  (0x150c, .SW .x7 .x13 16)]

def signaturePrefix (s : MachineState) : MachineState :=
  runSchedule signaturePrefixSchedule s

theorem signaturePrefix_code : ∀ e ∈ signaturePrefixSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.sign e.1 =
      some (.base e.2) := by decide

theorem signaturePrefix_checked (s : MachineState) (pc : s.pc = 0x14a4) :
    Checked signaturePrefixSchedule s := by
  simp [Checked,signaturePrefixSchedule,execInstrBr,ordinaryStep,
    memoryArgumentsValid,accessValid,rangeValid,MEMORY_BYTES,
    signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem signaturePrefix_trace (s : MachineState) (pc : s.pc = 0x14a4) :
    OrdinarySteps SphincsMaskedImages.sign s 27 (signaturePrefix s) :=
  checked_sound _ signaturePrefixSchedule
    signaturePrefix_code s (signaturePrefix_checked s pc)

theorem signaturePrefix_pc (s : MachineState) (pc : s.pc = 0x14a4) :
    (signaturePrefix s).pc = 0x1510 := by
  simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
    execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,MachineState.setWord32,
    MachineState.getWord32,alignToDword,byteOffset,pc]

theorem signaturePrefix_root_word (s : MachineState) (i : Fin 5) :
    (signaturePrefix s).getWord32
      (BitVec.ofNat 64 (0x20060 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x53020 + 4 * i.val)) := by
  fin_cases i <;>
    simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

theorem signaturePrefix_parameter_word (s : MachineState) (i : Fin 5) :
    (signaturePrefix s).getWord32
      (BitVec.ofNat 64 (0x20074 + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
  fin_cases i <;>
    simp [signaturePrefix,runSchedule,signaturePrefixSchedule,
      execInstrBr,signExtend12,MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,MachineState.setWord32,
      MachineState.getWord32,alignToDword,byteOffset]

/-- The real signer writes the honestly decrypted root into signature bytes 0–19. -/
theorem honest_signature_root (hash : Hash) (s : MachineState)
    (pc : s.pc = 0x132c)
    (parameter : BitVec 160) (seed : MasterSeed) (root : Digest)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed)
    (masked : Words20 s 0x60
      (root ^^^ padValue hash parameter seed 4094)) :
    let final := signaturePrefix (decrypted (padAnswer hash (init s)))
    Trace hash SphincsMaskedImages.sign s 139 154 1 2 final ∧
    final.pc = 0x1510 ∧
    ∀ i : Fin 5,
      final.getWord32 (BitVec.ofNat 64 (0x20060 + 4 * i.val)) =
        root.extractLsb' (32 * i.val) 32 := by
  dsimp
  have padPc : (padAnswer hash (init s)).pc = 0x1440 := by
    simp [padAnswer,writeHash,pad_pc,init_pc s pc]
  have decPc := decrypt_pc (padAnswer hash (init s)) padPc
  have copied := signaturePrefix_trace (decrypted (padAnswer hash (init s))) decPc
  refine ⟨?_, signaturePrefix_pc _ decPc, ?_⟩
  · exact (root_unmask_trace hash s pc).trans copied.trace
  · intro i
    rw [signaturePrefix_root_word]
    exact decrypted_root_words hash s parameter seed root par key masked i

theorem words20_of_bytes (s : MachineState) (base : Nat) (value : Digest)
    (small : base + 20 ≤ 0x50000) (aligned : base % 4 = 0)
    (input : ∀ i, i < 20 →
      s.getByte (BitVec.ofNat 64 (base + i)) =
        value.extractLsb' (8 * i) 8) :
    Words20 s base value := by
  intro index
  ext bit hbit
  let byte : Fin 4 := ⟨bit / 8, by omega⟩
  have hi : 4 * index.val + byte.val < 20 := by
    have := index.isLt
    omega
  have h := input (4 * index.val + byte.val) hi
  rw [show base + (4 * index.val + byte.val) =
      base + 4 * index.val + byte.val by omega,
    variableWord_byte s base small aligned index byte] at h
  have hb := congrArg (fun x : BitVec 8 => x.getLsbD (bit % 8)) h
  rw [← BitVec.getLsbD_eq_getElem]
  simpa [byte,BitVec.getLsbD_extractLsb',
    show bit % 8 < 8 by omega,
    show 8 * (bit / 8) + bit % 8 = bit by omega,
    show 8 * (4 * index.val + bit / 8) + bit % 8 =
      32 * index.val + bit by omega] using hb

theorem entry_cache_byte (secretKey : SigGolf.SecretKey) (cache : SigGolf.Cache)
    (message : SigGolf.Message) (i : Nat) (hi : i < CACHE_BYTES) :
    (SphincsMaskedSignPrefix.entryState secretKey cache message).getByte
      (BitVec.ofNat 64 (0x60 + i)) = cache.extractLsb' (8 * i) 8 := by
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  let keyed := blank.writeBytesAsWords 0x20 (SigGolf.bytes secretKey)
  let cached := keyed.writeBytesAsWords 0x60 (SigGolf.bytes cache)
  let messaged := cached.writeBytesAsWords 0x0 (SigGolf.bytes message)
  change (messaged.setReg .x2 0x1000000).getByte
    (BitVec.ofNat 64 (0x60 + i)) = _
  rw [SigGolfCandidate.Memory.getByte_setReg]
  change (cached.writeBytesAsWords 0x0 (SigGolf.bytes message)).getByte
    (BitVec.ofNat 64 (0x60 + i)) = _
  have unchanged := SigGolfCandidate.Memory.write_preserves_byte cached 0x0
    (SigGolf.bytes message) 0x60 i (by decide) (by simp [SigGolf.bytes])
    (by dsimp [CACHE_BYTES] at hi; omega)
    (by right; simp [SigGolf.bytes])
  have loaded := SigGolfCandidate.Memory.write_value_byte keyed 0x60 CACHE_BYTES cache i
    (by decide) (by simp [CACHE_BYTES]) hi
  exact unchanged.trans loaded

theorem cache_slice_byte (cache : SigGolf.Cache) (offset i : Nat)
    (hi : i < 20) :
    (cache.extractLsb' (8 * offset) 160).extractLsb' (8 * i) 8 =
      cache.extractLsb' (8 * (offset + i)) 8 := by
  ext bit hbit
  simp [show 8 * i + bit < 160 by omega]
  congr 1
  omega

theorem entry_cache_words20 (secretKey : SigGolf.SecretKey)
    (cache : SigGolf.Cache) (message : SigGolf.Message)
    (offset : Nat) (bound : offset + 20 ≤ CACHE_BYTES)
    (aligned : offset % 4 = 0) :
    Words20 (SphincsMaskedSignPrefix.entryState secretKey cache message)
      (0x60 + offset) (cache.extractLsb' (8 * offset) 160) := by
  apply words20_of_bytes _ _ _
    (by dsimp [CACHE_BYTES] at bound; omega)
    (by omega)
  intro i hi
  rw [show 0x60 + offset + i = 0x60 + (offset + i) by omega,
    entry_cache_byte secretKey cache message (offset + i) (by omega)]
  exact (cache_slice_byte cache offset i hi).symm

theorem entry_key_words32 (secretKey : SigGolf.SecretKey)
    (cache : SigGolf.Cache) (message : SigGolf.Message) :
    Words32 (SphincsMaskedSignPrefix.entryState secretKey cache message)
      secretKey := by
  intro i
  have k0 := SphincsMaskedSignPrefix.entry_word secretKey cache message 0
  have k1 := SphincsMaskedSignPrefix.entry_word secretKey cache message 1
  have k2 := SphincsMaskedSignPrefix.entry_word secretKey cache message 2
  have k3 := SphincsMaskedSignPrefix.entry_word secretKey cache message 3
  norm_num at k0 k1 k2 k3
  fin_cases i <;>
    simp [MachineState.getWord32,alignToDword,byteOffset,
      k0,k1,k2,k3,extractWord32]
  all_goals ext j hj;interval_cases j <;> simp

theorem entry_honest_cache (hash : Hash) (secretKey : MasterSeed)
    (cache : SigGolf.Cache) (message : SigGolf.Message)
    (sem : SphincsMaskedKeygenRefinement.CacheSemantics hash secretKey cache) :
    Words20 (SphincsMaskedSignPrefix.entryState secretKey cache message)
      0x60 (SphincsMaskedKeygenRefinement.root hash secretKey ^^^
        padValue hash (SphincsMaskedKeygenRefinement.parameter hash secretKey)
          secretKey 4094) ∧
    Words20 (SphincsMaskedSignPrefix.entryState secretKey cache message)
      0x74 (SphincsMaskedKeygenRefinement.parameter hash secretKey) ∧
    Words32 (SphincsMaskedSignPrefix.entryState secretKey cache message)
      secretKey := by
  refine ⟨?_,?_,entry_key_words32 secretKey cache message⟩
  · intro i
    have loaded := (entry_cache_words20 secretKey cache message 0
      (by decide) (by decide)) i
    simp only [Nat.mul_zero,Nat.add_zero] at loaded
    exact loaded.trans (congrArg
      (fun value : Digest => value.extractLsb' (32 * i.val) 32)
      sem.rootWords)
  · have loaded := entry_cache_words20 secretKey cache message 20
      (by decide) (by decide)
    intro i
    have cell := loaded i
    exact (by simpa only [show 0x60 + 20 = 0x74 by decide] using
      cell.trans (congrArg
        (fun value : Digest => value.extractLsb' (32 * i.val) 32)
        sem.parameterWords))

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.decrypted_root_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypted_root_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.root_pad_masked_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_pad_masked_word

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.honest_signature_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms honest_signature_root

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.entry_honest_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_honest_cache

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.entry_cache_words20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entry_cache_words20

end SigGolfCandidate.SphincsMaskedSignRootValue
