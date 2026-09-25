import SigGolfCandidate.SphincsMaskedSignRootDecrypt
import SigGolfCandidate.SphincsMaskedMaskSemantics

namespace SigGolfCandidate.SphincsMaskedSignRootValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SphincsMaskedKeygenPrefix SphincsVerifierFtsRootCopy
open SphincsMaskedSignRootPad SphincsMaskedSignRootPadDomain
open SphincsMaskedSignRootDecrypt
open SphincsMaskedChainDomain SphincsMaskedSecretDomain
open SphincsSecurity SphincsMaskedMaskSemantics
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

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.decrypted_root_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decrypted_root_words

/-- info: 'SigGolfCandidate.SphincsMaskedSignRootValue.root_pad_masked_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms root_pad_masked_word

end SigGolfCandidate.SphincsMaskedSignRootValue
