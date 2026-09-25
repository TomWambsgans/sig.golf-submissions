import SigGolfCandidate.SphincsMaskedSignParameterCheck

namespace SigGolfCandidate.SphincsMaskedSignParameterFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Parameter setup never overwrites the cache's public parameter words. -/
theorem firstHash_cache_word (s : MachineState) (i : Fin 3) :
    (SphincsMaskedSignPrefix.firstHashState s).getMem
      (BitVec.ofNat 64 (0x70 + 8 * i.val)) =
    s.getMem (BitVec.ofNat 64 (0x70 + 8 * i.val)) := by
  fin_cases i <;>
    simp [SphincsMaskedSignPrefix.firstHashState,
      SphincsMaskedKeygenPrefix.runSchedule,
      SphincsMaskedSignPrefix.prefixSchedule,
      SphincsMaskedKeygenPrefix.prefixSchedule,
      execInstrBr, MachineState.getMem_setMem_ne,
      signExtend12, signExtend13,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset]


theorem afterHash_cache_word (hash : SigGolf.Hash) (s : MachineState)
    (seed : SphincsSecurity.MasterSeed) (i : Fin 3) :
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getMem
      (BitVec.ofNat 64 (0x70 + 8 * i.val)) =
    s.getMem (BitVec.ofNat 64 (0x70 + 8 * i.val)) := by
  have dst := (SphincsMaskedSignPrefix.firstHash_registers s).2.2.1
  have frame := firstHash_cache_word s i
  fin_cases i <;>
    simpa [SphincsMaskedSignPrefix.afterHashState, writeHash, dst,
      MachineState.writeWords] using frame

theorem afterHash_cache_words32 (hash : SigGolf.Hash) (s : MachineState)
    (seed : SphincsSecurity.MasterSeed) (i : Fin 5) :
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getWord32
      (BitVec.ofNat 64 (0x74 + 4 * i.val)) =
    s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
  fin_cases i
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1) (afterHash_cache_word hash s seed 0)
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 0) (afterHash_cache_word hash s seed 1)
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1) (afterHash_cache_word hash s seed 1)
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 0) (afterHash_cache_word hash s seed 2)
  · simpa [MachineState.getWord32, alignToDword, byteOffset] using
      congrArg (fun w : Word => extractWord32 w 1) (afterHash_cache_word hash s seed 2)

/-- An honestly derived cache parameter passes the first signer check. -/
theorem parameter_equal_of_cache (hash : SigGolf.Hash) (s : MachineState)
    (seed : SphincsSecurity.MasterSeed)
    (cacheMatches : ∀ i : Fin 5,
      s.getWord32 (BitVec.ofNat 64 (0x74 + 4 * i.val)) =
      (hash (SphincsBridge.toQuery
        (SphincsSecurity.keygenHashInput 0 .parameter seed))).extractLsb'
          (32 * i.val) 32) (i : Fin 5) :
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getWord32
      (BitVec.ofNat 64 (0x42000 + 4 * i.val)) =
    (SphincsMaskedSignPrefix.afterHashState hash s seed).getWord32
      (BitVec.ofNat 64 (0x74 + 4 * i.val)) := by
  rw [SphincsMaskedSignParameterCheck.afterHash_words32,
    afterHash_cache_words32, cacheMatches]

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterFrame.parameter_equal_of_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parameter_equal_of_cache

/-- info: 'SigGolfCandidate.SphincsMaskedSignParameterFrame.afterHash_cache_words32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterHash_cache_words32

end SigGolfCandidate.SphincsMaskedSignParameterFrame
