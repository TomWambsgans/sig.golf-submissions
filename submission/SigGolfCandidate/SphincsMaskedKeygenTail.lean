import SigGolfCandidate.SphincsMaskedMaskLoop

namespace SigGolfCandidate.SphincsMaskedKeygenTail
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMaskCode SphincsMaskedMaskLoop
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsVerifierFtsRootCopy
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def final (hash : Hash) (s : MachineState) :=
  haltPrepare (tagCopy (SphincsMaskedMacTrace.result hash 0x1c48 (masked hash s)))

theorem haltPrepare_registers (s : MachineState) :
    (haltPrepare s).getReg .x5 = 0 ∧ (haltPrepare s).getReg .x10 = 1 := by
  simp [haltPrepare,runSchedule,haltPrepareSchedule,execInstrBr,signExtend12,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne]

theorem tail_trace (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a18) :
    Trace hash SphincsMaskedImages.keygen s 495784 573600 4096 10239 (final hash s) ∧
      (final hash s).pc = 0x1e10 ∧ (final hash s).getReg .x5 = 0 ∧ (final hash s).getReg .x10 = 1 := by
  obtain ⟨mask,loc⟩ := masked_trace hash s pc
  obtain ⟨mac,macpc⟩ := SphincsMaskedMacTrace.trace hash SphincsMaskedImages.keygen 0x1c48
    SphincsMaskedMacTrace.keygen_code (masked hash s) loc
  have macloc : (SphincsMaskedMacTrace.result hash 0x1c48 (masked hash s)).pc = 0x1dd0 := macpc
  have storepc := tagCopy_pc _ macloc
  exact ⟨mask.trans (mac.trans ((tagCopy_block _ macloc).trace.trans (haltPrepare_block _ storepc).trace)),
    haltPrepare_pc _ storepc,haltPrepare_registers _⟩

/-- The complete masking, authentication, tag-store and success-halt suffix. -/
theorem tail_executes (hash : Hash) (s : MachineState) (pc : s.pc = 0x1a18) :
    Executes hash SphincsMaskedImages.keygen s 495785
      ⟨.success,final hash s,573601,4096,10239⟩ := by
  obtain ⟨run,loc,service,success⟩ := tail_trace hash s pc
  have fetch : fetch SphincsMaskedImages.keygen (final hash s) = some (.base .ECALL) := by
    rw [fetch_at,loc];decide
  have halted := Executes.halt (hash := hash) (final hash s) fetch service
  have done := run.then_executes halted
  simpa [success,Execution.charge] using done

theorem tagCopy_data (s : MachineState) (i : Fin 5) :
    (tagCopy s).getWord32 (BitVec.ofNat 64 (0x2004c+4*i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x84000+4*i.val)) := by
  fin_cases i <;>
    simp [tagCopy,runSchedule,tagCopySchedule,execInstrBr,signExtend12,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset]

theorem haltPrepare_frame (s : MachineState) (a : Word) :
    (haltPrepare s).getMem a = s.getMem a := by simp [haltPrepare,runSchedule,haltPrepareSchedule,execInstrBr]

theorem final_tag (hash : Hash) (s : MachineState) (parameter : BitVec 160) (seed : SphincsSecurity.MasterSeed)
    (par : Words20 (masked hash s) 0x74 parameter) (key : Words32 (masked hash s) seed) :
    Words20 (final hash s) 0x2004c (SphincsSecurity.truncateHash
      (hash (SphincsBridge.toQuery (SphincsCacheSecretDomains.macInput parameter seed
        (SphincsMaskedMacDomain.ciphertext (masked hash s)))))) := by
  intro i
  change (haltPrepare (tagCopy (SphincsMaskedMacTrace.result hash 0x1c48 (masked hash s)))).getWord32 _ = _
  simp only [MachineState.getWord32,haltPrepare_frame]
  change (tagCopy (SphincsMaskedMacTrace.result hash 0x1c48 (masked hash s))).getWord32 _ = _
  rw [tagCopy_data,SphincsMaskedMacRestoration.result_words,
    SphincsMaskedMacDomain.query_eq 0x1c48 (masked hash s) parameter seed par key]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenTail.tail_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_executes

/-- info: 'SigGolfCandidate.SphincsMaskedKeygenTail.final_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms final_tag

end SigGolfCandidate.SphincsMaskedKeygenTail
