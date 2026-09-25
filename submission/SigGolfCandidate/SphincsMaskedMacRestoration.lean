import SigGolfCandidate.SphincsMaskedMacDomain

namespace SigGolfCandidate.SphincsMaskedMacRestoration
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedKeygenPrefix SphincsMaskedMacTrace SphincsMaskedMacDomain
open SphincsMaskedChainDomain SphincsMaskedSecretDomain SphincsBridge SphincsSecurity
open SphincsVerifierFtsRootCopy SphincsVerifierFtsRootCopyBytes SphincsCacheSecretDomains
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem prepare_saved (p : Word) (s : MachineState) (i : Fin 9) :
    (prepare p s).getMem (wordAddress 0x85000 i.val) = s.getMem (wordAddress 0x18 i.val) := by
  fin_cases i <;>
    simp [prepare,runSchedule,prepareSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,
      MachineState.setWord32,MachineState.getWord32,alignToDword,byteOffset,wordAddress]

theorem restore_data (p : Word) (s : MachineState) (i : Fin 9) :
    (restore p s).getMem (wordAddress 0x18 i.val) = s.getMem (wordAddress 0x85000 i.val) := by
  fin_cases i <;>
    simp [restore,runSchedule,restoreSchedule,execInstrBr,signExtend12,signExtend13,
      MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,wordAddress]

theorem restore_frame (p : Word) (s : MachineState) (a : Word) (outside : a ∉ lowWrites) :
    (restore p s).getMem a = s.getMem a := by
  simp only [lowWrites_eq,List.mem_cons,List.not_mem_nil,not_or] at outside
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := outside
  simp [restore,runSchedule,restoreSchedule,execInstrBr,signExtend12,signExtend13,
    MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,h0,h1,h2,h3,h4,h5,h6,h7,h8]

theorem answer_saved (hash : Hash) (p : Word) (s : MachineState) (i : Fin 9) :
    (answer hash p s).getMem (wordAddress 0x85000 i.val) = (prepare p s).getMem (wordAddress 0x85000 i.val) := by
  have dst := (prepare_registers p s).2.2.1
  fin_cases i <;> simp [answer,writeHash,dst,MachineState.writeWords,wordAddress]

theorem result_restored (hash : Hash) (p : Word) (s : MachineState) (i : Fin 9) :
    (result hash p s).getMem (wordAddress 0x18 i.val) = s.getMem (wordAddress 0x18 i.val) := by
  rw [result,restore_data,answer_saved,prepare_saved]

theorem answer_other_low (hash : Hash) (p : Word) (s : MachineState) (a : Word)
    (low : a.toNat < 0x40000) (outside : a ∉ lowWrites) :
    (answer hash p s).getMem a = s.getMem a := by
  have ne : ∀ b : Word, 0x40000 ≤ b.toNat → a ≠ b := by
    intro b high eq;rw [eq] at low;omega
  have h0 := ne 0x84000#64 (by decide)
  have h1 := ne 0x84008#64 (by decide)
  have h2 := ne 0x84010#64 (by decide)
  have h3 := ne 0x84018#64 (by decide)
  have dst := (prepare_registers p s).2.2.1
  simp [answer,writeHash,dst,MachineState.writeWords,h0,h1,h2,h3]
  apply prepare_frame
  simp only [prepareWrites,List.mem_append,not_or]
  refine ⟨outside,?_⟩
  intro member
  have bounds : ∀ b ∈ highWrites, 0x40000 ≤ b.toNat := by simp [highWrites]
  exact ne a (bounds a member) rfl

/-- The in-place MAC restores every original cell below the scratch hash buffer. -/
theorem result_low_frame (hash : Hash) (p : Word) (s : MachineState) (a : Word)
    (low : a.toNat < 0x40000) : (result hash p s).getMem a = s.getMem a := by
  by_cases member : a ∈ lowWrites
  · rw [lowWrites] at member
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp member
    subst a
    exact result_restored hash p s i
  · rw [result,restore_frame p _ a member,answer_other_low hash p s a low member]

theorem result_low_bytes (hash : Hash) (p : Word) (s : MachineState) (address : Nat)
    (bounded : address < 0x40000) :
    (result hash p s).getByte (BitVec.ofNat 64 address) = s.getByte (BitVec.ofNat 64 address) := by
  simp only [MachineState.getByte]
  rw [result_low_frame]
  unfold alignToDword
  rw [BitVec.toNat_and]
  apply lt_of_le_of_lt Nat.and_le_left
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bounded

theorem result_ciphertext (hash : Hash) (p : Word) (s : MachineState) :
    ciphertext (result hash p s) = ciphertext s := by
  apply congrArg List.ofFn
  funext i
  rw [result_low_bytes hash p s _ (by omega)]

theorem result_words (hash : Hash) (p : Word) (s : MachineState) (i : Fin 5) :
    (result hash p s).getWord32 (BitVec.ofNat 64 (0x84000+4*i.val)) =
      (hash (hashInput (prepare p s))).extractLsb' (32*i.val) 32 := by
  change (restore p (answer hash p s)).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [restore_frame p _ _ (by fin_cases i <;> simp [lowWrites_eq,alignToDword])]
  have dst := (prepare_registers p s).2.2.1
  fin_cases i <;> simp [answer,writeHash,dst,MachineState.writeWords,alignToDword,byteOffset,extractWord32]
  all_goals ext b hb;interval_cases b <;> simp

/-- Exact MAC evaluation, resource accounting, and restoration for either relocated image block. -/
theorem contract (hash : Hash) (image : Image) (p : Word) (code : Code image p)
    (s : MachineState) (pc : s.pc = p) (parameter : BitVec 160) (seed : MasterSeed)
    (par : Words20 s 0x74 parameter) (key : Words32 s seed) :
    Trace hash image s 236 16627 1 2049 (result hash p s) ∧ (result hash p s).pc = p + 0x188 ∧
      (∀ a : Word, a.toNat < 0x40000 → (result hash p s).getMem a = s.getMem a) ∧
      Words20 (result hash p s) 0x84000 (truncateHash (hash (toQuery (macInput parameter seed (ciphertext s))))) := by
  obtain ⟨run,loc⟩ := trace hash image p code s pc
  refine ⟨run,loc,result_low_frame hash p s,?_⟩
  intro i
  rw [result_words,query_eq p s parameter seed par key]
  exact (BitVec.extractLsb'_extractLsb'_of_le (by omega)).symm

/-- info: 'SigGolfCandidate.SphincsMaskedMacRestoration.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contract

/-- info: 'SigGolfCandidate.SphincsMaskedMacRestoration.result_low_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms result_low_frame

end SigGolfCandidate.SphincsMaskedMacRestoration
