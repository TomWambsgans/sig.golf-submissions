import SigGolfCandidate.SphincsBeta64Images
import SigGolfCandidate.SphincsMaskedKeygenPrefix
import SigGolfCandidate.Hypertree.KeygenTrace
import SigGolfCandidate.SphincsMaskedImages
import SigGolfCandidate.SphincsImages

namespace SigGolfCandidate.KeygenOrdinaryFetch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem whole :
    (SphincsMaskedImages.keygen.code.zipWith
      (fun old new => old == (0x73 : BitVec 32) || old == new)
      (Pc64KeygenImage.code.take 901)).all id = true := by decide

theorem keygen_word (i : Nat) (hi : i < 901) :
    SphincsMaskedImages.keygen.code[i]? = some (0x73 : BitVec 32) ∨
    SphincsMaskedImages.keygen.code[i]? = Pc64KeygenImage.code[i]? := by
  apply GenericWordTransport.pointwise (0x73 : BitVec 32) whole
  · rw [SphincsMaskedImages.keygen_code_length]
    exact hi
  · rw [Pc64KeygenImage.code_length]
    omega
  · exact hi

theorem keygen_ordinary_fetch (s : MachineState) (ins : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some ins)
    (ordinary : ins ≠ .base .ECALL) :
    fetch Pc64KeygenImage.image s = some ins := by
  apply GenericFetchTransport.ordinary_fetch SphincsMaskedImages.keygen
    Pc64KeygenImage.image s ins
  · intro i hi
    have hi' : i < 901 := by
      simpa only [SphincsMaskedImages.keygen_code_length] using hi
    simpa only [Pc64KeygenImage.image] using keygen_word i hi'
  · exact fetched
  · exact ordinary

#print axioms whole
#print axioms keygen_ordinary_fetch
end SigGolfCandidate.KeygenOrdinaryFetch

namespace SigGolfCandidate.SignOrdinaryFetch
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 262144
set_option maxHeartbeats 2000000

theorem whole :
    (SphincsMaskedImages.sign.code.zipWith
      (fun old new => old == (0x73 : BitVec 32) || old == new)
      (Pc64SignImage.code.take 10957)).all id = true := by decide

theorem sign_word (i : Nat) (hi : i < 10957) :
    SphincsMaskedImages.sign.code[i]? = some (0x73 : BitVec 32) ∨
    SphincsMaskedImages.sign.code[i]? = Pc64SignImage.code[i]? := by
  apply GenericWordTransport.pointwise (0x73 : BitVec 32) whole
  · rw [SphincsMaskedImages.sign_code_length]
    exact hi
  · rw [Pc64SignImage.code_length]
    omega
  · exact hi

theorem sign_ordinary_fetch (s : MachineState) (ins : Instruction)
    (fetched : fetch SphincsMaskedImages.sign s = some ins)
    (ordinary : ins ≠ .base .ECALL) :
    fetch Pc64SignImage.image s = some ins := by
  apply GenericFetchTransport.ordinary_fetch SphincsMaskedImages.sign
    Pc64SignImage.image s ins
  · intro i hi
    have hi' : i < 10957 := by
      simpa only [SphincsMaskedImages.sign_code_length] using hi
    simpa only [Pc64SignImage.image] using sign_word i hi'
  · exact fetched
  · exact ordinary

#print axioms whole
#print axioms sign_ordinary_fetch
end SigGolfCandidate.SignOrdinaryFetch

namespace SigGolfCandidate.UnitCycleLegacy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000

def unitOrEcall (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | none => true
  | some instruction => instructionCycles instruction == 1

theorem unit_of_fetch (image : Image) (s : MachineState) (instruction : Instruction)
    (himage : image.code.all unitOrEcall = true)
    (fetched : fetch image s = some instruction) :
    instructionCycles instruction = 1 := by
  let i := (s.pc.toNat - 0x1000) / 4
  have guard : ¬ (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) := by
    by_contra h
    simp [fetch, h] at fetched
  have hf : (image.code[i]?).bind decodeInstruction = some instruction := by
    simpa [fetch, guard, i] using fetched
  cases hcode : image.code[i]? with
  | none => simp [hcode] at hf
  | some w =>
      have hi : i < image.code.length := (List.getElem?_eq_some_iff.mp hcode).1
      have hw : image.code[i] = w := by
        simpa [List.getElem?_eq_getElem hi] using hcode
      have hmem : w ∈ image.code := by simpa [hw] using List.getElem_mem hi
      have hunit : unitOrEcall w = true := (List.all_eq_true.mp himage) w hmem
      have hdecode : decodeInstruction w = some instruction := by simpa [hcode] using hf
      have hcycles : (instructionCycles instruction == 1) = true := by
        simpa only [unitOrEcall, hdecode] using hunit
      exact beq_iff_eq.mp hcycles

theorem keygen_all : SphincsMaskedImages.keygen.code.all unitOrEcall = true := by decide
theorem sign_all : SphincsMaskedImages.sign.code.all unitOrEcall = true := by decide
theorem expand_all : SphincsImages.expand.code.all unitOrEcall = true := by decide
theorem verify_all : SphincsImages.verify.code.all unitOrEcall = true := by decide

#print axioms keygen_all
#print axioms sign_all
#print axioms expand_all
#print axioms verify_all
#print axioms unit_of_fetch

end SigGolfCandidate.UnitCycleLegacy

namespace SigGolfCandidate.KeygenScratchSemantics
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def target : Instr → Option Reg
  | .ADD rd _ _ => some rd
  | .SUB rd _ _ => some rd
  | .SLL rd _ _ => some rd
  | .SRL rd _ _ => some rd
  | .SRA rd _ _ => some rd
  | .AND rd _ _ => some rd
  | .OR rd _ _ => some rd
  | .XOR rd _ _ => some rd
  | .SLT rd _ _ => some rd
  | .SLTU rd _ _ => some rd
  | .ADDI rd _ _ => some rd
  | .ANDI rd _ _ => some rd
  | .ORI rd _ _ => some rd
  | .XORI rd _ _ => some rd
  | .SLTI rd _ _ => some rd
  | .SLTIU rd _ _ => some rd
  | .SLLI rd _ _ => some rd
  | .SRLI rd _ _ => some rd
  | .SRAI rd _ _ => some rd
  | .LUI rd _ => some rd
  | .AUIPC rd _ => some rd
  | .LD rd _ _ => some rd
  | .SD _ _ _ => none
  | .LW rd _ _ => some rd
  | .LWU rd _ _ => some rd
  | .SW _ _ _ => none
  | .LB rd _ _ => some rd
  | .LH rd _ _ => some rd
  | .LBU rd _ _ => some rd
  | .LHU rd _ _ => some rd
  | .SB _ _ _ => none
  | .SH _ _ _ => none
  | .BEQ _ _ _ => none
  | .BNE _ _ _ => none
  | .BLT _ _ _ => none
  | .BGE _ _ _ => none
  | .BLTU _ _ _ => none
  | .BGEU _ _ _ => none
  | .JAL rd _ => some rd
  | .JALR rd _ _ => some rd
  | .MV rd _ => some rd
  | .LI rd _ => some rd
  | .NOP  => none
  | .ADDIW rd _ _ => some rd
  | .SUBW rd _ _ => some rd
  | .SRLW rd _ _ => some rd
  | .SLLIW rd _ _ => some rd
  | .SRLIW rd _ _ => some rd
  | .ECALL  => none
  | .FENCE  => none
  | .EBREAK  => none
  | .MUL rd _ _ => some rd
  | .MULH rd _ _ => some rd
  | .MULHSU rd _ _ => some rd
  | .MULHU rd _ _ => some rd
  | .DIV rd _ _ => some rd
  | .DIVU rd _ _ => some rd
  | .REM rd _ _ => some rd
  | .REMU rd _ _ => some rd
  | .CSRS _ _ => none

def instructionTarget : Instruction → Option Reg
  | .base i => target i
  | .word _ rd _ _ => some rd
  | .sraiw rd _ _ => some rd

def scratchRegs : List Reg := [.x16, .x17, .x18, .x19, .x20, .x21, .x22]

def decodedWritesScratch (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | none => false
  | some instruction => scratchRegs.any (fun r => instructionTarget instruction == some r)

theorem keygen_no_decoded_scratch_write :
    (SphincsMaskedImages.keygen.code.map decodedWritesScratch).all (· == false) = true := by
  decide

def keygenHashPCs : List Word :=
  [0x10d4, 0x1224, 0x1374, 0x1544, 0x177c, 0x19ec, 0x1b5c, 0x1da4]

def sensitivePCs : List Word :=
  keygenHashPCs.flatMap (fun pc => [pc - 20, pc - 16, pc - 12, pc - 8, pc - 4, pc])

def mayJumpIntoSensitive (i : Nat) (word : BitVec 32) : Bool :=
  let pc : Word := BitVec.ofNat 64 (0x1000 + 4 * i)
  match decodeInstruction word with
  | some (.base (.JALR ..)) => true
  | some (.base (.JAL _ off)) => (pc + signExtend21 off) ∈ sensitivePCs
  | some (.base (.BEQ _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | some (.base (.BNE _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | some (.base (.BLT _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | some (.base (.BGE _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | some (.base (.BLTU _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | some (.base (.BGEU _ _ off)) => (pc + signExtend13 off) ∈ sensitivePCs
  | _ => false

theorem keygen_no_jump_into_sensitive :
    (SphincsMaskedImages.keygen.code.zipIdx.all
      (fun entry => mayJumpIntoSensitive entry.2 entry.1 == false)) = true := by
  decide

theorem keygen_instruction_target_not_scratch (i : Nat) (hi : i < 901)
    (instruction : Instruction)
    (decoded : decodeInstruction (SphincsMaskedImages.keygen.code[i]) = some instruction)
    (r : Reg) (hr : r ∈ scratchRegs) :
    instructionTarget instruction ≠ some r := by
  have hall := List.all_eq_true.mp keygen_no_decoded_scratch_write
  have hcode : SphincsMaskedImages.keygen.code[i] ∈
      SphincsMaskedImages.keygen.code := by
    apply List.getElem_mem
  have hmem : decodedWritesScratch SphincsMaskedImages.keygen.code[i] ∈
      SphincsMaskedImages.keygen.code.map decodedWritesScratch :=
    List.mem_map.mpr ⟨_, hcode, rfl⟩
  have hno := hall _ hmem
  intro heq
  simp only [decodedWritesScratch, decoded] at hno
  have hany : scratchRegs.any (fun q => instructionTarget instruction == some q) = true := by
    apply List.any_eq_true.mpr
    exact ⟨r, hr, by simp [heq]⟩
  simp [hany] at hno

theorem ordinary_preserves (s next : MachineState) (instruction : Instruction) (r : Reg)
    (h : ordinaryStep s instruction = some next)
    (ne : instructionTarget instruction ≠ some r) :
    next.getReg r = s.getReg r := by
  cases instruction with
  | base i =>
      cases i <;> simp_all [instructionTarget, target, ordinaryStep, execInstrBr]
      all_goals
        rcases h with ⟨_, heq⟩
        subst next
        try simp_all [MachineState.getReg_setReg_ne, MachineState.getReg_setPC,
          MachineState.setMem, MachineState.setWord32,
          MachineState.setByte, MachineState.setHalfword]
      all_goals first | rfl | (split_ifs <;> simp [MachineState.getReg_setPC])
  | word op rd rs1 rs2 =>
      simp_all [instructionTarget, ordinaryStep]
      subst next
      simp_all [MachineState.getReg_setReg_ne, MachineState.getReg_setPC]
  | sraiw rd rs1 shift =>
      simp_all [instructionTarget, ordinaryStep]
      subst next
      simp_all [MachineState.getReg_setReg_ne, MachineState.getReg_setPC]

theorem keygen_fetched_target_not_scratch (s : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (r : Reg) (hr : r ∈ scratchRegs) :
    instructionTarget instruction ≠ some r := by
  unfold fetch at fetched
  split at fetched
  · simp at fetched
  · let i := (s.pc.toNat - 0x1000) / 4
    have hword : ∃ word, SphincsMaskedImages.keygen.code[i]? = some word ∧
        decodeInstruction word = some instruction := by
      simpa [i, Option.bind_eq_some_iff] using fetched
    obtain ⟨word, hget, hdecode⟩ := hword
    have hi : i < 901 := by
      have := List.getElem?_eq_some_iff.mp hget
      simpa only [SphincsMaskedImages.keygen_code_length] using this.1
    have hw : word = SphincsMaskedImages.keygen.code[i] := by
      have := List.getElem?_eq_some_iff.mp hget
      exact this.2.symm
    subst word
    exact keygen_instruction_target_not_scratch i hi instruction hdecode r hr

theorem keygen_ordinary_scratch_frame (s next : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (step : ordinaryStep s instruction = some next)
    (r : Reg) (hr : r ∈ scratchRegs) :
    next.getReg r = s.getReg r :=
  ordinary_preserves s next instruction r step
    (keygen_fetched_target_not_scratch s instruction fetched r hr)

theorem keygen_trace_scratch_frame (hash : Legacy.Hash)
    {s t : MachineState} {steps cycles calls blocks : Nat}
    (trace : Trace hash SphincsMaskedImages.keygen s steps cycles calls blocks t)
    (r : Reg) (hr : r ∈ scratchRegs) :
    t.getReg r = s.getReg r := by
  induction trace with
  | refl => rfl
  | ordinary state next final instruction steps cycles calls blocks hf hs tail ih =>
      exact (ih).trans (keygen_ordinary_scratch_frame state next instruction hf hs r hr)
  | hash state final steps cycles calls blocks hf hs hv tail ih =>
      exact ih

end SigGolfCandidate.KeygenScratchSemantics

/-- info: 'SigGolfCandidate.KeygenScratchSemantics.keygen_no_decoded_scratch_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenScratchSemantics.keygen_no_decoded_scratch_write

/-- info: 'SigGolfCandidate.KeygenScratchSemantics.keygen_no_jump_into_sensitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenScratchSemantics.keygen_no_jump_into_sensitive

/-- info: 'SigGolfCandidate.KeygenScratchSemantics.keygen_trace_scratch_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenScratchSemantics.keygen_trace_scratch_frame

/-- info: 'SigGolfCandidate.KeygenScratchSemantics.ordinary_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenScratchSemantics.ordinary_preserves


namespace SigGolfCandidate.KeygenControlStep
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.KeygenScratchSemantics
set_option maxRecDepth 16384

theorem pc_of_index (s : MachineState)
    (hge : 4096 ≤ s.pc.toNat) (haligned : s.pc.toNat % 4 = 0) :
    (BitVec.ofNat 64 (4096 + 4 * ((s.pc.toNat - 4096) / 4))) = s.pc := by
  have hn : 4096 + 4 * ((s.pc.toNat - 4096) / 4) = s.pc.toNat := by omega
  rw [hn]
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt s.pc.isLt]

theorem fetch_alignment (s : MachineState) (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction) :
    4096 ≤ s.pc.toNat ∧ s.pc.toNat % 4 = 0 := by
  unfold fetch at fetched
  split at fetched
  · cases fetched
  · rename_i hfalse
    have hge : ¬s.pc.toNat < 4096 := by
      intro hlt
      have hb : (decide (s.pc.toNat < 4096) || s.pc.toNat % 4 != 0) = true := by
        simp [hlt]
      exact hfalse hb
    have haligned : s.pc.toNat % 4 = 0 := by
      by_contra hh
      have hb : (decide (s.pc.toNat < 4096) || s.pc.toNat % 4 != 0) = true := by
        simp [hh]
      exact hfalse hb
    exact ⟨by omega, haligned⟩

theorem keygen_fetched_no_jump (s : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (word : BitVec 32)
    (hget : SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word) :
    let i := (s.pc.toNat - 0x1000) / 4
    mayJumpIntoSensitive i word = false := by
  unfold fetch at fetched
  split at fetched
  · simp at fetched
  · let i := (s.pc.toNat - 0x1000) / 4
    have hi : i < 901 := by
      have := List.getElem?_eq_some_iff.mp hget
      simpa only [SphincsMaskedImages.keygen_code_length] using this.1
    have hall := List.all_eq_true.mp keygen_no_jump_into_sensitive
    have hmem : (word, i) ∈
        SphincsMaskedImages.keygen.code.zipIdx := by
      have hzip : (SphincsMaskedImages.keygen.code.zipIdx)[i]? = some (word, i) := by
        rw [List.getElem?_zipIdx]
        simpa [i, hget]
      obtain ⟨hiZip, heq⟩ := List.getElem?_eq_some_iff.mp hzip
      rw [← heq]
      exact List.getElem_mem hiZip
    have hbad := hall _ hmem
    simpa using hbad

theorem sensitive_entry_is_fallthrough (s next : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (step : ordinaryStep s instruction = some next)
    (sensitive : next.pc ∈ sensitivePCs) :
    next.pc = s.pc + 4 := by
  have hword : ∃ word,
      SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word ∧
      decodeInstruction word = some instruction := by
    unfold fetch at fetched
    split at fetched
    · simp at fetched
    · simpa [Option.bind_eq_some_iff] using fetched
  obtain ⟨word, hget, hdecode⟩ := hword
  have hnojump := keygen_fetched_no_jump s instruction fetched word hget
  simp only [mayJumpIntoSensitive, hdecode] at hnojump
  obtain ⟨hge, haligned⟩ := fetch_alignment s instruction fetched
  rw [pc_of_index s hge haligned] at hnojump
  cases instruction with
  | base instr =>
      cases instr <;> simp_all [ordinaryStep, execInstrBr]
      all_goals
        rcases step with ⟨_, heq⟩
        subst next
        try rfl
        try simp_all [MachineState.setPC]
        all_goals split_ifs at sensitive ⊢ <;> simp_all [MachineState.setPC]
  | word op rd rs1 rs2 =>
      simp_all [ordinaryStep]
      subst next
      rfl
  | sraiw rd rs1 shift =>
      simp_all [ordinaryStep]
      subst next
      rfl

end SigGolfCandidate.KeygenControlStep

/-- info: 'SigGolfCandidate.KeygenControlStep.sensitive_entry_is_fallthrough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenControlStep.sensitive_entry_is_fallthrough


namespace SigGolfCandidate.KeygenWideControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.KeygenScratchSemantics
set_option maxRecDepth 16384

def wideSensitivePCs : List Word :=
  (keygenHashPCs ++ [0x1e10]).flatMap (fun pc => [pc - 28, pc - 24, pc - 20, pc - 16, pc - 12, pc - 8, pc - 4, pc])

def mayJumpIntoWideSensitive (i : Nat) (word : BitVec 32) : Bool :=
  let pc : Word := BitVec.ofNat 64 (0x1000 + 4 * i)
  match decodeInstruction word with
  | some (.base (.JALR ..)) => true
  | some (.base (.JAL _ off)) => (pc + signExtend21 off) ∈ wideSensitivePCs
  | some (.base (.BEQ _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | some (.base (.BNE _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | some (.base (.BLT _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | some (.base (.BGE _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | some (.base (.BLTU _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | some (.base (.BGEU _ _ off)) => (pc + signExtend13 off) ∈ wideSensitivePCs
  | _ => false

theorem no_jump_into_wide_sensitive :
    (SphincsMaskedImages.keygen.code.zipIdx.all
      (fun entry => mayJumpIntoWideSensitive entry.2 entry.1 == false)) = true := by decide

theorem pc_of_index (s : MachineState)
    (hge : 4096 ≤ s.pc.toNat) (haligned : s.pc.toNat % 4 = 0) :
    (BitVec.ofNat 64 (4096 + 4 * ((s.pc.toNat - 4096) / 4))) = s.pc := by
  have hn : 4096 + 4 * ((s.pc.toNat - 4096) / 4) = s.pc.toNat := by omega
  rw [hn]
  apply BitVec.eq_of_toNat_eq
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt s.pc.isLt]

theorem fetch_alignment (s : MachineState) (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction) :
    4096 ≤ s.pc.toNat ∧ s.pc.toNat % 4 = 0 := by
  unfold fetch at fetched
  split at fetched
  · cases fetched
  · rename_i hfalse
    have hge : ¬s.pc.toNat < 4096 := by
      intro hlt
      have hb : (decide (s.pc.toNat < 4096) || s.pc.toNat % 4 != 0) = true := by
        simp [hlt]
      exact hfalse hb
    have haligned : s.pc.toNat % 4 = 0 := by
      by_contra hh
      have hb : (decide (s.pc.toNat < 4096) || s.pc.toNat % 4 != 0) = true := by
        simp [hh]
      exact hfalse hb
    exact ⟨by omega, haligned⟩

theorem keygen_fetched_no_jump (s : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (word : BitVec 32)
    (hget : SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word) :
    let i := (s.pc.toNat - 0x1000) / 4
    mayJumpIntoWideSensitive i word = false := by
  unfold fetch at fetched
  split at fetched
  · simp at fetched
  · let i := (s.pc.toNat - 0x1000) / 4
    have hi : i < 901 := by
      have := List.getElem?_eq_some_iff.mp hget
      simpa only [SphincsMaskedImages.keygen_code_length] using this.1
    have hall := List.all_eq_true.mp no_jump_into_wide_sensitive
    have hmem : (word, i) ∈
        SphincsMaskedImages.keygen.code.zipIdx := by
      have hzip : (SphincsMaskedImages.keygen.code.zipIdx)[i]? = some (word, i) := by
        rw [List.getElem?_zipIdx]
        simpa [i, hget]
      obtain ⟨hiZip, heq⟩ := List.getElem?_eq_some_iff.mp hzip
      rw [← heq]
      exact List.getElem_mem hiZip
    have hbad := hall _ hmem
    simpa using hbad

theorem sensitive_entry_is_fallthrough (s next : MachineState)
    (instruction : Instruction)
    (fetched : fetch SphincsMaskedImages.keygen s = some instruction)
    (step : ordinaryStep s instruction = some next)
    (sensitive : next.pc ∈ wideSensitivePCs) :
    next.pc = s.pc + 4 := by
  have hword : ∃ word,
      SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word ∧
      decodeInstruction word = some instruction := by
    unfold fetch at fetched
    split at fetched
    · simp at fetched
    · simpa [Option.bind_eq_some_iff] using fetched
  obtain ⟨word, hget, hdecode⟩ := hword
  have hnojump := keygen_fetched_no_jump s instruction fetched word hget
  simp only [mayJumpIntoWideSensitive, hdecode] at hnojump
  obtain ⟨hge, haligned⟩ := fetch_alignment s instruction fetched
  rw [pc_of_index s hge haligned] at hnojump
  cases instruction with
  | base instr =>
      cases instr <;> simp_all [ordinaryStep, execInstrBr]
      all_goals
        rcases step with ⟨_, heq⟩
        subst next
        try rfl
        try simp_all [MachineState.setPC]
        all_goals split_ifs at sensitive ⊢ <;> simp_all [MachineState.setPC]
  | word op rd rs1 rs2 =>
      simp_all [ordinaryStep]
      subst next
      rfl
  | sraiw rd rs1 shift =>
      simp_all [ordinaryStep]
      subst next
      rfl

end SigGolfCandidate.KeygenWideControl

/-- info: 'SigGolfCandidate.KeygenWideControl.sensitive_entry_is_fallthrough' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenWideControl.sensitive_entry_is_fallthrough


namespace SigGolfCandidate.KeygenReach
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.KeygenScratchSemantics SigGolfCandidate.KeygenWideControl
set_option maxRecDepth 16384

def hashSuccessorSensitive (i : Nat) (word : BitVec 32) : Bool :=
  decodeInstruction word == some (.base .ECALL) &&
    ((BitVec.ofNat 64 (0x1000 + 4 * (i + 1))) ∈ wideSensitivePCs)

theorem no_hash_successor_sensitive :
    (SphincsMaskedImages.keygen.code.zipIdx.all
      (fun entry => hashSuccessorSensitive entry.2 entry.1 == false)) = true := by
  decide

inductive Reach (hash : Legacy.Hash) (initial : MachineState) :
    MachineState → Prop where
  | start : Reach hash initial initial
  | ordinary {s next : MachineState} {instruction : Instruction}
      (prior : Reach hash initial s)
      (fetch : SigGolf.Riscv.fetch SphincsMaskedImages.keygen s = some instruction)
      (step : ordinaryStep s instruction = some next) :
      Reach hash initial next
  | hash {s : MachineState}
      (prior : Reach hash initial s)
      (fetch : SigGolf.Riscv.fetch SphincsMaskedImages.keygen s = some (.base .ECALL))
      (selector : s.getReg .x5 = 1)
      (valid : SigGolfCandidate.hashArgumentsValid s = true) :
      Reach hash initial (writeHash s (hash (SigGolfCandidate.hashInput s)))

theorem trace_reach (hash : Legacy.Hash) (initial : MachineState)
    {s t : MachineState} {steps cycles calls blocks : Nat}
    (trace : Trace hash SphincsMaskedImages.keygen s steps cycles calls blocks t)
    (prior : Reach hash initial s) :
    Reach hash initial t := by
  induction trace generalizing initial with
  | refl => exact prior
  | ordinary s next final instruction steps cycles calls blocks hf hs tail ih =>
      exact ih initial (Reach.ordinary prior hf hs)
  | hash s final steps cycles calls blocks hf hs hv tail ih =>
      exact ih initial (Reach.hash prior hf hs hv)

theorem hash_does_not_enter_sensitive (s : MachineState) (answer : BitVec 256)
    (fetched : fetch SphincsMaskedImages.keygen s = some (.base .ECALL)) :
    (writeHash s answer).pc ∉ wideSensitivePCs := by
  have hword : ∃ word,
      SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word ∧
      decodeInstruction word = some (.base .ECALL) := by
    unfold fetch at fetched
    split at fetched
    · simp at fetched
    · simpa [Option.bind_eq_some_iff] using fetched
  obtain ⟨word, hget, hdecode⟩ := hword
  let i := (s.pc.toNat - 0x1000) / 4
  have hmem : (word, i) ∈ SphincsMaskedImages.keygen.code.zipIdx := by
    have hzip : (SphincsMaskedImages.keygen.code.zipIdx)[i]? = some (word, i) := by
      rw [List.getElem?_zipIdx]
      simpa [i, hget]
    obtain ⟨hiZip, heq⟩ := List.getElem?_eq_some_iff.mp hzip
    rw [← heq]
    exact List.getElem_mem hiZip
  have hsafe := (List.all_eq_true.mp no_hash_successor_sensitive) _ hmem
  simp only [hashSuccessorSensitive, hdecode, beq_self_eq_true, Bool.true_and,
    Bool.not_eq_true'] at hsafe
  obtain ⟨hge, haligned⟩ := fetch_alignment s (.base .ECALL) fetched
  have hpc := pc_of_index s hge haligned
  have hnext : BitVec.ofNat 64 (0x1000 + 4 * (i + 1)) = s.pc + 4 := by
    have hn : 0x1000 + 4 * (i + 1) = (0x1000 + 4 * i) + 4 := by omega
    rw [hn, BitVec.ofNat_add]
    exact congrArg (· + (4 : BitVec 64)) (by simpa [i] using hpc)
  simpa [writeHash, MachineState.setPC, hnext] using hsafe

theorem reached_sensitive_has_ordinary_predecessor (hash : Legacy.Hash)
    (initial s : MachineState) (reached : Reach hash initial s)
    (initial_not_sensitive : initial.pc ∉ wideSensitivePCs)
    (sensitive : s.pc ∈ wideSensitivePCs) :
    ∃ prev instruction, Reach hash initial prev ∧
      fetch SphincsMaskedImages.keygen prev = some instruction ∧
      ordinaryStep prev instruction = some s ∧ s.pc = prev.pc + 4 := by
  cases reached with
  | start => exact False.elim (initial_not_sensitive sensitive)
  | ordinary prior hf hs =>
      exact ⟨_, _, prior, hf, hs,
        SigGolfCandidate.KeygenWideControl.sensitive_entry_is_fallthrough _ _ _ hf hs sensitive⟩
  | hash prior hf selector valid =>
      exact False.elim ((hash_does_not_enter_sensitive _ _ hf) sensitive)

theorem peel_setup (hash : Legacy.Hash) (initial : MachineState)
    (site : Word) (initial_not_sensitive : initial.pc ∉ wideSensitivePCs)
    (site_safe : ∀ j : Nat, j < 8 → site - BitVec.ofNat 64 (4 * j) ∈ wideSensitivePCs) :
    ∀ (n k : Nat) (s : MachineState), k + n ≤ 8 →
      Reach hash initial s → s.pc = site - BitVec.ofNat 64 (4 * k) →
      ∃ start, Reach hash initial start ∧
        start.pc = site - BitVec.ofNat 64 (4 * (k + n)) ∧
        OrdinarySteps SphincsMaskedImages.keygen start n s := by
  intro n
  induction n with
  | zero =>
      intro k s hkn reached hpc
      exact ⟨s, reached, by simpa using hpc, OrdinarySteps.refl s⟩
  | succ n ih =>
      intro k s hkn reached hpc
      have hk : k < 8 := by omega
      have hsensitive : s.pc ∈ wideSensitivePCs := by
        rw [hpc]
        exact site_safe k hk
      obtain ⟨prev, instruction, prior, fetched, step, pcStep⟩ :=
        reached_sensitive_has_ordinary_predecessor hash initial s
          reached initial_not_sensitive hsensitive
      have hprev : prev.pc = site - BitVec.ofNat 64 (4 * (k + 1)) := by
        rw [hpc] at pcStep
        have h : (site - BitVec.ofNat 64 (4 * k)) - 4 =
            site - BitVec.ofNat 64 (4 * (k + 1)) := by bv_omega
        calc
          prev.pc = s.pc - 4 := by bv_omega
          _ = site - BitVec.ofNat 64 (4 * (k + 1)) := by rw [hpc]; exact h
      obtain ⟨start, hstart, hstartPC, block⟩ :=
        ih (k + 1) prev (by omega) prior hprev
      refine ⟨start, hstart, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstartPC
      · have one : OrdinarySteps SphincsMaskedImages.keygen prev 1 s :=
          OrdinarySteps.step prev s s instruction 0 fetched step (OrdinarySteps.refl s)
        have both := OrdinarySteps.append block one
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using both

theorem ordinarySteps_unique {image : Image} {start a b : MachineState} {n : Nat}
    (first : OrdinarySteps image start n a)
    (second : OrdinarySteps image start n b) : a = b := by
  induction first generalizing b with
  | refl =>
      cases second
      rfl
  | step state next final instruction steps hf hs tail ih =>
      cases second with
      | step _ next' final' instruction' _ hf' hs' tail' =>
          have hinstr : instruction = instruction' := by
            simpa [hf] using hf'
          subst instruction'
          have hnext : next = next' := by simpa [hs] using hs'
          subst next'
          exact ih tail'

end SigGolfCandidate.KeygenReach

/-- info: 'SigGolfCandidate.KeygenReach.trace_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenReach.trace_reach

/-- info: 'SigGolfCandidate.KeygenReach.no_hash_successor_sensitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.KeygenReach.no_hash_successor_sensitive


namespace SigGolfCandidate.KeygenSetup
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.KeygenReach SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def standardSchedule (site : Word) (bits : BitVec 12) : List (Word × Instr) :=
  [(site-24, .LUI .x10 64),
   (site-20, .ADDI .x10 .x10 0),
   (site-16, .ADDI .x11 .x0 bits),
   (site-12, .LUI .x12 66),
   (site-8, .ADDI .x12 .x12 0),
   (site-4, .ADDI .x5 .x0 1)]

def standardSites : List (Word × BitVec 12) :=
  [(0x10d4, 576), (0x1224, 576), (0x1374, 480),
   (0x177c, 640), (0x19ec, 480), (0x1b5c, 576)]

theorem standard_schedule_code (site : Word) (bits : BitVec 12)
    (hsite : (site,bits) ∈ standardSites) :
    ∀ entry ∈ standardSchedule site bits,
      SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen
        entry.1 = some (.base entry.2) := by
  have hall : (standardSites.all fun sb =>
      (standardSchedule sb.1 sb.2).all fun entry =>
        SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen
          entry.1 == some (.base entry.2)) = true := by decide
  intro entry hentry
  have hs := (List.all_eq_true.mp hall) _ hsite
  have he := (List.all_eq_true.mp hs) _ hentry
  simpa using he

theorem standard_checked (site : Word) (bits : BitVec 12)
    (hsite : (site,bits) ∈ standardSites)
    (s : MachineState) (hpc : s.pc = site - 24) :
    Checked (standardSchedule site bits) s := by
  simp only [standardSites, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hsite
  rcases hsite with h | h | h | h | h | h
  all_goals
    have hs := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    simp only at hs hb
    subst site
    subst bits
    simp [Checked, standardSchedule, execInstrBr, ordinaryStep,
      memoryArgumentsValid, signExtend12, MachineState.getReg_setReg_eq, hpc]

theorem standard_controls (site : Word) (bits : BitVec 12)
    (s : MachineState) :
    (runSchedule (standardSchedule site bits) s).getReg .x10 = 0x40000 ∧
    (runSchedule (standardSchedule site bits) s).getReg .x11 = signExtend12 bits ∧
    (runSchedule (standardSchedule site bits) s).getReg .x12 = 0x42000 ∧
    (runSchedule (standardSchedule site bits) s).getReg .x5 = 1 := by
  simp [runSchedule, standardSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem standard_site_safe (site : Word) (bits : BitVec 12)
    (hsite : (site,bits) ∈ standardSites) (j : Nat) (hj : j < 8) :
    site - BitVec.ofNat 64 (4 * j) ∈ KeygenWideControl.wideSensitivePCs := by
  have hall : (standardSites.all fun sb =>
      (List.range 8).all fun j =>
        decide (sb.1 - BitVec.ofNat 64 (4 * j) ∈
          KeygenWideControl.wideSensitivePCs)) = true := by decide
  have hs := (List.all_eq_true.mp hall) _ hsite
  have hjmem : j ∈ List.range 8 := by simp; omega
  exact of_decide_eq_true ((List.all_eq_true.mp hs) _ hjmem)

theorem standard_reached_controls (hash : Legacy.Hash)
    (initial s : MachineState) (site : Word) (bits : BitVec 12)
    (hsite : (site,bits) ∈ standardSites)
    (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s) (site_pc : s.pc = site) :
    s.getReg .x10 = 0x40000 ∧
    s.getReg .x11 = signExtend12 bits ∧
    s.getReg .x12 = 0x42000 ∧ s.getReg .x5 = 1 := by
  have init_safe : initial.pc ∉ KeygenWideControl.wideSensitivePCs := by
    rw [initial_pc]
    decide
  obtain ⟨start, _, start_pc, block⟩ :=
    peel_setup hash initial site init_safe
      (standard_site_safe site bits hsite) 6 0 s (by decide)
      reached (by simpa using site_pc)
  have start_pc' : start.pc = site - 24 := by simpa using start_pc
  have checked := standard_checked site bits hsite start start_pc'
  have code := standard_schedule_code site bits hsite
  have other := checked_sound SphincsMaskedImages.keygen
    (standardSchedule site bits) code start checked
  have hend : s = runSchedule (standardSchedule site bits) start := by
    exact ordinarySteps_unique block (by simpa [standardSchedule] using other)
  rw [hend]
  exact standard_controls site bits start

def longSchedule : List (Word × Instr) :=
  [(0x1528, .LUI .x10 64), (0x152c, .ADDI .x10 .x10 0),
   (0x1530, .LUI .x11 2), (0x1534, .ADDI .x11 .x11 448),
   (0x1538, .LUI .x12 66), (0x153c, .ADDI .x12 .x12 0),
   (0x1540, .ADDI .x5 .x0 1)]

theorem long_code : ∀ entry ∈ longSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen
      entry.1 = some (.base entry.2) := by decide

theorem long_checked (s : MachineState) (hpc : s.pc = 0x1528) :
    Checked longSchedule s := by
  simp [Checked, longSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, signExtend12, MachineState.getReg_setReg_eq, hpc]

theorem long_controls (s : MachineState) :
    (runSchedule longSchedule s).getReg .x10 = 0x40000 ∧
    (runSchedule longSchedule s).getReg .x11 = 8640 ∧
    (runSchedule longSchedule s).getReg .x12 = 0x42000 ∧
    (runSchedule longSchedule s).getReg .x5 = 1 := by
  simp [runSchedule, longSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

def macSchedule : List (Word × Instr) :=
  [(0x1d8c, .ADDI .x10 .x0 24),
   (0x1d90, .LUI .x11 256), (0x1d94, .ADDI .x11 .x11 416),
   (0x1d98, .LUI .x12 132), (0x1d9c, .ADDI .x12 .x12 0),
   (0x1da0, .ADDI .x5 .x0 1)]

theorem mac_code : ∀ entry ∈ macSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen
      entry.1 = some (.base entry.2) := by decide

theorem mac_checked (s : MachineState) (hpc : s.pc = 0x1d8c) :
    Checked macSchedule s := by
  simp [Checked, macSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, signExtend12, MachineState.getReg_setReg_eq, hpc]

theorem mac_controls (s : MachineState) :
    (runSchedule macSchedule s).getReg .x10 = 0x18 ∧
    (runSchedule macSchedule s).getReg .x11 = 1048992 ∧
    (runSchedule macSchedule s).getReg .x12 = 0x84000 ∧
    (runSchedule macSchedule s).getReg .x5 = 1 := by
  simp [runSchedule, macSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

private theorem literal_site_safe (site : Word)
    (h : (List.range 8).all fun j => decide
      (site - BitVec.ofNat 64 (4 * j) ∈ KeygenWideControl.wideSensitivePCs)) :
    ∀ j : Nat, j < 8 →
      site - BitVec.ofNat 64 (4 * j) ∈ KeygenWideControl.wideSensitivePCs := by
  intro j hj
  have hjmem : j ∈ List.range 8 := by simp; omega
  exact of_decide_eq_true ((List.all_eq_true.mp h) _ hjmem)

theorem long_reached_controls (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s) (site_pc : s.pc = 0x1544) :
    s.getReg .x10 = 0x40000 ∧ s.getReg .x11 = 8640 ∧
    s.getReg .x12 = 0x42000 ∧ s.getReg .x5 = 1 := by
  have init_safe : initial.pc ∉ KeygenWideControl.wideSensitivePCs := by
    rw [initial_pc]
    decide
  have safe : ∀ j : Nat, j < 8 →
      (0x1544 : Word) - BitVec.ofNat 64 (4 * j) ∈
        KeygenWideControl.wideSensitivePCs :=
    literal_site_safe 0x1544 (by decide)
  obtain ⟨start, _, start_pc, block⟩ :=
    peel_setup hash initial 0x1544 init_safe safe 7 0 s (by decide)
      reached (by simpa using site_pc)
  have start_pc' : start.pc = 0x1528 := by simpa using start_pc
  have other := checked_sound SphincsMaskedImages.keygen longSchedule
    long_code start (long_checked start start_pc')
  have hend : s = runSchedule longSchedule start := by
    exact ordinarySteps_unique block (by simpa [longSchedule] using other)
  rw [hend]
  exact long_controls start

theorem mac_reached_controls (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s) (site_pc : s.pc = 0x1da4) :
    s.getReg .x10 = 0x18 ∧ s.getReg .x11 = 1048992 ∧
    s.getReg .x12 = 0x84000 ∧ s.getReg .x5 = 1 := by
  have init_safe : initial.pc ∉ KeygenWideControl.wideSensitivePCs := by
    rw [initial_pc]
    decide
  have safe : ∀ j : Nat, j < 8 →
      (0x1da4 : Word) - BitVec.ofNat 64 (4 * j) ∈
        KeygenWideControl.wideSensitivePCs :=
    literal_site_safe 0x1da4 (by decide)
  obtain ⟨start, _, start_pc, block⟩ :=
    peel_setup hash initial 0x1da4 init_safe safe 6 0 s (by decide)
      reached (by simpa using site_pc)
  have start_pc' : start.pc = 0x1d8c := by simpa using start_pc
  have other := checked_sound SphincsMaskedImages.keygen macSchedule
    mac_code start (mac_checked start start_pc')
  have hend : s = runSchedule macSchedule start := by
    exact ordinarySteps_unique block (by simpa [macSchedule] using other)
  rw [hend]
  exact mac_controls start

def ecallPCs : List Word :=
  KeygenScratchSemantics.keygenHashPCs ++ [0x1e10]

theorem all_ecall_positions :
    (SphincsMaskedImages.keygen.code.zipIdx.all fun entry =>
      if decodeInstruction entry.1 == some (.base .ECALL)
      then decide (BitVec.ofNat 64 (0x1000 + 4 * entry.2) ∈ ecallPCs)
      else true) = true := by decide

theorem fetched_ecall_position (s : MachineState)
    (fetched : fetch SphincsMaskedImages.keygen s = some (.base .ECALL)) :
    s.pc ∈ ecallPCs := by
  have hword : ∃ word,
      SphincsMaskedImages.keygen.code[(s.pc.toNat - 0x1000) / 4]? = some word ∧
      decodeInstruction word = some (.base .ECALL) := by
    unfold fetch at fetched
    split at fetched
    · simp at fetched
    · simpa [Option.bind_eq_some_iff] using fetched
  obtain ⟨word, hget, hdecode⟩ := hword
  let i := (s.pc.toNat - 0x1000) / 4
  have hmem : (word, i) ∈ SphincsMaskedImages.keygen.code.zipIdx := by
    have hzip : (SphincsMaskedImages.keygen.code.zipIdx)[i]? = some (word, i) := by
      rw [List.getElem?_zipIdx]
      simpa [i, hget]
    obtain ⟨hiZip, heq⟩ := List.getElem?_eq_some_iff.mp hzip
    rw [← heq]
    exact List.getElem_mem hiZip
  have hs := (List.all_eq_true.mp all_ecall_positions) _ hmem
  simp only [hdecode, beq_self_eq_true, ite_true] at hs
  obtain ⟨hge, haligned⟩ :=
    KeygenControlStep.fetch_alignment s (.base .ECALL) fetched
  have hpc := KeygenControlStep.pc_of_index s hge haligned
  rw [← hpc]
  exact of_decide_eq_true hs

def haltSchedule : List (Word × Instr) :=
  [(0x1e08, .ADDI .x5 .x0 0), (0x1e0c, .ADDI .x10 .x0 1)]

theorem halt_code : ∀ entry ∈ haltSchedule,
    SphincsVerifierFtsRootCopy.instructionAt SphincsMaskedImages.keygen
      entry.1 = some (.base entry.2) := by decide

theorem halt_checked (s : MachineState) (hpc : s.pc = 0x1e08) :
    Checked haltSchedule s := by
  simp [Checked, haltSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, signExtend12, MachineState.getReg_setReg_eq, hpc]

theorem halt_reached_controls (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s) (site_pc : s.pc = 0x1e10) :
    s.getReg .x5 = 0 ∧ s.getReg .x10 = 1 := by
  have init_safe : initial.pc ∉ KeygenWideControl.wideSensitivePCs := by
    rw [initial_pc]
    decide
  have safe : ∀ j : Nat, j < 8 →
      (0x1e10 : Word) - BitVec.ofNat 64 (4 * j) ∈
        KeygenWideControl.wideSensitivePCs :=
    literal_site_safe 0x1e10 (by decide)
  obtain ⟨start, _, start_pc, block⟩ :=
    peel_setup hash initial 0x1e10 init_safe safe 2 0 s (by decide)
      reached (by simpa using site_pc)
  have start_pc' : start.pc = 0x1e08 := by simpa using start_pc
  have other := checked_sound SphincsMaskedImages.keygen haltSchedule
    halt_code start (halt_checked start start_pc')
  have hend : s = runSchedule haltSchedule start := by
    exact ordinarySteps_unique block (by simpa [haltSchedule] using other)
  rw [hend]
  simp [runSchedule, haltSchedule, execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem hash_site_selector (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s)
    (site : s.pc ∈ KeygenScratchSemantics.keygenHashPCs) :
    s.getReg .x5 = 1 := by
  simp only [KeygenScratchSemantics.keygenHashPCs,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at site
  rcases site with h | h | h | h | h | h | h | h
  · exact (standard_reached_controls hash initial s 0x10d4 576
      (by decide) initial_pc reached h).2.2.2
  · exact (standard_reached_controls hash initial s 0x1224 576
      (by decide) initial_pc reached h).2.2.2
  · exact (standard_reached_controls hash initial s 0x1374 480
      (by decide) initial_pc reached h).2.2.2
  · exact (long_reached_controls hash initial s initial_pc reached h).2.2.2
  · exact (standard_reached_controls hash initial s 0x177c 640
      (by decide) initial_pc reached h).2.2.2
  · exact (standard_reached_controls hash initial s 0x19ec 480
      (by decide) initial_pc reached h).2.2.2
  · exact (standard_reached_controls hash initial s 0x1b5c 576
      (by decide) initial_pc reached h).2.2.2
  · exact (mac_reached_controls hash initial s initial_pc reached h).2.2.2

theorem reached_ecall_pc_of_selector (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s)
    (fetched : fetch SphincsMaskedImages.keygen s = some (.base .ECALL))
    (selector : s.getReg .x5 = 0) : s.pc = 0x1e10 := by
  have hpos := fetched_ecall_position s fetched
  simp only [ecallPCs, List.mem_append, List.mem_singleton] at hpos
  rcases hpos with hhash | hhalt
  · have hone := hash_site_selector hash initial s initial_pc reached hhash
    simp [selector] at hone
  · exact hhalt

theorem reached_hash_pc_of_selector (hash : Legacy.Hash)
    (initial s : MachineState) (initial_pc : initial.pc = 0x1000)
    (reached : Reach hash initial s)
    (fetched : fetch SphincsMaskedImages.keygen s = some (.base .ECALL))
    (selector : s.getReg .x5 = 1) :
    s.pc ∈ KeygenScratchSemantics.keygenHashPCs := by
  have hpos := fetched_ecall_position s fetched
  simp only [ecallPCs, List.mem_append, List.mem_singleton] at hpos
  rcases hpos with hhash | hhalt
  · exact hhash
  · have hzero := (halt_reached_controls hash initial s initial_pc reached hhalt).1
    simp [selector] at hzero

example (s : MachineState) (hpc : s.pc = 0x10d4-24) :
    Checked (standardSchedule 0x10d4 576) s := by
  simp [Checked, standardSchedule, execInstrBr, ordinaryStep,
    memoryArgumentsValid, accessValid, rangeValid, MEMORY_BYTES,
    signExtend12, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, hpc]

end SigGolfCandidate.KeygenSetup
