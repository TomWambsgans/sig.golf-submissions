import SigGolfCandidate.SphincsBeta64Images
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
