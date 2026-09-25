import SigGolfCandidate.SphincsVerifierFtsRootsPayload

namespace SigGolfCandidate.SphincsVerifierFtsRootCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace LocalLoop
@[simp] theorem reg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

@[simp] theorem reg_ite (p : Prop) [Decidable p] (s t : MachineState) (r : Reg) :
    (if p then s else t).getReg r = if p then s.getReg r else t.getReg r := by split <;> rfl

@[simp] theorem pc_ite (p : Prop) [Decidable p] (s t : MachineState) :
    (if p then s else t).pc = if p then s.pc else t.pc := by split <;> rfl

@[simp] theorem mem_ite (p : Prop) [Decidable p] (s t : MachineState) (a : Word) :
    (if p then s else t).getMem a = if p then s.getMem a else t.getMem a := by split <;> rfl

@[simp] theorem pc_setPC (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl
@[simp] theorem reg_zero (s : MachineState) : s.getReg .x0 = 0 := rfl
@[simp] theorem mem_setMem (s : MachineState) (a v b : Word) :
    (s.setMem a v).getMem b = if b = a then v else s.getMem b := by simp [MachineState.setMem, MachineState.getMem]

def loopBody (s : MachineState) : MachineState :=
  let s := execInstrBr s (.LD .x11 .x6 0)
  let s := execInstrBr s (.SD .x7 .x11 0)
  let s := execInstrBr s (.ADDI .x6 .x6 8)
  let s := execInstrBr s (.ADDI .x7 .x7 8)
  execInstrBr s (.ADDI .x10 .x10 (-1))

def loopNext (s : MachineState) : MachineState :=
  execInstrBr (loopBody s) (.BNE .x10 .x0 (-20))


theorem loop_next_regs (s : MachineState) :
    (loopNext s).getReg .x6 = s.getReg .x6 + 8 ∧
    (loopNext s).getReg .x7 = s.getReg .x7 + 8 ∧
    (loopNext s).getReg .x10 = s.getReg .x10 - 1 := by
  unfold loopNext loopBody
  simp only [execInstrBr]
  simp [MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    signExtend12, BitVec.sub_eq_add_neg]

theorem loop_body_pc (s : MachineState) : (loopBody s).pc = s.pc + 20 := by
  simp [loopBody, execInstrBr, BitVec.add_assoc]

theorem loop_body_count (s : MachineState) : (loopBody s).getReg .x10 = s.getReg .x10 - 1 := by
  unfold loopBody
  simp [execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    signExtend12, BitVec.sub_eq_add_neg]

theorem loop_next_mem (s : MachineState) (address : BitVec 64) :
    (loopNext s).getMem address =
      if address = s.getReg .x7 then s.getMem (s.getReg .x6) else s.getMem address := by
  unfold loopNext loopBody
  simp only [execInstrBr]
  simp [signExtend12,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]


end LocalLoop

def instructionAt (image : Image) (pc : Word) : Option Instruction :=
  fetch image { regs := fun _ => 0, mem := fun _ => 0, pc := pc }

theorem fetch_at (image : Image) (s : MachineState) :
    fetch image s = instructionAt image s.pc := rfl

/-- The six encodings of the generated word-copy loop. -/
def CopyCode (image : Image) (pc : Word) : Prop :=
  instructionAt image pc = some (.base (.LD .x11 .x6 0)) ∧
  instructionAt image (pc + 4) = some (.base (.SD .x7 .x11 0)) ∧
  instructionAt image (pc + 8) = some (.base (.ADDI .x6 .x6 8)) ∧
  instructionAt image (pc + 12) = some (.base (.ADDI .x7 .x7 8)) ∧
  instructionAt image (pc + 16) = some (.base (.ADDI .x10 .x10 (-1))) ∧
  instructionAt image (pc + 20) = some (.base (.BNE .x10 .x0 (-20)))

instance (image : Image) (pc : Word) : Decidable (CopyCode image pc) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A complete copy iteration checked against the organizer's protected interpreter. -/
theorem copy_block (image : Image) (p : Word) (code : CopyCode image p)
    (s : MachineState) (pc : s.pc = p)
    (src : accessValid (s.getReg .x6) 8 = true)
    (dst : accessValid (s.getReg .x7) 8 = true) :
    OrdinarySteps image s 6 (LocalLoop.loopNext s) := by
  obtain ⟨c0,c1,c2,c3,c4,c5⟩ := code
  let s1 := execInstrBr s (.LD .x11 .x6 0)
  let s2 := execInstrBr s1 (.SD .x7 .x11 0)
  let s3 := execInstrBr s2 (.ADDI .x6 .x6 8)
  let s4 := execInstrBr s3 (.ADDI .x7 .x7 8)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (-1))
  apply OrdinarySteps.step s s1 _ (.base (.LD .x11 .x6 0)) 5
  · simpa only [fetch_at, pc] using c0
  · simp [s1, ordinaryStep, memoryArgumentsValid, signExtend12, src]
  apply OrdinarySteps.step s1 s2 _ (.base (.SD .x7 .x11 0)) 4
  · simpa only [fetch_at, s1, execInstrBr, MachineState.setPC, pc] using c1
  · have hd : accessValid (s1.getReg .x7) 8 = true := by
      simpa [s1, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC] using dst
    simp [s2, ordinaryStep, memoryArgumentsValid, signExtend12, hd]
  apply OrdinarySteps.step s2 s3 _ (.base (.ADDI .x6 .x6 8)) 3
  · simpa [fetch_at, s1, s2, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c2
  · rfl
  apply OrdinarySteps.step s3 s4 _ (.base (.ADDI .x7 .x7 8)) 2
  · simpa [fetch_at, s1, s2, s3, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c3
  · rfl
  apply OrdinarySteps.step s4 s5 _ (.base (.ADDI .x10 .x10 (-1))) 1
  · simpa [fetch_at, s1, s2, s3, s4, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c4
  · rfl
  apply OrdinarySteps.step s5 (LocalLoop.loopNext s) _ (.base (.BNE .x10 .x0 (-20))) 0
  · simpa [fetch_at, s1, s2, s3, s4, s5, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc] using c5
  · rfl
  exact OrdinarySteps.refl _

theorem copy_next_pc (s : MachineState) :
    (LocalLoop.loopNext s).pc = if s.getReg .x10 = 1 then s.pc + 24 else s.pc := by
  have decrement (x : Word) : x - 1#64 = 0#64 ↔ x = 1#64 :=
    BitVec.sub_left_inj (x := x) (y := 1) 1
  simp only [LocalLoop.loopNext, execInstrBr, LocalLoop.pc_ite, LocalLoop.pc_setPC,
    LocalLoop.loop_body_pc, LocalLoop.loop_body_count, LocalLoop.reg_zero, signExtend13]
  simp [decrement, BitVec.add_assoc]

/-- The HASH service accepts exactly the fixed buffers used by all four images. -/

def CopyInvariant (p : Word) (source destination total n : Nat) (s : MachineState) : Prop :=
  n ≤ total ∧ total ≤ 2097152 ∧
  s.pc = (if n = 0 then p + 24 else p) ∧
  s.getReg .x6 = BitVec.ofNat 64 (source + 8 * (total - n)) ∧
  s.getReg .x7 = BitVec.ofNat 64 (destination + 8 * (total - n)) ∧
  s.getReg .x10 = BitVec.ofNat 64 n

theorem copy_invariant_next (p : Word) (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total (n + 1) s) :
    CopyInvariant p source destination total n (LocalLoop.loopNext s) := by
  obtain ⟨hn, ht, pc, src, dst, count⟩ := inv
  have hp : s.pc = p := by simpa using pc
  have heq : BitVec.ofNat 64 (n + 1) = 1 ↔ n = 0 := by
    have hsmall : n + 1 < 2 ^ 64 := by omega
    constructor
    · intro h
      have value := congrArg BitVec.toNat h
      change (n + 1) % 2 ^ 64 = 1 at value
      rw [Nat.mod_eq_of_lt hsmall] at value
      omega
    · intro h
      subst n
      rfl
  refine ⟨by omega, ht, ?_, ?_, ?_, ?_⟩
  · rw [copy_next_pc, count, hp]
    simp only [heq]
  · rw [(LocalLoop.loop_next_regs s).1, src]
    change BitVec.ofNat 64 (source + 8 * (total - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(LocalLoop.loop_next_regs s).2.1, dst]
    change BitVec.ofNat 64 (destination + 8 * (total - (n + 1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [(LocalLoop.loop_next_regs s).2.2, count, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

theorem copy_accesses (p : Word) (source destination total n : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total (n + 1) s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0) :
    accessValid (s.getReg .x6) 8 = true ∧ accessValid (s.getReg .x7) 8 = true := by
  obtain ⟨hn, ht, _, src, dst, _⟩ := inv
  simp only [MEMORY_BYTES] at srcbound dstbound
  have hs : source + 8 * (total - (n + 1)) < 2 ^ 64 := by omega
  have hd : destination + 8 * (total - (n + 1)) < 2 ^ 64 := by omega
  simp [accessValid, rangeValid, src, dst, BitVec.toNat_ofNat,
    MEMORY_BYTES, Nat.add_mod, Nat.mul_mod,
    srcalign, dstalign]
  omega

theorem ordinary_trans (image : Image) (s t u : MachineState) (m n : Nat)
    (first : OrdinarySteps image s m t) (second : OrdinarySteps image t n u) :
    OrdinarySteps image s (n + m) u := by
  induction first with
  | refl => simpa using second
  | step s t v instruction m hf hs block ih =>
    simpa only [Nat.add_assoc] using OrdinarySteps.step s t u instruction (n + m) hf hs (ih second)

/-- Every in-bounds generated copy loop terminates after exactly six instructions per word.
The theorem permits overlapping buffers and arbitrary memory contents. -/

def wordAddress (base i : Nat) : Word := BitVec.ofNat 64 (base + 8 * i)

/-- Copied prefix plus a complete frame condition for every other memory word. -/
def CopyContent (source destination total n : Nat) (original current : MachineState) : Prop :=
  (∀ a, (∀ j, j < total - n → a ≠ wordAddress destination j) →
    current.getMem a = original.getMem a) ∧
  (∀ i, i < total - n → current.getMem (wordAddress destination i) =
    original.getMem (wordAddress source i))

theorem wordAddress_injective (base total : Nat) (bound : base + 8 * total ≤ MEMORY_BYTES)
    (i j : Nat) (hi : i < total) (hj : j < total) (ne : i ≠ j) :
    wordAddress base i ≠ wordAddress base j := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have hbi : base + 8 * i < 2 ^ 64 := by simp only [MEMORY_BYTES] at bound; omega
  have hbj : base + 8 * j < 2 ^ 64 := by simp only [MEMORY_BYTES] at bound; omega
  change (base + 8 * i) % 2 ^ 64 = (base + 8 * j) % 2 ^ 64 at values
  rw [Nat.mod_eq_of_lt hbi, Nat.mod_eq_of_lt hbj] at values
  omega

/-- Disjoint byte intervals give the nonaliasing condition used by the copy proof. -/
theorem wordAddress_disjoint (source destination total : Nat)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (separate : source + 8 * total ≤ destination ∨ destination + 8 * total ≤ source)
    (i j : Nat) (hi : i < total) (hj : j < total) :
    wordAddress source i ≠ wordAddress destination j := by
  intro eq
  have values := congrArg BitVec.toNat eq
  have hsi : source + 8 * i < 2 ^ 64 := by simp only [MEMORY_BYTES] at srcbound; omega
  have hdj : destination + 8 * j < 2 ^ 64 := by simp only [MEMORY_BYTES] at dstbound; omega
  change (source + 8 * i) % 2 ^ 64 = (destination + 8 * j) % 2 ^ 64 at values
  rw [Nat.mod_eq_of_lt hsi, Nat.mod_eq_of_lt hdj] at values
  omega

theorem copy_content_next (p : Word) (source destination total n : Nat)
    (original s : MachineState) (inv : CopyInvariant p source destination total (n + 1) s)
    (content : CopyContent source destination total (n + 1) original s)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (disjoint : ∀ i j, i < total → j < total →
      wordAddress source i ≠ wordAddress destination j) :
    CopyContent source destination total n original (LocalLoop.loopNext s) := by
  obtain ⟨hn, _, _, src, dst, _⟩ := inv
  have current : total - (n + 1) < total := by omega
  change s.getReg .x6 = wordAddress source (total - (n + 1)) at src
  change s.getReg .x7 = wordAddress destination (total - (n + 1)) at dst
  constructor
  · intro a outside
    rw [LocalLoop.loop_next_mem, dst, if_neg (outside _ (by omega))]
    exact content.1 a (fun j hj => outside j (by omega))
  · intro i hi
    have hib : i < total := by omega
    by_cases eq : i = total - (n + 1)
    · subst i
      rw [LocalLoop.loop_next_mem, dst, src, if_pos rfl]
      exact content.1 _ (fun j hj => disjoint _ j current (by omega))
    · rw [LocalLoop.loop_next_mem, dst,
        if_neg (wordAddress_injective destination total dstbound i _ hib current eq)]
      exact content.2 i (by omega)

/-- The generated copy loop has both its actual execution derivation and its precise
memory effect. It is independent of the particular image, buffer sizes, and contents. -/
theorem copy_loop_content (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total n : Nat) (original s : MachineState)
    (inv : CopyInvariant p source destination total n s)
    (content : CopyContent source destination total n original s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (disjoint : ∀ i j, i < total → j < total →
      wordAddress source i ≠ wordAddress destination j) :
    ∃ final, OrdinarySteps image s (6 * n) final ∧
      CopyInvariant p source destination total 0 final ∧
      CopyContent source destination total 0 original final := by
  induction n generalizing s with
  | zero => exact ⟨s, OrdinarySteps.refl _, inv, content⟩
  | succ n ih =>
    have access := copy_accesses p source destination total n s inv srcbound dstbound srcalign dstalign
    have block := copy_block image p code s (by simpa using inv.2.2.1) access.1 access.2
    obtain ⟨final, tail, done, output⟩ := ih (LocalLoop.loopNext s)
      (copy_invariant_next p source destination total n s inv)
      (copy_content_next p source destination total n original s inv content dstbound disjoint)
    refine ⟨final, ?_, done, output⟩
    simpa only [Nat.mul_add, Nat.mul_one] using ordinary_trans image s _ final 6 (6 * n) block tail

/-- Entry-to-exit copy correctness for disjoint buffers, including the frame condition. -/
theorem copy_all (image : Image) (p : Word) (code : CopyCode image p)
    (source destination total : Nat) (s : MachineState)
    (inv : CopyInvariant p source destination total total s)
    (srcbound : source + 8 * total ≤ MEMORY_BYTES)
    (dstbound : destination + 8 * total ≤ MEMORY_BYTES)
    (srcalign : source % 8 = 0) (dstalign : destination % 8 = 0)
    (separate : source + 8 * total ≤ destination ∨ destination + 8 * total ≤ source) :
    ∃ final, OrdinarySteps image s (6 * total) final ∧
      CopyInvariant p source destination total 0 final ∧
      (∀ i, i < total → final.getMem (wordAddress destination i) = s.getMem (wordAddress source i)) ∧
      (∀ a, (∀ i, i < total → a ≠ wordAddress destination i) → final.getMem a = s.getMem a) := by
  have initial : CopyContent source destination total total s s := by
    constructor
    · intro _ _; rfl
    · intro i hi; omega
  obtain ⟨final, trace, done, output⟩ := copy_loop_content image p code source destination total total s s
    inv initial srcbound dstbound srcalign dstalign
    (wordAddress_disjoint source destination total srcbound dstbound separate)
  exact ⟨final, trace, done, by simpa using output.2, by simpa using output.1⟩


/-- The generated post-FORS loop is exactly the already certified six-instruction
    word-copy idiom. -/
theorem rootCopy_code : CopyCode SphincsImages.verify 0x1c74 := by decide

/-- Starting at the generated copy loop with its documented registers, all
    60 root words are copied from the forest slots into the HASH buffer. -/
theorem rootCopy_all (state : MachineState)
    (pc : state.pc = 0x1c74)
    (source : state.getReg .x6 = 0x44100)
    (destination : state.getReg .x7 = 0x40028)
    (count : state.getReg .x10 = 60) :
    ∃ final,
      OrdinarySteps SphincsImages.verify state 360 final ∧
      final.pc = 0x1c8c ∧
      (∀ i, i < 60 →
        final.getMem (BitVec.ofNat 64 (0x40028 + 8 * i)) =
          state.getMem (BitVec.ofNat 64 (0x44100 + 8 * i))) ∧
      (∀ address,
        (∀ i, i < 60 →
          address ≠ BitVec.ofNat 64 (0x40028 + 8 * i)) →
        final.getMem address = state.getMem address) := by
  have inv : CopyInvariant 0x1c74 0x44100 0x40028 60 60 state := by
    refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · simpa using pc
    · simpa using source
    · simpa using destination
    · simpa using count
  obtain ⟨final, trace, done, copied, frame⟩ :=
    copy_all SphincsImages.verify 0x1c74 rootCopy_code
      0x44100 0x40028 60 state inv
      (by decide) (by decide) (by decide) (by decide)
      (Or.inr (by decide))
  refine ⟨final, by simpa using trace, ?_, copied, frame⟩
  simpa [CopyInvariant] using done.2.2.1

/-- info: 'SigGolfCandidate.SphincsVerifierFtsRootCopy.rootCopy_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootCopy_all

end SigGolfCandidate.SphincsVerifierFtsRootCopy
