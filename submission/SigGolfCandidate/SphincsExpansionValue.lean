import SigGolfCandidate.SphincsExpansion
import SigGolfCandidate.SphincsVerifierFtsRootCopy
import SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
import SigGolfCandidate.Memory
import RiscvZkvm.Rv64.Logic.WordOps

/-! The expansion image's word-copy loop preserves the supplied signature data. -/

namespace SigGolfCandidate.Sphincs.ExpansionValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Sphincs.Expansion
open SigGolfCandidate.SphincsVerifierFtsRootCopy
open SigGolfCandidate.SphincsVerifierFtsRootCopyBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem copy_code : CopyCode SphincsImages.expand 0x1014 := by decide

theorem prefix_copy_invariant (s : MachineState) (pc : s.pc = 0x1000) :
    CopyInvariant 0x1014 0x20060 0x22ca0 1415 1415 (prefixState s) := by
  obtain ⟨_, hpc, hsrc, hdst, hcount⟩ := prefix_invariant s pc
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · simpa using hpc
  · simpa using hsrc
  · simpa using hdst
  · exact hcount

/-- The exact expansion code copies the first 11,320 signature bytes into the
    witness buffer, with a frame for all other words. -/
theorem copy_words (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final,
      OrdinarySteps SphincsImages.expand s 8495 final ∧
      final.pc = 0x102c ∧
      final.getReg .x6 = 0x22c98 ∧
      final.getReg .x7 = 0x258d8 ∧
      final.getReg .x10 = 0 ∧
      (∀ i, i < 1415 →
        final.getMem (wordAddress 0x22ca0 i) =
          s.getMem (wordAddress 0x20060 i)) ∧
      (∀ a, (∀ i, i < 1415 → a ≠ wordAddress 0x22ca0 i) →
        final.getMem a = s.getMem a) := by
  let start := prefixState s
  obtain ⟨final, loop, inv, copied, frame⟩ :=
    copy_all SphincsImages.expand 0x1014 copy_code
      0x20060 0x22ca0 1415 start
      (prefix_copy_invariant s pc)
      (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have pref := prefix_block s pc
    simpa only [expand, start] using pref.append loop
  · simpa [CopyInvariant] using inv.2.2.1
  · simpa [CopyInvariant] using inv.2.2.2.1
  · simpa [CopyInvariant] using inv.2.2.2.2.1
  · simpa [CopyInvariant] using inv.2.2.2.2.2
  · intro i hi
    rw [copied i hi]
    simp [start, prefixState, execInstrBr]
  · intro a ha
    rw [frame a ha]
    simp [start, prefixState, execInstrBr]

private theorem getWord32_setWord32_const (s : MachineState) (v : BitVec 32) :
    (s.setWord32 0x258d8 v).getWord32 0x258d8 = v := by
  change extractWord32 (replaceWord32 (s.getMem 0x258d8) 0 v) 0 = v
  exact extractWord32_replaceWord32_same _ ⟨0, by decide⟩ _

theorem tail_copy_word32 (s : MachineState)
    (src : s.getReg .x6 = 0x22c98) (dst : s.getReg .x7 = 0x258d8) :
    (tailState s).getWord32 0x258d8 = s.getWord32 0x22c98 := by
  let loaded := execInstrBr s (.LWU .x11 .x6 0)
  have loadedDst : loaded.getReg .x7 = 0x258d8 := by
    simpa [loaded, execInstrBr, MachineState.getReg_setReg_ne] using dst
  have loadedValue : loaded.getReg .x11 = (s.getWord32 0x22c98).zeroExtend 64 := by
    simp [loaded, execInstrBr, signExtend12, src,
      MachineState.getReg_setReg_eq]
  change (execInstrBr loaded (.SW .x7 .x11 0)).getWord32 0x258d8 = _
  simp only [execInstrBr, signExtend12]
  rw [loadedDst, loadedValue]
  simpa [MachineState.getWord32, MachineState.getMem_setPC] using
    getWord32_setWord32_const loaded (s.getWord32 0x22c98)

private theorem extractByte_low32 (word : Word) (i : Fin 4) :
    extractByte word i.val = (extractWord32 word 0).extractLsb' (8 * i.val) 8 := by
  ext j hj
  have bound : 8 * i.val + j < 32 := by have := i.isLt; omega
  simp [extractByte, extractWord32, Nat.mul_comm]; omega

theorem tail_copy_last_byte (s : MachineState)
    (src : s.getReg .x6 = 0x22c98) (dst : s.getReg .x7 = 0x258d8)
    (i : Fin 4) :
    (tailState s).getByte (BitVec.ofNat 64 (0x258d8 + i.val)) =
      s.getByte (BitVec.ofNat 64 (0x22c98 + i.val)) := by
  rw [getByte_word (tailState s) 0x258d8 i.val (by decide) (by omega),
    getByte_word s 0x22c98 i.val (by decide) (by omega)]
  have hi : i.val / 8 = 0 := Nat.div_eq_of_lt (by have := i.isLt; omega)
  simp only [hi, wordAddress, Nat.mul_zero, Nat.add_zero]
  have hm : i.val % 8 = i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
  rw [hm]
  rw [extractByte_low32 _ i, extractByte_low32 _ i]
  change ((tailState s).getWord32 0x258d8).extractLsb' (8 * i.val) 8 =
    (s.getWord32 0x22c98).extractLsb' (8 * i.val) 8
  rw [tail_copy_word32 s src dst]

theorem tail_mem_other (s : MachineState)
    (dst : s.getReg .x7 = 0x258d8) (a : Word) (hne : a ≠ 0x258d8) :
    (tailState s).getMem a = s.getMem a := by
  let loaded := execInstrBr s (.LWU .x11 .x6 0)
  have loadedDst : loaded.getReg .x7 = 0x258d8 := by
    simpa [loaded, execInstrBr, MachineState.getReg_setReg_ne] using dst
  change (execInstrBr loaded (.SW .x7 .x11 0)).getMem a = _
  simp only [execInstrBr, signExtend12, MachineState.getMem_setPC]
  rw [loadedDst]
  change (loaded.setWord32 0x258d8 ((loaded.getReg .x11).truncate 32)).getMem a = _
  have align : alignToDword (0x258d8 : Word) = 0x258d8 := by decide
  rw [setWord32_eq, align]
  rw [MachineState.getMem_setMem_ne hne]
  simp [loaded, execInstrBr]

/-- Expansion preserves the complete 11,324-byte signature, including its
    final partial word, as the verifier witness. -/
theorem copy_bytes (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final,
      OrdinarySteps SphincsImages.expand s 8497 final ∧
      final.pc = 0x1034 ∧
      (∀ i, i < 11324 →
        final.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
          s.getByte (BitVec.ofNat 64 (0x20060 + i))) := by
  obtain ⟨before, block, beforePc, src, dst, count, copied, frame⟩ := copy_words s pc
  let final := tailState before
  have inv0 : Invariant 0 before := by
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · simpa using beforePc
    · simpa using src
    · simpa using dst
    · exact count
  have access := tail_accesses before inv0
  have tail := tail_block before beforePc access.1 access.2
  refine ⟨final, ?_, ?_, ?_⟩
  · simpa [final] using block.append tail
  · simpa [final] using tail_pc before beforePc
  · intro i hi
    by_cases hfirst : i < 11320
    · have hj : i / 8 < 1415 := by omega
      rw [getByte_word final 0x22ca0 i (by decide) (by omega),
        getByte_word s 0x20060 i (by decide) (by omega)]
      have hne : wordAddress 0x22ca0 (i / 8) ≠ (0x258d8 : Word) := by
        change wordAddress 0x22ca0 (i / 8) ≠ wordAddress 0x22ca0 1415
        exact wordAddress_injective 0x22ca0 1416 (by decide)
          (i / 8) 1415 (by omega) (by decide) (by omega)
      rw [tail_mem_other before dst _ hne, copied (i / 8) hj]
    · have jlt : i - 11320 < 4 := by omega
      have idx : i = 11320 + (i - 11320) := by omega
      have sourceWord : before.getMem 0x22c98 = s.getMem 0x22c98 := by
        apply frame
        intro j hj eq
        have hne := wordAddress_disjoint 0x20060 0x22ca0 1416
          (by decide) (by decide) (by decide) 1415 j (by decide) (by omega)
        change (0x22c98 : Word) ≠ wordAddress 0x22ca0 j at hne
        exact hne eq
      have sourceByte (j : Fin 4) :
          before.getByte (BitVec.ofNat 64 (0x22c98 + j.val)) =
            s.getByte (BitVec.ofNat 64 (0x22c98 + j.val)) := by
        rw [getByte_word before 0x22c98 j.val (by decide) (by omega),
          getByte_word s 0x22c98 j.val (by decide) (by omega)]
        have hj : j.val / 8 = 0 := Nat.div_eq_of_lt (by have := j.isLt; omega)
        simp only [hj, wordAddress, Nat.mul_zero, Nat.add_zero]
        exact congrArg (fun word => extractByte word (j.val % 8)) sourceWord
      rw [idx]
      simpa only [show 0x22ca0 + (11320 + (i - 11320)) =
          0x258d8 + (i - 11320) by omega,
        show 0x20060 + (11320 + (i - 11320)) =
          0x22c98 + (i - 11320) by omega] using
        (tail_copy_last_byte before src dst ⟨i - 11320, jlt⟩).trans
          (sourceByte ⟨i - 11320, jlt⟩)

theorem finish_byte (s : MachineState) (addr : Word) :
    (finishState s).getByte addr = s.getByte addr := by
  simp [finishState, execInstrBr, MachineState.getByte]

theorem executes_copy (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final,
      Executes hash SphincsImages.expand s 8500
        ⟨.success, final, 8500, 0, 0⟩ ∧
      (∀ i, i < 11324 →
        final.getByte (BitVec.ofNat 64 (0x22ca0 + i)) =
          s.getByte (BitVec.ofNat 64 (0x20060 + i))) := by
  obtain ⟨after, block, afterPc, copied⟩ := copy_bytes s pc
  let final := finishState after
  have tail := finish hash after afterPc
  refine ⟨final, ?_, ?_⟩
  · have trace := (show OrdinarySteps SphincsImages.expand s 8497 after from block)
      |>.then_executes tail
    simpa [final, expand, Execution.charge] using trace
  · intro i hi
    rw [finish_byte]
    exact copied i hi

theorem readBuffer_copy (hash : Hash) (s : MachineState) (pc : s.pc = 0x1000) :
    ∃ final,
      Executes hash SphincsImages.expand s 8500
        ⟨.success, final, 8500, 0, 0⟩ ∧
      readBuffer final 0x22ca0 11324 = readBuffer s 0x20060 11324 := by
  obtain ⟨final, trace, copied⟩ := executes_copy hash s pc
  refine ⟨final, trace, ?_⟩
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8 * 11324))
  apply Memory.foldl_eq_on
  intro i hi acc
  rw [copied i (by simpa using hi)]

theorem runWith_copy (hash : Hash)
    (input : Input SphincsSubmission.submission.sizes .expand)
    (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .expand input = some state)
    (pc : state.pc = 0x1000) :
    SphincsSubmission.submission.runWith hash .expand input =
      ⟨some (readBuffer state 0x20060 11324), true, 8500, 0, 0⟩ := by
  obtain ⟨final, trace, copied⟩ := readBuffer_copy hash state pc
  have run := runWith_of_executes SphincsSubmission.submission hash .expand
    input state 8500 ⟨.success, final, 8500, 0, 0⟩ loaded
    (by simpa [SphincsSubmission.submission] using trace)
    (by decide)
  change SphincsSubmission.submission.runWith hash .expand input =
    ⟨some (readBuffer final 0x22ca0 11324), true, 8500, 0, 0⟩ at run
  rw [copied] at run
  exact run

theorem loaded_signature
    (input : Input SphincsSubmission.submission.sizes .expand)
    (state : MachineState)
    (loaded : initialState SphincsSubmission.submission .expand input = some state) :
    readBuffer state 0x20060 11324 = input.2.2 := by
  rcases input with ⟨message, pk, signature⟩
  have valid := SphincsSubmission.admissible.2 Phase.expand
  unfold initialState at loaded
  rw [if_pos valid] at loaded
  simp only [inputBuffers, List.foldl_cons, List.foldl_nil] at loaded
  cases loaded
  rw [Memory.readBuffer_setReg]
  exact Memory.read_write_buffer _ 0x20060 11324 signature
    (by decide) (by decide)

/-- The exact expansion image returns the compact signature unchanged as its
    witness for every input and oracle. -/
theorem runWith_expand (hash : Hash)
    (message : Message) (pk : PublicKey)
    (signature : Bytes SphincsSubmission.submission.sizes.signature) :
    SphincsSubmission.submission.runWith hash .expand (message, pk, signature) =
      ⟨some signature, true, 8500, 0, 0⟩ := by
  obtain ⟨state, loaded, pc⟩ := initialState_exists
    SphincsSubmission.submission SphincsSubmission.admissible
    .expand (message, pk, signature)
  rw [runWith_copy hash (message, pk, signature) state loaded pc]
  rw [loaded_signature (message, pk, signature) state loaded]

/-- info: 'SigGolfCandidate.Sphincs.ExpansionValue.runWith_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runWith_expand

end SigGolfCandidate.Sphincs.ExpansionValue
