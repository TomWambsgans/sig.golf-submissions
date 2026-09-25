import SigGolfCandidate.SphincsVerifierFtsRootBytes
namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
set_option maxRecDepth 16384

theorem copyWord_word_frame (offset : Fin 5) (state : MachineState)
    (read : Word)
    (other : alignToDword (state.getReg .x7 + signExtend12
      (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠ byteOffset read / 4) :
    (copyWordState offset state).getWord32 read = state.getWord32 read := by
  simp only [copyWordState]
  simp [execInstrBr, signExtend12,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rw [getWord32_setWord32_other]
  · rfl
  · simpa [signExtend12] using other
end SigGolfCandidate.SphincsVerifierFtsPriorRoots

namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

private theorem byteOffset_ofNat_mod (number : Nat)
    (small : number < 2 ^ 64) :
    byteOffset (BitVec.ofNat 64 number) = number % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  have cast : (BitVec.ofNat 64 number).toNat = number := by
    simp only [BitVec.toNat_ofNat]
    omega
  rw [cast]
  change number &&& (2 ^ 3 - 1) = number % 8
  exact Nat.and_two_pow_sub_one_eq_mod number 3

private theorem sameLane_eq (a b : Word)
    (align : alignToDword a = alignToDword b)
    (lane : byteOffset a / 4 = byteOffset b / 4)
    (ha : byteOffset a % 4 = 0)
    (hb : byteOffset b % 4 = 0) : a = b := by
  have oa := byteOffset_lt_8 (addr := a)
  have ob := byteOffset_lt_8 (addr := b)
  have offset : byteOffset a = byteOffset b := by omega
  rw [← alignToDword_add_byteOffset a,
    ← alignToDword_add_byteOffset b, align, offset]

theorem wordLaneDistinct (a b : Nat)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (aa : a % 4 = 0) (bb : b % 4 = 0) (hne : a ≠ b) :
    alignToDword (BitVec.ofNat 64 a) ≠ alignToDword (BitVec.ofNat 64 b) ∨
      byteOffset (BitVec.ofNat 64 a) / 4 ≠
        byteOffset (BitVec.ofNat 64 b) / 4 := by
  by_contra notDistinct
  push Not at notDistinct
  have aoffset : byteOffset (BitVec.ofNat 64 a) % 4 = 0 := by
    rw [byteOffset_ofNat_mod a ha]
    omega
  have boffset : byteOffset (BitVec.ofNat 64 b) % 4 = 0 := by
    rw [byteOffset_ofNat_mod b hb]
    omega
  have eq := sameLane_eq _ _ notDistinct.1 notDistinct.2 aoffset boffset
  have natEq := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at natEq
  have : a = b := by omega
  exact hne this

end SigGolfCandidate.SphincsVerifierFtsPriorRoots

namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory

theorem copyRoot_word_frame (state : MachineState) (read : Word)
    (outside : ∀ offset : Fin 5,
      alignToDword (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset (state.getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠ byteOffset read / 4) :
    (copyRootState state).getWord32 read = state.getWord32 read := by
  let s1 := copyWordState 0 state
  let s2 := copyWordState 1 s1
  let s3 := copyWordState 2 s2
  let s4 := copyWordState 3 s3
  have d1 : s1.getReg .x7 = state.getReg .x7 := (copyWord_pointers 0 state).2
  have d2 : s2.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 1 s1).2.trans d1
  have d3 : s3.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 2 s2).2.trans d2
  have d4 : s4.getReg .x7 = state.getReg .x7 :=
    (copyWord_pointers 3 s3).2.trans d3
  change (copyWordState 4 s4).getWord32 read = state.getWord32 read
  rw [copyWord_word_frame 4 s4 read (by rw [d4]; exact outside 4),
    copyWord_word_frame 3 s3 read (by rw [d3]; exact outside 3),
    copyWord_word_frame 2 s2 read (by rw [d2]; exact outside 2),
    copyWord_word_frame 1 s1 read (by rw [d1]; exact outside 1),
    copyWord_word_frame 0 state read (outside 0)]

end SigGolfCandidate.SphincsVerifierFtsPriorRoots

namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsRootStore
open SigGolfCandidate.SphincsVerifierFtsTreeAdvance
open SigGolfCandidate.SphincsVerifierCopy

private theorem treeAdvance_word_frame (state : MachineState) (read : Word)
    (outside : alignToDword read ≠ 0x43040) :
    (treeAdvanceState state).getWord32 read = state.getWord32 read := by
  simp only [MachineState.getWord32]
  rw [treeAdvance_mem_frame state (alignToDword read) outside]

theorem treeFinish_prior_root_word (state : MachineState)
    (tree prior : FtsTree) (index : Fin 5)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (older : prior.val < tree.val) :
    (treeFinishState state).getWord32
      (BitVec.ofNat 64 (0x44100 + 20 * prior.val + 4 * index.val)) =
      state.getWord32
        (BitVec.ofNat 64 (0x44100 + 20 * prior.val + 4 * index.val)) := by
  let read := BitVec.ofNat 64 (0x44100 + 20 * prior.val + 4 * index.val)
  have outsideCounter : alignToDword read ≠ 0x43040 := by
    fin_cases prior <;> fin_cases index <;> decide
  have destination := rootStoreSetup_destination state tree counter
  have outside : ∀ offset : Fin 5,
      alignToDword ((rootStoreSetupState state).getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) ≠ alignToDword read ∨
      byteOffset ((rootStoreSetupState state).getReg .x7 + signExtend12
        (4#12 * BitVec.ofNat 12 offset.val)) / 4 ≠
          byteOffset read / 4 := by
    intro offset
    rw [destination]
    have address :
        BitVec.ofNat 64 (0x44100 + 20 * tree.val) +
          signExtend12 (4#12 * BitVec.ofNat 12 offset.val) =
        BitVec.ofNat 64 (0x44100 + 20 * tree.val + 4 * offset.val) := by
      fin_cases tree <;> fin_cases offset <;> decide
    rw [address]
    apply wordLaneDistinct
    · have h := tree.isLt
      simp only [ftsTrees] at h
      omega
    · have h := prior.isLt
      simp only [ftsTrees] at h
      omega
    · omega
    · omega
    · omega
  change (treeAdvanceState (copyRootState (rootStoreSetupState state))).getWord32
      read = state.getWord32 read
  rw [treeAdvance_word_frame _ read outsideCounter,
    copyRoot_word_frame _ read outside]
  simp only [MachineState.getWord32]
  rw [rootStoreSetup_mem]

end SigGolfCandidate.SphincsVerifierFtsPriorRoots

namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsGenericTree
open SigGolfCandidate.SphincsVerifierFtsRootBytes

theorem treeFinish_prior_root_bytes (state : MachineState)
    (tree prior : FtsTree) (i : Nat) (hi : i < 20)
    (counter : state.getMem 0x43040 = BitVec.ofNat 64 tree.val)
    (older : prior.val < tree.val) :
    (treeFinishState state).getByte
      (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) =
      state.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  calc
    _ = ((treeFinishState state).getWord32
          (BitVec.ofNat 64
            (0x44100 + 20 * prior.val + 4 * index.val))).extractLsb'
              (8 * byte.val) 8 := by
      convert rootSlot_word_byte (treeFinishState state) prior index byte using 1 <;>
        simp only [Nat.add_assoc, split]
    _ = (state.getWord32
          (BitVec.ofNat 64
            (0x44100 + 20 * prior.val + 4 * index.val))).extractLsb'
              (8 * byte.val) 8 := by
      rw [treeFinish_prior_root_word state tree prior index counter older]
    _ = state.getByte (BitVec.ofNat 64 (0x44100 + 20 * prior.val + i)) := by
      rw [← rootSlot_word_byte state prior index byte]
      simp only [Nat.add_assoc, split]

end SigGolfCandidate.SphincsVerifierFtsPriorRoots

namespace SigGolfCandidate.SphincsVerifierFtsPriorRoots
/-- info: 'SigGolfCandidate.SphincsVerifierFtsPriorRoots.treeFinish_prior_root_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeFinish_prior_root_bytes
end SigGolfCandidate.SphincsVerifierFtsPriorRoots
