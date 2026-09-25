import SigGolfCandidate.SphincsVerifierWotsRootCopy
import SigGolfCandidate.SphincsVerifierCopy20DataGeneral

namespace SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierCopy20DataGeneral
open SigGolfCandidate.SphincsVerifierWotsChainEnd
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private def word (base : Nat) (i : Fin 5) : Word :=
  BitVec.ofNat 64 (base + 4 * i.val)

@[simp] private theorem word32_setPC (state : MachineState)
    (pc address : Word) :
    (state.setPC pc).getWord32 address = state.getWord32 address := rfl

@[simp] private theorem word32_setReg (state : MachineState)
    (reg : Reg) (value address : Word) :
    (state.setReg reg value).getWord32 address =
      state.getWord32 address := by
  simp [MachineState.getWord32]

theorem copyWord_source_general (state : MachineState)
    (sourceBase destinationBase : Nat)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (written read : Fin 5)
    (disjoint : ∀ i j : Fin 5,
      alignToDword (word sourceBase j) ≠
        alignToDword (word destinationBase i)) :
    (copyWordState written state).getWord32 (word sourceBase read) =
      state.getWord32 (word sourceBase read) := by
  have dst : state.getReg .x7 +
      signExtend12 (4#12 * BitVec.ofNat 12 written.val) =
      word destinationBase written := by
    fin_cases written <;> simp [word, destination, signExtend12,
      BitVec.ofNat_add]
  simp only [MachineState.getWord32]
  rw [copyWord_mem_frame written state _ (by rw [dst]; exact disjoint written read)]

theorem copyWord_other_general (state : MachineState)
    (destinationBase : Nat)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (written read : Fin 5) (different : written ≠ read)
    (separate : ∀ i j : Fin 5, i ≠ j →
      alignToDword (word destinationBase i) ≠
        alignToDword (word destinationBase j) ∨
      byteOffset (word destinationBase i) / 4 ≠
        byteOffset (word destinationBase j) / 4) :
    (copyWordState written state).getWord32
      (word destinationBase read) =
      state.getWord32 (word destinationBase read) := by
  let pre := (state.setReg .x13
    ((state.getWord32 (state.getReg .x6 +
      signExtend12 (4#12 * BitVec.ofNat 12 written.val))).zeroExtend 64)).setPC
      (state.pc + 4)
  have dst : pre.getReg .x7 +
      signExtend12 (4#12 * BitVec.ofNat 12 written.val) =
      word destinationBase written := by
    fin_cases written <;> simp [pre, word, destination, signExtend12,
      BitVec.ofNat_add, MachineState.getReg_setReg_ne]
  have preRead : pre.getWord32 (word destinationBase read) =
      state.getWord32 (word destinationBase read) := by
    simp [pre, MachineState.getWord32]
  change (pre.setWord32
    (pre.getReg .x7 + signExtend12
      (4#12 * BitVec.ofNat 12 written.val))
    (BitVec.truncate 32 (pre.getReg .x13))).getWord32
      (word destinationBase read) = _
  rw [dst]
  have preserved := getWord32_setWord32_other pre
    (word destinationBase written) (word destinationBase read)
    (BitVec.truncate 32 (pre.getReg .x13))
    (separate written read different)
  exact preserved.trans preRead

private def CopyInv (original : MachineState)
    (sourceBase destinationBase count : Nat)
    (state : MachineState) : Prop :=
  state.getReg .x6 = BitVec.ofNat 64 sourceBase ∧
  state.getReg .x7 = BitVec.ofNat 64 destinationBase ∧
  (∀ index : Fin 5,
    state.getWord32 (word sourceBase index) =
      original.getWord32 (word sourceBase index)) ∧
  (∀ index : Fin 5, index.val < count →
    state.getWord32 (word destinationBase index) =
      original.getWord32 (word sourceBase index))

private theorem copyStep (original state : MachineState)
    (sourceBase destinationBase : Nat)
    (written : Fin 5)
    (disjoint : ∀ i j : Fin 5,
      alignToDword (word sourceBase j) ≠
        alignToDword (word destinationBase i))
    (separate : ∀ i j : Fin 5, i ≠ j →
      alignToDword (word destinationBase i) ≠
        alignToDword (word destinationBase j) ∨
      byteOffset (word destinationBase i) / 4 ≠
        byteOffset (word destinationBase j) / 4)
    (inv : CopyInv original sourceBase destinationBase written.val state) :
    CopyInv original sourceBase destinationBase (written.val + 1)
      (copyWordState written state) := by
  rcases inv with ⟨source, destination, sourceWords, copiedWords⟩
  obtain ⟨sourceAfter, destinationAfter⟩ :=
    copyWord_pointers written state
  refine ⟨sourceAfter.trans source, destinationAfter.trans destination,
    ?_, ?_⟩
  · intro index
    rw [copyWord_source_general state sourceBase destinationBase
      destination written index disjoint]
    exact sourceWords index
  · intro index before
    by_cases same : written = index
    · subst index
      calc
        (copyWordState written state).getWord32
            (word destinationBase written) =
          state.getWord32 (word sourceBase written) := by
            simpa only [word] using
              copyWord_data_general written state sourceBase
                destinationBase source destination
        _ = original.getWord32 (word sourceBase written) :=
          sourceWords written
    · rw [copyWord_other_general state destinationBase destination
        written index same separate]
      have smaller : index.val < written.val := by
        have unequal : written.val ≠ index.val :=
          fun equality => same (Fin.ext equality)
        omega
      exact copiedWords index smaller

theorem copy20_data (state : MachineState)
    (sourceBase destinationBase : Nat)
    (source : state.getReg .x6 = BitVec.ofNat 64 sourceBase)
    (destination : state.getReg .x7 = BitVec.ofNat 64 destinationBase)
    (disjoint : ∀ i j : Fin 5,
      alignToDword (word sourceBase j) ≠
        alignToDword (word destinationBase i))
    (separate : ∀ i j : Fin 5, i ≠ j →
      alignToDword (word destinationBase i) ≠
        alignToDword (word destinationBase j) ∨
      byteOffset (word destinationBase i) / 4 ≠
        byteOffset (word destinationBase j) / 4)
    (index : Fin 5) :
    (copyRootState state).getWord32 (word destinationBase index) =
      state.getWord32 (word sourceBase index) := by
  have initial : CopyInv state sourceBase destinationBase 0 state := by
    refine ⟨source, destination, fun _ => rfl, ?_⟩
    intro index impossible
    omega
  have s0 := copyStep state state sourceBase destinationBase 0
    disjoint separate initial
  have s1 := copyStep state (copyWordState 0 state)
    sourceBase destinationBase 1 disjoint separate s0
  have s2 := copyStep state
    (copyWordState 1 (copyWordState 0 state))
    sourceBase destinationBase 2 disjoint separate s1
  have s3 := copyStep state
    (copyWordState 2 (copyWordState 1 (copyWordState 0 state)))
    sourceBase destinationBase 3 disjoint separate s2
  have s4 := copyStep state
    (copyWordState 3 (copyWordState 2
      (copyWordState 1 (copyWordState 0 state))))
    sourceBase destinationBase 4 disjoint separate s3
  exact s4.2.2.2 index (by have := index.isLt; omega)

private theorem endpoint_disjoint (chain : Fin 52) (i j : Fin 5) :
    alignToDword (word 0x44b00 j) ≠
      alignToDword (word (0x44300 + 20 * chain.val) i) := by
  fin_cases chain <;> fin_cases i <;> fin_cases j <;> decide

private theorem endpoint_lanes (chain : Fin 52) (i j : Fin 5)
    (different : i ≠ j) :
    alignToDword (word (0x44300 + 20 * chain.val) i) ≠
      alignToDword (word (0x44300 + 20 * chain.val) j) ∨
    byteOffset (word (0x44300 + 20 * chain.val) i) / 4 ≠
      byteOffset (word (0x44300 + 20 * chain.val) j) / 4 := by
  fin_cases chain <;> fin_cases i <;> fin_cases j <;>
    first | exact (different rfl).elim | decide

theorem endpointCopied_word (state : MachineState)
    (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (index : Fin 5) :
    (endpointCopied state).getWord32
      (word (0x44300 + 20 * chain.val) index) =
      state.getWord32 (word 0x44b00 index) := by
  let pre := endpointSourceState (endpointPointersState state)
  have source : pre.getReg .x6 = 0x44b00 := by
    simp [pre, endpointSourceState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have destination : pre.getReg .x7 =
      BitVec.ofNat 64 (0x44300 + 20 * chain.val) := by
    simpa [pre, endpointSourceState, execInstrBr,
      MachineState.getReg_setReg_ne] using
        endpointPointers_regs state chain counter
  have copied := copy20_data pre 0x44b00
    (0x44300 + 20 * chain.val) source destination
    (endpoint_disjoint chain) (endpoint_lanes chain) index
  have preFrame : pre.getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x44b00 index) := by
    simp [pre, endpointSourceState, endpointPointersState,
      execInstrBr, MachineState.getWord32]
  exact copied.trans preFrame

private theorem endpoint_cell_ne (chain : Fin 52)
    (index : Fin 5) :
    alignToDword (word (0x44300 + 20 * chain.val) index) ≠ 0x43028 ∧
    alignToDword (word (0x44300 + 20 * chain.val) index) ≠ 0x43050 := by
  fin_cases chain <;> fin_cases index <;> decide

theorem chainEnd_word (state : MachineState)
    (chain : Fin 52)
    (counter : state.getMem 0x43050 = BitVec.ofNat 64 chain.val)
    (index : Fin 5) :
    (chainEndState state).getWord32
      (word (0x44300 + 20 * chain.val) index) =
      state.getWord32 (word 0x44b00 index) := by
  let a := word (0x44300 + 20 * chain.val) index
  have ne := endpoint_cell_ne chain index
  have hn1 : alignToDword a ≠ 0x43028 := by simpa only [a] using ne.1
  have hn2 : alignToDword a ≠ 0x43050 := by simpa only [a] using ne.2
  have framePointer (s : MachineState) :
      (pointerAdvanceState s).getWord32 a = s.getWord32 a := by
    simp [pointerAdvanceState, execInstrBr, MachineState.getWord32,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    split_ifs with h
    · exact (hn1 h).elim
    · rfl
  have frameChain (s : MachineState) :
      (chainAdvanceState s).getWord32 a = s.getWord32 a := by
    simp [chainAdvanceState, execInstrBr, MachineState.getWord32,
      signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
    split_ifs with h
    · exact (hn2 h).elim
    · rfl
  have frameBranch (s : MachineState) :
      (chainBranchState s).getWord32 a = s.getWord32 a := by
    simp [chainBranchState, execInstrBr, MachineState.getWord32]
  change (chainBranchState (chainAdvanceState
    (pointerAdvanceState (endpointCopied state)))).getWord32 a = _
  rw [frameBranch, frameChain, framePointer]
  exact endpointCopied_word state chain counter index

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointCopy.copy20_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copy20_data

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointCopy.endpointCopied_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endpointCopied_word

/-- info: 'SigGolfCandidate.SphincsVerifierWotsEndpointCopy.chainEnd_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms chainEnd_word

end SigGolfCandidate.SphincsVerifierWotsEndpointCopy
