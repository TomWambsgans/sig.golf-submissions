import SigGolfCandidate.SphincsVerifierWotsEndpointAll
import SigGolfCandidate.SphincsVerifierMessageAnswer
import SigGolfCandidate.SphincsVerifierFtsGenericBytes
import SigGolfCandidate.SphincsBridge

namespace SigGolfCandidate.SphincsVerifierWotsValue
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsEndpointCopy
open SigGolfCandidate.SphincsVerifierWotsStepNext
open SigGolfCandidate.SphincsVerifierWotsStepIteration
open SigGolfCandidate.SphincsVerifierWotsStepHashReady
open SigGolfCandidate.SphincsVerifierFtsGenericBytes
open SigGolfCandidate.SphincsBridge
open SphincsSecurity
open SigGolfCandidate.SphincsVerifierCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem stepAnswerCopy_word (state : MachineState)
    (index : Fin 5) :
    (stepAnswerCopyState state).getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x42000 index) := by
  let pre := stepAnswerPointersState state
  have source : pre.getReg .x6 = 0x42000 := by
    simp [pre, stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  have destination : pre.getReg .x7 = 0x44b00 := by
    simp [pre, stepAnswerPointersState, execInstrBr, signExtend12,
      MachineState.getReg_setReg_eq]
  have copied := copy20_data pre 0x42000 0x44b00 source destination
    (by intro i j; fin_cases i <;> fin_cases j <;> decide)
    (by intro i j different
        fin_cases i <;> fin_cases j <;>
          first | exact (different rfl).elim | decide)
    index
  have preFrame : pre.getWord32 (word 0x42000 index) =
      state.getWord32 (word 0x42000 index) := by
    simp [pre, stepAnswerPointersState, execInstrBr,
      MachineState.getWord32]
  exact copied.trans preFrame

theorem stepReturn_valueFrame (state : MachineState)
    (index : Fin 5) :
    (stepReturnState state).getWord32 (word 0x44b00 index) =
      state.getWord32 (word 0x44b00 index) := by
  fin_cases index <;>
    simp [stepReturnState, stepAdvanceState, execInstrBr,
      MachineState.getWord32, signExtend12,
      MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, word, alignToDword,
      byteOffset]

theorem writeHash_word32 (state : MachineState) (answer : BitVec 256)
    (destination : state.getReg .x12 = 0x42000)
    (index : Fin 5) :
    (writeHash state answer).getWord32 (word 0x42000 index) =
      answer.extractLsb' (32 * index.val) 32 := by
  fin_cases index <;>
    simp [writeHash, MachineState.writeWords_cons,
      MachineState.getWord32, word, destination,
      MachineState.getMem_setMem_ne,
      MachineState.getMem_setMem_eq,
      extractWord32, alignToDword,
      byteOffset] <;>
    (ext bit (hbit : bit < 32);
      simp;
      first
      | omega
      | have hb : 32 + bit < 64 := by omega
        simp [hb, show 64 + (32 + bit) = 96 + bit by omega])

theorem stepNext_value (hash : Hash) (state : MachineState)
    (index : Fin 5) :
    (stepNext hash state).getWord32 (word 0x44b00 index) =
      (hash (hashInput (stepReady state))).extractLsb'
        (32 * index.val) 32 := by
  let answer := hash (hashInput (stepReady state))
  have destination : (stepReady state).getReg .x12 = 0x42000 := by
    simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  change (stepReturnState
      (stepAnswerCopyState (writeHash (stepReady state) answer))).getWord32
        (word 0x44b00 index) = _
  rw [stepReturn_valueFrame,
    stepAnswerCopy_word,
    writeHash_word32 (stepReady state) answer destination]

theorem stepNext_valueByte (hash : Hash) (state : MachineState)
    (i : Nat) (hi : i < 20) :
    (stepNext hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (hash (hashInput (stepReady state))).extractLsb' (8 * i) 8 := by
  let index : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * index.val + byte.val = i := by
    dsimp [index, byte]
    omega
  rw [← split,
    show 0x44b00 + (4 * index.val + byte.val) =
      0x44b00 + 4 * index.val + byte.val by omega,
    variableWord_byte _ 0x44b00 (by decide) (by decide) index byte]
  have value := stepNext_value hash state index
  simp only [word] at value
  rw [value]
  ext bit (hbit : bit < 8)
  simp
  have hb : 8 * byte.val + bit < 32 := by have := byte.isLt; omega
  simp [hb, show 32 * index.val + (8 * byte.val + bit) =
    8 * (4 * index.val + byte.val) + bit by omega]

theorem stepNext_valueByte_of_query (hash : Hash) (state : MachineState)
    (input : HashInput)
    (query : hashInput (stepReady state) = toQuery input)
    (i : Nat) (hi : i < 20) :
    (stepNext hash state).getByte (BitVec.ofNat 64 (0x44b00 + i)) =
      (truncateHash (hash (toQuery input))).extractLsb' (8 * i) 8 := by
  rw [stepNext_valueByte hash state i hi, query]
  exact
    (BitVec.extractLsb'_extractLsb'_of_le
      (x := hash (toQuery input))
      (start := 8 * i) (len := 8) (len' := digestBits)
      (by unfold digestBits; omega)).symm

def chainInput (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : HashInput :=
  tweakableHashInput parameter (.chain layer tree leaf chain step)
    (bytesLE 20 value)

theorem chainInput_length (parameter : PublicParameter) (layer : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    (chainInput parameter layer tree leaf chain step value).length = 60 := by
  simp [chainInput, tweakableHashInput, tweakBytes, fieldBytes, bytesLE]

theorem stepReady_chainQuery_of_bytes (state : MachineState)
    (parameter : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest)
    (bytes : ∀ i, (hi : i < 60) →
      (stepReady state).getByte (BitVec.ofNat 64 (0x40000 + i)) =
        ((chainInput parameter layer tree leaf chain step value).map
          UInt8.toBitVec)[i]'(by
            rw [List.length_map, chainInput_length]; exact hi)) :
    hashInput (stepReady state) =
      toQuery (chainInput parameter layer tree leaf chain step value) := by
  apply Serialization.hashInput_of_list (stepReady state) 0x40000
    ((chainInput parameter layer tree leaf chain step value).map UInt8.toBitVec)
  · simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne]
  · simp [stepReady, stepHashReadyState, stepHashRegistersState,
      execInstrBr, signExtend12, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, chainInput_length]
  · intro i hi
    exact bytes i (by simpa [chainInput_length] using hi)

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepNext_value

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_valueByte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_valueByte

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepNext_valueByte_of_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepNext_valueByte_of_query

/-- info: 'SigGolfCandidate.SphincsVerifierWotsValue.stepReady_chainQuery_of_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stepReady_chainQuery_of_bytes

end SigGolfCandidate.SphincsVerifierWotsValue
