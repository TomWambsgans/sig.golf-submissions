import SigGolfCandidate.SphincsVerifierXmssParity

namespace SigGolfCandidate.SphincsVerifierXmssAnswer
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssNodeSite
open SigGolfCandidate.SphincsVerifierWotsLeafResult
open SigGolfCandidate.SphincsMaskedKeygenPrefix
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def nodeAnswerCopySchedule (lay : Layer) : List (Word × Instr) :=
  leafAnswerCopySchedule.map
    (fun entry => (entry.1 + (nodeHashPc lay - 0x2a70), entry.2))

theorem nodeAnswerCopy_code (lay : Layer) : ∀ entry ∈ nodeAnswerCopySchedule lay,
    SphincsVerifierFtsRootCopy.instructionAt SphincsImages.verify entry.1 =
      some (.base entry.2) := by
  fin_cases lay <;> decide

private theorem runSchedule_mapPc (xs : List (Word × Instr)) (delta : Word)
    (s : MachineState) :
    runSchedule (xs.map (fun entry => (entry.1 + delta, entry.2))) s =
      runSchedule xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨pc, instr⟩
    exact ih _

theorem nodeAnswerCopy_state (lay : Layer) (s : MachineState) :
    runSchedule (nodeAnswerCopySchedule lay) s = leafAnswerCopyState s := by
  exact runSchedule_mapPc leafAnswerCopySchedule _ s

theorem nodeAnswerCopy_checked (lay : Layer) (s : MachineState)
    (pc : s.pc = nodeHashPc lay + 4) :
    Checked (nodeAnswerCopySchedule lay) s := by
  fin_cases lay <;>
    simp [Checked, nodeAnswerCopySchedule, leafAnswerCopySchedule,
      nodeHashPc, execInstrBr, ordinaryStep, memoryArgumentsValid,
      accessValid, rangeValid, MEMORY_BYTES, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      MachineState.setWord32, alignToDword, byteOffset, pc]

theorem nodeAnswerCopy_block (lay : Layer) (s : MachineState)
    (pc : s.pc = nodeHashPc lay + 4) :
    OrdinarySteps SphincsImages.verify s 14 (leafAnswerCopyState s) := by
  have block := checked_sound _ (nodeAnswerCopySchedule lay)
    (nodeAnswerCopy_code lay) s (nodeAnswerCopy_checked lay s pc)
  simpa [nodeAnswerCopy_state,
    show (nodeAnswerCopySchedule lay).length = 14 by
      simp [nodeAnswerCopySchedule, leafAnswerCopySchedule]] using block

theorem nodeAnswerCopy_pc (lay : Layer) (s : MachineState)
    (pc : s.pc = nodeHashPc lay + 4) :
    (leafAnswerCopyState s).pc = nodeHashPc lay + 60 := by
  rw [leafAnswerCopy_pc_general, pc]
  bv_decide

def nodeHashNext (hash : Hash) (s : MachineState) : MachineState :=
  leafAnswerCopyState (writeHash s (hash (hashInput s)))

theorem nodeHashNext_byte (hash : Hash) (s : MachineState)
    (destination : s.getReg .x12 = 0x42000)
    (i : Nat) (hi : i < 20) :
    (nodeHashNext hash s).getByte (BitVec.ofNat 64 (0x44a00 + i)) =
      (hash (hashInput s)).extractLsb' (8 * i) 8 := by
  let slot : Fin 5 := ⟨i / 4, by omega⟩
  let byte : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * slot.val + byte.val = i := by
    dsimp [slot, byte]
    omega
  rw [← split,
    show 0x44a00 + (4 * slot.val + byte.val) =
      0x44a00 + 4 * slot.val + byte.val by omega,
    SphincsVerifierFtsGenericBytes.variableWord_byte _ 0x44a00
      (by decide) (by decide) slot byte]
  have value : (nodeHashNext hash s).getWord32
      (SphincsVerifierWotsEndpointCopy.word 0x44a00 slot) =
      (hash (hashInput s)).extractLsb' (32 * slot.val) 32 := by
    rw [nodeHashNext, leafAnswerCopy_word]
    exact SphincsVerifierWotsValue.writeHash_word32 s (hash (hashInput s))
      destination slot
  simp only [SphincsVerifierWotsEndpointCopy.word] at value
  rw [value]
  ext bit (hbit : bit < 8)
  simp
  have hb : 8 * byte.val + bit < 32 := by have := byte.isLt; omega
  simp [hb, show 32 * slot.val + (8 * byte.val + bit) =
    8 * (4 * slot.val + byte.val) + bit by omega]

#print axioms nodeAnswerCopy_block
#print axioms nodeHashNext_byte

end SigGolfCandidate.SphincsVerifierXmssAnswer
