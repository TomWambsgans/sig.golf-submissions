import SigGolfCandidate.SphincsVerifierWotsLeafHashReady
import SigGolfCandidate.SphincsVerifierSecondHashParameterData
import SigGolfCandidate.SphincsVerifierFtsForestHashReady
import SigGolfCandidate.SphincsVerifierSecondHashBytes

namespace SigGolfCandidate.SphincsVerifierWotsLeafParameter
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierWotsLeafHashReady
open SigGolfCandidate.SphincsMaskedKeygenPrefix
open SigGolfCandidate.SphincsVerifierFtsForestHashReady
open SigGolfCandidate.SphincsVerifierSecondHashParameterData
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierSecondHashBytes
open SigGolfCandidate.SphincsVerifierLoader
open SigGolfCandidate.SphincsVerifierHashBytes
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def leafHeaderSchedule : List (Word × Instr) := leafHashSchedule.take 21
def leafParameterPointersSchedule : List (Word × Instr) :=
  (leafHashSchedule.drop 21).take 4
def leafParameterCopySchedule : List (Word × Instr) :=
  (leafHashSchedule.drop 25).take 10
def leafRegistersSchedule : List (Word × Instr) := leafHashSchedule.drop 35

private theorem leafHash_segments : leafHashSchedule =
    leafHeaderSchedule ++ leafParameterPointersSchedule ++
      leafParameterCopySchedule ++ leafRegistersSchedule := by decide

private theorem runSchedule_append (xs ys : List (Word × Instr)) (s : MachineState) :
    runSchedule (xs ++ ys) s = runSchedule ys (runSchedule xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem leafParameterPointers_eq (s : MachineState) :
    runSchedule leafParameterPointersSchedule s = forestParameterPointers s := by
  rfl

theorem leafParameterCopy_eq (s : MachineState) :
    runSchedule leafParameterCopySchedule s = copyRootState s := by
  rfl

theorem leafHeader_source_word (s : MachineState) (slot : Fin 5) :
    (runSchedule leafHeaderSchedule s).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) =
    s.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) := by
  fin_cases slot <;>
    simp [leafHeaderSchedule, leafHashSchedule, runSchedule, execInstrBr,
      MachineState.getWord32, setWord32_eq, signExtend12,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      alignToDword, byteOffset]

private theorem leafRegisters_memory (s : MachineState) (address : Word) :
    (runSchedule leafRegistersSchedule s).getMem address = s.getMem address := by
  simp [leafRegistersSchedule, leafHashSchedule, runSchedule, execInstrBr]

theorem leafReady_parameter_word (s : MachineState) (slot : Fin 5) :
    (leafHashReadyState s).getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * slot.val)) =
    (runSchedule leafHeaderSchedule s).getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) := by
  let headed := runSchedule leafHeaderSchedule s
  let pointers := runSchedule leafParameterPointersSchedule headed
  let copied := runSchedule leafParameterCopySchedule pointers
  have pointerEq : pointers = forestParameterPointers headed :=
    leafParameterPointers_eq headed
  have source : pointers.getReg .x6 = 0x22cb4 := by
    rw [pointerEq]
    exact (forestParameterPointers_regs headed).1
  have destination : pointers.getReg .x7 = 0x40014 := by
    rw [pointerEq]
    exact (forestParameterPointers_regs headed).2
  have copiedWord : copied.getWord32
      (BitVec.ofNat 64 (0x40014 + 4 * slot.val)) =
      pointers.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) := by
    rw [show copied = copyRootState pointers from leafParameterCopy_eq pointers]
    exact copySecondParameter_data pointers source destination slot
  have pointersFrame : pointers.getWord32
      (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) =
      headed.getWord32 (BitVec.ofNat 64 (0x22cb4 + 4 * slot.val)) := by
    rw [pointerEq]
    simp [forestParameterPointers, execInstrBr, MachineState.getWord32]
  rw [leafHashReadyState, leafHash_segments,
    runSchedule_append, runSchedule_append, runSchedule_append]
  change (runSchedule leafRegistersSchedule copied).getWord32 _ = _
  simp only [MachineState.getWord32]
  rw [leafRegisters_memory]
  simpa only [MachineState.getWord32] using copiedWord.trans pointersFrame

theorem leafReady_parameter_byte (s : MachineState) (pk : SphincsSecurity.PublicKey)
    (encoded : WitnessPrefix s pk) (i : Nat) (hi : i < 20) :
    (leafHashReadyState s).getByte (BitVec.ofNat 64 (0x40014 + i)) =
      pk.parameter.extractLsb' (8 * i) 8 := by
  apply parameter_bytes_of_words (leafHashReadyState s) s pk
    (fun slot => (leafReady_parameter_word s slot).trans
      (leafHeader_source_word s slot)) encoded i hi

#print axioms leafReady_parameter_word
#print axioms leafReady_parameter_byte

end SigGolfCandidate.SphincsVerifierWotsLeafParameter
