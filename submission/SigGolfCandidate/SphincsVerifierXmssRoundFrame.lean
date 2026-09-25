import SigGolfCandidate.SphincsVerifierXmssRoundInvariant

namespace SigGolfCandidate.SphincsVerifierXmssRoundFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssNodeReady
open SigGolfCandidate.SphincsVerifierXmssNodeValue
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssRoundInvariant
open SigGolfCandidate.SphincsVerifierFtsParentMemoryFrame
open SigGolfCandidate.SphincsVerifierFtsParentTag
open SigGolfCandidate.SphincsVerifierFtsParentParameter
open SigGolfCandidate.SphincsVerifierFtsParentSetup
open SigGolfCandidate.SphincsVerifierCopy
open SigGolfCandidate.SphincsVerifierCopyMemory
open SigGolfCandidate.SphincsVerifierWotsLeafResult
open SigGolfCandidate.SphincsVerifierFtsParentResult
open SigGolfCandidate.SphincsVerifierFtsLevelInit
open SigGolfCandidate.SphincsVerifierXmssPrefix
open SigGolfCandidate.SphincsVerifierXmssNodeTransport
open SigGolfCandidate.SphincsVerifierFtsPairAdvance
open SigGolfCandidate.SphincsVerifierFtsLevelShift
open SigGolfCandidate.SphincsVerifierFtsLevelPosition
open SigGolfCandidate.SphincsVerifierFtsPair
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem outside_hash_ne (read written : Word)
    (outside : OutsideHashBuffer read)
    (lower : 0x40000 ≤ written.toNat)
    (upper : written.toNat < 0x40100) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  rcases outside with low | high <;> omega

theorem low_ne (read written : Word)
    (low : read.toNat < 0x40000)
    (high : 0x40000 ≤ written.toNat) : read ≠ written := by
  intro equal
  have same := congrArg BitVec.toNat equal
  omega

theorem ready_mem_frame (s : MachineState) (read : Word)
    (outside : OutsideHashBuffer read) :
    (nodeReadyState s).getMem read = s.getMem read := by
  let tagged := nodeTagState s
  let positioned := SphincsVerifierHeader.positionState tagged
  let treed := SphincsVerifierHeader.treeState positioned
  let headed := nodeHeaderState tagged
  let pointers := parameterPointers headed
  have tagDestination := tag_pointer s
  have positionDestination : positioned.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.position_hash_pointer tagged).trans tagDestination
  have treeDestination : treed.getReg .x7 = 0x40000 :=
    (SphincsVerifierHeader.tree_hash_pointer positioned).trans positionDestination
  change (hashRegistersState (copyRootState pointers)).getMem read = _
  have registers (t : MachineState) (address : Word) :
      (hashRegistersState t).getMem address = t.getMem address := by
    simp [hashRegistersState, execInstrBr]
  rw [registers]
  have destination := (parameterPointers_regs headed).2
  rw [copyRoot_mem_frame pointers read (by
    intro offset
    rw [destination]
    apply outside_hash_ne read _ outside
    · fin_cases offset <;> decide
    · fin_cases offset <;> decide)]
  have unchanged : pointers.getMem read = headed.getMem read := by
    simp [pointers, parameterPointers, execInstrBr]
  rw [unchanged]
  change (SphincsVerifierHeader.indexState treed).getMem read = _
  rw [parentIndex_mem_frame treed read outside treeDestination,
    parentTree_mem_frame positioned read outside positionDestination,
    parentPosition_mem_frame tagged tagDestination read
      (outside_hash_ne read 0x40000 outside (by decide) (by decide)),
    tag_mem_frame s read
      (outside_hash_ne read 0x40000 outside (by decide) (by decide))]

theorem round_mem_frame (hash : Hash) (lay : Layer) (s : MachineState)
    (read : Word)
    (outsideHash : OutsideHashBuffer read)
    (notAnswer0 : read ≠ 0x42000)
    (notAnswer8 : read ≠ 0x42008)
    (notAnswer16 : read ≠ 0x42010)
    (notAnswer24 : read ≠ 0x42018)
    (notCurrent : ∀ offset : Fin 5,
      read ≠ alignToDword
        (0x44a00 + signExtend12 (4#12 * BitVec.ofNat 12 offset.val)))
    (notLevel : read ≠ 0x43048) :
    (roundState hash lay s).getMem read =
      (nodePrefixState (SphincsVerifierXmssRound.pairState s)).getMem read := by
  let ready := readyState s
  let hashed := writeHash ready (hash (hashInput ready))
  rw [roundState, next_mem_frame lay _ read notLevel]
  change (leafAnswerCopyState hashed).getMem read = _
  rw [leafAnswerCopy_eq_result]
  change (SphincsVerifierFtsResult.resultState hashed).getMem read = _
  rw [SphincsVerifierFtsLevelInit.result_mem_frame hashed read notCurrent]
  have destination : ready.getReg .x12 = 0x42000 := by
    have regs := hashRegisters_ready
      (copyRootState (parameterPointers
        (nodeHeaderState (nodeTagState
          (nodePrefixState (SphincsVerifierXmssRound.pairState s))))))
    exact regs.2.2.1
  rw [writeHash_mem_frame ready _ destination read
    notAnswer0 notAnswer8 notAnswer16 notAnswer24]
  exact ready_mem_frame _ read outsideHash

theorem round_low_mem (hash : Hash) (lay : Layer) (s : MachineState)
    (read : Word) (low : read.toNat < 0x40000) :
    (roundState hash lay s).getMem read = s.getMem read := by
  rw [round_mem_frame hash lay s read (Or.inl low)
    (low_ne read 0x42000 low (by decide))
    (low_ne read 0x42008 low (by decide))
    (low_ne read 0x42010 low (by decide))
    (low_ne read 0x42018 low (by decide))
    (by intro offset
        apply low_ne read _ low
        fin_cases offset <;> decide)
    (low_ne read 0x43048 low (by decide))]
  exact prefix_low_mem s read low

theorem round_layer_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43000 = s.getMem 0x43000 := by
  rw [round_mem_frame hash lay s 0x43000
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide)]
  exact prefix_layer_cell s

theorem round_tree_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43008 = s.getMem 0x43008 := by
  rw [round_mem_frame hash lay s 0x43008
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide)]
  exact prefix_tree_cell s

theorem round_pointer_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43028 =
      s.getMem 0x43028 + 20 := by
  rw [round_mem_frame hash lay s 0x43028
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide),
    prefixState_eq_generic]
  change (levelPositionState (shiftIndexState
    (advancePointerState (SphincsVerifierFtsPair.pairState s)))).getMem 0x43028 = _
  rw [levelPosition_mem_frame _ 0x43028 (by decide),
    shiftIndex_mem_frame _ 0x43028 (by decide) (by decide),
    advancePointer_cell]
  congr 1
  apply pair_scratch_frame
  · intro offset; fin_cases offset <;> decide
  · intro offset; fin_cases offset <;> decide

theorem round_bit_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43070 =
      s.getMem 0x43070 >>> 1 := by
  rw [round_mem_frame hash lay s 0x43070
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide),
    prefixState_eq_generic]
  change (levelPositionState (shiftIndexState
    (advancePointerState (SphincsVerifierFtsPair.pairState s)))).getMem 0x43070 = _
  rw [levelPosition_mem_frame _ 0x43070 (by decide),
    (shiftIndex_cells _).1,
    advancePointer_mem_frame _ 0x43070 (by decide)]
  congr 1
  apply pair_scratch_frame
  · intro offset; fin_cases offset <;> decide
  · intro offset; fin_cases offset <;> decide

theorem round_index_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43018 =
      s.getMem 0x43070 >>> 1 := by
  rw [round_mem_frame hash lay s 0x43018
    (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by intro offset; fin_cases offset <;> decide)
    (by decide)]
  exact prefix_index_cell s

theorem round_level_cell (hash : Hash) (lay : Layer) (s : MachineState) :
    (roundState hash lay s).getMem 0x43048 =
      s.getMem 0x43048 + 1 := by
  let ready := readyState s
  let hashed := writeHash ready (hash (hashInput ready))
  rw [roundState, next_level_cell]
  congr 1
  change (leafAnswerCopyState hashed).getMem 0x43048 = _
  rw [leafAnswerCopy_eq_result]
  change (SphincsVerifierFtsResult.resultState hashed).getMem 0x43048 = _
  rw [SphincsVerifierFtsLevelInit.result_mem_frame hashed 0x43048
    (by intro offset; fin_cases offset <;> decide)]
  have destination : ready.getReg .x12 = 0x42000 := by
    have regs := hashRegisters_ready
      (copyRootState (parameterPointers
        (nodeHeaderState (nodeTagState
          (nodePrefixState (SphincsVerifierXmssRound.pairState s))))))
    exact regs.2.2.1
  rw [writeHash_mem_frame ready _ destination 0x43048
    (by decide) (by decide) (by decide) (by decide)]
  change (nodeReadyState (nodePrefixState
    (SphincsVerifierXmssRound.pairState s))).getMem 0x43048 = _
  rw [ready_mem_frame _ 0x43048 (Or.inr (by decide))]
  apply prefix_scratch_mem s 0x43048 <;> decide

#print axioms ready_mem_frame
#print axioms round_mem_frame
#print axioms round_low_mem
#print axioms round_layer_cell
#print axioms round_tree_cell
#print axioms round_pointer_cell
#print axioms round_bit_cell
#print axioms round_index_cell
/-- info: 'SigGolfCandidate.SphincsVerifierXmssRoundFrame.round_level_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms round_level_cell

end SigGolfCandidate.SphincsVerifierXmssRoundFrame
