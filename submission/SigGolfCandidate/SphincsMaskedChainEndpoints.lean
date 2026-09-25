import SigGolfCandidate.SphincsMaskedChainLoop

namespace SigGolfCandidate.SphincsMaskedChainEndpoints
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedChainLoop SphincsVerifierCopy SphincsVerifierCopyMemory
open SphincsVerifierCopy20DataGeneral SphincsVerifierFtsPriorRoots
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- 32-bit lane framing preserves adjacent 20-byte endpoints sharing a 64-bit cell. -/
theorem copyWord_lane_frame (s : MachineState) (destination read : Nat) (i : Fin 5)
    (dst : s.getReg .x7 = BitVec.ofNat 64 destination)
    (small : destination + 20 < 2 ^ 64) (readSmall : read < 2 ^ 64)
    (aligned : destination % 4 = 0) (readAligned : read % 4 = 0)
    (different : destination + 4 * i.val ≠ read) :
    (copyWordState i s).getWord32 (BitVec.ofNat 64 read) = s.getWord32 (BitVec.ofNat 64 read) := by
  apply copyWord_word_frame
  have address : s.getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
      BitVec.ofNat 64 (destination + 4 * i.val) := by
    rw [dst]
    fin_cases i <;> simp [signExtend12, ← BitVec.ofNat_add]
  rw [address]
  exact wordLaneDistinct _ _ (by omega) readSmall (by omega) readAligned different

private def CopyInvariant (original : MachineState) (c : Fin 52) (count : Nat)
    (s : MachineState) : Prop :=
  s.getReg .x6 = 0x44b00 ∧ s.getReg .x7 = BitVec.ofNat 64 (0x44300 + 20 * c.val) ∧
  (∀ i : Fin 5, s.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val))) ∧
  (∀ i : Fin 5, i.val < count → s.getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
    original.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)))

private theorem copyStep (original s : MachineState) (c : Fin 52) (slot : Fin 5)
    (inv : CopyInvariant original c slot.val s) :
    CopyInvariant original c (slot.val + 1) (copyWordState slot s) := by
  obtain ⟨src, dst, source, copied⟩ := inv
  obtain ⟨srcAfter, dstAfter⟩ := copyWord_pointers slot s
  refine ⟨srcAfter.trans src, dstAfter.trans dst, ?_, ?_⟩
  · intro i
    rw [copyWord_lane_frame s (0x44300 + 20 * c.val) (0x44b00 + 4 * i.val) slot dst
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact source i
  · intro i hi
    by_cases same : slot = i
    · subst i
      rw [copyWord_data_general slot s 0x44b00 (0x44300 + 20 * c.val) src dst]
      exact source slot
    · have ne : slot.val ≠ i.val := fun h => same (Fin.ext h)
      rw [copyWord_lane_frame s (0x44300 + 20 * c.val) (0x44300 + 20 * c.val + 4 * i.val) slot dst
        (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact copied i (by omega)

theorem copy_data (s : MachineState) (c : Fin 52)
    (src : s.getReg .x6 = 0x44b00)
    (dst : s.getReg .x7 = BitVec.ofNat 64 (0x44300 + 20 * c.val)) (i : Fin 5) :
    (copyRootState s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) := by
  have initial : CopyInvariant s c 0 s := ⟨src, dst, fun _ => rfl, by intro _ h; omega⟩
  have s0 := copyStep s s c 0 initial
  have s1 := copyStep s (copyWordState 0 s) c 1 s0
  have s2 := copyStep s (copyWordState 1 (copyWordState 0 s)) c 2 s1
  have s3 := copyStep s (copyWordState 2 (copyWordState 1 (copyWordState 0 s))) c 3 s2
  have s4 := copyStep s (copyWordState 3 (copyWordState 2 (copyWordState 1 (copyWordState 0 s)))) c 4 s3
  exact s4.2.2.2 i (by omega)

theorem endpointStored_data (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (i : Fin 5) :
    (endpointStored s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) := by
  have regs := endpointSetup_registers s c.val chain
  rw [endpointStored, copy_data _ c regs.1 regs.2 i]
  simp only [MachineState.getWord32, endpointSetup_frame]

theorem endpointFinish_frame (s : MachineState) (a : Word) (outside : a ≠ 0x43050#64) :
    (endpointFinish s).getMem a = s.getMem a := by
  simp [endpointFinish, SphincsMaskedKeygenPrefix.runSchedule, endpointFinishSchedule,
    execInstrBr, signExtend12, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, outside]

theorem endpointFinish_word (s : MachineState) (c : Fin 52) (i : Fin 5) :
    (endpointFinish s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) := by
  simp only [MachineState.getWord32]
  rw [endpointFinish_frame]
  fin_cases c <;> fin_cases i <;> decide

theorem endpointNext_data (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (i : Fin 5) :
    (endpointNext s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) := by
  rw [endpointNext, endpointFinish_word, endpointStored_data s c chain i]

theorem endpointNext_other (s : MachineState) (c other : Fin 52) (ne : c ≠ other)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (i : Fin 5) :
    (endpointNext s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * other.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44300 + 20 * other.val + 4 * i.val)) := by
  rw [endpointNext, endpointFinish_word]
  change (copyRootState (endpointSetup s)).getWord32 _ = _
  rw [copyRoot_word_frame]
  · simp only [MachineState.getWord32, endpointSetup_frame]
  · intro j
    have address : (endpointSetup s).getReg .x7 + signExtend12 (4#12 * BitVec.ofNat 12 j.val) =
        BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * j.val) := by
      rw [(endpointSetup_registers s c.val chain).2]
      fin_cases j <;> simp [signExtend12, ← BitVec.ofNat_add]
    rw [address]
    have hn : c.val ≠ other.val := fun h => ne (Fin.ext h)
    exact wordLaneDistinct _ _ (by omega) (by omega) (by omega) (by omega) (by omega)


theorem endpoint_outside_initial : ∀ (c : Fin 52) (i : Fin 5),
    alignToDword (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) ∉ initialWrites := by decide

theorem endpoint_outside_walk : ∀ (c : Fin 52) (i : Fin 5),
    alignToDword (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) ∉
      SphincsMaskedChainStep.stepWrites := by decide

theorem chainValue_endpoint_frame (hash : Hash) (s : MachineState) (c : Fin 52) (i : Fin 5) :
    (chainValue hash s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) := by
  simp only [chainValue, MachineState.getWord32]
  rw [SphincsMaskedChainStep.walk_frame hash 7 _ _ (endpoint_outside_walk c i),
    initialChain_frame hash s _ (endpoint_outside_initial c i)]

theorem chainNext_data (hash : Hash) (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (i : Fin 5) :
    (chainNext hash s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
      (chainValue hash s).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) := by
  exact endpointNext_data (chainValue hash s) c ((chainValue_counter hash s).trans chain) i

theorem chainNext_other (hash : Hash) (s : MachineState) (c other : Fin 52) (ne : c ≠ other)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (i : Fin 5) :
    (chainNext hash s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * other.val + 4 * i.val)) =
      s.getWord32 (BitVec.ofNat 64 (0x44300 + 20 * other.val + 4 * i.val)) := by
  change (endpointNext (chainValue hash s)).getWord32 _ = _
  rw [endpointNext_other _ c other ne ((chainValue_counter hash s).trans chain),
    chainValue_endpoint_frame]

/-- Every previously generated endpoint survives every subsequent chain iteration. -/
theorem chains_data (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) (n : Nat) (hn : n ≤ 52) :
    ∀ c : Fin 52, c.val < n → ∀ i : Fin 5,
      (chains hash n s).getWord32 (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val)) =
        (chainValue hash (chains hash c.val s)).getWord32 (BitVec.ofNat 64 (0x44b00 + 4 * i.val)) := by
  induction n with
  | zero => intro c hc; omega
  | succ n ih =>
    intro c hc i
    have count := (chains_trace hash s pc counter n (by omega)).2.1
    by_cases eq : c.val = n
    · have current : (chains hash n s).getMem 0x43050 = BitVec.ofNat 64 c.val := by rw [count, eq]
      rw [chains, chainNext_data hash _ c current i, eq]
    · change (chainNext hash (chains hash n s)).getWord32 _ = _
      rw [chainNext_other hash _ ⟨n, by omega⟩ c (by intro same; have := congrArg Fin.val same; simp at this; omega) count i]
      exact ih (by omega) c (by omega) i

/-- Exact 20-byte transfer from five 32-bit lanes at any supported buffer address. -/
theorem bytes_of_lanes (original final : MachineState) (source destination : Nat)
    (sourceBound : source + 20 ≤ 0x50000) (destBound : destination + 20 ≤ 0x50000)
    (sourceAlign : source % 4 = 0) (destAlign : destination % 4 = 0)
    (lanes : ∀ i : Fin 5, final.getWord32 (BitVec.ofNat 64 (destination + 4 * i.val)) =
      original.getWord32 (BitVec.ofNat 64 (source + 4 * i.val))) (j : Fin 20) :
    final.getByte (BitVec.ofNat 64 (destination + j.val)) =
      original.getByte (BitVec.ofNat 64 (source + j.val)) := by
  let i : Fin 5 := ⟨j.val / 4, by omega⟩
  let b : Fin 4 := ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
  have split : 4 * i.val + b.val = j.val := by dsimp [i, b]; omega
  have target := SphincsVerifierFtsGenericBytes.variableWord_byte final destination destBound destAlign i b
  have src := SphincsVerifierFtsGenericBytes.variableWord_byte original source sourceBound sourceAlign i b
  rw [lanes] at target
  rw [← src] at target
  simpa only [Nat.add_assoc, split] using target

theorem fifty_two_endpoint_bytes (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) (c : Fin 52) (j : Fin 20) :
    (chains hash 52 s).getByte (BitVec.ofNat 64 (0x44300 + 20 * c.val + j.val)) =
      (chainValue hash (chains hash c.val s)).getByte (BitVec.ofNat 64 (0x44b00 + j.val)) := by
  exact bytes_of_lanes _ _ 0x44b00 (0x44300 + 20 * c.val) (by decide) (by omega)
    (by decide) (by omega) (chains_data hash s pc counter 52 (by decide) c c.isLt) j

/-- info: 'SigGolfCandidate.SphincsMaskedChainEndpoints.endpointNext_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpointNext_data

/-- info: 'SigGolfCandidate.SphincsMaskedChainEndpoints.endpointNext_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpointNext_other

/-- info: 'SigGolfCandidate.SphincsMaskedChainEndpoints.chains_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chains_data

/-- info: 'SigGolfCandidate.SphincsMaskedChainEndpoints.fifty_two_endpoint_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fifty_two_endpoint_bytes

end SigGolfCandidate.SphincsMaskedChainEndpoints
