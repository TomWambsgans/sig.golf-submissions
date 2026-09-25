import SigGolfCandidate.SphincsMaskedChainEndpoints

namespace SigGolfCandidate.SphincsMaskedChainFrame
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp
open SphincsMaskedChainLoop SphincsMaskedChainEndpoints SphincsVerifierCopyMemory
open SphincsMaskedChainStep
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The public cache and the enclosing leaf-loop counter survive all WOTS-chain work. -/
def Protected (a : Word) : Prop := a.toNat < 0x40000 ∨ a = 0x43020#64

theorem protected_ne (a b : Word) (ha : Protected a)
    (hb : 0x40000 ≤ b.toNat ∧ b ≠ 0x43020#64) : a ≠ b := by
  intro eq
  subst b
  rcases ha with low | leaf
  · omega
  · exact hb.2 leaf

theorem protected_outside (writes : List Word)
    (bounds : ∀ b ∈ writes, 0x40000 ≤ b.toNat ∧ b ≠ 0x43020#64)
    (a : Word) (ha : Protected a) : a ∉ writes := by
  intro member
  exact protected_ne a a ha (bounds a member) rfl

theorem chainValue_frame (hash : Hash) (s : MachineState) (a : Word) (ha : Protected a) :
    (chainValue hash s).getMem a = s.getMem a := by
  rw [chainValue, walk_frame hash 7 _ a (protected_outside _ (by simp [stepWrites, prepareWrites, answerWrites, finishWrites]) a ha)]
  exact initialChain_frame hash s a (protected_outside _ (by simp [initialWrites, secretPrepareWrites, answerWrites, secretFinishWrites]) a ha)

def endpointCell (c : Fin 52) (i : Fin 5) : Word :=
  alignToDword (BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val))

theorem endpointCell_bounds : ∀ (c : Fin 52) (i : Fin 5),
    0x40000 ≤ (endpointCell c i).toNat ∧ endpointCell c i ≠ 0x43020#64 := by decide

theorem endpointStored_frame (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (a : Word) (ha : Protected a) :
    (endpointStored s).getMem a = s.getMem a := by
  change (SphincsVerifierCopy.copyRootState (endpointSetup s)).getMem a = _
  rw [copyRoot_mem_frame]
  · exact endpointSetup_frame s a
  · intro i
    rw [(endpointSetup_registers s c.val chain).2]
    have address : BitVec.ofNat 64 (0x44300 + 20 * c.val) +
        signExtend12 (4#12 * BitVec.ofNat 12 i.val) =
          BitVec.ofNat 64 (0x44300 + 20 * c.val + 4 * i.val) := by
      fin_cases i <;> simp [signExtend12, ← BitVec.ofNat_add]
    rw [address]
    exact protected_ne a (endpointCell c i) ha (endpointCell_bounds c i)

theorem chainNext_frame (hash : Hash) (s : MachineState) (c : Fin 52)
    (chain : s.getMem 0x43050 = BitVec.ofNat 64 c.val) (a : Word) (ha : Protected a) :
    (chainNext hash s).getMem a = s.getMem a := by
  change (endpointFinish (endpointStored (chainValue hash s))).getMem a = _
  rw [endpointFinish_frame _ a (protected_ne a _ ha (by decide)),
    endpointStored_frame _ c ((chainValue_counter hash s).trans chain) a ha,
    chainValue_frame hash s a ha]

theorem chains_frame (hash : Hash) (s : MachineState) (pc : s.pc = 0x112c)
    (counter : s.getMem 0x43050 = 0) (n : Nat) (hn : n ≤ 52) (a : Word) (ha : Protected a) :
    (chains hash n s).getMem a = s.getMem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chains, chainNext_frame hash _ ⟨n, by omega⟩
      (chains_trace hash s pc counter n (by omega)).2.1 a ha]
    exact ih (by omega)

/-- info: 'SigGolfCandidate.SphincsMaskedChainFrame.chains_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chains_frame

end SigGolfCandidate.SphincsMaskedChainFrame
