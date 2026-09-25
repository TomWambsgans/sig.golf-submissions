import SigGolfCandidate.SphincsVerifierXmssRoundControl

namespace SigGolfCandidate.SphincsVerifierXmssPathControl
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierXmssParity
open SigGolfCandidate.SphincsVerifierXmssNext
open SigGolfCandidate.SphincsVerifierXmssRound
open SigGolfCandidate.SphincsVerifierXmssRoundFrame
open SigGolfCandidate.SphincsVerifierXmssRoundControl
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def pathState (hash : Hash) (lay : Layer) : Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s => pathState hash lay n (roundState hash lay s)

theorem pathState_succ (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathState hash lay (n + 1) s =
      pathState hash lay n (roundState hash lay s) := rfl

theorem pointer_add20_nat (pointer : Word)
    (small : pointer.toNat + 20 ≤ 0x40000) :
    (pointer + 20).toNat = pointer.toNat + 20 := by
  rw [BitVec.toNat_add]
  have bound : pointer.toNat + 20 < 2 ^ 64 := by omega
  simpa [Nat.mod_eq_of_lt bound]

theorem path_pc_done (hash : Hash) (lay : Layer) (n : Nat) :
    ∀ (k : Nat) (s : MachineState) (pointer : Word),
      1 ≤ k → k ≤ layerHeight lay →
      k + n = layerHeight lay + 1 →
      s.pc = nodePc lay →
      s.getMem 0x43048 = BitVec.ofNat 64 k →
      s.getMem 0x43028 = pointer →
      pointer.toNat + 20 * n ≤ 0x40000 →
      pointer.toNat % 4 = 0 →
      (pathState hash lay n s).pc = branchPc lay + 4 := by
  induction n with
  | zero =>
      intro k s pointer hk hheight hn hpc hlevel hpointer hsmall haligned
      omega
  | succ remaining ih =>
      intro k s pointer hk hheight hn hpc hlevel hpointer hsmall haligned
      by_cases final : remaining = 0
      · subst remaining
        have last : k = layerHeight lay := by omega
        change (roundState hash lay s).pc = branchPc lay + 4
        exact round_pc_done hash lay s hpc pointer hpointer (by omega)
          haligned (by simpa [last] using hlevel)
      · have beforeLast : k < layerHeight lay := by omega
        have pc' := round_pc_repeat hash lay s hpc pointer hpointer
          (by omega) haligned k hlevel beforeLast
        have level' : (roundState hash lay s).getMem 0x43048 =
            BitVec.ofNat 64 (k + 1) := by
          rw [round_level_cell, hlevel, BitVec.ofNat_add]
          rfl
        have pointer' : (roundState hash lay s).getMem 0x43028 =
            pointer + 20 := by rw [round_pointer_cell, hpointer]
        have pointerNat : (pointer + 20).toNat = pointer.toNat + 20 :=
          pointer_add20_nat pointer (by omega)
        have bound' : (pointer + 20).toNat + 20 * remaining ≤ 0x40000 := by
          rw [pointerNat]
          omega
        have aligned' : (pointer + 20).toNat % 4 = 0 := by
          rw [pointerNat]
          omega
        rw [pathState_succ]
        exact ih (k + 1) (roundState hash lay s) (pointer + 20)
          (by omega) (by omega) (by omega) pc' level' pointer'
          bound' aligned'

def pathInstructions (hash : Hash) (lay : Layer) : Nat → MachineState → Nat
  | 0, _ => 0
  | n + 1, s =>
      pairInstructions s + 91 +
        pathInstructions hash lay n (roundState hash lay s)

def pathCycles (hash : Hash) (lay : Layer) : Nat → MachineState → Nat
  | 0, _ => 0
  | n + 1, s =>
      pairInstructions s + 106 +
        pathCycles hash lay n (roundState hash lay s)

def pathRights (hash : Hash) (lay : Layer) : Nat → MachineState → Nat
  | 0, _ => 0
  | n + 1, s =>
      (if s.getMem 0x43070 &&& 1 = 0 then 0 else 1) +
        pathRights hash lay n (roundState hash lay s)

theorem pathCycles_eq (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathCycles hash lay n s = 140 * n + pathRights hash lay n s := by
  induction n generalizing s with
  | zero => simp [pathCycles, pathRights]
  | succ n ih =>
      simp only [pathCycles, pathRights]
      rw [ih]
      simp only [pairInstructions]
      split_ifs <;> omega

theorem pathInstructions_eq (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathInstructions hash lay n s = 125 * n + pathRights hash lay n s := by
  induction n generalizing s with
  | zero => simp [pathInstructions, pathRights]
  | succ n ih =>
      simp only [pathInstructions, pathRights]
      rw [ih]
      simp only [pairInstructions]
      split_ifs <;> omega

theorem pathRights_le (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathRights hash lay n s ≤ n := by
  induction n generalizing s with
  | zero => simp [pathRights]
  | succ n ih =>
      simp only [pathRights]
      have rest := ih (roundState hash lay s)
      split <;> omega

theorem pairInstructions_le (s : MachineState) :
    pairInstructions s ≤ 35 := by
  simp [pairInstructions]
  split <;> omega

theorem pathCycles_le (hash : Hash) (lay : Layer) (n : Nat) (s : MachineState) :
    pathCycles hash lay n s ≤ 141 * n := by
  induction n generalizing s with
  | zero => simp [pathCycles]
  | succ n ih =>
      simp only [pathCycles]
      have first := pairInstructions_le s
      have rest := ih (roundState hash lay s)
      omega

theorem pathInstructions_le (hash : Hash) (lay : Layer) (n : Nat)
    (s : MachineState) :
    pathInstructions hash lay n s ≤ 126 * n := by
  induction n generalizing s with
  | zero => simp [pathInstructions]
  | succ n ih =>
      simp only [pathInstructions]
      have first := pairInstructions_le s
      have rest := ih (roundState hash lay s)
      omega

theorem path_executes (hash : Hash) (lay : Layer) (n : Nat) :
    ∀ (k : Nat) (s : MachineState) (pointer : Word)
      (steps : Nat) (result : Execution),
      k + n = layerHeight lay + 1 →
      (n = 0 ∨ s.pc = nodePc lay) →
      s.getMem 0x43048 = BitVec.ofNat 64 k →
      s.getMem 0x43028 = pointer →
      pointer.toNat + 20 * n ≤ 0x40000 →
      pointer.toNat % 4 = 0 →
      Executes hash SphincsImages.verify (pathState hash lay n s)
        steps result →
      Executes hash SphincsImages.verify s
        (steps + pathInstructions hash lay n s)
        (result.charge (pathCycles hash lay n s) n (2 * n)) := by
  induction n with
  | zero =>
      intro k s pointer steps result hn hpc hlevel hpointer hsmall haligned tail
      simpa [pathState, pathInstructions, pathCycles, Execution.charge] using tail
  | succ remaining ih =>
      intro k s pointer steps result hn hpc hlevel hpointer hsmall haligned tail
      have pc : s.pc = nodePc lay := by
        rcases hpc with h | h
        · omega
        · exact h
      have pointerBound : pointer.toNat + 20 ≤ 0x40000 := by omega
      have nextLevel : (roundState hash lay s).getMem 0x43048 =
          BitVec.ofNat 64 (k + 1) := by
        rw [round_level_cell, hlevel, BitVec.ofNat_add]
        rfl
      have nextPointer : (roundState hash lay s).getMem 0x43028 =
          pointer + 20 := by rw [round_pointer_cell, hpointer]
      have pointerNat : (pointer + 20).toNat = pointer.toNat + 20 :=
        pointer_add20_nat pointer pointerBound
      have nextBound : (pointer + 20).toNat + 20 * remaining ≤ 0x40000 := by
        rw [pointerNat]
        omega
      have nextAligned : (pointer + 20).toNat % 4 = 0 := by
        rw [pointerNat]
        omega
      have nextPc : remaining = 0 ∨
          (roundState hash lay s).pc = nodePc lay := by
        by_cases last : remaining = 0
        · exact Or.inl last
        · right
          apply round_pc_repeat hash lay s pc pointer hpointer pointerBound
            haligned k hlevel
          omega
      have rest := ih (k + 1) (roundState hash lay s) (pointer + 20)
        steps result (by omega) nextPc nextLevel nextPointer
        nextBound nextAligned (by simpa [pathState_succ] using tail)
      have whole := round_executes hash lay s pc pointer hpointer pointerBound
        haligned (steps + pathInstructions hash lay remaining (roundState hash lay s))
        (result.charge (pathCycles hash lay remaining (roundState hash lay s))
          remaining (2 * remaining)) rest
      convert whole using 1
      · simp [pathInstructions]
        omega
      · cases result
        simp [pathCycles, Execution.charge]
        omega

#print axioms path_pc_done
/-- info: 'SigGolfCandidate.SphincsVerifierXmssPathControl.path_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms path_executes
#print axioms pathCycles_le
#print axioms pathCycles_eq
#print axioms pathInstructions_eq
#print axioms pathRights_le

end SigGolfCandidate.SphincsVerifierXmssPathControl
