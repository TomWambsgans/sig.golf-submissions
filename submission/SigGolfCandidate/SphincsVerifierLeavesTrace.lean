import SigGolfCandidate.SphincsVerifierLeavesFrame

/-! The 24 unrolled FORS selectors as one certified verifier trace. -/

namespace SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.SphincsVerifierLeafCode
open SigGolfCandidate.SphincsVerifierLeavesFrame
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash

def leafStates (initial : MachineState) :
    (n : Nat) → n ≤ 24 → MachineState
  | 0, _ => initial
  | n + 1, h =>
      leafState ⟨n, by omega⟩ (leafStates initial n (by omega))

def AnswerBytes (state : MachineState) (answer : BitVec 256) : Prop :=
  ∀ index : Fin 30,
    state.getByte (BitVec.ofNat 64 (0x42000 + index.val)) =
      answer.extractLsb' (8 * index.val) 8

theorem leafStates_answer (initial : MachineState) (answer : BitVec 256)
    (original : AnswerBytes initial answer) :
    ∀ n (bound : n ≤ 24), AnswerBytes (leafStates initial n bound) answer := by
  intro n
  induction n with
  | zero =>
      intro bound
      simpa [leafStates] using original
  | succ n ih =>
      intro bound index
      change (leafState ⟨n, by omega⟩
        (leafStates initial n (by omega))).getByte
          (BitVec.ofNat 64 (0x42000 + index.val)) = _
      rw [leafState_answer_byte]
      exact ih (by omega) index

theorem leafStates_pc (initial : MachineState)
    (start : initial.pc = BitVec.ofNat 64 (0x1000 + 4 * 180)) :
    ∀ n (bound : n ≤ 24),
      (leafStates initial n bound).pc =
        BitVec.ofNat 64 (0x1000 + 4 * (180 + 11 * n)) := by
  intro n
  induction n with
  | zero =>
      intro bound
      simpa [leafStates] using start
  | succ n ih =>
      intro bound
      have middle := ih (by omega)
      have next := leafState_pc ⟨n, by omega⟩
        (leafStates initial n (by omega)) (by simpa using middle)
      simpa [leafStates, Nat.mul_add, Nat.add_assoc] using next

theorem leafStates_block (initial : MachineState)
    (start : initial.pc = BitVec.ofNat 64 (0x1000 + 4 * 180)) :
    ∀ n (bound : n ≤ 24),
      OrdinarySteps SphincsImages.verify initial (11 * n)
        (leafStates initial n bound) := by
  intro n
  induction n with
  | zero =>
      intro bound
      simpa [leafStates] using (OrdinarySteps.refl initial)
  | succ n ih =>
      intro bound
      have front := ih (by omega)
      have middlePc := leafStates_pc initial start n (by omega)
      have back := leaf_block ⟨n, by omega⟩
        (leafStates initial n (by omega)) (by simpa using middlePc)
      simpa [leafStates, Nat.mul_add, Nat.add_assoc] using front.append back

def abstractLeaf (answer : BitVec 256) (tree : Fin 24) : Nat :=
  (SphincsSecurity.Concrete.digestLeaves
    (SphincsSecurity.truncateMessageDigest answer)
    ⟨tree.val, by
      have bound := tree.isLt
      simp [SphincsSecurity.ftsTrees]
      omega⟩).val

theorem leafStates_selectors (initial : MachineState) (answer : BitVec 256)
    (original : AnswerBytes initial answer) :
    ∀ n (bound : n ≤ 24) (tree : Fin 24), tree.val < n →
      ((leafStates initial n bound).getByte
        (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
        abstractLeaf answer tree := by
  intro n
  induction n with
  | zero =>
      intro bound tree less
      omega
  | succ n ih =>
      intro bound tree less
      have nSmall : n < 24 := by omega
      by_cases same : tree.val = n
      · have treeEq : tree = (⟨n, nSmall⟩ : Fin 24) := Fin.ext same
        subst tree
        change ((leafState ⟨n, nSmall⟩
          (leafStates initial n (by omega))).getByte
            (BitVec.ofNat 64 (0x44800 + n))).toNat = _
        have decoded := leafSelector_correct ⟨n, nSmall⟩
          (leafStates initial n (by omega)) answer
          (leafStates_answer initial answer original n (by omega))
        simpa [abstractLeaf] using decoded
      · have different : tree ≠ (⟨n, nSmall⟩ : Fin 24) := by
          intro equal
          exact same (congrArg Fin.val equal)
        change ((leafState ⟨n, nSmall⟩
          (leafStates initial n (by omega))).getByte
            (BitVec.ofNat 64 (0x44800 + tree.val))).toNat = _
        rw [leafState_other_leaf ⟨n, nSmall⟩ tree _ different]
        exact ih (by omega) tree (by omega)

theorem messageReady_leaves (state : MachineState)
    (pk : SphincsSecurity.PublicKey)
    (message : SphincsSecurity.Message)
    (randomness : SphincsSecurity.Randomness)
    (ready : MessageReady state pk message randomness)
    (pc : state.pc = 0x12a0) (answer : BitVec 256) :
    let initial := indexStoredState (indexValueState (writeHash state answer))
    let final := leafStates initial 24 (by decide)
    OrdinarySteps SphincsImages.verify (writeHash state answer) 275 final ∧
      final.pc = 0x16f0 ∧
      ∀ tree : Fin 24,
        (final.getByte (BitVec.ofNat 64 (0x44800 + tree.val))).toNat =
          abstractLeaf answer tree := by
  obtain ⟨front, initialPc, _, _⟩ :=
    messageReady_indexStored state pk message randomness ready pc answer
  let initial := indexStoredState (indexValueState (writeHash state answer))
  have start : initial.pc = BitVec.ofNat 64 (0x1000 + 4 * 180) := by
    simpa [initial] using initialPc
  have bytes : AnswerBytes initial answer := by
    intro index
    exact messageReady_indexStored_answerBytes
      state pk message randomness ready answer index
  have leaves := leafStates_block initial start 24 (by decide)
  have finalPc := leafStates_pc initial start 24 (by decide)
  have selectors := leafStates_selectors initial answer bytes 24 (by decide)
  exact ⟨by simpa [initial] using front.append leaves,
    by simpa [initial] using finalPc,
    by simpa [initial] using fun tree => selectors tree (by have bound := tree.isLt; omega)⟩

/-- info: 'SigGolfCandidate.SphincsVerifierLeavesTrace.messageReady_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms messageReady_leaves

end SigGolfCandidate.SphincsVerifierLeavesTrace
