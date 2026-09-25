import SigGolfCandidate.SphincsCachedSignValue

/-! A deterministic top-down uniqueness lemma for a publicly checked Merkle cache. -/

namespace SigGolfCandidate.SphincsCacheTreeUniqueness

theorem nodes_eq_of_consistent_root {α : Type} (height : Nat)
    (reference candidate : Nat → Nat → α)
    (parent : Nat → Nat → α → α → α)
    (reference_step : ∀ depth, depth < height → ∀ node, node < 2 ^ depth →
      reference (height - depth) node =
        parent (height - depth) node
          (reference (height - (depth + 1)) (2 * node))
          (reference (height - (depth + 1)) (2 * node + 1)))
    (candidate_step : ∀ depth, depth < height → ∀ node, node < 2 ^ depth →
      candidate (height - depth) node =
        parent (height - depth) node
          (candidate (height - (depth + 1)) (2 * node))
          (candidate (height - (depth + 1)) (2 * node + 1)))
    (no_collision : ∀ depth, depth < height → ∀ node, node < 2 ^ depth →
      parent (height - depth) node
          (reference (height - (depth + 1)) (2 * node))
          (reference (height - (depth + 1)) (2 * node + 1)) =
        parent (height - depth) node
          (candidate (height - (depth + 1)) (2 * node))
          (candidate (height - (depth + 1)) (2 * node + 1)) →
      reference (height - (depth + 1)) (2 * node) =
          candidate (height - (depth + 1)) (2 * node) ∧
      reference (height - (depth + 1)) (2 * node + 1) =
          candidate (height - (depth + 1)) (2 * node + 1))
    (root_eq : reference height 0 = candidate height 0) :
    ∀ level, level ≤ height → ∀ node, node < 2 ^ (height - level) →
      reference level node = candidate level node := by
  have by_depth : ∀ depth, depth ≤ height → ∀ node, node < 2 ^ depth →
      reference (height - depth) node = candidate (height - depth) node := by
    intro depth
    induction depth with
    | zero =>
        intro _ node hnode
        have hzero : node = 0 := by simpa using hnode
        simpa [hzero] using root_eq
    | succ depth ih =>
        intro hdepth node hnode
        have hd : depth < height := by omega
        have hparent : node / 2 < 2 ^ depth := by
          have hbound : node < 2 ^ depth * 2 := by
            simpa [pow_succ] using hnode
          omega
        have hparent_eq := ih (by omega) (node / 2) hparent
        have hcollision := no_collision depth hd (node / 2) hparent
        have hhash :
            parent (height - depth) (node / 2)
                (reference (height - (depth + 1)) (2 * (node / 2)))
                (reference (height - (depth + 1)) (2 * (node / 2) + 1)) =
              parent (height - depth) (node / 2)
                (candidate (height - (depth + 1)) (2 * (node / 2)))
                (candidate (height - (depth + 1)) (2 * (node / 2) + 1)) := by
          rw [← reference_step depth hd (node / 2) hparent,
            ← candidate_step depth hd (node / 2) hparent]
          exact hparent_eq
        obtain ⟨hleft, hright⟩ := hcollision hhash
        have hparity : node = 2 * (node / 2) ∨ node = 2 * (node / 2) + 1 := by
          omega
        rcases hparity with h | h
        · rw [h]
          exact hleft
        · rw [h]
          exact hright
  intro level hlevel node hnode
  have hdepth := by_depth (height - level) (by omega) node hnode
  simpa [Nat.sub_sub_self hlevel] using hdepth

end SigGolfCandidate.SphincsCacheTreeUniqueness

/-- info: 'SigGolfCandidate.SphincsCacheTreeUniqueness.nodes_eq_of_consistent_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheTreeUniqueness.nodes_eq_of_consistent_root
