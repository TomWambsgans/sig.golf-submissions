import Std

/-! A generic collision extractor for two authentication paths. -/

namespace SigGolfCandidate.SphincsCachePathCollision

variable {Digest : Type}

def orderedPair (right : Bool) (current sibling : Digest) : Digest × Digest :=
  if right then (sibling, current) else (current, sibling)

theorem orderedPair_eq_iff (right : Bool) (x y sx sy : Digest) :
    orderedPair right x sx = orderedPair right y sy ↔ x = y ∧ sx = sy := by
  cases right <;> simp [orderedPair, Prod.mk.injEq, and_comm]

def pathValue (hash : Nat → Digest × Digest → Digest) (right : Nat → Bool)
    (leaf : Digest) (siblings : Nat → Digest) : Nat → Digest
  | 0 => leaf
  | level + 1 =>
      hash level (orderedPair (right level)
        (pathValue hash right leaf siblings level) (siblings level))

def nodeInput (hash : Nat → Digest × Digest → Digest) (right : Nat → Bool)
    (leaf : Digest) (siblings : Nat → Digest) (level : Nat) : Digest × Digest :=
  orderedPair (right level) (pathValue hash right leaf siblings level) (siblings level)

theorem collision_or_same_siblings
    (hash : Nat → Digest × Digest → Digest) (right : Nat → Bool)
    (leaf : Digest) (leftPath rightPath : Nat → Digest) (height : Nat)
    (sameRoot : pathValue hash right leaf leftPath height =
      pathValue hash right leaf rightPath height) :
    (∃ level, level < height ∧
      nodeInput hash right leaf leftPath level ≠
        nodeInput hash right leaf rightPath level ∧
      hash level (nodeInput hash right leaf leftPath level) =
        hash level (nodeInput hash right leaf rightPath level)) ∨
    (∀ level, level < height → leftPath level = rightPath level) := by
  induction height with
  | zero =>
      exact Or.inr (by intro level h; omega)
  | succ height ih =>
      by_cases hinput : nodeInput hash right leaf leftPath height =
          nodeInput hash right leaf rightPath height
      · have hparts := (orderedPair_eq_iff (right height)
          (pathValue hash right leaf leftPath height)
          (pathValue hash right leaf rightPath height)
          (leftPath height) (rightPath height)).mp hinput
        rcases ih hparts.1 with hcollision | hsiblings
        · exact Or.inl (by
            obtain ⟨level, hlt, hne, heq⟩ := hcollision
            exact ⟨level, Nat.lt_succ_of_lt hlt, hne, heq⟩)
        · exact Or.inr (by
            intro level hlt
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
            · exact hsiblings level hlt
            · simpa [heq] using hparts.2)
      · exact Or.inl (by
          refine ⟨height, Nat.lt_succ_self _, hinput, ?_⟩
          simpa only [nodeInput, pathValue] using sameRoot)

/-- Two distinct sibling paths from the same leaf to the same root expose a
    collision at one level, including the node position in the oracle domain. -/
theorem exists_collision_of_distinct_paths
    (hash : Nat → Digest × Digest → Digest) (right : Nat → Bool)
    (leaf : Digest) (leftPath rightPath : Nat → Digest) (height : Nat)
    (sameRoot : pathValue hash right leaf leftPath height =
      pathValue hash right leaf rightPath height)
    (different : ∃ level, level < height ∧ leftPath level ≠ rightPath level) :
    ∃ level, level < height ∧
      nodeInput hash right leaf leftPath level ≠
        nodeInput hash right leaf rightPath level ∧
      hash level (nodeInput hash right leaf leftPath level) =
        hash level (nodeInput hash right leaf rightPath level) := by
  rcases collision_or_same_siblings hash right leaf leftPath rightPath height sameRoot with
    hcollision | hsame
  · exact hcollision
  · obtain ⟨level, hlt, hne⟩ := different
    exact False.elim (hne (hsame level hlt))

/-- info: 'SigGolfCandidate.SphincsCachePathCollision.exists_collision_of_distinct_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exists_collision_of_distinct_paths

end SigGolfCandidate.SphincsCachePathCollision
