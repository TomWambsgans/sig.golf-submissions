import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude

/-! Information-theoretic masking for a prospective encrypted public cache.
This says nothing yet about the adaptive probability of querying a secret-keyed
pad or MAC input. -/

namespace SigGolfCandidate.SphincsCacheMasking

def mask {n : Nat} (pads nodes : Fin n → BitVec 160) : Fin n → BitVec 160 :=
  fun i => pads i ^^^ nodes i

theorem mask_involutive {n : Nat} (nodes pads : Fin n → BitVec 160) :
    mask (mask pads nodes) nodes = pads := by
  funext i
  simp only [mask, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem mask_bijective {n : Nat} (nodes : Fin n → BitVec 160) :
    Function.Bijective (fun pads => mask pads nodes) := by
  constructor
  · intro x y h
    have := congrArg (fun pads => mask pads nodes) h
    simpa only [mask_involutive] using this
  · intro y
    exact ⟨mask y nodes, mask_involutive nodes y⟩

/-- For any fixed tree, fresh independent pads make the entire ciphertext
uniform, including all correlations among the tree nodes. -/
theorem uniform_mask {n : Nat} (nodes : Fin n → BitVec 160) :
    (PMF.uniformOfFintype (Fin n → BitVec 160)).map (fun pads => mask pads nodes) =
      PMF.uniformOfFintype (Fin n → BitVec 160) :=
  PMF.uniformOfFintype_map_of_bijective _ (mask_bijective nodes)

/-- The ciphertext remains independent of an arbitrary prior setup state,
provided the pad table is sampled fresh after that state. -/
theorem mask_independent {n : Nat} {State : Type} (prior : PMF State)
    (nodes : State → Fin n → BitVec 160) :
    prior.bind (fun state =>
      (PMF.uniformOfFintype (Fin n → BitVec 160)).map
        (fun pads => (state, mask pads (nodes state)))) =
    prior.bind (fun state =>
      (PMF.uniformOfFintype (Fin n → BitVec 160)).map
        (fun cipher => (state, cipher))) := by
  apply congrArg (prior.bind ·)
  funext state
  have h := uniform_mask (nodes state)
  calc
    _ = ((PMF.uniformOfFintype (Fin n → BitVec 160)).map
          (fun pads => mask pads (nodes state))).map
          (fun cipher => (state, cipher)) := by
            rw [PMF.map_comp]
            rfl
    _ = _ := congrArg (fun law : PMF (Fin n → BitVec 160) =>
      law.map (fun cipher => (state, cipher))) h

/-- A fresh domain-separated MAC output can be sampled as an independent
uniform tag alongside the masked cache. This is conditional on no one having
queried its hidden secret-key input already. -/
theorem mask_and_tag_independent {n : Nat} {State : Type} (prior : PMF State)
    (nodes : State → Fin n → BitVec 160) :
    prior.bind (fun state =>
      (PMF.uniformOfFintype (Fin n → BitVec 160)).bind (fun pads =>
        (PMF.uniformOfFintype (BitVec 160)).map
          (fun tag => (state, mask pads (nodes state), tag)))) =
    prior.bind (fun state =>
      (PMF.uniformOfFintype (Fin n → BitVec 160)).bind (fun cipher =>
        (PMF.uniformOfFintype (BitVec 160)).map
          (fun tag => (state, cipher, tag)))) := by
  apply congrArg (prior.bind ·)
  funext state
  have h := uniform_mask (nodes state)
  calc
    _ = ((PMF.uniformOfFintype (Fin n → BitVec 160)).map
          (fun pads => mask pads (nodes state))).bind (fun cipher =>
          (PMF.uniformOfFintype (BitVec 160)).map
            (fun tag => (state, cipher, tag))) := by
              rw [PMF.bind_map]
              rfl
    _ = _ := congrArg (fun law : PMF (Fin n → BitVec 160) =>
      law.bind (fun cipher => (PMF.uniformOfFintype (BitVec 160)).map
        (fun tag => (state, cipher, tag)))) h

end SigGolfCandidate.SphincsCacheMasking

/-- info: 'SigGolfCandidate.SphincsCacheMasking.mask_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMasking.mask_independent

/-- info: 'SigGolfCandidate.SphincsCacheMasking.mask_and_tag_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMasking.mask_and_tag_independent
