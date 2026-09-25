import SigGolfCandidate.SphincsLowerLayerCost

/-! Small monadic cost lemmas for assembling a successful signer prefix. -/

namespace SigGolfCandidate.SphincsCostComposition
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.CachedSignerTrace

def bindSome {α β : Type} (head : OracleComp HashSpec (Option α))
    (next : α → OracleComp HashSpec (Option β)) :
    OracleComp HashSpec (Option β) := do
  let some value ← head | return none
  next value

theorem bindSome_assoc {α β γ : Type}
    (first : OracleComp HashSpec (Option α))
    (middle : α → OracleComp HashSpec (Option β))
    (last : β → OracleComp HashSpec (Option γ)) :
    bindSome (bindSome first middle) last =
      bindSome first (fun value => bindSome (middle value) last) := by
  simp only [bindSome, bind_assoc]
  apply congrArg (fun (continuation : Option α →
    OracleComp HashSpec (Option γ)) => first >>= continuation)
  funext result
  cases result <;> simp [bind_assoc]

theorem runCount_bindSome {α β : Type} (hash : QueryImpl HashSpec Id)
    (head : OracleComp HashSpec (Option α))
    (next : α → OracleComp HashSpec (Option β)) :
    runCount hash (bindSome head next) =
      let first := runCount hash head
      match first.1 with
      | none => (none, first.2)
      | some value =>
          let second := runCount hash (next value)
          (second.1, first.2 + second.2) := by
  rw [bindSome, runCount_bind]
  cases h : runCount hash head with
  | mk result cost =>
      cases result <;> simp [h, runCount_pure]

theorem bindSome_success_floor {α β : Type} (hash : QueryImpl HashSpec Id)
    (head : OracleComp HashSpec (Option α))
    (next : α → OracleComp HashSpec (Option β))
    (floorHead floorTail : Nat)
    (headFloor : ∀ value, (runCount hash head).1 = some value →
      floorHead ≤ (runCount hash head).2)
    (tailFloor : ∀ value, (runCount hash (next value)).1 ≠ none →
      floorTail ≤ (runCount hash (next value)).2)
    (success : (runCount hash (bindSome head next)).1 ≠ none) :
    floorHead + floorTail ≤ (runCount hash (bindSome head next)).2 := by
  rw [runCount_bindSome] at success ⊢
  cases h : runCount hash head with
  | mk result cost =>
      cases result with
      | none => simp [h] at success
      | some value =>
          simp only [h] at success ⊢
          have hhead : floorHead ≤ cost := by
            simpa only [h] using headFloor value (by simp [h])
          have htail := tailFloor value success
          omega

theorem runCount_signLayer_success_ge (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (result : LayerSignature lay)
    (success : (runCount hash
      (Seeded.signLayer secretKey index lay :
        OracleComp HashSpec (Option (LayerSignature lay)))).1 = some result) :
    seededTreePathCalls lay ≤
      (runCount hash
        (Seeded.signLayer secretKey index lay :
          OracleComp HashSpec (Option (LayerSignature lay)))).2 := by
  simp only [Seeded.signLayer, runCount_bind] at success ⊢
  let messageRun := runCount hash
    (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest)
  cases hots : runCount hash
      (Seeded.otsSign secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) secretKey.seed messageRun.1 :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) with
  | mk option cost =>
      cases option with
      | none => simp [messageRun, hots, runCount_pure] at success
      | some pair =>
          rcases pair with ⟨counter, values⟩
          simp only [messageRun, hots, runCount_bind, runCount_pure] at success ⊢
          rw [runCount_treePath]
          omega

def appendSome {α β : Type} (first : OracleComp HashSpec (Option α))
    (second : OracleComp HashSpec (Option β)) :
    OracleComp HashSpec (Option (α × β)) :=
  bindSome first fun left => bindSome second fun right => pure (some (left, right))

theorem appendSome_success_floor {α β : Type} (hash : QueryImpl HashSpec Id)
    (first : OracleComp HashSpec (Option α))
    (second : OracleComp HashSpec (Option β))
    (firstFloor secondFloor : Nat)
    (leftBound : (runCount hash first).1 ≠ none →
      firstFloor ≤ (runCount hash first).2)
    (rightBound : (runCount hash second).1 ≠ none →
      secondFloor ≤ (runCount hash second).2)
    (success : (runCount hash (appendSome first second)).1 ≠ none) :
    firstFloor + secondFloor ≤
      (runCount hash (appendSome first second)).2 := by
  unfold appendSome at success ⊢
  rw [runCount_bindSome] at success ⊢
  cases hfirst : runCount hash first with
  | mk firstResult firstCost =>
      cases firstResult with
      | none => simp [hfirst] at success
      | some left =>
          simp only [hfirst] at success ⊢
          rw [runCount_bindSome] at success ⊢
          cases hsecond : runCount hash second with
          | mk secondResult secondCost =>
              cases secondResult with
              | none => simp [hsecond] at success
              | some right =>
                  simp only [hsecond, runCount_pure] at success ⊢
                  have hleft : firstFloor ≤ firstCost := by
                    simpa only [hfirst] using leftBound (by simp [hfirst])
                  have hright : secondFloor ≤ secondCost := by
                    simpa only [hsecond] using rightBound (by simp [hsecond])
                  omega

def lowerFive (secretKey : Seeded.SecretKey) (index : Index) :=
  appendSome
    (appendSome
      (appendSome
        (appendSome
          (Seeded.signLayer secretKey index bottomLayer)
          (Seeded.signLayer secretKey index middle4Layer))
        (Seeded.signLayer secretKey index middle3Layer))
      (Seeded.signLayer secretKey index middle2Layer))
    (Seeded.signLayer secretKey index middleLayer)

theorem lowerFive_success_floor (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index)
    (success : (runCount hash (lowerFive secretKey index)).1 ≠ none) :
    lowerFiveTreePathCalls ≤
      (runCount hash (lowerFive secretKey index)).2 := by
  let bottom : OracleComp HashSpec (Option (LayerSignature bottomLayer)) :=
    Seeded.signLayer secretKey index bottomLayer
  let m4 : OracleComp HashSpec (Option (LayerSignature middle4Layer)) :=
    Seeded.signLayer secretKey index middle4Layer
  let m3 : OracleComp HashSpec (Option (LayerSignature middle3Layer)) :=
    Seeded.signLayer secretKey index middle3Layer
  let m2 : OracleComp HashSpec (Option (LayerSignature middle2Layer)) :=
    Seeded.signLayer secretKey index middle2Layer
  let m : OracleComp HashSpec (Option (LayerSignature middleLayer)) :=
    Seeded.signLayer secretKey index middleLayer
  have stage (lay : Layer) (result : LayerSignature lay) :
      (runCount hash (Seeded.signLayer secretKey index lay)).1 = some result →
      seededTreePathCalls lay ≤
        (runCount hash (Seeded.signLayer secretKey index lay)).2 :=
    runCount_signLayer_success_ge hash secretKey index lay result
  have stageBound (lay : Layer) :
      (runCount hash (Seeded.signLayer secretKey index lay)).1 ≠ none →
      seededTreePathCalls lay ≤
        (runCount hash (Seeded.signLayer secretKey index lay)).2 := by
    intro nonempty
    cases h : (runCount hash (Seeded.signLayer secretKey index lay)).1 with
    | none => exact (nonempty h).elim
    | some result => exact stage lay result h
  have two (nonempty : (runCount hash (appendSome bottom m4)).1 ≠ none) :
      seededTreePathCalls bottomLayer + seededTreePathCalls middle4Layer ≤
        (runCount hash (appendSome bottom m4)).2 :=
    appendSome_success_floor hash bottom m4 _ _
      (stageBound bottomLayer) (stageBound middle4Layer) nonempty
  have three (nonempty : (runCount hash
      (appendSome (appendSome bottom m4) m3)).1 ≠ none) :
      (seededTreePathCalls bottomLayer + seededTreePathCalls middle4Layer) +
        seededTreePathCalls middle3Layer ≤
      (runCount hash (appendSome (appendSome bottom m4) m3)).2 :=
    appendSome_success_floor hash (appendSome bottom m4) m3 _ _
      two (stageBound middle3Layer) nonempty
  have four (nonempty : (runCount hash
      (appendSome (appendSome (appendSome bottom m4) m3) m2)).1 ≠ none) :
      ((seededTreePathCalls bottomLayer + seededTreePathCalls middle4Layer) +
        seededTreePathCalls middle3Layer) + seededTreePathCalls middle2Layer ≤
      (runCount hash
        (appendSome (appendSome (appendSome bottom m4) m3) m2)).2 :=
    appendSome_success_floor hash
      (appendSome (appendSome bottom m4) m3) m2 _ _
      three (stageBound middle2Layer) nonempty
  exact appendSome_success_floor hash
    (appendSome (appendSome (appendSome bottom m4) m3) m2) m _ _
    four (stageBound middleLayer) success

/-- info: 'SigGolfCandidate.SphincsCostComposition.bindSome_success_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bindSome_success_floor

/-- info: 'SigGolfCandidate.SphincsCostComposition.runCount_signLayer_success_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runCount_signLayer_success_ge

end SigGolfCandidate.SphincsCostComposition
