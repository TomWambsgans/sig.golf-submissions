import SigGolfCandidate.SphincsCachedSignTrace

namespace SigGolfCandidate.CachedSignerTrace

open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev PrefixOutput :=
  Randomness × Index × (FtsTree → Digest) ×
    (FtsTree → Fin ftsTreeHeight → Digest)

def signPrefix (secretKey : Seeded.SecretKey) (message : Message) :
    OracleComp HashSpec (Option PrefixOutput) := do
  let some (randomness, index, leaves) ←
    (Seeded.signDigestLoop secretKey message digestAttemptLimit 0 :
      OracleComp HashSpec _) | return none
  let secrets ← sequenceFin fun tree =>
    (deriveKey secretKey.parameter
      (.fts index tree (leaves (ftsIndexOf tree))) secretKey.seed :
      OracleComp HashSpec Digest)
  let ftsPath ←
    (Seeded.ftsOpen secretKey.parameter index leaves secretKey.seed :
      OracleComp HashSpec _)
  return some (randomness, index, secrets, ftsPath)

def rawTail (secretKey : Seeded.SecretKey) :
    Option PrefixOutput → OracleComp HashSpec (Option Signature)
  | none => pure none
  | some (randomness, index, secrets, ftsPath) => do
      let some layers ←
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec _) | return none
      let _ ← (Seeded.treeRoot secretKey.parameter topLayer rootTree secretKey.seed :
        OracleComp HashSpec Digest)
      return some ⟨randomness, secrets, ftsPath, layers⟩

def cachedTail (secretKey : Seeded.SecretKey) (cache : Nat → Nat → Digest) :
    Option PrefixOutput → OracleComp HashSpec (Option Signature)
  | none => pure none
  | some (randomness, index, secrets, ftsPath) => do
      let some layers ← signLayersWithCache secretKey index cache | return none
      return some ⟨randomness, secrets, ftsPath, layers⟩

theorem sign_eq_prefix_tail (secretKey : Seeded.SecretKey) (message : Message) :
    (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature)) =
      signPrefix secretKey message >>= rawTail secretKey := by
  unfold Seeded.sign signPrefix
  simp only [bind_assoc]
  congr 1
  funext attempt
  cases attempt with
  | none => simp [rawTail]
  | some data =>
    rcases data with ⟨randomness, index, leaves⟩
    simp [rawTail, bind_assoc]
    rfl

theorem cachedSign_eq_prefix_tail (secretKey : Seeded.SecretKey) (message : Message)
    (cache : Nat → Nat → Digest) :
    signWithCache secretKey message cache =
      signPrefix secretKey message >>= cachedTail secretKey cache := by
  unfold signWithCache signPrefix
  simp only [bind_assoc]
  congr 1
  funext attempt
  cases attempt with
  | none => simp [cachedTail]
  | some data =>
    rcases data with ⟨randomness, index, leaves⟩
    simp [cachedTail, bind_assoc]
    rfl

theorem runCount_bind_cost_le {α β : Type} (hash : QueryImpl HashSpec Id)
    (head : OracleComp HashSpec α)
    (raw cached : α → OracleComp HashSpec β) (extra : Nat)
    (hcost : ∀ input, (runCount hash (raw input)).2 ≤
      (runCount hash (cached input)).2 + extra) :
    (runCount hash (head >>= raw)).2 ≤
      (runCount hash (head >>= cached)).2 + extra := by
  simp only [runCount_bind]
  have h := hcost (runCount hash head).1
  omega

theorem runCount_tail_cost (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (state : Option PrefixOutput) :
    (runCount hash (rawTail secretKey state)).2 ≤
      (runCount hash
        (cachedTail secretKey (canonicalTopCache hash secretKey) state)).2 +
        (seededTopPathCalls + seededTreeNodeCalls (layerHeight topLayer)) := by
  cases state with
  | none => simp [rawTail, cachedTail, runCount_pure]
  | some data =>
    rcases data with ⟨randomness, index, secrets, ftsPath⟩
    simp only [rawTail, cachedTail, runCount_bind]
    have hcost := runCount_signLayers_cost hash secretKey index
      (canonicalTopCache hash secretKey)
    have hvalue := signLayersWithCache_value hash secretKey index
    have heq :
        (runCount hash
          (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
            OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))).1 =
        (runCount hash
          (signLayersWithCache secretKey index (canonicalTopCache hash secretKey))).1 := by
      rw [runCount_value, runCount_value]
      exact hvalue.symm
    cases hraw : runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))) with
    | mk rawLayers rawCost =>
      cases hc : runCount hash
          (signLayersWithCache secretKey index (canonicalTopCache hash secretKey)) with
      | mk cachedLayers cachedCost =>
        simp only [hraw, hc] at hcost heq ⊢
        subst cachedLayers
        cases rawLayers with
        | none => simp [runCount_pure] at hcost ⊢; omega
        | some layers =>
          simp only [runCount_bind, runCount_pure, runCount_treeRoot]
          omega

theorem runCount_sign_cost (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) :
    (runCount hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))).2 ≤
      (runCount hash
        (signWithCache secretKey message (canonicalTopCache hash secretKey))).2 +
        (seededTopPathCalls + seededTreeNodeCalls (layerHeight topLayer)) := by
  rw [sign_eq_prefix_tail, cachedSign_eq_prefix_tail]
  exact runCount_bind_cost_le hash (signPrefix secretKey message)
    (rawTail secretKey)
    (cachedTail secretKey (canonicalTopCache hash secretKey)) _
    (runCount_tail_cost hash secretKey)

theorem runCount_sign_related (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) :
    let raw := runCount hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))
    let cached := runCount hash
      (signWithCache secretKey message (canonicalTopCache hash secretKey))
    raw.1 = cached.1 ∧ raw.2 ≤ cached.2 + 1711698 := by
  dsimp only
  constructor
  · rw [runCount_value, runCount_value]
    exact signWithCanonicalCache_value hash secretKey message
  · have hcost := runCount_sign_cost hash secretKey message
    rw [seededTopPathCalls_eq, seededFinalTreeCalls_eq] at hcost
    norm_num at hcost ⊢
    exact hcost

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_sign_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runCount_sign_related

end SigGolfCandidate.CachedSignerTrace
