import SigGolfCandidate.SphincsCachedRatioArithmetic
import SigGolfCandidate.SphincsCachedSignRatio

namespace SigGolfCandidate.CachedSignerTrace
open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCostFullFloor
open SigGolfCandidate.SphincsCachedLayersBridge

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Seeded.signLayer signTopWithCache

theorem runCount_rawTail_ratio_of_layers (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (cache : Nat → Nat → Digest)
    (state : Option PrefixOutput)
    (hvalue : ∀ index : Index,
      (runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))).1 =
      (runCount hash (signLayersWithCache secretKey index cache)).1)
    (hcost : ∀ index : Index,
      (runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay)))).2 =
      (runCount hash (signLayersWithCache secretKey index cache)).2 +
        if (runCount hash (signLayersWithCache secretKey index cache)).1.isSome
        then seededTopPathCalls else 0) :
    (runCount hash (rawTail secretKey state)).2 ≤
      48 * (runCount hash (cachedTail secretKey cache state)).2 := by
  cases state with
  | none => simp [runCount_rawTail_exact, runCount_cachedTail_none]
  | some data =>
    rcases data with ⟨randomness, index, secrets, ftsPath⟩
    have hfloor := signLayersWithCache_success_floor hash secretKey index cache
    have hratio := layer_ratio_arithmetic
      (runCount hash
        (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec (Option ((lay : Layer) → LayerSignature lay))))
      (runCount hash (signLayersWithCache secretKey index cache))
      (hvalue index) (hcost index) hfloor
    have hraw := runCount_rawTail_exact hash secretKey
      (some (randomness, index, secrets, ftsPath))
    have hcached := runCount_cachedTail_some hash secretKey cache
      randomness index secrets ftsPath
    rw [hraw, hcached]
    exact hratio

theorem runCount_rawTail_ratio (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (state : Option PrefixOutput) :
    (runCount hash (rawTail secretKey state)).2 ≤
      48 * (runCount hash
        (cachedTail secretKey (canonicalTopCache hash secretKey) state)).2 := by
  apply runCount_rawTail_ratio_of_layers
  · exact runCount_layers_value hash secretKey
  · exact runCount_layers_cost hash secretKey

theorem runCount_bind_ratio {α β : Type} (hash : QueryImpl HashSpec Id)
    (head : OracleComp HashSpec α)
    (raw cached : α → OracleComp HashSpec β)
    (hcost : ∀ input, (runCount hash (raw input)).2 ≤
      48 * (runCount hash (cached input)).2) :
    (runCount hash (head >>= raw)).2 ≤
      48 * (runCount hash (head >>= cached)).2 := by
  simp only [runCount_bind]
  have h := hcost (runCount hash head).1
  omega

theorem runCount_sign_ratio (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) :
    (runCount hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))).2 ≤
      48 * (runCount hash
        (signWithCache secretKey message (canonicalTopCache hash secretKey))).2 := by
  rw [sign_eq_prefix_tail, cachedSign_eq_prefix_tail]
  exact runCount_bind_ratio hash (signPrefix secretKey message)
    (rawTail secretKey)
    (cachedTail secretKey (canonicalTopCache hash secretKey))
    (runCount_rawTail_ratio hash secretKey)

theorem single_signer_ratio (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) :
    (rawSigner hash secretKey message).1 = (cachedSigner hash secretKey message).1 ∧
      (rawSigner hash secretKey message).2 ≤
        48 * (cachedSigner hash secretKey message).2 := by
  constructor
  · exact (runCount_sign_related hash secretKey message).1
  · exact runCount_sign_ratio hash secretKey message

/-- A raw-security reduction consumes at most 48 times the whole concrete hash budget. -/
theorem adaptive_raw_budget_48
    (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (world : QueryImpl OracleWorld Id)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (outsideCalls q : Nat)
    (hcost : outsideCalls +
      (runInteraction world (cachedSigner hash secretKey) computation).hashCalls ≤ q) :
    outsideCalls +
      (runInteraction world (rawSigner hash secretKey) computation).hashCalls ≤ 48 * q :=
  adaptive_raw_budget_ratio hash secretKey world
    (single_signer_ratio hash secretKey) computation outsideCalls q hcost

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_rawTail_ratio_of_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.runCount_rawTail_ratio_of_layers

/-- info: 'SigGolfCandidate.CachedSignerTrace.runCount_rawTail_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.runCount_rawTail_ratio

/-- info: 'SigGolfCandidate.CachedSignerTrace.single_signer_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.single_signer_ratio

/-- info: 'SigGolfCandidate.CachedSignerTrace.adaptive_raw_budget_48' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.CachedSignerTrace.adaptive_raw_budget_48
