import SigGolfCandidate.SphincsCacheTreeCollisionEvent
import SigGolfCandidate.SphincsAlteredCacheCanonical
import SigGolfCandidate.SphincsAlteredCacheSplit
import SigGolfCandidate.SphincsCachedRatioGeneric

/-! Fixed-oracle meaning of a public full-tree precheck performed before signing. -/

namespace SigGolfCandidate.SphincsCheckedCacheSigner
open SphincsSecurity SphincsSecurity.Concrete OracleComp
open SigGolfCandidate.SphincsCachedSignValue
open SigGolfCandidate.SphincsCacheTreeConcrete
open SigGolfCandidate.SphincsCacheTreeCollisionEvent
open SigGolfCandidate.SphincsAlteredCacheSplit
open SigGolfCandidate.SphincsWire

set_option maxHeartbeats 1000000

def Pass (hash : QueryImpl HashSpec Id) (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest) : Prop :=
  parameter = secretKey.parameter ∧
  committedKey hash ⟨root, parameter⟩ =
    committedKey hash ⟨secretKey.root, secretKey.parameter⟩ ∧
  Consistent hash parameter cache ∧ cache 11 0 = root

/-- The abstract signer performs no secret-dependent signing when its public
precheck rejects. Oracle calls made by the precheck itself are modeled
separately from this answer-level function. -/
noncomputable def checkedAnswer (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest) : Option Signature := by
  classical
  exact if Pass hash secretKey parameter root cache then
    evalWithAnswerFn hash (signWithCache secretKey message cache)
  else none

theorem checkedAnswer_rejects (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest)
    (hbad : ¬ Pass hash secretKey parameter root cache) :
    checkedAnswer hash secretKey message parameter root cache = none := by
  simp [checkedAnswer, hbad]

/-- An accepted cache is canonical at every used node unless its header
commits to a different key or one of its 2047 parent hashes collides. -/
theorem accepted_cache_split (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest)
    (hkeygen : secretKey.root = (canonicalTopCache hash secretKey) 11 0)
    (hpass : Pass hash secretKey parameter root cache) :
    (∀ level, level ≤ 11 → ∀ node, node < 2 ^ (11 - level) →
      cache level node = (canonicalTopCache hash secretKey) level node) ∨
    NodeCollision hash secretKey cache ∨
    (commitmentInput ⟨root, parameter⟩ ≠
        commitmentInput ⟨secretKey.root, secretKey.parameter⟩ ∧
      (hash (commitmentInput ⟨root, parameter⟩)).extractLsb' 0 128 =
        (hash (commitmentInput ⟨secretKey.root, secretKey.parameter⟩)).extractLsb' 0 128) := by
  rcases hpass with ⟨hparam, hcommit, hconsistent, hroot⟩
  rcases same_commitment_key_or_collision hash
      ⟨secretKey.root, secretKey.parameter⟩ ⟨root, parameter⟩ hcommit with
    hsame | hcollision
  · have hrootCanonical : cache 11 0 = (canonicalTopCache hash secretKey) 11 0 := by
      have hrootEq : root = secretKey.root := congrArg PublicKey.root hsame
      exact hroot.trans (hrootEq.trans hkeygen)
    rcases canonical_or_node_collision hash secretKey cache
        (hparam ▸ hconsistent) hrootCanonical with hnodes | hnode
    · exact Or.inl hnodes
    · exact Or.inr (Or.inl hnode)
  · exact Or.inr (Or.inr hcollision)

/-- Once both collision events are excluded, an accepted request returns
exactly the same signature as the inherited abstract signer. -/
theorem checkedAnswer_eq_abstract (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest)
    (hkeygen : secretKey.root = (canonicalTopCache hash secretKey) 11 0)
    (hpass : Pass hash secretKey parameter root cache)
    (hnoNode : ¬ NodeCollision hash secretKey cache)
    (hnoCommit : ¬ (commitmentInput ⟨root, parameter⟩ ≠
        commitmentInput ⟨secretKey.root, secretKey.parameter⟩ ∧
      (hash (commitmentInput ⟨root, parameter⟩)).extractLsb' 0 128 =
        (hash (commitmentInput ⟨secretKey.root, secretKey.parameter⟩)).extractLsb' 0 128)) :
    checkedAnswer hash secretKey message parameter root cache =
      evalWithAnswerFn hash (Seeded.sign secretKey message) := by
  rcases accepted_cache_split hash secretKey parameter root cache hkeygen hpass with
    hnodes | hnode | hcommit
  · have hpath (index : Index) :
        topPathFromCache cache (leafIndexAt index topLayer) =
        topPathFromCache (canonicalTopCache hash secretKey)
          (leafIndexAt index topLayer) :=
      selected_path_eq_of_nodes_eq hash secretKey cache
        (leafIndexAt index topLayer) hnodes
        (selected_sibling_bound (leafIndexAt index topLayer))
    have heq := SigGolfCandidate.SphincsAlteredCacheCanonical.runCount_signWithCache_eq_of_selected_path
      hash secretKey message cache (canonicalTopCache hash secretKey)
      (fun _ index _ _ _ => hpath index)
    have hvalue : evalWithAnswerFn hash (signWithCache secretKey message cache) =
        evalWithAnswerFn hash
          (signWithCache secretKey message (canonicalTopCache hash secretKey)) := by
      simpa only [CachedSignerTrace.runCount_value] using congrArg Prod.fst heq
    rw [checkedAnswer, if_pos hpass, hvalue]
    exact (signWithCanonicalCache_value hash secretKey message).symm
  · exact False.elim (hnoNode hnode)
  · exact False.elim (hnoCommit hcommit)

/-- On a passing collision-free request, replacing the cached signer with the
inherited raw signer costs at most 48 times the actual cached signing calls.
The public precheck's own calls only increase the concrete-side budget. -/
theorem accepted_signer_ratio (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (parameter : PublicParameter) (root : Digest)
    (cache : Nat → Nat → Digest)
    (hkeygen : secretKey.root = (canonicalTopCache hash secretKey) 11 0)
    (hpass : Pass hash secretKey parameter root cache)
    (hnoNode : ¬ NodeCollision hash secretKey cache)
    (hnoCommit : ¬ (commitmentInput ⟨root, parameter⟩ ≠
        commitmentInput ⟨secretKey.root, secretKey.parameter⟩ ∧
      (hash (commitmentInput ⟨root, parameter⟩)).extractLsb' 0 128 =
        (hash (commitmentInput ⟨secretKey.root, secretKey.parameter⟩)).extractLsb' 0 128)) :
    let raw := CachedSignerTrace.runCount hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))
    let cached := CachedSignerTrace.runCount hash
      (signWithCache secretKey message cache)
    raw.1 = cached.1 ∧ raw.2 ≤ 48 * cached.2 := by
  rcases accepted_cache_split hash secretKey parameter root cache hkeygen hpass with
    hnodes | hnode | hcommit
  · have hpath (index : Index) :
        topPathFromCache cache (leafIndexAt index topLayer) =
        topPathFromCache (canonicalTopCache hash secretKey)
          (leafIndexAt index topLayer) :=
      selected_path_eq_of_nodes_eq hash secretKey cache
        (leafIndexAt index topLayer) hnodes
        (selected_sibling_bound (leafIndexAt index topLayer))
    have heq := SigGolfCandidate.SphincsAlteredCacheCanonical.runCount_signWithCache_eq_of_selected_path
      hash secretKey message cache (canonicalTopCache hash secretKey)
      (fun _ index _ _ _ => hpath index)
    have hratio := CachedSignerTrace.single_signer_ratio hash secretKey message
    change
      (CachedSignerTrace.runCount hash
        (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))).1 =
          (CachedSignerTrace.runCount hash
            (signWithCache secretKey message (canonicalTopCache hash secretKey))).1 ∧
      (CachedSignerTrace.runCount hash
        (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))).2 ≤
          48 * (CachedSignerTrace.runCount hash
            (signWithCache secretKey message (canonicalTopCache hash secretKey))).2 at hratio
    simpa only [heq] using hratio
  · exact False.elim (hnoNode hnode)
  · exact False.elim (hnoCommit hcommit)

end SigGolfCandidate.SphincsCheckedCacheSigner

/-- info: 'SigGolfCandidate.SphincsCheckedCacheSigner.accepted_cache_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCheckedCacheSigner.accepted_cache_split

/-- info: 'SigGolfCandidate.SphincsCheckedCacheSigner.checkedAnswer_eq_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCheckedCacheSigner.checkedAnswer_eq_abstract

/-- info: 'SigGolfCandidate.SphincsCheckedCacheSigner.accepted_signer_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCheckedCacheSigner.accepted_signer_ratio
