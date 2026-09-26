import SigGolfCandidate.SphincsSecurity.Completeness.Assembly
import SigGolf.Statements
import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsAlignedQuery
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/- Shared-oracle all-message failure bound for the current beta HASH query type. -/
namespace SigGolfCandidate.SphincsCompletenessUnion
open SigGolf OracleComp
set_option maxRecDepth 4096

private theorem foldlM_allSucceed (hash : Hash)
    (program : Message → OracleComp HashSpec HonestResult)
    (messages : List Message) (initial : HonestSummary) :
    (evalWithAnswerFn hash (messages.foldlM (fun summary message => do
      let result ← program message
      return (⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) initial)).allSucceed =
      (initial.allSucceed &&
        messages.all (fun message =>
          (evalWithAnswerFn hash (program message)).success)) := by
  induction messages generalizing initial with
  | nil => simp
  | cons message messages ih =>
    simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [ih]
    simp [Bool.and_assoc]

theorem allMessages_success_iff (submission : Submission)
    (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).allSucceed = true ↔
      ∀ message : Message,
        (evalWithAnswerFn hash (submission.honest secretKey message)).success = true := by
  simp only [Submission.allMessages, foldlM_allSucceed]
  simp only [Bool.true_and, List.all_eq_true]
  constructor
  · intro h message
    exact h message (Finset.mem_toList.mpr (Finset.mem_univ message))
  · intro h message _
    exact h message

theorem allMessages_failure_iff (submission : Submission)
    (hash : Hash) (secretKey : SecretKey) :
    (evalWithAnswerFn hash (submission.allMessages secretKey)).allSucceed = false ↔
      ∃ message : Message,
        (evalWithAnswerFn hash (submission.honest secretKey message)).success = false := by
  simpa only [Bool.not_eq_true, not_forall] using
    not_congr (allMessages_success_iff submission hash secretKey)

end SigGolfCandidate.SphincsCompletenessUnion

/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.allMessages_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.allMessages_success_iff

/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.allMessages_failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.allMessages_failure_iff

namespace SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint
open SigGolf OracleComp OracleSpec

/-- The finite set of oracle inputs reachable in any branch of this finite computation. -/
noncomputable def queryFootprintSet {α : Type} (p : OracleComp HashSpec α) : Set Query :=
  OracleComp.construct (fun _ => ∅) (fun t _ ih =>
    {t} ∪ ⋃ u : BitVec 256, ih u) p


inductive AllQueriesWithinSet (S : Set Query) {α : Type} : OracleComp HashSpec α → Prop
  | pure (a : α) : AllQueriesWithinSet S (pure a)
  | query_bind (t : Query) (k : BitVec 256 → OracleComp HashSpec α)
      (ht : t ∈ S) (hk : ∀ u, AllQueriesWithinSet S (k u)) :
      AllQueriesWithinSet S (liftM (HashSpec.query t) >>= k)


theorem footprint_finite {α : Type} (p : OracleComp HashSpec α) :
    (queryFootprintSet p).Finite := by
  induction p using OracleComp.inductionOn with
  | pure a =>
      simp only [queryFootprintSet, OracleComp.construct_pure]
      exact Set.finite_empty
  | query_bind t k ih =>
      simp only [queryFootprintSet, OracleComp.construct_query_bind]
      apply Set.Finite.union (Set.finite_singleton t)
      apply Set.Finite.iUnion (t := Set.univ) Set.finite_univ
      · intro u _; exact ih u
      · intro u hu; exact False.elim (hu (Set.mem_univ u))

theorem AllQueriesWithinSet.mono {S T : Set Query} {α : Type}
    {p : OracleComp HashSpec α} (hST : S ⊆ T) (hp : AllQueriesWithinSet S p) :
    AllQueriesWithinSet T p := by
  induction hp with
  | pure a => exact .pure a
  | query_bind t k ht hk ih =>
      exact .query_bind t k (hST ht) (fun u => ih u)

theorem footprint_covers {α : Type} (p : OracleComp HashSpec α) :
    AllQueriesWithinSet (queryFootprintSet p) p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact .pure a
  | query_bind t k ih =>
      let S : Set Query := queryFootprintSet (liftM (HashSpec.query t) >>= k)
      have hmem : t ∈ S := by
        simp [S, queryFootprintSet, OracleComp.construct_query_bind]
      have hsub (u : BitVec 256) : queryFootprintSet (k u) ⊆ S := by
        intro x hx
        simp only [S, queryFootprintSet, OracleComp.construct_query_bind]
        exact Or.inr (Set.mem_iUnion.mpr ⟨u, hx⟩)
      have htail (u : BitVec 256) : AllQueriesWithinSet S (k u) :=
        AllQueriesWithinSet.mono (hsub u) (ih u)
      exact AllQueriesWithinSet.query_bind t k hmem htail



noncomputable def extendTable (S : Set Query)
    (g : Subtype S → BitVec 256) : Query → BitVec 256 :=
  by
    classical
    exact fun q => if h : q ∈ S then g ⟨q, h⟩ else 0

noncomputable def extendCached (S : Set Query) (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) : Query → BitVec 256 :=
  by
    classical
    exact fun q => if h : q ∈ S then (c q).getD (g ⟨q, h⟩) else 0

private theorem extendCached_empty (S : Set Query)
    (g : Subtype S → BitVec 256) :
    extendCached S (∅ : QueryCache HashSpec) g = extendTable S g := by
  funext q
  classical
  simp [extendCached, extendTable]

private theorem extendCached_query (S : Set Query) (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) (t : Query) (ht : t ∈ S) :
    extendCached S c g t = (c t).getD (g ⟨t, ht⟩) := by
  classical
  simp [extendCached, ht]

private theorem extendCached_cacheQuery (S : Set Query) [DecidableEq (Subtype S)] (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) (t : Query) (ht : t ∈ S)
    (u : BitVec 256) (hc : c t = none) :
    extendCached S (c.cacheQuery t u) g =
      extendCached S c (Function.update g ⟨t, ht⟩ u) := by
  funext q
  classical
  by_cases hq : q ∈ S
  · by_cases hqt : q = t
    · subst q
      simp [extendCached, ht, QueryCache.cacheQuery, hc]
    · have hne : (⟨q, hq⟩ : Subtype S) ≠ ⟨t, ht⟩ := by
        intro heq
        exact hqt (congrArg Subtype.val heq)
      simp [extendCached, hq, QueryCache.cacheQuery, hqt,
        Function.update, hne]
  · simp [extendCached, hq]



private abbrev RestrictedTable (S : Set Query) := Subtype S → BitVec 256

/-- A lazy random oracle agrees in distribution with a uniform table on the finite query footprint. -/
private theorem eagerFootprint (S : Set Query) [Finite (Subtype S)]
    [SampleableType (RestrictedTable S)] {α : Type}
    (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p)
    (c : QueryCache HashSpec) :
    𝒮[(simulateQ randomOracle p).run' c] =
      𝒮[do let g ← $ᵗ (RestrictedTable S);
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g)) p)] := by
  classical
  letI : DecidableEq α := Classical.decEq _
  induction hp generalizing c with
  | pure a =>
      refine evalSPMF_ext fun x => ?_
      simp [simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind t k ht hk ih =>
      have hred :
          (simulateQ randomOracle (liftM (HashSpec.query t) >>= k)).run' c =
            ((randomOracle (spec := HashSpec) t).run c) >>=
              fun pair : BitVec 256 × QueryCache HashSpec =>
                (simulateQ randomOracle (k pair.1)).run' pair.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
          StateT.run_bind, map_bind]
        rfl
      have heval : ∀ g : RestrictedTable S,
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g))
            (liftM (HashSpec.query t) >>= k) =
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g))
            (k (extendCached S c g t)) := by
        intro g
        rw [evalWithAnswerFn_bind]
        simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
      rw [hred]
      simp_rw [heval]
      rcases hc : c t with _ | u
      · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
        simp only [Function.comp, bind_assoc, pure_bind]
        set ψ : RestrictedTable S → α := fun g' =>
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g'))
            (k (extendCached S c g' t)) with hψ
        have hfun : ∀ u : BitVec 256,
            (fun g : RestrictedTable S =>
              evalWithAnswerFn
                (QueryImpl.ofFn (extendCached S (c.cacheQuery t u) g)) (k u)) =
            fun g : RestrictedTable S => ψ (Function.update g ⟨t, ht⟩ u) := by
          intro u
          funext g
          simp only [hψ]
          rw [extendCached_cacheQuery S c g t ht u hc]
          rw [extendCached_query S c _ t ht]
          simp only [hc, Option.getD_none]
          rw [Function.update_self]
        trans 𝒮[do let u ← $ᵗ (BitVec 256);
                        let g ← $ᵗ (RestrictedTable S);
                        pure (ψ (Function.update g ⟨t, ht⟩ u))]
        · rw [evalSPMF_bind, evalSPMF_bind]
          refine congrArg _ (funext fun u => ?_)
          rw [ih u (c.cacheQuery t u), bind_pure_comp, bind_pure_comp, hfun u]
        · letI : DecidableEq (Subtype S) := Classical.decEq _
          have hfinite : Finite (BitVec 256) := inferInstance
          have hnonempty : Nonempty (BitVec 256) := inferInstance
          simpa only [hψ] using
            (@evalSPMF_uniformSample_bind_update_map (Subtype S)
              (BitVec 256) (Classical.decEq _) inferInstance hfinite hnonempty
              (FinEnum.SampleableType (BitVec 256)) inferInstance α ⟨t, ht⟩ ψ)
      · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
        have h : ∀ g : RestrictedTable S, extendCached S c g t = u := fun g => by
          rw [extendCached_query S c g t ht]
          simp [hc]
        simp_rw [h]



noncomputable def sampleRestrictedTable (S : Set Query) (hS : S.Finite) :
    ProbComp (RestrictedTable S) := by
  classical
  letI : Finite (Subtype S) := hS.to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  exact $ᵗ (RestrictedTable S)

theorem eagerFootprint_empty {α : Type} (p : OracleComp HashSpec α) :
    let S := queryFootprintSet p
    𝒮[(simulateQ randomOracle p).run' ∅] =
      𝒮[do let g ← sampleRestrictedTable S (footprint_finite p);
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] := by
  classical
  let S := queryFootprintSet p
  letI : Finite (Subtype S) := (footprint_finite p).to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  simpa only [sampleRestrictedTable, extendCached_empty] using
    eagerFootprint S p (footprint_covers p) (∅ : QueryCache HashSpec)


noncomputable def familyFootprint {ι α β : Type} (p : OracleComp HashSpec α)
    (q : ι → OracleComp HashSpec β) : Set Query :=
  queryFootprintSet p ∪ ⋃ i : ι, queryFootprintSet (q i)

theorem familyFootprint_finite {ι α β : Type} [Finite ι]
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) :
    (familyFootprint p q).Finite := by
  apply Set.Finite.union (footprint_finite p)
  apply Set.Finite.iUnion (t := Set.univ) Set.finite_univ
  · intro i _; exact footprint_finite (q i)
  · intro i hi; exact False.elim (hi (Set.mem_univ i))

theorem familyFootprint_covers_all {ι α β : Type}
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) :
    AllQueriesWithinSet (familyFootprint p q) p := by
  apply AllQueriesWithinSet.mono (fun x hx => Or.inl hx) (footprint_covers p)

theorem familyFootprint_covers_member {ι α β : Type}
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) (i : ι) :
    AllQueriesWithinSet (familyFootprint p q) (q i) := by
  apply AllQueriesWithinSet.mono
    (S := queryFootprintSet (q i)) (T := familyFootprint p q)
    (fun x hx => show x ∈ familyFootprint p q from
      Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
    (footprint_covers (q i))

theorem eagerFootprint_on (S : Set Query) (hS : S.Finite) {α : Type}
    (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p) :
    𝒮[(simulateQ randomOracle p).run' ∅] =
      𝒮[do let g ← sampleRestrictedTable S hS;
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] := by
  classical
  letI : Finite (Subtype S) := hS.to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  simpa only [sampleRestrictedTable, extendCached_empty] using
    eagerFootprint S p hp (∅ : QueryCache HashSpec)


theorem probEvent_eagerFootprint_on (S : Set Query) (hS : S.Finite)
    {α : Type} (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p)
    (E : α → Prop) :
    Pr[E | SigGolf.withRandomOracle p] =
      Pr[fun g : RestrictedTable S =>
        E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p) |
        sampleRestrictedTable S hS] := by
  have h := eagerFootprint_on S hS p hp
  rw [probEvent_def, SigGolf.withRandomOracle, h]
  rw [← probEvent_def]
  change Pr[E | sampleRestrictedTable S hS >>= pure ∘
      (fun g => evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] = _
  exact probEvent_bind_pure_comp _ _ _


/-- Union bound under one shared random oracle, using one table for the whole family of experiments. -/
theorem sharedOracle_union_bound {ι α β : Type} [Fintype ι]
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β)
    (E : α → Prop) (F : ι → β → Prop)
    (hpointwise : ∀ hash : Hash,
      E (evalWithAnswerFn hash p) →
        ∃ i : ι, F i (evalWithAnswerFn hash (q i))) :
    Pr[E | SigGolf.withRandomOracle p] ≤
      ∑ i : ι, Pr[F i | SigGolf.withRandomOracle (q i)] := by
  classical
  let S := familyFootprint p q
  have hS : S.Finite := familyFootprint_finite p q
  let sample := sampleRestrictedTable S hS
  let hash : RestrictedTable S → Hash := fun g => QueryImpl.ofFn (extendTable S g)
  calc
    Pr[E | SigGolf.withRandomOracle p] =
        Pr[fun g => E (evalWithAnswerFn (hash g) p) | sample] := by
          exact probEvent_eagerFootprint_on S hS p (familyFootprint_covers_all p q) E
    _ ≤ Pr[fun g => ∃ i ∈ (Finset.univ : Finset ι),
          F i (evalWithAnswerFn (hash g) (q i)) | sample] := by
          apply probEvent_mono
          intro g _ hg
          obtain ⟨i, hi⟩ := hpointwise (hash g) hg
          exact ⟨i, Finset.mem_univ i, hi⟩
    _ ≤ ∑ i : ι, Pr[fun g => F i (evalWithAnswerFn (hash g) (q i)) | sample] :=
          probEvent_exists_finset_le_sum Finset.univ sample _
    _ = ∑ i : ι, Pr[F i | SigGolf.withRandomOracle (q i)] := by
          apply Finset.sum_congr rfl
          intro i _
          exact (probEvent_eagerFootprint_on S hS (q i)
            (familyFootprint_covers_member p q i) (F i)).symm


/-- Failure on any message is charged to the sum of the individual honest-run failure probabilities. -/
theorem submission_allMessages_failure_le_sum
    (submission : Submission) (secretKey : SecretKey) :
    Pr[fun summary => summary.allSucceed = false |
      SigGolf.withRandomOracle (submission.allMessages secretKey)] ≤
    ∑ message : Message,
      Pr[fun result => result.success = false |
        SigGolf.withRandomOracle (submission.honest secretKey message)] := by
  apply sharedOracle_union_bound
    (p := submission.allMessages secretKey)
    (q := fun message => submission.honest secretKey message)
    (E := fun summary => summary.allSucceed = false)
    (F := fun _ result => result.success = false)
  intro hash hfail
  exact (allMessages_failure_iff submission hash secretKey).mp hfail


/-- A per-secret-key sum of single-message failure probabilities proves the competition completeness claim. -/
theorem submission_complete_of_failure_sum
    (submission : Submission)
    (hbound : ∀ secretKey : SecretKey,
      ∑ message : Message,
        Pr[fun result => result.success = false |
          SigGolf.withRandomOracle (submission.honest secretKey message)] ≤ FAILURE) :
    submission.Complete := by
  intro secretKey
  let p := submission.allMessages secretKey
  have hrun : NeverFail ((simulateQ randomOracle p).run ∅) :=
    neverFail_simulateQ_randomOracle_run p ∅
  have htotal : NeverFail (SigGolf.withRandomOracle p) := by
    change NeverFail (Prod.fst <$> (simulateQ randomOracle p).run ∅)
    exact (neverFail_map_iff _ Prod.fst).mpr hrun
  have hfailed :
      Pr[fun summary => summary.allSucceed = false |
        SigGolf.withRandomOracle p] ≤ FAILURE :=
    (submission_allMessages_failure_le_sum submission secretKey).trans (hbound secretKey)
  have hcompl :
      Pr[fun summary => ¬ summary.allSucceed = true |
        SigGolf.withRandomOracle p] ≤ FAILURE := by
    simpa only [Bool.not_eq_true] using hfailed
  exact probEvent_one_sub_le_of_compl_le htotal.probFailure_eq_zero hcompl


theorem sharedOracle_event_mono {α β : Type}
    (p : OracleComp HashSpec α) (q : OracleComp HashSpec β)
    (E : α → Prop) (F : β → Prop)
    (hpointwise : ∀ hash : Hash,
      E (evalWithAnswerFn hash p) → F (evalWithAnswerFn hash q)) :
    Pr[E | SigGolf.withRandomOracle p] ≤
      Pr[F | SigGolf.withRandomOracle q] := by
  have h := sharedOracle_union_bound (ι := PUnit) p (fun _ => q)
    E (fun _ => F) (by
      intro hash he
      exact ⟨PUnit.unit, hpointwise hash he⟩)
  simpa using h
end SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint

/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.eagerFootprint_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.eagerFootprint_empty
/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.sharedOracle_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.sharedOracle_union_bound

/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.submission_allMessages_failure_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.submission_allMessages_failure_le_sum

/-- info: 'SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.submission_complete_of_failure_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.submission_complete_of_failure_sum


namespace SigGolfCandidate.AbstractQueryFootprint
open OracleComp OracleSpec
abbrev Query := SphincsSecurity.HashInput
abbrev HashSpec := Query →ₒ BitVec 256
abbrev Hash := QueryImpl HashSpec Id
noncomputable def withRandomOracle {α : Type} (p : OracleComp HashSpec α) : ProbComp α :=
  (simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) p).run' ∅

/-- The finite set of oracle inputs reachable in any branch of this finite computation. -/
noncomputable def queryFootprintSet {α : Type} (p : OracleComp HashSpec α) : Set Query :=
  OracleComp.construct (fun _ => ∅) (fun t _ ih =>
    {t} ∪ ⋃ u : BitVec 256, ih u) p


inductive AllQueriesWithinSet (S : Set Query) {α : Type} : OracleComp HashSpec α → Prop
  | pure (a : α) : AllQueriesWithinSet S (pure a)
  | query_bind (t : Query) (k : BitVec 256 → OracleComp HashSpec α)
      (ht : t ∈ S) (hk : ∀ u, AllQueriesWithinSet S (k u)) :
      AllQueriesWithinSet S (liftM (HashSpec.query t) >>= k)


theorem footprint_finite {α : Type} (p : OracleComp HashSpec α) :
    (queryFootprintSet p).Finite := by
  induction p using OracleComp.inductionOn with
  | pure a =>
      simp only [queryFootprintSet, OracleComp.construct_pure]
      exact Set.finite_empty
  | query_bind t k ih =>
      simp only [queryFootprintSet, OracleComp.construct_query_bind]
      apply Set.Finite.union (Set.finite_singleton t)
      apply Set.Finite.iUnion (t := Set.univ) Set.finite_univ
      · intro u _; exact ih u
      · intro u hu; exact False.elim (hu (Set.mem_univ u))

theorem AllQueriesWithinSet.mono {S T : Set Query} {α : Type}
    {p : OracleComp HashSpec α} (hST : S ⊆ T) (hp : AllQueriesWithinSet S p) :
    AllQueriesWithinSet T p := by
  induction hp with
  | pure a => exact .pure a
  | query_bind t k ht hk ih =>
      exact .query_bind t k (hST ht) (fun u => ih u)

theorem footprint_covers {α : Type} (p : OracleComp HashSpec α) :
    AllQueriesWithinSet (queryFootprintSet p) p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact .pure a
  | query_bind t k ih =>
      let S : Set Query := queryFootprintSet (liftM (HashSpec.query t) >>= k)
      have hmem : t ∈ S := by
        simp [S, queryFootprintSet, OracleComp.construct_query_bind]
      have hsub (u : BitVec 256) : queryFootprintSet (k u) ⊆ S := by
        intro x hx
        simp only [S, queryFootprintSet, OracleComp.construct_query_bind]
        exact Or.inr (Set.mem_iUnion.mpr ⟨u, hx⟩)
      have htail (u : BitVec 256) : AllQueriesWithinSet S (k u) :=
        AllQueriesWithinSet.mono (hsub u) (ih u)
      exact AllQueriesWithinSet.query_bind t k hmem htail



noncomputable def extendTable (S : Set Query)
    (g : Subtype S → BitVec 256) : Query → BitVec 256 :=
  by
    classical
    exact fun q => if h : q ∈ S then g ⟨q, h⟩ else 0

noncomputable def extendCached (S : Set Query) (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) : Query → BitVec 256 :=
  by
    classical
    exact fun q => if h : q ∈ S then (c q).getD (g ⟨q, h⟩) else 0

private theorem extendCached_empty (S : Set Query)
    (g : Subtype S → BitVec 256) :
    extendCached S (∅ : QueryCache HashSpec) g = extendTable S g := by
  funext q
  classical
  simp [extendCached, extendTable]

private theorem extendCached_query (S : Set Query) (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) (t : Query) (ht : t ∈ S) :
    extendCached S c g t = (c t).getD (g ⟨t, ht⟩) := by
  classical
  simp [extendCached, ht]

private theorem extendCached_cacheQuery (S : Set Query) [DecidableEq (Subtype S)] (c : QueryCache HashSpec)
    (g : Subtype S → BitVec 256) (t : Query) (ht : t ∈ S)
    (u : BitVec 256) (hc : c t = none) :
    extendCached S (c.cacheQuery t u) g =
      extendCached S c (Function.update g ⟨t, ht⟩ u) := by
  funext q
  classical
  by_cases hq : q ∈ S
  · by_cases hqt : q = t
    · subst q
      simp [extendCached, ht, QueryCache.cacheQuery, hc]
    · have hne : (⟨q, hq⟩ : Subtype S) ≠ ⟨t, ht⟩ := by
        intro heq
        exact hqt (congrArg Subtype.val heq)
      simp [extendCached, hq, QueryCache.cacheQuery, hqt,
        Function.update, hne]
  · simp [extendCached, hq]



private abbrev RestrictedTable (S : Set Query) := Subtype S → BitVec 256

/-- A lazy random oracle agrees in distribution with a uniform table on the finite query footprint. -/
private theorem eagerFootprint (S : Set Query) [Finite (Subtype S)]
    [SampleableType (RestrictedTable S)] {α : Type}
    (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p)
    (c : QueryCache HashSpec) :
    𝒮[(simulateQ randomOracle p).run' c] =
      𝒮[do let g ← $ᵗ (RestrictedTable S);
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g)) p)] := by
  classical
  letI : DecidableEq α := Classical.decEq _
  induction hp generalizing c with
  | pure a =>
      refine evalSPMF_ext fun x => ?_
      simp [simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind t k ht hk ih =>
      have hred :
          (simulateQ randomOracle (liftM (HashSpec.query t) >>= k)).run' c =
            ((randomOracle (spec := HashSpec) t).run c) >>=
              fun pair : BitVec 256 × QueryCache HashSpec =>
                (simulateQ randomOracle (k pair.1)).run' pair.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
          StateT.run_bind, map_bind]
        rfl
      have heval : ∀ g : RestrictedTable S,
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g))
            (liftM (HashSpec.query t) >>= k) =
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g))
            (k (extendCached S c g t)) := by
        intro g
        rw [evalWithAnswerFn_bind]
        simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]
      rw [hred]
      simp_rw [heval]
      rcases hc : c t with _ | u
      · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
        simp only [Function.comp, bind_assoc, pure_bind]
        set ψ : RestrictedTable S → α := fun g' =>
          evalWithAnswerFn (QueryImpl.ofFn (extendCached S c g'))
            (k (extendCached S c g' t)) with hψ
        have hfun : ∀ u : BitVec 256,
            (fun g : RestrictedTable S =>
              evalWithAnswerFn
                (QueryImpl.ofFn (extendCached S (c.cacheQuery t u) g)) (k u)) =
            fun g : RestrictedTable S => ψ (Function.update g ⟨t, ht⟩ u) := by
          intro u
          funext g
          simp only [hψ]
          rw [extendCached_cacheQuery S c g t ht u hc]
          rw [extendCached_query S c _ t ht]
          simp only [hc, Option.getD_none]
          rw [Function.update_self]
        trans 𝒮[do let u ← $ᵗ (BitVec 256);
                        let g ← $ᵗ (RestrictedTable S);
                        pure (ψ (Function.update g ⟨t, ht⟩ u))]
        · rw [evalSPMF_bind, evalSPMF_bind]
          refine congrArg _ (funext fun u => ?_)
          rw [ih u (c.cacheQuery t u), bind_pure_comp, bind_pure_comp, hfun u]
        · letI : DecidableEq (Subtype S) := Classical.decEq _
          have hfinite : Finite (BitVec 256) := inferInstance
          have hnonempty : Nonempty (BitVec 256) := inferInstance
          simpa only [hψ] using
            (@evalSPMF_uniformSample_bind_update_map (Subtype S)
              (BitVec 256) (Classical.decEq _) inferInstance hfinite hnonempty
              (FinEnum.SampleableType (BitVec 256)) inferInstance α ⟨t, ht⟩ ψ)
      · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
        have h : ∀ g : RestrictedTable S, extendCached S c g t = u := fun g => by
          rw [extendCached_query S c g t ht]
          simp [hc]
        simp_rw [h]



noncomputable def sampleRestrictedTable (S : Set Query) (hS : S.Finite) :
    ProbComp (RestrictedTable S) := by
  classical
  letI : Finite (Subtype S) := hS.to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  exact $ᵗ (RestrictedTable S)

theorem eagerFootprint_empty {α : Type} (p : OracleComp HashSpec α) :
    let S := queryFootprintSet p
    𝒮[(simulateQ randomOracle p).run' ∅] =
      𝒮[do let g ← sampleRestrictedTable S (footprint_finite p);
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] := by
  classical
  let S := queryFootprintSet p
  letI : Finite (Subtype S) := (footprint_finite p).to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  simpa only [sampleRestrictedTable, extendCached_empty] using
    eagerFootprint S p (footprint_covers p) (∅ : QueryCache HashSpec)


noncomputable def familyFootprint {ι α β : Type} (p : OracleComp HashSpec α)
    (q : ι → OracleComp HashSpec β) : Set Query :=
  queryFootprintSet p ∪ ⋃ i : ι, queryFootprintSet (q i)

theorem familyFootprint_finite {ι α β : Type} [Finite ι]
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) :
    (familyFootprint p q).Finite := by
  apply Set.Finite.union (footprint_finite p)
  apply Set.Finite.iUnion (t := Set.univ) Set.finite_univ
  · intro i _; exact footprint_finite (q i)
  · intro i hi; exact False.elim (hi (Set.mem_univ i))

theorem familyFootprint_covers_all {ι α β : Type}
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) :
    AllQueriesWithinSet (familyFootprint p q) p := by
  apply AllQueriesWithinSet.mono (fun x hx => Or.inl hx) (footprint_covers p)

theorem familyFootprint_covers_member {ι α β : Type}
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β) (i : ι) :
    AllQueriesWithinSet (familyFootprint p q) (q i) := by
  apply AllQueriesWithinSet.mono
    (S := queryFootprintSet (q i)) (T := familyFootprint p q)
    (fun x hx => show x ∈ familyFootprint p q from
      Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
    (footprint_covers (q i))

theorem eagerFootprint_on (S : Set Query) (hS : S.Finite) {α : Type}
    (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p) :
    𝒮[(simulateQ randomOracle p).run' ∅] =
      𝒮[do let g ← sampleRestrictedTable S hS;
            pure (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] := by
  classical
  letI : Finite (Subtype S) := hS.to_subtype
  letI : Fintype (Subtype S) := Fintype.ofFinite _
  simpa only [sampleRestrictedTable, extendCached_empty] using
    eagerFootprint S p hp (∅ : QueryCache HashSpec)


theorem probEvent_eagerFootprint_on (S : Set Query) (hS : S.Finite)
    {α : Type} (p : OracleComp HashSpec α) (hp : AllQueriesWithinSet S p)
    (E : α → Prop) :
    Pr[E | withRandomOracle p] =
      Pr[fun g : RestrictedTable S =>
        E (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p) |
        sampleRestrictedTable S hS] := by
  have h := eagerFootprint_on S hS p hp
  rw [probEvent_def, withRandomOracle, h]
  rw [← probEvent_def]
  change Pr[E | sampleRestrictedTable S hS >>= pure ∘
      (fun g => evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) p)] = _
  exact probEvent_bind_pure_comp _ _ _


/-- Union bound under one shared random oracle, using one table for the whole family of experiments. -/
theorem sharedOracle_union_bound {ι α β : Type} [Fintype ι]
    (p : OracleComp HashSpec α) (q : ι → OracleComp HashSpec β)
    (E : α → Prop) (F : ι → β → Prop)
    (hpointwise : ∀ hash : Hash,
      E (evalWithAnswerFn hash p) →
        ∃ i : ι, F i (evalWithAnswerFn hash (q i))) :
    Pr[E | withRandomOracle p] ≤
      ∑ i : ι, Pr[F i | withRandomOracle (q i)] := by
  classical
  let S := familyFootprint p q
  have hS : S.Finite := familyFootprint_finite p q
  let sample := sampleRestrictedTable S hS
  let hash : RestrictedTable S → Hash := fun g => QueryImpl.ofFn (extendTable S g)
  calc
    Pr[E | withRandomOracle p] =
        Pr[fun g => E (evalWithAnswerFn (hash g) p) | sample] := by
          exact probEvent_eagerFootprint_on S hS p (familyFootprint_covers_all p q) E
    _ ≤ Pr[fun g => ∃ i ∈ (Finset.univ : Finset ι),
          F i (evalWithAnswerFn (hash g) (q i)) | sample] := by
          apply probEvent_mono
          intro g _ hg
          obtain ⟨i, hi⟩ := hpointwise (hash g) hg
          exact ⟨i, Finset.mem_univ i, hi⟩
    _ ≤ ∑ i : ι, Pr[fun g => F i (evalWithAnswerFn (hash g) (q i)) | sample] :=
          probEvent_exists_finset_le_sum Finset.univ sample _
    _ = ∑ i : ι, Pr[F i | withRandomOracle (q i)] := by
          apply Finset.sum_congr rfl
          intro i _
          exact (probEvent_eagerFootprint_on S hS (q i)
            (familyFootprint_covers_member p q i) (F i)).symm


theorem sharedOracle_event_mono {α β : Type}
    (p : OracleComp HashSpec α) (q : OracleComp HashSpec β)
    (E : α → Prop) (F : β → Prop)
    (hpointwise : ∀ hash : Hash,
      E (evalWithAnswerFn hash p) → F (evalWithAnswerFn hash q)) :
    Pr[E | withRandomOracle p] ≤
      Pr[F | withRandomOracle q] := by
  have h := sharedOracle_union_bound (ι := PUnit) p (fun _ => q)
    E (fun _ => F) (by
      intro hash he
      exact ⟨PUnit.unit, hpointwise hash he⟩)
  simpa using h
end SigGolfCandidate.AbstractQueryFootprint

/-- info: 'SigGolfCandidate.AbstractQueryFootprint.sharedOracle_event_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.AbstractQueryFootprint.sharedOracle_event_mono

namespace SigGolfCandidate.AbstractQueryFootprint
open OracleComp OracleSpec SigGolfCandidate.QueryDecoder

noncomputable def liftBeta {α : Type} (p : OracleComp SigGolf.HashSpec α) :
    OracleComp HashSpec α :=
  simulateQ (fun query : SigGolf.Query =>
    liftM (HashSpec.query (QueryDecoder.decode query))) p

theorem liftBeta_eval {α : Type} (p : OracleComp SigGolf.HashSpec α)
    (hash : QueryImpl HashSpec Id) :
    evalWithAnswerFn hash (liftBeta p) =
      evalWithAnswerFn
        (QueryImpl.ofFn (fun query : SigGolf.Query => hash (QueryDecoder.decode query))) p := by
  change simulateQ hash (simulateQ (fun query : SigGolf.Query =>
    liftM (HashSpec.query (QueryDecoder.decode query))) p) = _
  rw [← QueryImpl.simulateQ_compose]
  congr 1

theorem liftBeta_distribution {α : Type} (p : OracleComp SigGolf.HashSpec α) :
    SigGolf.withRandomOracle p = withRandomOracle (liftBeta p) := by
  change (simulateQ (randomOracle : QueryImpl SigGolf.HashSpec
      (StateT (QueryCache SigGolf.HashSpec) ProbComp)) p).run' ∅ =
    (simulateQ (randomOracle : QueryImpl HashSpec
      (StateT (QueryCache HashSpec) ProbComp))
      (simulateQ (fun query : SigGolf.Query =>
        liftM (HashSpec.query (QueryDecoder.decode query))) p)).run' ∅
  rw [← QueryImpl.simulateQ_compose]
  have hcomp :
      (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)) ∘ₛ
        (fun query : SigGolf.Query =>
          liftM (HashSpec.query (QueryDecoder.decode query))) =
        QueryDecoder.pulledRandomOracle := by
    funext query
    change simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query (QueryDecoder.decode query))) = _
    exact simulateQ_spec_query _ _
  rw [hcomp]
  rw [StateT.run'_eq, StateT.run'_eq]
  calc
    Prod.fst <$> (simulateQ (randomOracle : QueryImpl SigGolf.HashSpec
      (StateT (QueryCache SigGolf.HashSpec) ProbComp)) p).run ∅ =
      Prod.fst <$> ((fun result => (result.1,
        QueryDecoder.projectCache result.2)) <$>
        (simulateQ QueryDecoder.pulledRandomOracle p).run ∅) := by
          exact congrArg (Functor.map Prod.fst)
            (QueryDecoder.simulate_pulled_empty p).symm
    _ = Prod.fst <$> (simulateQ QueryDecoder.pulledRandomOracle p).run ∅ := by
      rw [Functor.map_map]

end SigGolfCandidate.AbstractQueryFootprint

/-- info: 'SigGolfCandidate.AbstractQueryFootprint.liftBeta_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.AbstractQueryFootprint.liftBeta_distribution

namespace SigGolfCandidate.AbstractQueryFootprint
open OracleComp OracleSpec

theorem implementation_failure_le_abstract
    (implementation : OracleComp SigGolf.HashSpec SigGolf.HonestResult)
    (abstract : OracleComp HashSpec Bool)
    (hsem : ∀ hash : QueryImpl HashSpec Id,
      (evalWithAnswerFn hash (liftBeta implementation)).success = false →
        evalWithAnswerFn hash abstract = false) :
    Pr[fun r => r.success = false | SigGolf.withRandomOracle implementation] ≤
      Pr[= false | withRandomOracle abstract] := by
  rw [liftBeta_distribution]
  simpa only [probEvent_eq_eq_probOutput] using
    (sharedOracle_event_mono (liftBeta implementation) abstract
      (fun r => r.success = false) (fun b => b = false) hsem)

end SigGolfCandidate.AbstractQueryFootprint

/-- info: 'SigGolfCandidate.AbstractQueryFootprint.implementation_failure_le_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.AbstractQueryFootprint.implementation_failure_le_abstract

namespace SigGolfCandidate.AbstractQueryFootprint
open OracleComp OracleSpec

theorem complete_of_abstract_failure_sum
    (submission : SigGolf.Submission)
    (abstractHonest : SigGolf.SecretKey → SigGolf.Message → OracleComp HashSpec Bool)
    (hsem : ∀ (hash : QueryImpl HashSpec Id)
      (secretKey : SigGolf.SecretKey) (message : SigGolf.Message),
      (evalWithAnswerFn hash (liftBeta (submission.honest secretKey message))).success = false →
        evalWithAnswerFn hash (abstractHonest secretKey message) = false)
    (hbound : ∀ secretKey : SigGolf.SecretKey,
      ∑ message : SigGolf.Message,
        Pr[= false | withRandomOracle (abstractHonest secretKey message)] ≤ SigGolf.FAILURE) :
    submission.Complete := by
  apply SigGolfCandidate.SphincsCompletenessUnion.QueryFootprint.submission_complete_of_failure_sum
  intro secretKey
  calc
    ∑ message : SigGolf.Message,
      Pr[fun result => result.success = false |
        SigGolf.withRandomOracle (submission.honest secretKey message)] ≤
      ∑ message : SigGolf.Message,
        Pr[= false | withRandomOracle (abstractHonest secretKey message)] := by
          apply Finset.sum_le_sum
          intro message _
          exact implementation_failure_le_abstract
            (submission.honest secretKey message)
            (abstractHonest secretKey message) (hsem · secretKey message)
    _ ≤ SigGolf.FAILURE := hbound secretKey

end SigGolfCandidate.AbstractQueryFootprint

/-- info: 'SigGolfCandidate.AbstractQueryFootprint.complete_of_abstract_failure_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.AbstractQueryFootprint.complete_of_abstract_failure_sum

namespace SigGolfCandidate
open OracleComp OracleSpec ENNReal
/-- The abstract failure event is the same under the shared-oracle sampler. -/
theorem abstract_honest_prob_eq (seed : SigGolf.SecretKey) (message : SigGolf.Message) :
      Pr[= false | AbstractQueryFootprint.withRandomOracle
        (SphincsSecurity.Completeness.honest seed message)] =
      Pr[fun r => r.1 = false |
        (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
          (SphincsSecurity.Completeness.honest seed message)).run ∅] := by
  rw [← probEvent_eq_eq_probOutput]
  unfold AbstractQueryFootprint.withRandomOracle
  rw [StateT.run'_eq, probEvent_map]
  rfl
/-- The abstract all-message failure bound matches the beta constant. -/
theorem abstract_honest_failure_sum (seed : SigGolf.SecretKey) :
    ∑ message : SigGolf.Message,
      Pr[= false | AbstractQueryFootprint.withRandomOracle
        (SphincsSecurity.Completeness.honest seed message)] ≤ SigGolf.FAILURE := by
  have h := SphincsSecurity.Completeness.complete_each_seed seed
  rw [tsum_fintype] at h
  have h2 :
      (∑ message : SigGolf.Message,
        Pr[= false | AbstractQueryFootprint.withRandomOracle
          (SphincsSecurity.Completeness.honest seed message)]) ≤
        ((↑(2 ^ 256 : Nat) : ENNReal))⁻¹ := by
    calc
      _ = ∑ message : SigGolf.Message,
          Pr[fun r => r.1 = false |
            (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec _)
              (SphincsSecurity.Completeness.honest seed message)).run ∅] := by
            apply Finset.sum_congr rfl
            intro message _
            exact abstract_honest_prob_eq seed message
      _ ≤ _ := by exact h
  exact h2.trans (by norm_num [SigGolf.FAILURE, Nat.cast_pow])
end SigGolfCandidate

namespace SigGolfCandidate
open OracleComp OracleSpec

/-- Completeness reduces to a pathwise failure implication for the concrete programs. -/
theorem complete_of_honest_refinement (submission : SigGolf.Submission)
    (hsem : ∀ (hash : QueryImpl AbstractQueryFootprint.HashSpec Id)
      (secretKey : SigGolf.SecretKey) (message : SigGolf.Message),
      (evalWithAnswerFn hash
        (AbstractQueryFootprint.liftBeta (submission.honest secretKey message))).success = false →
        evalWithAnswerFn hash (SphincsSecurity.Completeness.honest secretKey message) = false) :
    submission.Complete :=
  AbstractQueryFootprint.complete_of_abstract_failure_sum
    submission SphincsSecurity.Completeness.honest hsem
    abstract_honest_failure_sum
end SigGolfCandidate

/-- info: 'SigGolfCandidate.complete_of_honest_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.complete_of_honest_refinement
