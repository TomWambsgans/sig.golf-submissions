import SigGolfCandidate.SphincsBridge

/-! Split the organizer's bit-string oracle into byte-aligned scheme queries
and a disjoint non-aligned part. -/

namespace SigGolfCandidate.SphincsAlignedQuery
open SigGolf SphincsSecurity
def alignedInput (query : SigGolf.Query) (aligned : query.1 % 8 = 0) : HashInput :=
  SphincsSecurity.bytesLE (query.1 / 8)
    (cast (congrArg BitVec (by omega : query.1 = 8 * (query.1 / 8))) query.2)

theorem toQuery_alignedInput (query : SigGolf.Query)
    (aligned : query.1 % 8 = 0) :
    SphincsBridge.toQuery (alignedInput query aligned) = query := by
  cases query with
  | mk n bits =>
      change n % 8 = 0 at aligned
      have hn : n = 8 * (n / 8) := by omega
      simp only [alignedInput, SphincsBridge.toQuery_bytesLE]
      apply Sigma.ext hn.symm
      exact cast_heq (congrArg BitVec hn) bits

theorem aligned_toQuery (input : HashInput) : (SphincsBridge.toQuery input).1 % 8 = 0 := by
  simp [SphincsBridge.toQuery, Hypertree.Reference.packed]

theorem alignedInput_toQuery (input : HashInput) :
    alignedInput (SphincsBridge.toQuery input) (aligned_toQuery input) = input := by
  apply SphincsBridge.toQuery_injective
  exact toQuery_alignedInput _ _

abbrev NonalignedQuery := {q : SigGolf.Query // q.1 % 8 ≠ 0}
abbrev NonalignedSpec : OracleSpec NonalignedQuery := NonalignedQuery →ₒ BitVec 256
abbrev SplitCache := OracleSpec.QueryCache SphincsSecurity.HashSpec ×
  OracleSpec.QueryCache NonalignedSpec

def splitQuery (query : SigGolf.Query) : HashInput ⊕ NonalignedQuery :=
  if aligned : query.1 % 8 = 0 then
    .inl (alignedInput query aligned)
  else
    .inr ⟨query, aligned⟩

def joinQuery : HashInput ⊕ NonalignedQuery → SigGolf.Query
  | .inl input => SphincsBridge.toQuery input
  | .inr query => query.1

theorem join_split (query : SigGolf.Query) : joinQuery (splitQuery query) = query := by
  simp only [splitQuery]
  split_ifs with h
  · exact toQuery_alignedInput query h
  · rfl

theorem split_join (query : HashInput ⊕ NonalignedQuery) : splitQuery (joinQuery query) = query := by
  cases query with
  | inl input => simp [splitQuery, joinQuery, aligned_toQuery, alignedInput_toQuery]
  | inr query =>
      have h := query.2
      simp [splitQuery, joinQuery, h]

theorem split_injective : Function.Injective splitQuery := by
  intro first second h
  have := congrArg joinQuery h
  simpa only [join_split] using this

def encodeCache (cache : SplitCache) : OracleSpec.QueryCache SigGolf.HashSpec :=
  fun query => match splitQuery query with
    | .inl input => cache.1 input
    | .inr input => cache.2 input

def decodeCache (cache : OracleSpec.QueryCache SigGolf.HashSpec) : SplitCache :=
  (fun input => cache (SphincsBridge.toQuery input), fun input => cache input.1)

theorem encode_decode (cache : OracleSpec.QueryCache SigGolf.HashSpec) :
    encodeCache (decodeCache cache) = cache := by
  funext query
  change (match splitQuery query with
    | .inl input => cache (SphincsBridge.toQuery input)
    | .inr input => cache input.1) = cache query
  cases h : splitQuery query with
  | inl input =>
      have hj : SphincsBridge.toQuery input = query := by
        simpa [joinQuery, h] using join_split query
      simpa only [h] using (by cases hj; rfl : cache (SphincsBridge.toQuery input) = cache query)
  | inr input =>
      have hj : input.1 = query := by
        simpa [joinQuery, h] using join_split query
      simpa only [h] using (by cases hj; rfl : cache input.1 = cache query)

theorem decode_encode (cache : SplitCache) : decodeCache (encodeCache cache) = cache := by
  apply Prod.ext
  · funext input
    change (match splitQuery (SphincsBridge.toQuery input) with
      | .inl value => cache.1 value
      | .inr value => cache.2 value) = cache.1 input
    rw [show splitQuery (SphincsBridge.toQuery input) = .inl input from
      split_join (.inl input)]
  · funext input
    change (match splitQuery input.1 with
      | .inl value => cache.1 value
      | .inr value => cache.2 value) = cache.2 input
    rw [show splitQuery input.1 = .inr input from split_join (.inr input)]

theorem encode_update_inl (cache : SplitCache) (query : SigGolf.Query)
    (input : HashInput) (u : BitVec 256) (h : splitQuery query = .inl input) :
    encodeCache (cache.1.cacheQuery input u, cache.2) =
      (encodeCache cache).cacheQuery query u := by
  funext query'
  cases h' : splitQuery query' with
  | inl input' =>
      by_cases heq : input' = input
      · have hq : query' = query := split_injective (by simp [h', h, heq])
        subst query'
        simp only [encodeCache, h]
        rw [OracleSpec.QueryCache.cacheQuery_self]
        exact OracleSpec.QueryCache.cacheQuery_self cache.1 input u
      · have hq : query' ≠ query := by
          intro same
          subst query'
          have hs : input' = input := Sum.inl.inj (h'.symm.trans h)
          exact heq hs
        simp only [encodeCache, h', OracleSpec.QueryCache.cacheQuery_of_ne cache.1 u heq,
          OracleSpec.QueryCache.cacheQuery_of_ne (encodeCache cache) u hq]
        rfl
  | inr input' =>
      have hq : query' ≠ query := by
        intro same
        subst query'
        simp [h] at h'
      simp [encodeCache, h', OracleSpec.QueryCache.cacheQuery_of_ne, hq]

theorem encode_update_inr (cache : SplitCache) (query : SigGolf.Query)
    (input : NonalignedQuery) (u : BitVec 256) (h : splitQuery query = .inr input) :
    encodeCache (cache.1, cache.2.cacheQuery input u) =
      (encodeCache cache).cacheQuery query u := by
  funext query'
  cases h' : splitQuery query' with
  | inl input' =>
      have hq : query' ≠ query := by
        intro same
        subst query'
        simp [h] at h'
      simp [encodeCache, h', OracleSpec.QueryCache.cacheQuery_of_ne, hq]
      rfl
  | inr input' =>
      by_cases heq : input' = input
      · have hq : query' = query := split_injective (by simp [h', h, heq])
        subst query'
        simp only [encodeCache, h]
        rw [OracleSpec.QueryCache.cacheQuery_self]
        exact (OracleSpec.QueryCache.cacheQuery_self (encodeCache cache) query u).symm
      · have hq : query' ≠ query := by
          intro same
          subst query'
          have hs : input' = input := Sum.inr.inj (h'.symm.trans h)
          exact heq hs
        simp only [encodeCache, h', OracleSpec.QueryCache.cacheQuery_of_ne cache.2 u heq,
          OracleSpec.QueryCache.cacheQuery_of_ne (encodeCache cache) u hq]

theorem decode_update_inl (cache : SplitCache) (query : SigGolf.Query)
    (input : HashInput) (u : BitVec 256) (h : splitQuery query = .inl input) :
    decodeCache ((encodeCache cache).cacheQuery query u) =
      (cache.1.cacheQuery input u, cache.2) := by
  rw [← encode_update_inl cache query input u h, decode_encode]

theorem decode_update_inr (cache : SplitCache) (query : SigGolf.Query)
    (input : NonalignedQuery) (u : BitVec 256) (h : splitQuery query = .inr input) :
    decodeCache ((encodeCache cache).cacheQuery query u) =
      (cache.1, cache.2.cacheQuery input u) := by
  rw [← encode_update_inr cache query input u h, decode_encode]

theorem encode_empty : encodeCache (∅, ∅) = (∅ : OracleSpec.QueryCache SigGolf.HashSpec) := by
  funext query
  change (match splitQuery query with | .inl _ => none | .inr _ => none) = none
  cases splitQuery query <;> rfl

/-- Transport the organizer's lazy oracle through the exact cache decomposition. -/
noncomputable def splitRandomOracle :
    QueryImpl SigGolf.HashSpec (StateT SplitCache ProbComp) :=
  fun query cache =>
    (fun result => (result.1, decodeCache result.2)) <$> 
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run (encodeCache cache)

/-- A byte-aligned query touches only the inherited byte-string table. -/
theorem splitRandomOracle_aligned (cache : SplitCache) (query : SigGolf.Query)
    (input : HashInput) (h : splitQuery query = .inl input) :
    (splitRandomOracle query).run cache =
      match cache.1 input with
      | some u => pure (u, cache)
      | none => ($ᵗ BitVec 256) >>= fun u =>
          pure (u, (cache.1.cacheQuery input u, cache.2)) := by
  change (fun result => (result.1, decodeCache result.2)) <$>
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run (encodeCache cache) = _
  rw [randomOracle.run_eq]
  have hlook : encodeCache cache query = cache.1 input := by
    simp only [encodeCache, h]
    rfl
  rw [hlook]
  cases hc : cache.1 input with
  | some u => simp [decode_encode]
  | none =>
      simp only [map_bind, map_pure]
      exact bind_congr fun u => by simp [decode_update_inl cache query input u h]

/-- A non-byte-aligned query touches only its separate private table. -/
theorem splitRandomOracle_nonaligned (cache : SplitCache) (query : SigGolf.Query)
    (input : NonalignedQuery) (h : splitQuery query = .inr input) :
    (splitRandomOracle query).run cache =
      match cache.2 input with
      | some u => pure (u, cache)
      | none => ($ᵗ BitVec 256) >>= fun u =>
          pure (u, (cache.1, cache.2.cacheQuery input u)) := by
  change (fun result => (result.1, decodeCache result.2)) <$>
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run (encodeCache cache) = _
  rw [randomOracle.run_eq]
  have hlook : encodeCache cache query = cache.2 input := by simp [encodeCache, h]
  rw [hlook]
  cases hc : cache.2 input with
  | some u => simp [decode_encode]
  | none =>
      simp only [map_bind, map_pure]
      exact bind_congr fun u => by simp [decode_update_inr cache query input u h]

/-- The aligned component is precisely the inherited byte-string lazy random oracle. -/
theorem splitRandomOracle_byte (cache : SplitCache) (input : HashInput) :
    (splitRandomOracle (SphincsBridge.toQuery input)).run cache =
    (fun result => (result.1, (result.2, cache.2))) <$>
      (OracleSpec.randomOracle (spec := SphincsSecurity.HashSpec) input).run cache.1 := by
  have h : splitQuery (SphincsBridge.toQuery input) = .inl input :=
    split_join (.inl input)
  rw [splitRandomOracle_aligned cache _ input h]
  rw [randomOracle.run_eq]
  cases cache.1 input <;> simp [map_pure] <;> rfl

/-- The nonaligned component is a separate lazy random oracle and never changes the byte table. -/
theorem splitRandomOracle_other (cache : SplitCache) (input : NonalignedQuery) :
    (splitRandomOracle input.1).run cache =
    (fun result => (result.1, (cache.1, result.2))) <$>
      (OracleSpec.randomOracle (spec := NonalignedSpec) input).run cache.2 := by
  have h : splitQuery input.1 = .inr input := split_join (.inr input)
  rw [splitRandomOracle_nonaligned cache _ input h]
  rw [randomOracle.run_eq]
  cases cache.2 input <;> simp [map_pure]

/-- One query has exactly the same joint law of answer and resulting cache. -/
theorem splitRandomOracle_run (query : SigGolf.Query) (cache : SplitCache) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (splitRandomOracle query).run cache =
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run (encodeCache cache) := by
  change (fun result => (result.1, encodeCache result.2)) <$>
    ((fun result => (result.1, decodeCache result.2)) <$>
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run (encodeCache cache)) = _
  rw [Functor.map_map]
  simp [encode_decode]

theorem splitRandomOracle_run_empty (query : SigGolf.Query) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (splitRandomOracle query).run (∅, ∅) =
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run ∅ := by
  simpa only [encode_empty] using splitRandomOracle_run query (∅, ∅)

/-- The oracle-cache decomposition preserves the full joint distribution of every finite
hash-query computation, including adaptively selected and repeated queries. -/
theorem simulate_split (α : Type) (program : OracleComp SigGolf.HashSpec α)
    (cache : SplitCache) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (simulateQ splitRandomOracle program).run cache =
    (simulateQ (OracleSpec.randomOracle (spec := SigGolf.HashSpec)) program).run
      (encodeCache cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query continuation ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [map_bind]
      rw [← splitRandomOracle_run query cache, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2

def splitCoinOracle : QueryImpl unifSpec (StateT SplitCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT SplitCache ProbComp)

noncomputable def splitWorldOracle :
    QueryImpl SigGolf.World (StateT SplitCache ProbComp) :=
  splitCoinOracle + splitRandomOracle

theorem splitCoinOracle_run (query : unifSpec.Domain) (cache : SplitCache) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (splitCoinOracle query).run cache =
    (unifFwdImpl SigGolf.HashSpec query).run (encodeCache cache) := by
  rfl

theorem splitWorldOracle_run (query : SigGolf.World.Domain) (cache : SplitCache) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (splitWorldOracle query).run cache =
    ((unifFwdImpl SigGolf.HashSpec +
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec))) query).run
      (encodeCache cache) := by
  cases query with
  | inl coin => exact splitCoinOracle_run coin cache
  | inr hash => exact splitRandomOracle_run hash cache

/-- The same split preserves computations that combine private uniform coins with arbitrary
organizer hash queries. This is the form needed for the security experiment. -/
theorem simulate_world_split (α : Type) (program : OracleComp SigGolf.World α)
    (cache : SplitCache) :
    (fun result => (result.1, encodeCache result.2)) <$>
      (simulateQ splitWorldOracle program).run cache =
    (simulateQ (unifFwdImpl SigGolf.HashSpec +
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec))) program).run
      (encodeCache cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query continuation ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [map_bind]
      rw [← splitWorldOracle_run query cache, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2

noncomputable def withSplitRandomness {α : Type} (program : OracleComp SigGolf.World α) :
    ProbComp α :=
  (simulateQ splitWorldOracle program).run' (∅, ∅)

/-- Organizer sampling is unchanged when its bit-string random oracle is realized by the
independent byte-aligned and nonaligned lazy tables. -/
theorem withSplitRandomness_eq {α : Type} (program : OracleComp SigGolf.World α) :
    withSplitRandomness program = SigGolf.withRandomness program := by
  have h := simulate_world_split α program (∅, ∅)
  have h' := congrArg (Functor.map Prod.fst) h
  simpa only [withSplitRandomness, SigGolf.withRandomness, StateT.run'_eq,
    Functor.map_map, encode_empty] using h'

/-- A scheme computation can use the inherited byte-string RO in the first component
while the nonaligned organizer table remains untouched. -/
noncomputable def splitByteWorldOracle :
    QueryImpl SphincsSecurity.OracleWorld (StateT SplitCache ProbComp) :=
  splitCoinOracle + (fun input => splitRandomOracle (SphincsBridge.toQuery input))

theorem splitByteWorldOracle_run (query : SphincsSecurity.OracleWorld.Domain)
    (byteCache : OracleSpec.QueryCache SphincsSecurity.HashSpec)
    (otherCache : OracleSpec.QueryCache NonalignedSpec) :
    (splitByteWorldOracle query).run (byteCache, otherCache) =
    (fun result => (result.1, (result.2, otherCache))) <$>
      ((unifFwdImpl SphincsSecurity.HashSpec +
        (OracleSpec.randomOracle (spec := SphincsSecurity.HashSpec))) query).run
        byteCache := by
  cases query with
  | inl coin => rfl
  | inr input => exact splitRandomOracle_byte (byteCache, otherCache) input

theorem simulate_byte_world (α : Type)
    (program : OracleComp SphincsSecurity.OracleWorld α)
    (byteCache : OracleSpec.QueryCache SphincsSecurity.HashSpec)
    (otherCache : OracleSpec.QueryCache NonalignedSpec) :
    (simulateQ splitByteWorldOracle program).run (byteCache, otherCache) =
    (fun result => (result.1, (result.2, otherCache))) <$>
      (simulateQ (unifFwdImpl SphincsSecurity.HashSpec +
        (OracleSpec.randomOracle (spec := SphincsSecurity.HashSpec))) program).run
        byteCache := by
  induction program using OracleComp.inductionOn generalizing byteCache with
  | pure value => simp [simulateQ_pure]
  | query_bind query continuation ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [splitByteWorldOracle_run query byteCache otherCache]
      rw [bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.simulate_byte_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.simulate_byte_world

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.splitRandomOracle_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.splitRandomOracle_byte

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.splitRandomOracle_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.splitRandomOracle_other

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.simulate_world_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.simulate_world_split

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.withSplitRandomness_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.withSplitRandomness_eq

end SigGolfCandidate.SphincsAlignedQuery

/-- info: 'SigGolfCandidate.SphincsAlignedQuery.toQuery_alignedInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsAlignedQuery.toQuery_alignedInput
