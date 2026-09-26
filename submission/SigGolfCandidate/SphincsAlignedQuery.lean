import SigGolf.Oracle
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.RandomizedStatement
import SigGolfCandidate.SphincsBeta64Images
import SigGolf.Security

namespace SigGolfCandidate.QueryDecoder
open SigGolf SphincsSecurity
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def queryBytes (query : SigGolf.Query) : SphincsSecurity.HashInput :=
  SphincsSecurity.bytesLE (64 * (query.1 + 1)) query.2

theorem queryBytes_length (query : SigGolf.Query) :
    (queryBytes query).length = 64 * (query.1 + 1) :=
  SphincsSecurity.bytesLE_length _ _

theorem queryBytes_injective : Function.Injective queryBytes := by
  intro x y h
  have hl := congrArg List.length h
  rw [queryBytes_length, queryBytes_length] at hl
  have hn : x.1 = y.1 := by omega
  cases x with
  | mk nx bx =>
    cases y with
    | mk ny bitsY =>
      change nx = ny at hn
      subst ny
      exact congrArg (Sigma.mk nx) (SphincsSecurity.bytesLE_injective h)

def sourceLength (tag : UInt8) : Nat :=
  if tag == 0 || tag == 5 || tag == 8 || tag == 14 then 72
  else if tag == 1 || tag == 9 || tag == 13 then 60
  else if tag == 3 || tag == 10 then 80
  else if tag == 7 then 104
  else if tag == 12 then 112
  else if tag == 11 then 520
  else if tag == 2 then 1080
  else if tag == 15 then 131124
  else if tag == 4 then 64
  else 0

def blockLength (n : Nat) : Nat := 64 * ((n + 63) / 64)

def recognized (bytes : SphincsSecurity.HashInput) : Prop :=
  bytes[0]? = some 1 ∧
  let n := sourceLength (bytes[1]?.getD 255)
  2 ≤ n ∧ n ≤ bytes.length ∧ bytes.length = blockLength n ∧
    bytes.drop n = List.replicate (blockLength n - n) 0

instance (bytes : SphincsSecurity.HashInput) : Decidable (recognized bytes) := by
  unfold recognized
  infer_instance

def decode (query : SigGolf.Query) : SphincsSecurity.HashInput :=
  let bytes := queryBytes query
  if recognized bytes then bytes.take (sourceLength (bytes[1]?.getD 255))
  else [0, 255] ++ bytes

private theorem recognized_take_length (bytes : SphincsSecurity.HashInput)
    (h : recognized bytes) :
    (bytes.take (sourceLength (bytes[1]?.getD 255))).length =
      sourceLength (bytes[1]?.getD 255) := by
  have hn : sourceLength (bytes[1]?.getD 255) ≤ bytes.length := h.2.2.1
  simp [List.length_take, hn]

private theorem recognized_reconstruct (bytes : SphincsSecurity.HashInput)
    (h : recognized bytes) :
    bytes = bytes.take (sourceLength (bytes[1]?.getD 255)) ++
      List.replicate (blockLength (sourceLength (bytes[1]?.getD 255)) -
        sourceLength (bytes[1]?.getD 255)) 0 := by
  have htail := h.2.2.2.2
  rw [← htail]
  exact (List.take_append_drop _ _).symm

private theorem recognized_take_head (bytes : SphincsSecurity.HashInput)
    (h : recognized bytes) :
    (bytes.take (sourceLength (bytes[1]?.getD 255)))[0]? = some 1 := by
  have hn' : 2 ≤ sourceLength (bytes[1]?.getD 255) := h.2.1
  have hn : 0 < sourceLength (bytes[1]?.getD 255) := by omega
  simpa [List.getElem?_take, hn] using h.1

/-- Queries outside the tagged padded image are disjoint from honest scheme domains. -/
abbrev NonalignedQuery := {query : SigGolf.Query // ¬ recognized (queryBytes query)}

def alignedInput (query : SigGolf.Query) (_h : recognized (queryBytes query)) :
    SphincsSecurity.HashInput := decode query

theorem recognized_decode_head (query : SigGolf.Query)
    (h : recognized (queryBytes query)) : (decode query)[0]? = some 1 := by
  simp only [decode, if_pos h]
  exact recognized_take_head (queryBytes query) h

theorem foreign_decode_head (query : SigGolf.Query)
    (h : ¬ recognized (queryBytes query)) : (decode query)[0]? = some 0 := by
  simp [decode, h]

theorem recognized_foreign_disjoint (good bad : SigGolf.Query)
    (hgood : recognized (queryBytes good))
    (hbad : ¬ recognized (queryBytes bad)) : decode good ≠ decode bad := by
  intro heq
  have := congrArg (fun bytes : SphincsSecurity.HashInput => bytes[0]?) heq
  rw [recognized_decode_head good hgood, foreign_decode_head bad hbad] at this
  cases this

theorem decode_injective : Function.Injective decode := by
  intro first second h
  let a := queryBytes first
  let b := queryBytes second
  by_cases ha : recognized a
  · by_cases hb : recognized b
    · have htake : a.take (sourceLength (a[1]?.getD 255)) =
          b.take (sourceLength (b[1]?.getD 255)) := by
        simpa [decode, a, b, ha, hb] using h
      have hlen : sourceLength (a[1]?.getD 255) = sourceLength (b[1]?.getD 255) := by
        have := congrArg List.length htake
        simpa [recognized_take_length a ha, recognized_take_length b hb] using this
      have hbytes : a = b := by
        calc
          a = a.take (sourceLength (a[1]?.getD 255)) ++
              List.replicate (blockLength (sourceLength (a[1]?.getD 255)) -
                sourceLength (a[1]?.getD 255)) 0 := recognized_reconstruct a ha
          _ = b.take (sourceLength (b[1]?.getD 255)) ++
              List.replicate (blockLength (sourceLength (b[1]?.getD 255)) -
                sourceLength (b[1]?.getD 255)) 0 := by rw [htake, hlen]
          _ = b := (recognized_reconstruct b hb).symm
      exact queryBytes_injective hbytes
    · have hhead := recognized_take_head a ha
      have hh := congrArg (fun bytes : List UInt8 => bytes[0]?) h
      simp [decode, a, b, ha, hb, hhead] at hh
  · by_cases hb : recognized b
    · have hhead := recognized_take_head b hb
      have hh := congrArg (fun bytes : List UInt8 => bytes[0]?) h
      simp [decode, a, b, ha, hb, hhead] at hh
    · have hbytes : a = b := by
        have : [0, 255] ++ a = [0, 255] ++ b := by
          simpa [decode, a, b, ha, hb] using h
        injection this with _ htail
        injection htail with _ hbytes
      exact queryBytes_injective hbytes

theorem decode_padded (query : SigGolf.Query) (input : SphincsSecurity.HashInput)
    (n : Nat) (hsize : input.length = n) (hminimum : 2 ≤ n)
    (hfirst : input[0]? = some 1)
    (htag : sourceLength (input[1]?.getD 255) = n)
    (hbytes : queryBytes query = input ++ List.replicate (blockLength n - n) 0)
    (hblock : (queryBytes query).length = blockLength n) :
    decode query = input := by
  let bytes := queryBytes query
  have hprefix : bytes.take n = input := by
    change (queryBytes query).take n = input
    rw [hbytes]
    simp [hsize]
  have htagBytes : bytes[1]? = input[1]? := by
    have h := congrArg (fun xs : List UInt8 => xs[1]?) hprefix
    simpa [List.getElem?_take, show 1 < n by omega] using h
  have hfirstBytes : bytes[0]? = some 1 := by
    have h := congrArg (fun xs : List UInt8 => xs[0]?) hprefix
    simpa [List.getElem?_take, show 0 < n by omega, hfirst] using h
  have hn : sourceLength (bytes[1]?.getD 255) = n := by rw [htagBytes, htag]
  have hrecognized : recognized bytes := by
    refine ⟨hfirstBytes, ?_⟩
    simp only [hn]
    have hle : n ≤ bytes.length := by
      change n ≤ (queryBytes query).length
      rw [hbytes]
      simp [hsize]
    have hlength : bytes.length = blockLength n := by simpa [bytes] using hblock
    have htail : bytes.drop n = List.replicate (blockLength n - n) 0 := by
      change (queryBytes query).drop n = _
      rw [hbytes]
      simp [hsize]
    exact ⟨hminimum, hle, hlength, htail⟩
  change (if recognized bytes then bytes.take (sourceLength (bytes[1]?.getD 255))
    else [0, 255] ++ bytes) = input
  rw [if_pos hrecognized, hn, hprefix]

theorem finite_oracle_pullback (queries : Finset SigGolf.Query) :
    𝒮[do
      let table ← ($ᵗ ((queries.image decode) → BitVec 256) : ProbComp _)
      pure (fun query : queries => table ⟨decode query.1,
        Finset.mem_image.mpr ⟨query.1, query.2, rfl⟩⟩)] =
    𝒮[($ᵗ (queries → BitVec 256) : ProbComp _)] := by
  classical
  let e : queries → (queries.image decode) := fun query =>
    ⟨decode query.1, Finset.mem_image.mpr ⟨query.1, query.2, rfl⟩⟩
  have he : Function.Injective e := by
    intro left right h
    apply Subtype.ext
    exact decode_injective (congrArg Subtype.val h)
  exact evalSPMF_uniformSample_map_comp_injective he

def projectCache (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec) :
    OracleSpec.QueryCache SigGolf.HashSpec :=
  fun query => cache (decode query)

theorem projectCache_empty :
    projectCache (∅ : OracleSpec.QueryCache SphincsSecurity.HashSpec) =
      (∅ : OracleSpec.QueryCache SigGolf.HashSpec) := by
  funext query
  rfl

theorem projectCache_update (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec)
    (query : SigGolf.Query) (answer : BitVec 256) :
    projectCache (cache.cacheQuery (decode query) answer) =
      (projectCache cache).cacheQuery query answer := by
  funext other
  by_cases h : other = query
  · subst other
    change cache.cacheQuery (decode query) answer (decode query) =
      (projectCache cache).cacheQuery query answer query
    simp [OracleSpec.QueryCache.cacheQuery]
    rfl
  · have hd : decode other ≠ decode query := fun eq => h (decode_injective eq)
    change cache.cacheQuery (decode query) answer (decode other) =
      (projectCache cache).cacheQuery query answer other
    rw [OracleSpec.QueryCache.cacheQuery_of_ne cache answer hd,
      OracleSpec.QueryCache.cacheQuery_of_ne (projectCache cache) answer h]
    rfl

noncomputable def pulledRandomOracle :
    QueryImpl SigGolf.HashSpec (StateT (OracleSpec.QueryCache SphincsSecurity.HashSpec) ProbComp) :=
  fun query => OracleSpec.randomOracle (spec := SphincsSecurity.HashSpec) (decode query)

theorem pulledRandomOracle_step (query : SigGolf.Query)
    (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec) :
    (fun result => (result.1, projectCache result.2)) <$>
      (pulledRandomOracle query).run cache =
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run
      (projectCache cache) := by
  change (fun result => (result.1, projectCache result.2)) <$>
    (OracleSpec.randomOracle (spec := SphincsSecurity.HashSpec) (decode query)).run cache =
    (OracleSpec.randomOracle (spec := SigGolf.HashSpec) query).run
      (projectCache cache)
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have hlook : projectCache cache query = cache (decode query) := rfl
  rw [hlook]
  cases hc : cache (decode query) with
  | some answer => simp; rfl
  | none =>
      simp only [map_bind, map_pure]
      change (fun a : BitVec 256 => (a, projectCache (cache.cacheQuery (decode query) a))) <$>
        ($ᵗ BitVec 256 : ProbComp _) =
        (fun a : BitVec 256 => (a, (projectCache cache).cacheQuery query a)) <$>
          ($ᵗ BitVec 256 : ProbComp _)
      simp only [projectCache_update]

theorem simulate_pulled {α : Type} (program : OracleComp SigGolf.HashSpec α)
    (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec) :
    (fun result => (result.1, projectCache result.2)) <$>
      (simulateQ pulledRandomOracle program).run cache =
    (simulateQ (OracleSpec.randomOracle (spec := SigGolf.HashSpec)) program).run
      (projectCache cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query continuation ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [map_bind]
      rw [← pulledRandomOracle_step query cache, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2

theorem simulate_pulled_empty {α : Type} (program : OracleComp SigGolf.HashSpec α) :
    (fun result => (result.1, projectCache result.2)) <$>
      (simulateQ pulledRandomOracle program).run ∅ =
    (simulateQ (OracleSpec.randomOracle (spec := SigGolf.HashSpec)) program).run ∅ := by
  simpa only [projectCache_empty] using simulate_pulled program ∅

def pulledCoinOracle :
    QueryImpl unifSpec (StateT (OracleSpec.QueryCache SphincsSecurity.HashSpec) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (OracleSpec.QueryCache SphincsSecurity.HashSpec) ProbComp)

noncomputable def pulledWorldOracle :
    QueryImpl SigGolf.World (StateT (OracleSpec.QueryCache SphincsSecurity.HashSpec) ProbComp) :=
  pulledCoinOracle + pulledRandomOracle

theorem pulledWorldOracle_step (query : SigGolf.World.Domain)
    (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec) :
    (fun result => (result.1, projectCache result.2)) <$>
      (pulledWorldOracle query).run cache =
    ((unifFwdImpl SigGolf.HashSpec +
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec))) query).run
      (projectCache cache) := by
  cases query with
  | inl coin => rfl
  | inr hash => exact pulledRandomOracle_step hash cache

theorem simulate_world_pulled {α : Type} (program : OracleComp SigGolf.World α)
    (cache : OracleSpec.QueryCache SphincsSecurity.HashSpec) :
    (fun result => (result.1, projectCache result.2)) <$>
      (simulateQ pulledWorldOracle program).run cache =
    (simulateQ (unifFwdImpl SigGolf.HashSpec +
      (OracleSpec.randomOracle (spec := SigGolf.HashSpec))) program).run
      (projectCache cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure]
  | query_bind query continuation ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [map_bind]
      rw [← pulledWorldOracle_step query cache, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2

theorem simulate_world_pulled_empty {α : Type} (program : OracleComp SigGolf.World α) :
    (simulateQ pulledWorldOracle program).run' ∅ = SigGolf.withRandomness program := by
  have h := congrArg (Functor.map Prod.fst) (simulate_world_pulled program ∅)
  simpa only [SigGolf.withRandomness, StateT.run'_eq, Functor.map_map, projectCache_empty]
    using h

noncomputable def embedWorld : QueryImpl SigGolf.World (OracleComp SphincsSecurity.OracleWorld) :=
  fun | .inl n => liftM (SphincsSecurity.OracleWorld.query (.inl n))
      | .inr query => liftM (SphincsSecurity.OracleWorld.query (.inr (decode query)))

noncomputable def reindex {α : Type} (program : OracleComp SigGolf.World α) :
    OracleComp SphincsSecurity.OracleWorld α := simulateQ embedWorld program

theorem composed_oracle_eq :
    SphincsSecurity.romImpl ∘ₛ embedWorld = pulledWorldOracle := by
  funext query
  cases query with
  | inl n => rfl
  | inr query =>
      change simulateQ SphincsSecurity.romImpl
        (liftM (SphincsSecurity.OracleWorld.query (.inr (decode query)))) = _
      rw [simulateQ_spec_query]
      rfl

theorem reindex_law {α : Type} (program : OracleComp SigGolf.World α) :
    (simulateQ SphincsSecurity.romImpl (reindex program)).run' ∅ =
      SigGolf.withRandomness program := by
  rw [reindex, ← QueryImpl.simulateQ_compose]
  rw [composed_oracle_eq]
  exact simulate_world_pulled_empty program

noncomputable def securityCore (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes) (rounds : Nat) :
    OracleComp SigGolf.World SigGolf.AttackResult := do
  let secretKey ← liftM SigGolf.sampleSecretKey
  let keygen ← liftM (submission.run .keygen secretKey)
  let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
  submission.interact adversary secretKey pk rounds (adversary.initial pk cache)
    { hashCalls := keygen.hashCalls }

theorem securityExperiment_reindexed (submission : SigGolf.Submission)
    (adversary : SigGolf.Adversary submission.sizes) (rounds : Nat) :
    submission.securityExperiment adversary rounds =
      (simulateQ SphincsSecurity.romImpl
        (reindex (securityCore submission adversary rounds))).run' ∅ := by
  change SigGolf.withRandomness (securityCore submission adversary rounds) = _
  exact (reindex_law (securityCore submission adversary rounds)).symm

theorem candidate64_securityExperiment_reindexed
    (adversary : SigGolf.Adversary Candidate64.submission.sizes) (rounds : Nat) :
    Candidate64.submission.securityExperiment adversary rounds =
      (simulateQ SphincsSecurity.romImpl
        (reindex (securityCore Candidate64.submission adversary rounds))).run' ∅ :=
  securityExperiment_reindexed Candidate64.submission adversary rounds




section DomainShapes
set_option backward.isDefEq.respectTransparency false

theorem keygen_sourceLength (p : PublicParameter) (d : KeygenDomain) (seed : MasterSeed) :
    sourceLength ((keygenHashInput p d seed)[1]?.getD 255) =
      (keygenHashInput p d seed).length := by
  cases d <;> simp [keygenHashInput, keygenDomainFields, fieldBytes,
    tweakFields, bytesLE, sourceLength]

theorem keygen_first (p : PublicParameter) (d : KeygenDomain) (seed : MasterSeed) :
    (keygenHashInput p d seed)[0]? = some 1 := by
  cases d <;> simp [keygenHashInput, keygenDomainFields, fieldBytes,
    tweakFields, bytesLE, protocolDomainSep]

theorem randomizer_sourceLength (p : PublicParameter) (seed : MasterSeed)
    (m : SphincsSecurity.Message) (trial : BitVec 32) :
    sourceLength ((randomizerHashInput p seed m trial)[1]?.getD 255) =
      (randomizerHashInput p seed m trial).length := by
  simp [randomizerHashInput, fieldBytes, bytesLE, sourceLength] <;> decide

theorem randomizer_first (p : PublicParameter) (seed : MasterSeed)
    (m : SphincsSecurity.Message) (trial : BitVec 32) :
    (randomizerHashInput p seed m trial)[0]? = some 1 := by
  simp [randomizerHashInput, fieldBytes, bytesLE, protocolDomainSep]


def expectedPayloadLength : HashDomain → Nat
  | .chain .. => 20
  | .leaf .. => 1040
  | .node .. => 40
  | .encoding .. => 24
  | .ftsLeaf .. => 20
  | .ftsNode .. => 40
  | .ftsRoots .. => 480
  | .message => 72

theorem tweakable_sourceLength (p : PublicParameter) (d : HashDomain)
    (payload : HashInput) (h : payload.length = expectedPayloadLength d) :
    sourceLength ((tweakableHashInput p d payload)[1]?.getD 255) =
      (tweakableHashInput p d payload).length := by
  cases d <;> simp [tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, tweakFields, bytesLE, sourceLength, expectedPayloadLength, h] <;> decide

theorem tweakable_first (p : PublicParameter) (d : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput p d payload)[0]? = some 1 := by
  cases d <;> simp [tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, tweakFields, bytesLE, protocolDomainSep]


theorem chain_payload_length (d : Digest) : (bytesLE 20 d).length = 20 := by simp [bytesLE]
theorem leaf_payload_length (endpoints : ChainIndex → Digest) :
    (Concrete.leafPayload endpoints).length = 1040 := by
  have h (xs : List Digest) : (xs.flatMap (bytesLE 20)).length = 20 * xs.length := by
    induction xs with
    | nil => rfl
    | cons value tail ih =>
        simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
        simp [bytesLE]; omega
  unfold Concrete.leafPayload
  rw [h]
  simp [numChains]
theorem node_payload_length (left right : Digest) :
    (Concrete.nodePayload left right).length = 40 := by simp [Concrete.nodePayload, bytesLE]
theorem encoding_payload_length (message : Digest) (counter : Counter) :
    (bytesLE 20 message ++ bytesLE 4 (BitVec.ofNat 32 counter.toNat)).length = 24 := by
  simp [bytesLE]
theorem fts_roots_payload_length (roots : FtsTree → Digest) :
    (Concrete.ftsRootsPayload roots).length = 480 := by
  have h (xs : List Digest) : (xs.flatMap (bytesLE 20)).length = 20 * xs.length := by
    induction xs with
    | nil => rfl
    | cons value tail ih =>
        simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
        simp [bytesLE]; omega
  unfold Concrete.ftsRootsPayload
  rw [h]
  simp [ftsTrees]
theorem message_payload_length (root : Digest) (message : SphincsSecurity.Message)
    (randomness : Randomness) :
    (Concrete.messageDigestPayload root message randomness).length = 72 := by
  simp [Concrete.messageDigestPayload, bytesLE]


end DomainShapes

end SigGolfCandidate.QueryDecoder

/-- info: 'SigGolfCandidate.QueryDecoder.decode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.decode_injective

/-- info: 'SigGolfCandidate.QueryDecoder.decode_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.decode_padded

/-- info: 'SigGolfCandidate.QueryDecoder.finite_oracle_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.finite_oracle_pullback

/-- info: 'SigGolfCandidate.QueryDecoder.pulledRandomOracle_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.pulledRandomOracle_step

/-- info: 'SigGolfCandidate.QueryDecoder.simulate_pulled_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.simulate_pulled_empty

/-- info: 'SigGolfCandidate.QueryDecoder.simulate_world_pulled_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.simulate_world_pulled_empty

/-- info: 'SigGolfCandidate.QueryDecoder.reindex_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.reindex_law

/-- info: 'SigGolfCandidate.QueryDecoder.candidate64_securityExperiment_reindexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.candidate64_securityExperiment_reindexed

/-- info: 'SigGolfCandidate.QueryDecoder.recognized_foreign_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.recognized_foreign_disjoint

/-- info: 'SigGolfCandidate.QueryDecoder.tweakable_sourceLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.QueryDecoder.tweakable_sourceLength
