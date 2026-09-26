import SigGolf.Oracle
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.RandomizedStatement
import SigGolfCandidate.SphincsBeta64Images
import SigGolf.Security
import SigGolfCandidate.SphincsCommitment
import SigGolf.Riscv

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

namespace SigGolfCandidate.BetaQuery
open SigGolf SphincsSecurity RiscvZkvm.Rv64

private def byteValue (data : Nat → UInt8) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (data i).toNat * 2 ^ (8 * i)) 0

private theorem byteValue_succ (data : Nat → UInt8) (n : Nat) :
    byteValue data (n + 1) = byteValue data n + (data n).toNat * 2 ^ (8 * n) := by
  simp [byteValue, List.range_succ, List.foldl_append]

private theorem ofDigits_range (data : Nat → UInt8) (n : Nat) :
    byteValue data n = Nat.ofDigits 256 ((List.range n).map fun i => (data i).toNat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [byteValue_succ, ih, List.range_succ, List.map_append, Nat.ofDigits_append]
      simp only [List.map_singleton, Nat.ofDigits_singleton, List.length_map,
        List.length_range, Nat.pow_mul]
      norm_num
      ac_rfl

private theorem byteValue_digit (data : Nat → UInt8) (n i : Nat) (hi : i < n) :
    (byteValue data n / 256 ^ i) % 256 = (data i).toNat := by
  let ds := (List.range n).map fun j => (data j).toNat
  have bound : ∀ l ∈ ds, l < 256 := by
    intro l hl
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
    exact (data j).toBitVec.isLt
  have hlen : ds.length = n := by simp [ds]
  have get : ds[i]'(by omega) = (data i).toNat := by simp [ds]
  have hdrop : ds.drop i = (data i).toNat :: ds.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by omega)]
    rw [get]
  rw [ofDigits_range, Nat.ofDigits_div_pow_eq_ofDigits_drop i (by decide) ds bound,
    hdrop, Nat.ofDigits_cons]
  simp [Nat.add_mod]

private theorem byteValue_bound (data : Nat → UInt8) (n : Nat) :
    byteValue data n < 2 ^ (8 * n) := by
  rw [ofDigits_range]
  have h := Nat.ofDigits_lt_base_pow_length (b := 256)
    (l := (List.range n).map fun i => (data i).toNat) (by decide)
    (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact (data i).toBitVec.isLt)
  simpa [Nat.pow_mul] using h

private theorem bytesLE_byteValue (data : Nat → UInt8) (n : Nat) :
    SphincsSecurity.bytesLE n (BitVec.ofNat (8 * n) (byteValue data n)) =
      (List.range n).map data := by
  apply List.ext_getElem
  · simp [SphincsSecurity.bytesLE]
  · intro i hi hj
    have hi' : i < n := by simpa [SphincsSecurity.bytesLE] using hi
    have hdigit :
        ((BitVec.ofNat (8 * n) (byteValue data n)).extractLsb' (8 * i) 8).toNat =
          (data i).toNat := by
      rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (byteValue_bound data n)]
      simpa [Nat.pow_mul] using byteValue_digit data n i hi'
    have hbv : (BitVec.ofNat (8 * n) (byteValue data n)).extractLsb' (8 * i) 8 =
        (data i).toBitVec := BitVec.eq_of_toNat_eq hdigit
    simpa [SphincsSecurity.bytesLE, List.getElem_ofFn] using
      congrArg UInt8.ofBitVec hbv

def pack (blocksMinusOne : Nat) (data : List UInt8) : SigGolf.Query :=
  ⟨blocksMinusOne, BitVec.ofNat (8 * (64 * (blocksMinusOne + 1)))
    (byteValue (fun i => data[i]?.getD 0) (64 * (blocksMinusOne + 1)))⟩

theorem queryBytes_pack (blocksMinusOne : Nat) (data : List UInt8) :
    QueryDecoder.queryBytes (pack blocksMinusOne data) =
      (List.range (64 * (blocksMinusOne + 1))).map (fun i => data[i]?.getD 0) := by
  exact bytesLE_byteValue _ _

theorem range_getD_eq_take (data : List UInt8) (n : Nat) (h : n ≤ data.length) :
    (List.range n).map (fun i => data[i]?.getD 0) = data.take n := by
  apply List.ext_getElem
  · simp [List.length_take, h]
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hid : i < data.length := by omega
    simp [List.getElem_map, List.getElem_take, hid]

theorem queryBytes_pack_padded (blocksMinusOne : Nat) (data : List UInt8)
    (h : data.length ≤ 64 * (blocksMinusOne + 1)) :
    QueryDecoder.queryBytes (pack blocksMinusOne data) =
      data ++ List.replicate (64 * (blocksMinusOne + 1) - data.length) 0 := by
  rw [queryBytes_pack]
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    have hi' : i < 64 * (blocksMinusOne + 1) := by simpa using hi
    by_cases hdata : i < data.length
    · simp [List.getElem_map, hdata, List.getElem_append_left hdata]
    · simp [List.getElem_map, hdata, List.getElem_append_right (by omega : data.length ≤ i)]

def canonicalTagged (input : HashInput) : Prop :=
  input[0]? = some 1 ∧ 2 ≤ input.length ∧
    QueryDecoder.sourceLength (input[1]?.getD 255) = input.length

instance (input : HashInput) : Decidable (canonicalTagged input) := by
  unfold canonicalTagged
  infer_instance

def betaToQuery (input : HashInput) : SigGolf.Query :=
  if canonicalTagged input then
    pack ((input.length + 63) / 64 - 1) input
  else
    pack input.length (0 :: input)

private theorem canonical_blocks (input : HashInput) (h : canonicalTagged input) :
    1 ≤ (input.length + 63) / 64 ∧
      input.length ≤ 64 * ((input.length + 63) / 64) := by
  have hn : 2 ≤ input.length := h.2.1
  omega

private theorem canonical_queryBytes (input : HashInput) (h : canonicalTagged input) :
    QueryDecoder.queryBytes (betaToQuery input) =
      input ++ List.replicate (QueryDecoder.blockLength input.length - input.length) 0 := by
  have hb := canonical_blocks input h
  simp only [betaToQuery, if_pos h]
  rw [queryBytes_pack_padded]
  · simp [QueryDecoder.blockLength, show (input.length + 63) / 64 - 1 + 1 =
        (input.length + 63) / 64 by omega]
  · simpa [show (input.length + 63) / 64 - 1 + 1 =
        (input.length + 63) / 64 by omega] using hb.2

private theorem fallback_queryBytes (input : HashInput) (h : ¬ canonicalTagged input) :
    QueryDecoder.queryBytes (betaToQuery input) =
      (0 :: input) ++ List.replicate
        (64 * (input.length + 1) - (input.length + 1)) 0 := by
  simp only [betaToQuery, if_neg h]
  exact queryBytes_pack_padded _ _ (by simp)

theorem decode_betaToQuery_canonical (input : HashInput) (h : canonicalTagged input) :
    QueryDecoder.decode (betaToQuery input) = input := by
  have hbytes := canonical_queryBytes input h
  apply QueryDecoder.decode_padded (betaToQuery input) input input.length rfl h.2.1
    h.1 h.2.2 hbytes
  rw [hbytes]
  have hb := canonical_blocks input h
  simp [QueryDecoder.blockLength]
  omega

theorem canonicalTagged_keygen (p : PublicParameter) (d : KeygenDomain)
    (seed : MasterSeed) : canonicalTagged (keygenHashInput p d seed) := by
  refine ⟨QueryDecoder.keygen_first p d seed, ?_,
    QueryDecoder.keygen_sourceLength p d seed⟩
  cases d <;> simp [keygenHashInput, keygenDomainFields,
    fieldBytes, bytesLE]

theorem canonicalTagged_randomizer (p : PublicParameter) (seed : MasterSeed)
    (message : SphincsSecurity.Message) (trial : BitVec 32) :
    canonicalTagged (randomizerHashInput p seed message trial) := by
  refine ⟨QueryDecoder.randomizer_first p seed message trial, ?_,
    QueryDecoder.randomizer_sourceLength p seed message trial⟩
  simp [randomizerHashInput, fieldBytes, bytesLE]

theorem canonicalTagged_tweakable (p : PublicParameter) (d : HashDomain)
    (payload : HashInput) (h : payload.length = QueryDecoder.expectedPayloadLength d) :
    canonicalTagged (tweakableHashInput p d payload) := by
  refine ⟨QueryDecoder.tweakable_first p d payload, ?_,
    QueryDecoder.tweakable_sourceLength p d payload h⟩
  cases d <;> simp [tweakableHashInput, tweakBytes, hashDomainFields,
    fieldBytes, bytesLE]

theorem canonicalTagged_commitmentInput (pk : SphincsSecurity.PublicKey) :
    canonicalTagged (SphincsWire.commitmentInput pk) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [SphincsWire.commitmentInput, SphincsSecurity.fieldBytes,
      SphincsSecurity.protocolDomainSep]
  · rw [SphincsWire.commitmentInput_length]
    omega
  · rw [SphincsWire.commitmentInput_length]
    simp [SphincsWire.commitmentInput, SphincsSecurity.fieldBytes,
      SphincsSecurity.tweakFields, SphincsSecurity.bytesLE,
      QueryDecoder.sourceLength]
    decide

theorem betaToQuery_injective : Function.Injective betaToQuery := by
  intro first second heq
  by_cases hf : canonicalTagged first
  · by_cases hs : canonicalTagged second
    · have := congrArg QueryDecoder.decode heq
      simpa [decode_betaToQuery_canonical first hf, decode_betaToQuery_canonical second hs]
        using this
    · have hfirst := canonical_queryBytes first hf
      have hsecond := fallback_queryBytes second hs
      have hhead := congrArg (fun q : SigGolf.Query =>
        (QueryDecoder.queryBytes q)[0]?) heq
      rw [hfirst, hsecond] at hhead
      have hn : 0 < first.length := by have := hf.2.1; omega
      simp [hn] at hhead
      have hbyte : first[0] = 1 := by
        have := hf.1
        simpa [List.getElem?_eq_getElem hn] using this
      rw [hbyte] at hhead
      cases hhead
  · by_cases hs : canonicalTagged second
    · have hfirst := fallback_queryBytes first hf
      have hsecond := canonical_queryBytes second hs
      have hhead := congrArg (fun q : SigGolf.Query =>
        (QueryDecoder.queryBytes q)[0]?) heq
      rw [hfirst, hsecond] at hhead
      have hn : 0 < second.length := by have := hs.2.1; omega
      simp [hn] at hhead
      have hbyte : second[0] = 1 := by
        have := hs.1
        simpa [List.getElem?_eq_getElem hn] using this
      rw [hbyte] at hhead
      cases hhead
    · have hlen : first.length = second.length := by
        have := congrArg Sigma.fst heq
        simpa [betaToQuery, hf, hs, pack] using this
      have hbytes := congrArg QueryDecoder.queryBytes heq
      rw [fallback_queryBytes first hf, fallback_queryBytes second hs] at hbytes
      rw [hlen] at hbytes
      have hp := List.append_cancel_right hbytes
      exact List.cons.inj hp |>.2

def adaptOracle (hash : SigGolf.Hash) : SphincsSecurity.HashInput → SphincsSecurity.HashOutput :=
  fun input => hash (betaToQuery input)

theorem commitmentQuery_ne_tweakable (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    betaToQuery (SphincsWire.commitmentInput pk) ≠
      betaToQuery (tweakableHashInput parameter domain payload) := by
  intro h
  exact SphincsWire.commitmentInput_ne_tweakableHashInput pk parameter domain payload
    (betaToQuery_injective h)

theorem commitmentQuery_ne_keygen (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    betaToQuery (SphincsWire.commitmentInput pk) ≠
      betaToQuery (keygenHashInput parameter domain seed) := by
  intro h
  exact SphincsWire.commitmentInput_ne_keygenHashInput pk parameter domain seed
    (betaToQuery_injective h)

theorem commitmentQuery_ne_randomizer (pk : SphincsSecurity.PublicKey)
    (parameter : PublicParameter) (seed : MasterSeed) (message : SphincsSecurity.Message)
    (trial : BitVec 32) :
    betaToQuery (SphincsWire.commitmentInput pk) ≠
      betaToQuery (randomizerHashInput parameter seed message trial) := by
  intro h
  exact SphincsWire.commitmentInput_ne_randomizerHashInput pk parameter seed message trial
    (betaToQuery_injective h)

/-- State after the beta padding stub, immediately before the commitment HASH service. -/
structure BetaCommitmentReady (state : MachineState)
    (pk : SphincsSecurity.PublicKey) : Prop where
  source : state.getReg .x10 = 0x40000
  bytes : state.getReg .x11 = 64
  destination : state.getReg .x12 = 0x42000
  service : state.getReg .x5 = 0
  padded : QueryDecoder.queryBytes (SigGolf.Riscv.hashInput state) =
    SphincsWire.commitmentInput pk ++ List.replicate 4 0

theorem betaCommitmentReady_hashInput (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (ready : BetaCommitmentReady state pk) :
    SigGolf.Riscv.hashInput state = betaToQuery (SphincsWire.commitmentInput pk) := by
  apply QueryDecoder.decode_injective
  rw [decode_betaToQuery_canonical _ (canonicalTagged_commitmentInput pk)]
  apply QueryDecoder.decode_padded _ _ 60
    (SphincsWire.commitmentInput_length pk)
    (by omega)
    (canonicalTagged_commitmentInput pk).1
    (canonicalTagged_commitmentInput pk).2.2
  · simpa [QueryDecoder.blockLength, SphincsWire.commitmentInput_length] using ready.padded
  · simp [QueryDecoder.queryBytes_length, SigGolf.Riscv.hashInput,
      ready.bytes, QueryDecoder.blockLength]

theorem betaCommitmentReady_hashCost (state : MachineState)
    (pk : SphincsSecurity.PublicKey) (ready : BetaCommitmentReady state pk) :
    SigGolf.Riscv.hashArgumentsValid state = true ∧
      (SigGolf.Riscv.hashInput state).blocks = 1 := by
  constructor
  · simp [SigGolf.Riscv.hashArgumentsValid, ready.source, ready.bytes,
      ready.destination, SigGolf.Riscv.accessValid, SigGolf.Riscv.rangeValid,
      MEMORY_BYTES]
  · simp [SigGolf.Query.blocks, SigGolf.Riscv.hashInput, ready.bytes]

/-- info: 'SigGolfCandidate.BetaQuery.betaToQuery_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms betaToQuery_injective

/-- info: 'SigGolfCandidate.BetaQuery.betaCommitmentReady_hashInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms betaCommitmentReady_hashInput

/-- info: 'SigGolfCandidate.BetaQuery.betaCommitmentReady_hashCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms betaCommitmentReady_hashCost

/-- info: 'SigGolfCandidate.BetaQuery.canonicalTagged_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalTagged_keygen

/-- info: 'SigGolfCandidate.BetaQuery.canonicalTagged_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalTagged_randomizer

/-- info: 'SigGolfCandidate.BetaQuery.canonicalTagged_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalTagged_tweakable

end SigGolfCandidate.BetaQuery
