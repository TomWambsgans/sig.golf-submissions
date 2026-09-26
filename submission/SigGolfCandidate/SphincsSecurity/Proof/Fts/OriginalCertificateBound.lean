import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateBankCompleteness
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificatePathBudget
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UnitCertificateCoverage
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateOriginalMessageCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme signAfterDigest certificateCacheProposalImpl retainedGameRestComputation

abbrev CertificateContextResult := SecretKey × CertificateCacheGameResult
abbrev OriginalCertificateResult := SecretKey × RetainedRestResult × QueryCache HashSpec

noncomputable def originalCertificateSource (adversary : Adversary) : ProbComp OriginalCertificateResult := do
  let generated ← (simulateQ romImpl scheme.keygen).run ∅
  let result ← (simulateQ (unloggedMappedAdversaryImpl generated.1.2)
    (retainedGameRestComputation adversary generated.1.1)).run generated.2
  pure (generated.1.2, result)

noncomputable def certificateContextGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateContextResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  let result ← (simulateQ (certificateCacheProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)
  pure (key, result)

theorem certificateContextGame_project (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Prod.snd <$> certificateContextGame adversary budget required stopAfter stopped =
      certificateCacheGame adversary budget required stopAfter stopped := by
  simp only [certificateContextGame, certificateCacheGame, map_bind, map_pure, bind_pure]

theorem certificateCacheProposal_original {Result : Type} (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : List Index × CertificateCacheMonitorState) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state =
        (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run state.2.1) : PMF _) := by
  rw [certificateCacheProposalImpl]
  exact simulateQ_originalProposalImpl_original key _ _ _ computation state

def CertificateContextResult.original (result : CertificateContextResult) : OriginalCertificateResult :=
  (result.1, result.2.1, result.2.2.2.1)

theorem certificateContextGame_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    CertificateContextResult.original <$> certificateContextGame adversary budget required stopAfter stopped =
      (liftM (originalCertificateSource adversary) : PMF _) := by
  have hrest (generated : ((PublicKey × SecretKey) × SigningBoundaryTrace) × QueryCache HashSpec) :
      (fun result : CertificateCacheGameResult => (generated.1.1.2, result.1, result.2.2.1)) <$>
        (simulateQ (certificateCacheProposalImpl generated.1.1.2 budget required (stopAfter generated.1.1.2))
          (retainedGameRestComputation adversary generated.1.1.1)).run
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) =
      (liftM (do
        let result ← (simulateQ (unloggedMappedAdversaryImpl generated.1.1.2)
          (retainedGameRestComputation adversary generated.1.1.1)).run generated.2
        pure (generated.1.1.2, result)) : PMF _) := by
    have h := congrArg (Functor.map (fun result => (generated.1.1.2, result)))
      (certificateCacheProposal_original generated.1.1.2 budget required (stopAfter generated.1.1.2)
        (retainedGameRestComputation adversary generated.1.1.1)
        ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false))
    simpa only [Functor.map_map, ← liftM_map (m := ProbComp) (n := PMF), bind_pure_comp] using h
  simp only [certificateContextGame, map_bind, bind_pure_comp, Functor.map_map, CertificateContextResult.original]
  simp_rw [hrest]
  rw [← liftM_bind (m := ProbComp) (n := PMF)]
  apply congrArg (fun computation : ProbComp OriginalCertificateResult => (liftM computation : PMF _))
  rw [originalCertificateSource, ← boundaryRun_forget 0 scheme.keygen ∅, bind_map_left]

def OriginalFullCertificate (result : OriginalCertificateResult) : Prop :=
  SigningTranscript.Valid result.2.1.1.2 ∧
    ∃ input, TargetCertificateAt result.1 Finset.univ (result.2.2, result.2.1.1.2) input

theorem certificateContextGame_full_count (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (hbound : HasHashQueryBound scheme adversary q) (result : CertificateContextResult)
    (hr : result ∈ (certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false).support)
    (hfull : OriginalFullCertificate result.original) (hclean : ¬CertificateGameExceptional result.2) :
    1 ≤ certificateBankCount result.2.2.2.2.1.bank := by
  rw [certificateContextGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  rw [probCompLift_support] at hgenerated
  have hwhole : HashQueryBound (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2)
      ∅ q := (hasHashQueryBound_iff scheme adversary q).mp hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q ∅ hwhole generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, hashQueryBound_map_iff] at hrest
  have hretained : OtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1 =
      retainedGameRestComputation adversary generated.1.1.1 := by
    unfold OtsProbeSimulation.retainedGameRestComputation retainedGameRestComputation
    rfl
  rw [hretained] at hrest
  have hcache := boundaryRun_enncard_le 0 scheme.keygen ∅ generated hgenerated
  simp only [QueryCache.enncard_empty, zero_add] at hcache
  have hg : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hgenerated, rfl⟩
  dsimp only [OriginalFullCertificate, CertificateContextResult.original] at hfull
  obtain ⟨hvalid, input, hcertificate⟩ := hfull
  exact certificateCacheProposal_rest_clean_certificate adversary generated.1.1.1 generated.1.1.2
    q (q - generated.1.2.hashCalls) generated.1.2.hashCalls Finset.univ hbudget generated.2 hrest
    (Nat.add_sub_of_le hkeygen.1).le hcache (keygen_cache_message_none (generated.1.1, generated.2) hg) output houtput hvalid hclean input hcertificate

private theorem probOutput_probCompLift {Result : Type} (computation : ProbComp Result) (result : Result) :
    Pr[= result | (liftM computation : PMF Result)] = Pr[= result | computation] := rfl

private theorem expected_probCompLift_of_map_eq {Source Result : Type}
    (source : ProbComp Source) (result : ProbComp Result) (project : Source → Result)
    (hproject : project <$> source = result) (cost : Result → ENNReal) :
    (∑' value, Pr[= value | (liftM source : PMF Source)] * cost (project value)) =
      ∑' value, Pr[= value | result] * cost value := by
  rw [← hproject, tsum_probOutput_map_mul]
  simp only [probOutput_probCompLift]

private theorem probEvent_probCompLift {Result : Type} (computation : ProbComp Result) (event : Result → Prop) :
    Pr[event | (liftM computation : PMF Result)] = Pr[event | computation] := by
  simp only [probEvent_eq_tsum_ite]
  rfl

theorem originalCertificateSource_full_le_count_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (∑' result, Pr[= result | certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] *
        certificateBankCount result.2.2.2.2.1.bank) +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  let law : SPMF CertificateContextResult := liftM (certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false)
  have hsource : Pr[OriginalFullCertificate | originalCertificateSource adversary] =
      Pr[fun result => OriginalFullCertificate result.original | law] := by
    have h := congrArg (fun source : PMF OriginalCertificateResult => Pr[OriginalFullCertificate | source])
      (certificateContextGame_original adversary q Finset.univ (fun _ => proposalPrefixStop) false)
    rw [probEvent_map, probEvent_probCompLift] at h
    simpa only [law, SPMF.probEvent_liftM, Function.comp_def] using h.symm
  rw [hsource]
  change Pr[fun result => OriginalFullCertificate result.original | law] ≤
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.2.1.bank) +
    Pr[fun result => CertificateGameExceptional result.2 | law]
  refine (probEvent_mono (q := fun result =>
    (OriginalFullCertificate result.original ∧ ¬CertificateGameExceptional result.2) ∨ CertificateGameExceptional result.2)
      (fun result _ h => by by_cases hc : CertificateGameExceptional result.2; exact Or.inr hc; exact Or.inl ⟨h, hc⟩)).trans
    ((probEvent_or_le law _ _).trans (add_le_add ?_ le_rfl))
  apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
  intro result hr h
  exact certificateContextGame_full_count adversary q hbudget hbound result (by simpa only [law, SPMF.support_eq_support, SPMF.support_liftM] using hr) h.1 h.2

theorem originalCertificateSource_full_le_message_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (2 ^ 144 : ENNReal)⁻¹ *
        (∑' result, Pr[= result | certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] *
          (result.2.2.2.2.1.messageCalls : ENNReal)) + (q : ENNReal) * fullCertificateExcessRate +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have h := expected_certificateCacheGame_full_unit_count_le adversary q (fun _ _ _ _ _ => false) hbudget hbound
  dsimp only at h
  simp only [Bool.or_false] at h
  rw [← certificateContextGame_project adversary q Finset.univ (fun _ => proposalPrefixStop) false] at h
  simp only [tsum_probOutput_map_mul] at h
  exact (originalCertificateSource_full_le_count_add_exception adversary q hbudget hbound).trans (add_le_add h le_rfl)

noncomputable def originalCertificateMessageCost (adversary : Adversary) : ENNReal :=
  ∑' generated, Pr[= generated | (simulateQ romImpl scheme.keygen).run ∅] *
    expectedBoundaryMessageCalls generated.1.2.parameter
      (simulateQ (expandedAdversaryImpl generated.1.2) (retainedGameRestComputation adversary generated.1.1)) generated.2

theorem certificateContextGame_messageCalls_le_original (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateContextGame adversary budget required stopAfter stopped] *
      (result.2.2.2.2.1.messageCalls : ENNReal)) ≤ originalCertificateMessageCost adversary := by
  rw [certificateContextGame, tsum_probOutput_bind_mul]
  calc
    _ ≤ ∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (retainedGameRestComputation adversary generated.1.1.1)) generated.2 := by
      apply ENNReal.tsum_le_tsum
      intro generated
      apply mul_le_mul' le_rfl
      rw [tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_pure_mul]
      simpa only [initialCertificateMonitor, Nat.cast_zero, zero_add] using
        expected_certificateCacheProposal_messageCalls_le_original generated.1.1.2 budget required (stopAfter generated.1.1.2)
          (retainedGameRestComputation adversary generated.1.1.1)
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false)
    _ = _ := by
      exact expected_probCompLift_of_map_eq (boundaryRun 0 scheme.keygen ∅)
        ((simulateQ romImpl scheme.keygen).run ∅) (fun result => (result.1.1, result.2))
        (boundaryRun_forget 0 scheme.keygen ∅) (fun generated =>
          expectedBoundaryMessageCalls generated.1.2.parameter
            (simulateQ (expandedAdversaryImpl generated.1.2)
              (retainedGameRestComputation adversary generated.1.1)) generated.2)

theorem originalCertificateSource_full_le_original_message_add_exception (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (2 ^ 144 : ENNReal)⁻¹ * originalCertificateMessageCost adversary + (q : ENNReal) * fullCertificateExcessRate +
      Pr[fun result => CertificateGameExceptional result.2 |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] :=
  (originalCertificateSource_full_le_message_add_exception adversary q hbudget hbound).trans
    (add_le_add (add_le_add (mul_le_mul' le_rfl
      (certificateContextGame_messageCalls_le_original adversary q Finset.univ (fun _ => proposalPrefixStop) false)) le_rfl) le_rfl)

theorem certificateContextGame_mass_le_spent (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) (result : CertificateContextResult)
    (hr : result ∈ (certificateContextGame adversary budget required stopAfter stopped).support) :
    result.2.2.2.2.1.creationMass ≤ (result.2.2.2.2.1.spent : ENNReal) := by
  rw [certificateContextGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  apply certificateCacheProposal_run_mass_le_spent
    generated.1.1.2 budget required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1)
    ([], (generated.2, (initialCertificateMonitor generated.1.2.hashCalls stopped, false)))
  · simp only [initialCertificateMonitor]
    exact zero_le
  · exact houtput

abbrev CertificateCountedState := QueryCache HashSpec × ((CertificateMonitor × Bool) × Nat)

def certificateCountedProject (state : CertificateCountedState) : CertificateCacheMonitorState :=
  (state.1, state.2.1)

noncomputable def certificateCountedUpdate (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (length : Nat) (record : ProposalExecutionRecord input) : (CertificateMonitor × Bool) × Nat :=
  (certificateCacheMonitorUpdate key budget required stopAfter input
      (certificateCountedProject state) length record,
    state.2.2 + record.trace.hashCalls)

noncomputable def certificateCountedProposalImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × CertificateCountedState) PMF) :=
  originalProposalImpl key (fun state => state.2.1.1.spent)
    (fun message state => certificateMonitorEnabled key budget message
      (certificateCacheMonitorProject (certificateCountedProject state)))
    (certificateCountedUpdate key budget required stopAfter)

noncomputable def certificateCountedLengthImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CertificateCountedState PMF) :=
  originalLengthImpl key (fun state => state.2.1.1.spent)
    (fun message state => certificateMonitorEnabled key budget message
      (certificateCacheMonitorProject (certificateCountedProject state)))
    (certificateCountedUpdate key budget required stopAfter)

def certificateCountedRawProject (state : CertificateCountedState) :
    QueryCache HashSpec × Nat := (state.1, state.2.2)

noncomputable def countedAdversaryPMFImpl (key : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec × Nat) PMF) :=
  fun input => StateT.mk fun state =>
    (originalProposalRecord key input state.1).map fun record =>
      (record.output, (record.cache, state.2 + record.trace.hashCalls))

theorem certificateCountedUpdate_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    (certificateCountedProject (record.cache,
      certificateCountedUpdate key budget required stopAfter input state length record)) =
    (record.cache, certificateCacheMonitorUpdate key budget required stopAfter input
      (certificateCountedProject state) length record) := rfl

theorem certificateCountedProposalImpl_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × CertificateCountedState) :
    Prod.map id (Prod.map id certificateCountedProject) <$>
      (certificateCountedProposalImpl key budget required stopAfter input).run state =
    (certificateCacheProposalImpl key budget required stopAfter input).run
      (state.1, certificateCountedProject state.2) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateCountedProposalImpl, certificateCacheProposalImpl,
        originalProposalImpl, proposalRecordImpl, StateT.run_mk,
        originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateCountedProposalImpl, certificateCacheProposalImpl,
        originalProposalImpl, proposalRecordImpl, StateT.run_mk,
        originalProposalActive, certificateCountedProject]
      split <;> simp only [PMF.map_comp] <;> rfl

theorem simulateQ_certificateCountedProposalImpl_project {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState) :
    Prod.map id (Prod.map id certificateCountedProject) <$>
      (simulateQ (certificateCountedProposalImpl key budget required stopAfter) computation).run state =
    (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run
      (state.1, certificateCountedProject state.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map id certificateCountedProject)
    (certificateCountedProposalImpl_project key budget required stopAfter) computation state

theorem simulateQ_certificateCountedLengthImpl_raw {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateCountedState) :
    Prod.map id certificateCountedRawProject <$>
      (simulateQ (certificateCountedLengthImpl key budget required stopAfter) computation).run state =
    (simulateQ (countedAdversaryPMFImpl key) computation).run
      (certificateCountedRawProject state) := by
  exact simulateQ_lengthRecordImpl_project
    (fun input current => originalProposalRecord key input current.1)
    (fun _ record => record.output)
    (originalProposalAdvance (certificateCountedUpdate key budget required stopAfter))
    (originalProposalActive key (fun current => current.2.1.1.spent)
      (fun message current => certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject current))))
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
    (countedAdversaryPMFImpl key) certificateCountedRawProject
    (fun _ current record => (record.cache, current.2.2 + record.trace.hashCalls))
    (by intros; rfl) (by intros; rfl) computation state

theorem simulateQ_certificateCountedProposalImpl_raw {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState) :
    (fun result => (result.1, certificateCountedRawProject result.2.2)) <$>
      (simulateQ (certificateCountedProposalImpl key budget required stopAfter) computation).run state =
    (simulateQ (countedAdversaryPMFImpl key) computation).run
      (certificateCountedRawProject state.2) := by
  calc
    _ = Prod.map id certificateCountedRawProject <$>
        (Prod.map id Prod.snd <$>
          (simulateQ (certificateCountedProposalImpl key budget required stopAfter) computation).run state) := by
      simp only [Functor.map_map]
      rfl
    _ = _ := by
      unfold certificateCountedProposalImpl
      rw [simulateQ_originalProposalImpl_length]
      exact simulateQ_certificateCountedLengthImpl_raw key budget required stopAfter computation state.2

theorem countedAdversaryPMFImpl_query_count (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : QueryCache HashSpec × Nat) :
    (countedAdversaryPMFImpl key input).run state =
      (fun result => (result.1.1, (result.2, state.2 + result.1.2))) <$>
        (liftM ((simulateQ romImpl
          (countHashQueries (expandedAdversaryImpl key input))).run state.1) : PMF _) := by
  rw [countedAdversaryPMFImpl]
  rw [← originalProposalRecord_counted key input state.1]
  simp only [StateT.run_mk, Functor.map_map]
  rfl

theorem countedAdversaryPMFImpl_run_count {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (spent : Nat) :
    (fun result : α × (QueryCache HashSpec × Nat) =>
      ((result.1, result.2.2), result.2.1)) <$>
      (simulateQ (countedAdversaryPMFImpl key) computation).run (cache, spent) =
    (liftM ((fun result : (α × Nat) × QueryCache HashSpec =>
      ((result.1.1, spent + result.1.2), result.2)) <$>
      (simulateQ romImpl
        (countHashQueries (simulateQ (expandedAdversaryImpl key) computation))).run cache) : PMF _) := by
  induction computation using OracleComp.inductionOn generalizing cache spent with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, countHashQueries_pure,
        Nat.add_zero, PMF.monad_map_eq_map, map_pure, liftM_pure]
      change PMF.map (fun result : α × (QueryCache HashSpec × Nat) =>
        ((result.1, result.2.2), result.2.1)) (PMF.pure (value, (cache, spent))) =
        PMF.pure ((value, spent), cache)
      rw [PMF.pure_map]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [simulateQ_bind, simulateQ_spec_query, countHashQueries_bind]
      simp only [StateT.run_bind, simulateQ_bind, map_bind, bind_pure_comp]
      rw [countedAdversaryPMFImpl_query_count]
      simp only [PMF.monad_map_eq_map, liftM_bind, liftM_map]
      simp only [PMF.monad_bind_eq_bind, PMF.bind_map]
      apply PMF.bind_congr
      intro a _
      simp only [Function.comp_def]
      have htail := ih a.1.1 a.2 (spent + a.1.2)
      rw [PMF.monad_map_eq_map] at htail
      rw [htail]
      simp only [simulateQ_map, StateT.run_map, liftM_map,
        PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, Nat.add_assoc]

theorem simulateQ_certificateCountedProposalImpl_count {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState) :
    (fun result : α × (List Index × CertificateCountedState) =>
      ((result.1, result.2.2.2.2), result.2.2.1)) <$>
      (simulateQ (certificateCountedProposalImpl key budget required stopAfter) computation).run state =
    (liftM ((fun result : (α × Nat) × QueryCache HashSpec =>
      ((result.1.1, state.2.2.2 + result.1.2), result.2)) <$>
      (simulateQ romImpl
        (countHashQueries (simulateQ (expandedAdversaryImpl key) computation))).run state.2.1) : PMF _) := by
  let f : α × (QueryCache HashSpec × Nat) → (α × Nat) × QueryCache HashSpec :=
    fun result => ((result.1, result.2.2), result.2.1)
  calc
    _ = f <$> ((fun result : α × (List Index × CertificateCountedState) =>
        (result.1, certificateCountedRawProject result.2.2)) <$>
        (simulateQ (certificateCountedProposalImpl key budget required stopAfter) computation).run state) := by
      simp only [Functor.map_map, f, certificateCountedRawProject]
    _ = f <$> (simulateQ (countedAdversaryPMFImpl key) computation).run
        (certificateCountedRawProject state.2) := by
      rw [simulateQ_certificateCountedProposalImpl_raw]
    _ = _ := countedAdversaryPMFImpl_run_count key computation state.2.1 state.2.2.2

theorem certificateCountedUpdate_spent_le_allCalls (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hpre : state.2.1.1.spent ≤ state.2.2)
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateCountedUpdate key budget required stopAfter input state length record).1.1.spent ≤
      (certificateCountedUpdate key budget required stopAfter input state length record).2 := by
  have hstep := (certificateMonitorUpdate_le_hashCalls key budget required stopAfter input
    (certificateCacheMonitorProject (certificateCountedProject state)) length record hr).1
  simp only [certificateCountedUpdate, certificateCacheMonitorUpdate,
    certificateCountedProject, certificateCacheMonitorProject] at hstep ⊢
  omega

theorem certificateCountedLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateCountedState)
    (hr : result ∈ ((certificateCountedLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateCountedUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateCountedLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩

theorem certificateCountedLength_run_spent_le_allCalls {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateCountedState)
    (hpre : state.2.1.1.spent ≤ state.2.2)
    (result : α × CertificateCountedState)
    (hr : result ∈ ((simulateQ (certificateCountedLengthImpl key budget required stopAfter)
      computation).run state).support) :
    result.2.2.1.1.spent ≤ result.2.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact hpre
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateCountedLengthImpl_support key budget required stopAfter input state middle hmiddle
      exact ih record.output _
        (certificateCountedUpdate_spent_le_allCalls key budget required stopAfter input state length record hpre hrecord)
        result hr

theorem certificateCountedProposal_run_spent_le_allCalls {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState)
    (hpre : state.2.2.1.1.spent ≤ state.2.2.2)
    (result : α × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required stopAfter)
      computation).run state).support) :
    result.2.2.2.1.1.spent ≤ result.2.2.2.2 := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  unfold certificateCountedProposalImpl at hm
  rw [← PMF.monad_map_eq_map] at hm
  rw [simulateQ_originalProposalImpl_length] at hm
  exact certificateCountedLength_run_spent_le_allCalls key budget required stopAfter computation
    state.2 hpre _ hm

abbrev CertificateCountedContextResult := SecretKey ×
  (RetainedRestResult × (List Index × CertificateCountedState))

noncomputable def certificateCountedContextGame (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) : PMF CertificateCountedContextResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  let result ← (simulateQ (certificateCountedProposalImpl key budget required (stopAfter key))
    (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)).run
      ([], (generated.2, ((initialCertificateMonitor generated.1.2.hashCalls stopped, false),
        generated.1.2.hashCalls)))
  pure (key, result)

def CertificateCountedContextResult.project (result : CertificateCountedContextResult) :
    CertificateContextResult :=
  (result.1, (result.2.1, (result.2.2.1, certificateCountedProject result.2.2.2)))

theorem certificateCountedContextGame_project (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) :
    CertificateCountedContextResult.project <$>
      certificateCountedContextGame adversary budget required stopAfter stopped =
    certificateContextGame adversary budget required stopAfter stopped := by
  simp only [certificateCountedContextGame, certificateContextGame,
    map_bind, map_pure]
  apply PMF.bind_congr
  intro generated _
  simp only [bind_pure_comp]
  have h := congrArg (Functor.map (Prod.mk generated.1.1.2))
    (simulateQ_certificateCountedProposalImpl_project generated.1.1.2 budget required
      (stopAfter generated.1.1.2)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
      ([], (generated.2, ((initialCertificateMonitor generated.1.2.hashCalls stopped, false),
        generated.1.2.hashCalls))))
  simpa only [Functor.map_map, CertificateCountedContextResult.project,
    Function.comp_def, Prod.map, id_eq, certificateCountedProject] using h

theorem certificateCountedContextGame_mass_le_allCalls (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) (result : CertificateCountedContextResult)
    (hr : result ∈ (certificateCountedContextGame adversary budget required stopAfter stopped).support) :
    result.2.2.2.2.1.1.creationMass ≤ (result.2.2.2.2.2 : ENNReal) := by
  have hproject : result.project ∈
      (certificateContextGame adversary budget required stopAfter stopped).support := by
    have hm := (PMF.mem_support_map_iff CertificateCountedContextResult.project _ _).mpr
      ⟨result, hr, rfl⟩
    rwa [← PMF.monad_map_eq_map,
      certificateCountedContextGame_project] at hm
  have hmass := certificateContextGame_mass_le_spent adversary budget required stopAfter
    stopped result.project hproject
  rw [certificateCountedContextGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  have hspent := certificateCountedProposal_run_spent_le_allCalls generated.1.1.2 budget
    required (stopAfter generated.1.1.2)
    (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
    ([], (generated.2, ((initialCertificateMonitor generated.1.2.hashCalls stopped, false),
      generated.1.2.hashCalls))) (by rfl) output houtput
  exact hmass.trans (Nat.cast_le.mpr hspent)

def CertificateCountedContextResult.originalCost (result : CertificateCountedContextResult) :
    OriginalCertificateResult × Nat :=
  ((result.1, result.2.1, result.2.2.2.1), result.2.2.2.2.2)

noncomputable def originalCertificateCountedSource (adversary : Adversary) :
    ProbComp (OriginalCertificateResult × Nat) := do
  let generated ← boundaryRun 0 scheme.keygen ∅
  let key := generated.1.1.2
  let result ← (simulateQ romImpl (countHashQueries
    (simulateQ (expandedAdversaryImpl key)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)))).run generated.2
  pure ((key, result.1.1, result.2), generated.1.2.hashCalls + result.1.2)

theorem certificateCountedContextGame_originalCost (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) :
    CertificateCountedContextResult.originalCost <$>
      certificateCountedContextGame adversary budget required stopAfter stopped =
    (liftM (originalCertificateCountedSource adversary) : PMF _) := by
  simp only [certificateCountedContextGame, originalCertificateCountedSource,
    map_bind, map_pure]
  rw [liftM_bind (m := ProbComp) (n := PMF)]
  apply bind_congr
  intro generated
  have h := congrArg (Functor.map (fun result : (RetainedRestResult × Nat) × QueryCache HashSpec =>
    ((generated.1.1.2, result.1.1, result.2), result.1.2)))
    (simulateQ_certificateCountedProposalImpl_count generated.1.1.2 budget required
      (stopAfter generated.1.1.2)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
      ([], (generated.2, ((initialCertificateMonitor generated.1.2.hashCalls stopped, false),
        generated.1.2.hashCalls))))
  simpa only [Functor.map_map, Function.comp_def, bind_pure_comp, Nat.add_assoc,
    liftM_map, CertificateCountedContextResult.originalCost] using h

noncomputable def originalCertificateBoundaryTraceSource (adversary : Adversary) :
    ProbComp (OriginalCertificateResult × Nat) := do
  let generated ← boundaryRun 0 scheme.keygen ∅
  let key := generated.1.1.2
  let result ← boundaryRun key.parameter
    (simulateQ (expandedAdversaryImpl key)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2
  pure ((key, result.1.1, result.2), generated.1.2.hashCalls + result.1.2.hashCalls)

theorem originalCertificateCountedSource_eq_boundary (adversary : Adversary) :
    originalCertificateCountedSource adversary =
      originalCertificateBoundaryTraceSource adversary := by
  simp only [originalCertificateCountedSource, originalCertificateBoundaryTraceSource]
  apply bind_congr
  intro generated
  rw [← boundaryRun_count generated.1.1.2.parameter
    (simulateQ (expandedAdversaryImpl generated.1.1.2)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2]
  simp only [bind_pure_comp, Functor.map_map]

theorem certificateCountedLengthImpl_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCountedState) :
    Prod.map id certificateCountedProject <$>
      (certificateCountedLengthImpl key budget required stopAfter input).run state =
    (certificateCacheLengthImpl key budget required stopAfter input).run
      (certificateCountedProject state) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateCountedLengthImpl, certificateCacheLengthImpl,
        originalLengthImpl, lengthRecordImpl, StateT.run_mk,
        originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateCountedLengthImpl, certificateCacheLengthImpl,
        originalLengthImpl, lengthRecordImpl, StateT.run_mk,
        originalProposalActive, certificateCountedProject]
      by_cases h : (certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject state)) &&
          decide (ProposalCacheBound key state.1 state.2.1.1.spent)) = true
      · simp only [certificateCountedProject] at h
        simp only [h, if_true, PMF.map_comp]
        rfl
      · simp only [certificateCountedProject] at h
        simp only [h]
        simp only [Bool.false_eq_true, if_false, PMF.map_comp]
        rfl

theorem simulateQ_certificateCountedLengthImpl_project {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateCountedState) :
    Prod.map id certificateCountedProject <$>
      (simulateQ (certificateCountedLengthImpl key budget required stopAfter) computation).run state =
    (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run
      (certificateCountedProject state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ certificateCountedProject
    (certificateCountedLengthImpl_project key budget required stopAfter) computation state

set_option maxHeartbeats 800000
theorem certificateCountedLength_run_calls_monotone {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateCountedState) (result : α × CertificateCountedState)
    (hr : result ∈ ((simulateQ (certificateCountedLengthImpl key budget required stopAfter)
      computation).run state).support) :
    state.2.2 ≤ result.2.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateCountedLengthImpl_support key budget required stopAfter input state middle hmiddle
      have htail := ih record.output _ result hr
      change state.2.2 + record.trace.hashCalls ≤ result.2.2.2 at htail
      omega

theorem certificateCountedProposal_run_calls_monotone {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState)
    (result : α × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required stopAfter)
      computation).run state).support) :
    state.2.2.2 ≤ result.2.2.2.2 := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  unfold certificateCountedProposalImpl at hm
  rw [← PMF.monad_map_eq_map, simulateQ_originalProposalImpl_length] at hm
  exact certificateCountedLength_run_calls_monotone key budget required stopAfter
    computation state.2 _ hm

theorem certificateCountedLength_withSigningLog_clean {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 128)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateCountedState)
    (hready : CertificateMonitorReady key budget
      (certificateCacheMonitorProject (certificateCountedProject state)))
    (halive : state.2.1.1.stopped = false)
    (hspent : state.2.1.1.spent ≤ state.2.2)
    (result : (α × QueryLog SigningSpec) × CertificateCountedState)
    (hr : result ∈ ((simulateQ (certificateCountedLengthImpl key budget required proposalPrefixStop)
      (FtsProbeSimulation.withSigningLog computation state.2.1.1.log)).run state).support)
    (hfinal : result.2.2.2 ≤ budget)
    (hvalid : SigningTranscript.Valid result.1.2) (hhit : result.2.2.1.2 = false)
    (hprefix : ¬ ProposalPrefixExceptional result.2.2.1.1.proposals result.2.2.1.1.log.length) :
    result.2.2.1.1.stopped = false ∧ result.2.2.1.1.log = result.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject
        (certificateCountedProject result.2)) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [FtsProbeSimulation.withSigningLog_pure, simulateQ_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨halive, rfl, hready⟩
  | query_bind input next ih =>
      rw [FtsProbeSimulation.withSigningLog_query_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateCountedLengthImpl_support key budget required proposalPrefixStop
          input state middle hmiddle
      let after := originalProposalAdvance
        (certificateCountedUpdate key budget required proposalPrefixStop)
        input state length record
      have htailCalls := certificateCountedLength_run_calls_monotone key budget required
        proposalPrefixStop
        (FtsProbeSimulation.withSigningLog (next record.output)
          (state.2.1.1.log ++ signingLogFragment input record.output)) after result hr
      have hstepCost : state.2.1.1.spent + record.trace.hashCalls ≤ budget := by
        change state.2.2 + record.trace.hashCalls ≤ result.2.2.2 at htailCalls
        omega
      have hlogLength := withSigningLog_run_length_le
        (certificateCountedLengthImpl key budget required proposalPrefixStop)
        (next record.output)
        (state.2.1.1.log ++ signingLogFragment input record.output) after result hr
      have hstepValid : ValidSigningStep state.2.1.1.log input := by
        change result.1.2.length ≤ signatureLimit at hvalid
        cases input <;> simp only [ValidSigningStep, signingLogFragment, List.length_append,
          List.length_nil, List.length_singleton] at hlogLength ⊢ <;> omega
      have hmin := signingMacroHashCost_le_record key input state.1 record hrecord
      have hactive : CertificateMonitorActive key budget input
          (certificateCacheMonitorProject (certificateCountedProject state)) :=
        ⟨halive, hready, hstepValid, by
          change signingMacroHashCost input ≤ budget - state.2.1.1.spent
          omega⟩
      have hafterHit : after.2.1.2 = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have htailSupport := (PMF.mem_support_map_iff
          (Prod.map id certificateCountedProject) _ _).mpr ⟨result, hr, rfl⟩
        rw [← PMF.monad_map_eq_map, simulateQ_certificateCountedLengthImpl_project]
          at htailSupport
        have hfinalHit := certificateCacheLength_run_hit key budget required proposalPrefixStop
          (FtsProbeSimulation.withSigningLog (next record.output)
            (state.2.1.1.log ++ signingLogFragment input record.output))
          (certificateCountedProject after) htrue _ htailSupport
        change result.2.2.1.2 = true at hfinalHit
        rw [hhit] at hfinalHit
        contradiction
      have hafterClean : ¬ CertificateCacheExceptional key record.cache := by
        intro hbad
        have htrue := certificateCacheMonitorUpdate_bad_after key budget required
          proposalPrefixStop input (certificateCountedProject state) length record hbad
        change after.2.1.2 = true at htrue
        rw [hafterHit] at htrue
        contradiction
      have hafterReady : CertificateMonitorReady key budget
          (certificateCacheMonitorProject (certificateCountedProject after)) :=
        certificateMonitorUpdate_ready key budget required proposalPrefixStop input
          (certificateCacheMonitorProject (certificateCountedProject state)) length record
          hrecord hactive hbudget hstepCost hafterClean
      have hstop : proposalPrefixStop input
          (certificateCacheMonitorProject (certificateCountedProject state))
          length record = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        have hstopped : after.2.1.1.stopped = true := by
          simp only [after, originalProposalAdvance, certificateCountedUpdate,
            certificateCacheMonitorUpdate, certificateMonitorUpdate,
            if_pos hactive, htrue, Bool.true_or]
        have hoverflow := htrue
        rw [proposalPrefixStop_eq_after_exception key budget required proposalPrefixStop
          input (certificateCacheMonitorProject (certificateCountedProject state))
          length record hactive, decide_eq_true_eq] at hoverflow
        have htailSupport := (PMF.mem_support_map_iff
          (Prod.map id certificateCountedProject) _ _).mpr ⟨result, hr, rfl⟩
        rw [← PMF.monad_map_eq_map, simulateQ_certificateCountedLengthImpl_project]
          at htailSupport
        exact hprefix (certificateCacheLength_run_prefixOverflow key budget required
          proposalPrefixStop
          (FtsProbeSimulation.withSigningLog (next record.output)
            (state.2.1.1.log ++ signingLogFragment input record.output))
          (certificateCountedProject after) hstopped hoverflow _ htailSupport)
      have hafterAlive : after.2.1.1.stopped = false := by
        change (certificateMonitorUpdate key budget required proposalPrefixStop input
          (certificateCacheMonitorProject (certificateCountedProject state)) length record).stopped = false
        rw [certificateMonitorUpdate_stopped_eq key budget required proposalPrefixStop input
          (certificateCacheMonitorProject (certificateCountedProject state)) length record hactive]
        change (proposalPrefixStop input (certificateCacheMonitorProject
          (certificateCountedProject state)) length record ||
          decide (¬ CertificateMonitorReady key budget
            (certificateCacheMonitorProject (certificateCountedProject after)))) = false
        simp only [hstop, hafterReady, not_true_eq_false, decide_false, Bool.false_or]
      have hafterLog : after.2.1.1.log =
          state.2.1.1.log ++ signingLogFragment input record.output := by
        change (certificateMonitorUpdate key budget required proposalPrefixStop input
          (certificateCacheMonitorProject (certificateCountedProject state)) length record).log = _
        simp only [certificateMonitorUpdate, if_pos hactive, proposalRecordLogState]
        rfl
      have hafterSpent : after.2.1.1.spent ≤ after.2.2 := by
        exact certificateCountedUpdate_spent_le_allCalls key budget required
          proposalPrefixStop input state length record hspent hrecord
      apply ih record.output after hafterReady hafterAlive hafterSpent result
      · simpa only [hafterLog] using hr
      · exact hfinal
      · exact hvalid
      · exact hhit
      · exact hprefix

theorem certificateCountedProposal_withSigningLog_clean {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 128)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState)
    (hready : CertificateMonitorReady key budget
      (certificateCacheMonitorProject (certificateCountedProject state.2)))
    (halive : state.2.2.1.1.stopped = false)
    (hspent : state.2.2.1.1.spent ≤ state.2.2.2)
    (result : (α × QueryLog SigningSpec) × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required proposalPrefixStop)
      (FtsProbeSimulation.withSigningLog computation state.2.2.1.1.log)).run state).support)
    (hfinal : result.2.2.2.2 ≤ budget)
    (hvalid : SigningTranscript.Valid result.1.2)
    (hhit : result.2.2.2.1.2 = false)
    (hprefix : ¬ ProposalPrefixExceptional result.2.2.2.1.1.proposals
      result.2.2.2.1.1.log.length) :
    result.2.2.2.1.1.stopped = false ∧
      result.2.2.2.1.1.log = result.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject
        (certificateCountedProject result.2.2)) := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  unfold certificateCountedProposalImpl at hm
  rw [← PMF.monad_map_eq_map, simulateQ_originalProposalImpl_length] at hm
  exact certificateCountedLength_withSigningLog_clean key budget required hbudget
    computation state.2 hready halive hspent _ hm hfinal hvalid hhit hprefix

theorem certificateCountedProposal_rest_clean (adversary : Adversary)
    (publicKey : PublicKey) (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 128)
    (state : List Index × CertificateCountedState)
    (hready : CertificateMonitorReady key budget
      (certificateCacheMonitorProject (certificateCountedProject state.2)))
    (halive : state.2.2.1.1.stopped = false)
    (hlog : state.2.2.1.1.log = [])
    (hspent : state.2.2.1.1.spent ≤ state.2.2.2)
    (result : RetainedRestResult × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required
      proposalPrefixStop)
      (FtsProbeSimulation.retainedGameRestComputation adversary publicKey)).run state).support)
    (hfinal : result.2.2.2.2 ≤ budget)
    (hvalid : SigningTranscript.Valid result.1.1.2)
    (hclean : ¬ CertificateGameExceptional
      (result.1, (result.2.1, certificateCountedProject result.2.2))) :
    result.2.2.2.1.1.stopped = false ∧
      result.2.2.2.1.1.log = result.1.1.2 ∧
      CertificateMonitorReady key budget (certificateCacheMonitorProject
        (certificateCountedProject result.2.2)) := by
  rw [FtsProbeSimulation.retainedGameRestComputation_eq_signingTrace,
    simulateQ_map, StateT.run_map, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at hr
  obtain ⟨source, hsource, rfl⟩ := hr
  have htrace : FtsProbeSimulation.withSigningLog
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary publicKey)
      state.2.2.1.1.log =
      FtsProbeSimulation.signingTraceComputation
        (FtsProbeSimulation.unloggedRetainedRestComputation adversary publicKey) := by
    simp only [FtsProbeSimulation.withSigningLog, hlog, List.nil_append, Prod.mk.eta]
    exact id_map _
  exact certificateCountedProposal_withSigningLog_clean key budget required hbudget
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary publicKey) state
    hready halive hspent source (by rwa [htrace]) hfinal hvalid
    (Bool.eq_false_iff.mpr (fun h => hclean (Or.inl h)))
    (fun h => hclean (Or.inr h))

theorem certificateCountedProposal_run_bank_complete {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateCountedState)
    (hbank : state.2.2.1.1.stopped = false →
      CertificateBankComplete key required
        (certificateCacheMonitorProject (certificateCountedProject state.2)))
    (result : α × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required stopAfter)
      computation).run state).support)
    (halive : result.2.2.2.1.1.stopped = false) :
    CertificateBankComplete key required
      (certificateCacheMonitorProject (certificateCountedProject result.2.2)) := by
  have hm := (PMF.mem_support_map_iff
    (Prod.map id (Prod.map id certificateCountedProject)) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, simulateQ_certificateCountedProposalImpl_project] at hm
  exact certificateCacheProposal_run_bank_complete key budget required stopAfter computation
    (state.1, certificateCountedProject state.2) hbank _ hm halive

theorem certificateCountedProposal_rest_clean_certificate (adversary : Adversary)
    (publicKey : PublicKey) (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (hbudget : budget ≤ 2 ^ 128)
    (cache : QueryCache HashSpec) (hspent : spent ≤ budget)
    (hcache : QueryCache.enncard cache ≤ spent)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input →
      cache input = none)
    (result : RetainedRestResult × (List Index × CertificateCountedState))
    (hr : result ∈ ((simulateQ (certificateCountedProposalImpl key budget required
      proposalPrefixStop)
      (FtsProbeSimulation.retainedGameRestComputation adversary publicKey)).run
        ([], (cache, ((initialCertificateMonitor spent false, false), spent)))).support)
    (hfinal : result.2.2.2.2 ≤ budget)
    (hvalid : SigningTranscript.Valid result.1.1.2)
    (hclean : ¬ CertificateGameExceptional
      (result.1, (result.2.1, certificateCountedProject result.2.2)))
    (input : HashInput)
    (hcertificate : TargetCertificateAt key required
      (result.2.2.1, result.1.1.2) input) :
    1 ≤ certificateBankCount result.2.2.2.1.1.bank := by
  have hready := initialCertificateMonitor_ready key budget spent cache false
    hbudget hspent hcache hnone
  have hresult := certificateCountedProposal_rest_clean adversary publicKey key budget
    required hbudget
    ([], (cache, ((initialCertificateMonitor spent false, false), spent)))
    hready rfl rfl (le_refl spent) result hr hfinal hvalid hclean
  have hbank := certificateCountedProposal_run_bank_complete key budget required
    proposalPrefixStop
    (FtsProbeSimulation.retainedGameRestComputation adversary publicKey)
    ([], (cache, ((initialCertificateMonitor spent false, false), spent)))
    (fun _ => initialCertificateMonitor_bank_complete key spent required cache false hnone)
    result hr hresult.1
  apply one_le_certificateBankCount _ input
  apply hbank input
  change TargetCertificateAt key required (result.2.2.1, result.2.2.2.1.1.log) input
  rwa [hresult.2.1]

theorem certificateCountedContextGame_full_count (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 128) (result : CertificateCountedContextResult)
    (hr : result ∈ (certificateCountedContextGame adversary q Finset.univ
      (fun _ => proposalPrefixStop) false).support)
    (hfull : OriginalFullCertificate result.originalCost.1)
    (hclean : ¬ CertificateGameExceptional result.project.2)
    (hcost : result.originalCost.2 ≤ q) :
    1 ≤ certificateBankCount result.2.2.2.2.1.1.bank := by
  rw [certificateCountedContextGame, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  rw [probCompLift_support] at hgenerated
  have hcache := boundaryRun_enncard_le 0 scheme.keygen ∅ generated hgenerated
  simp only [QueryCache.enncard_empty, zero_add] at hcache
  have hg : (generated.1.1, generated.2) ∈
      support ((simulateQ romImpl scheme.keygen).run ∅) := by
    rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
    exact ⟨generated, hgenerated, rfl⟩
  have hspent : generated.1.2.hashCalls ≤ q := by
    have hmono := certificateCountedProposal_run_calls_monotone generated.1.1.2
      q Finset.univ proposalPrefixStop
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
      ([], (generated.2, ((initialCertificateMonitor
        generated.1.2.hashCalls false, false), generated.1.2.hashCalls)))
      output houtput
    exact hmono.trans hcost
  dsimp only [OriginalFullCertificate, CertificateCountedContextResult.originalCost]
    at hfull
  obtain ⟨hvalid, input, hcertificate⟩ := hfull
  exact certificateCountedProposal_rest_clean_certificate adversary generated.1.1.1
    generated.1.1.2 q generated.1.2.hashCalls Finset.univ hbudget generated.2
    hspent hcache (keygen_cache_message_none (generated.1.1, generated.2) hg)
    output houtput hcost hvalid hclean input hcertificate

def OriginalBudgetedFullCertificate (q : Nat)
    (result : OriginalCertificateResult × Nat) : Prop :=
  OriginalFullCertificate result.1 ∧ result.2 ≤ q

noncomputable def CertificateCountedWeightedBank (q : Nat)
    (result : CertificateCountedContextResult) : ENNReal :=
  if result.originalCost.2 ≤ q then
    (certificateBankCount result.2.2.2.2.1.1.bank : ENNReal) else 0

def CertificateCountedBudgetExceptional (q : Nat)
    (result : CertificateCountedContextResult) : Prop :=
  CertificateGameExceptional result.project.2 ∧ result.originalCost.2 ≤ q

private theorem probEvent_probComp_lift {α : Type} (source : ProbComp α)
    (event : α → Prop) :
    Pr[event | (liftM source : PMF α)] = Pr[event | source] := by
  simp only [probEvent_eq_tsum_ite]
  rfl

private theorem probEvent_cover_le_weighted {α : Type} (law : SPMF α)
    (main good bad : α → Prop) (weight : α → ENNReal)
    (hcover : ∀ value, main value → good value ∨ bad value)
    (hgood : ∀ value ∈ law.support, good value → 1 ≤ weight value) :
    Pr[main | law] ≤
      (∑' value, Pr[= value | law] * weight value) + Pr[bad | law] := by
  refine (probEvent_mono (q := fun value => good value ∨ bad value)
    (fun value _ h => hcover value h)).trans
    ((probEvent_or_le law _ _).trans (add_le_add ?_ le_rfl))
  exact probEvent_le_tsum_probOutput_mul_cost_of_mem_support law good weight hgood

set_option maxHeartbeats 50000
theorem originalCertificateCountedSource_full_budget_le_count_add_exception
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128) :
    Pr[OriginalBudgetedFullCertificate q |
      originalCertificateCountedSource adversary] ≤
      (∑' result, Pr[= result | certificateCountedContextGame adversary q Finset.univ
        (fun _ => proposalPrefixStop) false] *
        CertificateCountedWeightedBank q result) +
      Pr[CertificateCountedBudgetExceptional q |
        certificateCountedContextGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] := by
  let law : SPMF CertificateCountedContextResult :=
    liftM (certificateCountedContextGame adversary q Finset.univ
      (fun _ => proposalPrefixStop) false)
  have hsource : Pr[OriginalBudgetedFullCertificate q |
      originalCertificateCountedSource adversary] =
      Pr[fun result => OriginalBudgetedFullCertificate q result.originalCost | law] := by
    have h := congrArg (fun source : PMF (OriginalCertificateResult × Nat) =>
      Pr[OriginalBudgetedFullCertificate q | source])
      (certificateCountedContextGame_originalCost adversary q Finset.univ
        (fun _ => proposalPrefixStop) false)
    rw [probEvent_map] at h
    calc
      _ = Pr[OriginalBudgetedFullCertificate q |
          (liftM (originalCertificateCountedSource adversary) : PMF _)] := by
            exact (probEvent_probComp_lift _ _).symm
      _ = Pr[fun result => OriginalBudgetedFullCertificate q result.originalCost |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] := by
            simpa only [Function.comp_def] using h.symm
      _ = _ := by simp only [law, SPMF.probEvent_liftM]
  rw [hsource]
  unfold OriginalBudgetedFullCertificate CertificateCountedWeightedBank
  change Pr[fun result => OriginalFullCertificate result.originalCost.1 ∧
      result.originalCost.2 ≤ q | law] ≤
    (∑' result, Pr[= result | law] *
      if result.originalCost.2 ≤ q then
        (certificateBankCount result.2.2.2.2.1.1.bank : ENNReal) else 0) +
    Pr[fun result => CertificateGameExceptional result.project.2 ∧
      result.originalCost.2 ≤ q | law]
  refine probEvent_cover_le_weighted law
    (fun result => OriginalFullCertificate result.originalCost.1 ∧
      result.originalCost.2 ≤ q)
    (fun result => OriginalFullCertificate result.originalCost.1 ∧
      result.originalCost.2 ≤ q ∧
      ¬ CertificateGameExceptional result.project.2)
    (fun result => CertificateGameExceptional result.project.2 ∧
      result.originalCost.2 ≤ q)
    (fun result => if result.originalCost.2 ≤ q then
      (certificateBankCount result.2.2.2.2.1.1.bank : ENNReal) else 0)
    ?_ ?_
  · intro result h
    by_cases hc : CertificateGameExceptional result.project.2
    · exact Or.inr ⟨hc, h.2⟩
    · exact Or.inl ⟨h.1, h.2, hc⟩
  intro result hr h
  have hsupport : result ∈ (certificateCountedContextGame adversary q Finset.univ
      (fun _ => proposalPrefixStop) false).support := by
    simpa only [law, SPMF.support_eq_support, SPMF.support_liftM] using hr
  have hcount := certificateCountedContextGame_full_count adversary q hbudget result
    hsupport h.1 h.2.2 h.2.1
  simp only [if_pos h.2.1]
  exact_mod_cast hcount

def CertificateCountedContextResult.gameResult
    (result : CertificateCountedContextResult) : CertificateGameResult :=
  certificateCacheGameProject result.project.2

theorem certificateCountedContextGame_game (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (stopped : Bool) :
    CertificateCountedContextResult.gameResult <$>
      certificateCountedContextGame adversary budget required stopAfter stopped =
    certificateGame adversary budget required stopAfter stopped := by
  calc
    _ = certificateCacheGameProject <$>
        (Prod.snd <$> (CertificateCountedContextResult.project <$>
          certificateCountedContextGame adversary budget required stopAfter stopped)) := by
          simp only [Functor.map_map]
          rfl
    _ = certificateCacheGameProject <$>
        certificateCacheGame adversary budget required stopAfter stopped := by
          rw [certificateCountedContextGame_project,
            certificateContextGame_project]
    _ = _ := certificateCacheGame_project adversary budget required stopAfter stopped

noncomputable def certificateCountedTerminalGame (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    PMF (CertificateCountedContextResult × List Index) :=
  (certificateCountedContextGame adversary budget required stopAfter stopped).bind
    fun result => (completeProposalWord (PMF.uniformOfFintype Index) total
      result.gameResult.2.1).map (fun word => (result, word))

theorem certificateCountedTerminalGame_game (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateCountedTerminalGame adversary budget required stopAfter stopped total).map
      Prod.fst = certificateCountedContextGame adversary budget required stopAfter stopped := by
  rw [certificateCountedTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateCountedContextGame adversary budget required stopAfter stopped).bind
    (fun result => (completeProposalWord (PMF.uniformOfFintype Index) total
      result.gameResult.2.1).map (Function.const _ result)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem certificateCountedTerminalGame_word (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateCountedTerminalGame adversary budget required stopAfter stopped total).map
      Prod.snd =
    independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateCountedTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def,
    show (fun x : List Index => x) = id from rfl, PMF.map_id]
  change (certificateCountedContextGame adversary budget required stopAfter stopped).bind
    (fun result => completeProposalWord (PMF.uniformOfFintype Index) total
      result.gameResult.2.1) = _
  rw [← certificateGame_complete adversary budget required stopAfter stopped total]
  rw [← certificateCountedContextGame_game adversary budget required stopAfter stopped]
  change _ = (PMF.map CertificateCountedContextResult.gameResult
    (certificateCountedContextGame adversary budget required stopAfter stopped)).bind
      (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1)
  rw [PMF.bind_map]
  rfl

private theorem pmf_budget_mass_payoff_le {α ω : Type} (law : PMF (α × ω))
    (wordLaw : PMF ω) (mass : α → ENNReal) (cost : α → Nat)
    (payoff : ω → ENNReal) (q : Nat)
    (hword : law.map Prod.snd = wordLaw)
    (hmass : ∀ result ∈ law.support, cost result.1 ≤ q → mass result.1 ≤ q) :
    (∑' result, Pr[= result | law] *
      (if cost result.1 ≤ q then mass result.1 * payoff result.2 else 0)) ≤
    (q : ENNReal) * ∑' word, Pr[= word | wordLaw] * payoff word := by
  classical
  have hwordExpected := congrArg
    (fun distribution : PMF ω => ∑' word, Pr[= word | distribution] * payoff word) hword
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hwordExpected
  calc
    _ ≤ ∑' result, (q : ENNReal) * (Pr[= result | law] * payoff result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hcost : cost result.1 ≤ q
      · by_cases hr : result ∈ law.support
        · have hq := hmass result hr hcost
          simp only [if_pos hcost]
          calc
            _ ≤ Pr[= result | law] * ((q : ENNReal) * payoff result.2) :=
              mul_le_mul' le_rfl (mul_le_mul' hq le_rfl)
            _ = _ := by ring
        · have hz : Pr[= result | law] = 0 := by
            rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
            exact hr
          simp only [if_pos hcost, hz, zero_mul, mul_zero]
          exact le_rfl
      · simp only [if_neg hcost, mul_zero]
        exact zero_le
    _ = _ := by rw [ENNReal.tsum_mul_left, hwordExpected]

theorem expected_certificateCountedTerminalGame_budget_mass_payoff_le
    (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | certificateCountedTerminalGame adversary q required
      stopAfter stopped total] *
      (if result.1.originalCost.2 ≤ q then
        result.1.2.2.2.2.1.1.creationMass * payoff result.2 else 0)) ≤
    (q : ENNReal) *
      ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index)
        total] * payoff word := by
  apply pmf_budget_mass_payoff_le
    (certificateCountedTerminalGame adversary q required stopAfter stopped total)
    (independentProposalWord (PMF.uniformOfFintype Index) total)
    (fun result => result.2.2.2.2.1.1.creationMass)
    (fun result => result.originalCost.2) payoff q
    (certificateCountedTerminalGame_word adversary q required stopAfter stopped total)
  intro result hr hcost
  have hcontext : result.1 ∈
      (certificateCountedContextGame adversary q required stopAfter stopped).support := by
    have hm := (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨result, hr, rfl⟩
    rwa [certificateCountedTerminalGame_game] at hm
  exact (certificateCountedContextGame_mass_le_allCalls adversary q required stopAfter
    stopped result.1 hcontext).trans (Nat.cast_le.mpr hcost)

abbrev CertificateShadowState := QueryCache HashSpec ×
  (((CertificateMonitor × Bool) × Nat) × CertificateMonitor)

def certificateShadowActualProject (state : CertificateShadowState) :
    CertificateCountedState := (state.1, state.2.1)

def certificateShadowMonitorProject (state : CertificateShadowState) :
    CertificateMonitorState :=
  certificateCacheMonitorProject
    (certificateCountedProject (certificateShadowActualProject state))

noncomputable def certificateShadowUpdate (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    ((CertificateMonitor × Bool) × Nat) × CertificateMonitor :=
  (certificateCountedUpdate key budget required stopAfter input
      (certificateShadowActualProject state) length record,
    if state.2.1.2 + record.trace.hashCalls ≤ budget then
      certificateMonitorUpdate key budget required stopAfter input
        (state.1, state.2.2) length record
    else { state.2.2 with stopped := true })

noncomputable def certificateShadowProposalImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (List Index × CertificateShadowState) PMF) :=
  originalProposalImpl key (fun state => state.2.1.1.1.spent)
    (fun message state => certificateMonitorEnabled key budget message
      (certificateCacheMonitorProject
        (certificateCountedProject (certificateShadowActualProject state))))
    (certificateShadowUpdate key budget required stopAfter)

noncomputable def certificateShadowLengthImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CertificateShadowState PMF) :=
  originalLengthImpl key (fun state => state.2.1.1.1.spent)
    (fun message state => certificateMonitorEnabled key budget message
      (certificateCacheMonitorProject
        (certificateCountedProject (certificateShadowActualProject state))))
    (certificateShadowUpdate key budget required stopAfter)

theorem certificateShadowLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateShadowState)
    (hr : result ∈ ((certificateShadowLengthImpl key budget required stopAfter input).run
      state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateShadowUpdate key budget required stopAfter)
        input state length record) := by
  simp only [certificateShadowLengthImpl, originalLengthImpl, lengthRecordImpl,
    StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr
      ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩

theorem certificateShadowLengthImpl_actual_project (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) :
    Prod.map id certificateShadowActualProject <$>
      (certificateShadowLengthImpl key budget required stopAfter input).run state =
    (certificateCountedLengthImpl key budget required stopAfter input).run
      (certificateShadowActualProject state) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateShadowLengthImpl, certificateCountedLengthImpl,
        originalLengthImpl, lengthRecordImpl, StateT.run_mk,
        originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateShadowLengthImpl, certificateCountedLengthImpl,
        originalLengthImpl, lengthRecordImpl, StateT.run_mk,
        originalProposalActive, certificateShadowActualProject]
      by_cases h : (certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject
          (certificateShadowActualProject state))) &&
        decide (ProposalCacheBound key state.1 state.2.1.1.1.spent)) = true
      · simp only [certificateShadowActualProject, certificateCountedProject] at h ⊢
        simp only [h, if_true, PMF.map_comp]
        rfl
      · simp only [certificateShadowActualProject, certificateCountedProject] at h ⊢
        simp only [h, if_false, Bool.false_eq_true, PMF.map_comp]
        rfl

theorem certificateShadowLengthImpl_monitor_project (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) :
    Prod.map id certificateShadowMonitorProject <$>
      (certificateShadowLengthImpl key budget required stopAfter input).run state =
    (certificateLengthImpl key budget required stopAfter input).run
      (certificateShadowMonitorProject state) := by
  calc
    _ = Prod.map id certificateCacheMonitorProject <$>
        (Prod.map id certificateCountedProject <$>
          (Prod.map id certificateShadowActualProject <$>
            (certificateShadowLengthImpl key budget required stopAfter input).run state)) := by
          simp only [Functor.map_map]
          rfl
    _ = Prod.map id certificateCacheMonitorProject <$>
        (Prod.map id certificateCountedProject <$>
          (certificateCountedLengthImpl key budget required stopAfter input).run
            (certificateShadowActualProject state)) := by
          rw [certificateShadowLengthImpl_actual_project]
    _ = Prod.map id certificateCacheMonitorProject <$>
        (certificateCacheLengthImpl key budget required stopAfter input).run
          (certificateCountedProject (certificateShadowActualProject state)) := by
          rw [certificateCountedLengthImpl_project]
    _ = _ := certificateCacheLengthImpl_project key budget required stopAfter input
      (certificateCountedProject (certificateShadowActualProject state))

theorem certificateShadowLength_run_calls_monotone {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) (result : α × CertificateShadowState)
    (hr : result ∈ ((simulateQ (certificateShadowLengthImpl key budget required
      stopAfter) computation).run state).support) :
    state.2.1.2 ≤ result.2.2.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateShadowLengthImpl_support key budget required stopAfter input state
          middle hmiddle
      have htail := ih record.output _ result hr
      change state.2.1.2 + record.trace.hashCalls ≤ result.2.2.1.2 at htail
      omega

theorem certificateShadowUpdate_good (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hpre : state.2.2 = state.2.1.1.1)
    (hcost : state.2.1.2 + record.trace.hashCalls ≤ budget) :
    (certificateShadowUpdate key budget required stopAfter input state length
      record).2 =
    (certificateShadowUpdate key budget required stopAfter input state length
      record).1.1.1 := by
  simp only [certificateShadowUpdate, if_pos hcost, certificateCountedUpdate,
    certificateCacheMonitorUpdate, certificateShadowActualProject]
  rw [hpre]
  rfl

theorem certificateShadowUpdate_mass_budget (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support)
    (hbudget : state.2.2.creationMass ≤ (budget : ENNReal))
    (hcalls : state.2.2.creationMass ≤ (state.2.1.2 : ENNReal)) :
    (certificateShadowUpdate key budget required stopAfter input state length
      record).2.creationMass ≤ (budget : ENNReal) ∧
    (certificateShadowUpdate key budget required stopAfter input state length
      record).2.creationMass ≤
      ((certificateShadowUpdate key budget required stopAfter input state length
        record).1.2 : ENNReal) := by
  by_cases hcost : state.2.1.2 + record.trace.hashCalls ≤ budget
  · have hstep := (certificateMonitorUpdate_le_hashCalls key budget required
      stopAfter input (state.1, state.2.2) length record hr).2
    simp only [certificateShadowUpdate, if_pos hcost, certificateCountedUpdate] at hstep ⊢
    constructor
    · calc
        _ ≤ (state.2.2.creationMass + record.trace.hashCalls) := hstep
        _ ≤ (state.2.1.2 + record.trace.hashCalls : Nat) := by
          simpa only [Nat.cast_add] using
            (add_le_add hcalls (le_refl (record.trace.hashCalls : ENNReal)))
        _ ≤ (budget : ENNReal) := Nat.cast_le.mpr hcost
    · exact hstep.trans (by
        simpa only [certificateShadowActualProject, Nat.cast_add] using
          (add_le_add hcalls (le_refl (record.trace.hashCalls : ENNReal))))
  · simp only [certificateShadowUpdate, if_neg hcost, certificateCountedUpdate]
    exact ⟨hbudget, hcalls.trans (Nat.cast_le.mpr (Nat.le_add_right _ _))⟩

theorem certificateShadowLength_run_good {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) (hpre : state.2.2 = state.2.1.1.1)
    (result : α × CertificateShadowState)
    (hr : result ∈ ((simulateQ (certificateShadowLengthImpl key budget required
      stopAfter) computation).run state).support)
    (hcost : result.2.2.1.2 ≤ budget) :
    result.2.2.2 = result.2.2.1.1.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hpre
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateShadowLengthImpl_support key budget required stopAfter input state
          middle hmiddle
      let after := originalProposalAdvance (certificateShadowUpdate key budget required
        stopAfter) input state length record
      have htail := certificateShadowLength_run_calls_monotone key budget required
        stopAfter (next record.output) after result hr
      have hstep : state.2.1.2 + record.trace.hashCalls ≤ budget := by
        change state.2.1.2 + record.trace.hashCalls ≤ result.2.2.1.2 at htail
        omega
      have hafter : after.2.2 = after.2.1.1.1 :=
        certificateShadowUpdate_good key budget required stopAfter input state length
          record hpre hstep
      exact ih record.output after hafter result hr hcost

theorem certificateShadowLength_run_mass_budget {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState)
    (hbudget : state.2.2.creationMass ≤ (budget : ENNReal))
    (hcalls : state.2.2.creationMass ≤ (state.2.1.2 : ENNReal))
    (result : α × CertificateShadowState)
    (hr : result ∈ ((simulateQ (certificateShadowLengthImpl key budget required
      stopAfter) computation).run state).support) :
    result.2.2.2.creationMass ≤ (budget : ENNReal) ∧
    result.2.2.2.creationMass ≤ (result.2.2.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨hbudget, hcalls⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateShadowLengthImpl_support key budget required stopAfter input state
          middle hmiddle
      have hnext := certificateShadowUpdate_mass_budget key budget required stopAfter
        input state length record hrecord hbudget hcalls
      exact ih record.output _ hnext.1 hnext.2 result hr

theorem certificateShadowProposal_run_mass_budget {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateShadowState)
    (hbudget : state.2.2.2.creationMass ≤ (budget : ENNReal))
    (hcalls : state.2.2.2.creationMass ≤ (state.2.2.1.2 : ENNReal))
    (result : α × (List Index × CertificateShadowState))
    (hr : result ∈ ((simulateQ (certificateShadowProposalImpl key budget required
      stopAfter) computation).run state).support) :
    result.2.2.2.2.creationMass ≤ (budget : ENNReal) ∧
    result.2.2.2.2.creationMass ≤ (result.2.2.2.1.2 : ENNReal) := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr
    ⟨result, hr, rfl⟩
  unfold certificateShadowProposalImpl at hm
  rw [← PMF.monad_map_eq_map, simulateQ_originalProposalImpl_length] at hm
  exact certificateShadowLength_run_mass_budget key budget required stopAfter
    computation state.2 hbudget hcalls _ hm

theorem certificateShadowProposal_run_good {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateShadowState)
    (hpre : state.2.2.2 = state.2.2.1.1.1)
    (result : α × (List Index × CertificateShadowState))
    (hr : result ∈ ((simulateQ (certificateShadowProposalImpl key budget required
      stopAfter) computation).run state).support)
    (hcost : result.2.2.2.1.2 ≤ budget) :
    result.2.2.2.2 = result.2.2.2.1.1.1 := by
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr
    ⟨result, hr, rfl⟩
  unfold certificateShadowProposalImpl at hm
  rw [← PMF.monad_map_eq_map, simulateQ_originalProposalImpl_length] at hm
  exact certificateShadowLength_run_good key budget required stopAfter computation
    state.2 hpre _ hm hcost

theorem certificateShadowProposalImpl_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : List Index × CertificateShadowState) :
    Prod.map id (Prod.map id certificateShadowActualProject) <$>
      (certificateShadowProposalImpl key budget required stopAfter input).run state =
    (certificateCountedProposalImpl key budget required stopAfter input).run
      (state.1, certificateShadowActualProject state.2) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateShadowProposalImpl, certificateCountedProposalImpl,
        originalProposalImpl, proposalRecordImpl, StateT.run_mk,
        originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateShadowProposalImpl, certificateCountedProposalImpl,
        originalProposalImpl, proposalRecordImpl, StateT.run_mk,
        originalProposalActive, certificateShadowActualProject]
      by_cases h : (certificateMonitorEnabled key budget message
        (certificateCacheMonitorProject (certificateCountedProject
          (certificateShadowActualProject state.2))) &&
        decide (ProposalCacheBound key state.2.1 state.2.2.1.1.1.spent)) = true
      · simp only [certificateShadowActualProject, certificateCountedProject] at h ⊢
        simp only [h, if_true, PMF.map_comp]
        rfl
      · simp only [certificateShadowActualProject, certificateCountedProject] at h ⊢
        simp only [h, if_false, Bool.false_eq_true, PMF.map_comp]
        rfl

theorem simulateQ_certificateShadowProposalImpl_project {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateShadowState) :
    Prod.map id (Prod.map id certificateShadowActualProject) <$>
      (simulateQ (certificateShadowProposalImpl key budget required stopAfter)
        computation).run state =
    (simulateQ (certificateCountedProposalImpl key budget required stopAfter)
      computation).run (state.1, certificateShadowActualProject state.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.map id certificateShadowActualProject)
    (certificateShadowProposalImpl_project key budget required stopAfter)
    computation state

abbrev CertificateShadowContextResult := SecretKey ×
  (RetainedRestResult × (List Index × CertificateShadowState))

def CertificateShadowContextResult.actual (result : CertificateShadowContextResult) :
    CertificateCountedContextResult :=
  (result.1, (result.2.1,
    (result.2.2.1, certificateShadowActualProject result.2.2.2)))

noncomputable def certificateShadowContextGame (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    PMF CertificateShadowContextResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  let initial := initialCertificateMonitor generated.1.2.hashCalls stopped
  let result ← (simulateQ (certificateShadowProposalImpl key budget required
    (stopAfter key))
    (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)).run
      ([], (generated.2, (((initial, false), generated.1.2.hashCalls), initial)))
  pure (key, result)

theorem certificateShadowContextGame_actual (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    CertificateShadowContextResult.actual <$>
      certificateShadowContextGame adversary budget required stopAfter stopped =
    certificateCountedContextGame adversary budget required stopAfter stopped := by
  simp only [certificateShadowContextGame, certificateCountedContextGame,
    map_bind, map_pure]
  apply PMF.bind_congr
  intro generated _
  simp only [bind_pure_comp]
  have h := congrArg (Functor.map (Prod.mk generated.1.1.2))
    (simulateQ_certificateShadowProposalImpl_project generated.1.1.2 budget required
      (stopAfter generated.1.1.2)
      (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
      ([], (generated.2, (((initialCertificateMonitor generated.1.2.hashCalls stopped,
        false), generated.1.2.hashCalls),
        initialCertificateMonitor generated.1.2.hashCalls stopped))))
  simpa only [Functor.map_map, CertificateShadowContextResult.actual,
    Function.comp_def, Prod.map, id_eq, certificateShadowActualProject] using h

theorem certificateShadowContextGame_good (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (result : CertificateShadowContextResult)
    (hr : result ∈ (certificateShadowContextGame adversary budget required
      stopAfter stopped).support)
    (hcost : result.actual.originalCost.2 ≤ budget) :
    result.2.2.2.2.2 = result.2.2.2.2.1.1.1 := by
  rw [certificateShadowContextGame, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  exact certificateShadowProposal_run_good generated.1.1.2 budget required
    (stopAfter generated.1.1.2)
    (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
    ([], (generated.2, (((initialCertificateMonitor
      generated.1.2.hashCalls stopped, false), generated.1.2.hashCalls),
      initialCertificateMonitor generated.1.2.hashCalls stopped)))
    rfl output houtput hcost

theorem certificateShadowContextGame_mass_budget (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (result : CertificateShadowContextResult)
    (hr : result ∈ (certificateShadowContextGame adversary budget required
      stopAfter stopped).support) :
    result.2.2.2.2.2.creationMass ≤ (budget : ENNReal) := by
  rw [certificateShadowContextGame, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  rw [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨output, houtput, hr⟩ := hr
  rw [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  subst result
  exact (certificateShadowProposal_run_mass_budget generated.1.1.2 budget required
    (stopAfter generated.1.1.2)
    (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
    ([], (generated.2, (((initialCertificateMonitor
      generated.1.2.hashCalls stopped, false), generated.1.2.hashCalls),
      initialCertificateMonitor generated.1.2.hashCalls stopped)))
    (by simp only [initialCertificateMonitor, zero_le])
    (by simp only [initialCertificateMonitor, zero_le])
    output houtput).1

private theorem certificateBankCount_mono (before after : HashInput → Bool)
    (hpointwise : ∀ input, before input = true → after input = true) :
    certificateBankCount before ≤ certificateBankCount after := by
  unfold certificateBankCount
  apply ENNReal.tsum_le_tsum
  intro input
  cases h : before input with
  | false => exact zero_le
  | true =>
      simp only [if_true, hpointwise input h]
      exact le_rfl

private theorem certificateMonitorUpdate_bank_mono (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) :
    certificateBankCount state.2.bank ≤
      certificateBankCount
        (certificateMonitorUpdate key budget required stopAfter input state length record).bank := by
  apply certificateBankCount_mono
  intro query hbank
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive, completedTargetBank,
      hbank, Bool.true_or]
  · simp only [certificateMonitorUpdate, if_neg hactive, hbank]

private theorem certificateBankCount_le_monitorPotential (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree)
    (state : CertificateMonitorState) :
    certificateBankCount state.2.bank ≤
      certificateMonitorPotential key budget required state := by
  unfold certificateMonitorPotential bankedTargetEnvelope
  exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

private theorem certificateMonitorUpdate_bank_le_potential (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) :
    certificateBankCount state.2.bank ≤
      certificateMonitorPotential key budget required
        (record.cache, certificateMonitorUpdate key budget required stopAfter
          input state length record) := by
  exact (certificateMonitorUpdate_bank_mono key budget required stopAfter input state
    length record).trans (certificateBankCount_le_monitorPotential key budget required _)

private theorem certificateShadowUpdate_potential_le_actual (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (hpre : state.2.2 = state.2.1.1.1) :
    certificateMonitorPotential key budget required
      (record.cache, (certificateShadowUpdate key budget required stopAfter input
        state length record).2) ≤
    certificateMonitorPotential key budget required
      (record.cache, (certificateShadowUpdate key budget required stopAfter input
        state length record).1.1.1) := by
  by_cases hcost : state.2.1.2 + record.trace.hashCalls ≤ budget
  · rw [certificateShadowUpdate_good key budget required stopAfter input state
      length record hpre hcost]
  · simp only [certificateShadowUpdate, if_neg hcost, certificateCountedUpdate,
      certificateCacheMonitorUpdate, certificateMonitorPotential,
      bankedTargetEnvelope_stopped]
    rw [hpre]
    exact certificateMonitorUpdate_bank_le_potential key budget required stopAfter
      input (certificateCacheMonitorProject
        (certificateCountedProject (certificateShadowActualProject state))) length record

private theorem pmf_expected_le_of_support {α : Type} (law : PMF α)
    (first second : α → ENNReal)
    (hle : ∀ result ∈ law.support, first result ≤ second result) :
    (∑' result, Pr[= result | law] * first result) ≤
      ∑' result, Pr[= result | law] * second result := by
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (hle result hr)
  · have hz : Pr[= result | law] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hz, zero_mul, zero_mul]

theorem expected_certificateShadowLengthImpl_potential_le_of_equal
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState)
    (hpre : state.2.2 = state.2.1.1.1) :
    (∑' result,
      Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
        input).run state] *
      certificateMonitorPotential key budget required (result.2.1, result.2.2.2)) ≤
    certificateMonitorPotential key budget required (state.1, state.2.2) +
      certificateMonitorCharge key budget required input (state.1, state.2.2) := by
  let law := (certificateShadowLengthImpl key budget required stopAfter input).run state
  have hpoint :
      (∑' result, Pr[= result | law] *
        certificateMonitorPotential key budget required (result.2.1, result.2.2.2)) ≤
      ∑' result, Pr[= result | law] *
        certificateMonitorPotential key budget required
          (certificateShadowMonitorProject result.2) := by
    apply pmf_expected_le_of_support
    intro result hr
    obtain ⟨length, record, _, rfl⟩ := certificateShadowLengthImpl_support
      key budget required stopAfter input state result hr
    exact certificateShadowUpdate_potential_le_actual key budget required
      stopAfter input state length record hpre
  have hproject := congrArg
    (fun law : PMF ((OracleWorld + SigningSpec).Range input × CertificateMonitorState) =>
      ∑' result, Pr[= result | law] * certificateMonitorPotential key budget required result.2)
    (certificateShadowLengthImpl_monitor_project key budget required stopAfter input state)
  rw [tsum_probOutput_map_mul] at hproject
  calc
    _ ≤ _ := hpoint
    _ = ∑' result,
        Pr[= result | (certificateLengthImpl key budget required stopAfter input).run
          (certificateShadowMonitorProject state)] *
        certificateMonitorPotential key budget required result.2 := hproject
    _ ≤ certificateMonitorPotential key budget required
        (certificateShadowMonitorProject state) +
        certificateMonitorCharge key budget required input
          (certificateShadowMonitorProject state) :=
      expected_certificateLengthImpl_potential_le key budget required stopAfter
        input (certificateShadowMonitorProject state)
    _ = _ := by simp only [certificateShadowMonitorProject,
        certificateShadowActualProject, certificateCountedProject,
        certificateCacheMonitorProject, hpre]

private theorem certificateShadowUpdate_stopped (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (hstop : state.2.2.stopped = true) :
    (certificateShadowUpdate key budget required stopAfter input state length
      record).2 = state.2.2 := by
  by_cases hcost : state.2.1.2 + record.trace.hashCalls ≤ budget
  · simp only [certificateShadowUpdate, if_pos hcost]
    exact certificateMonitorUpdate_stopped key budget required stopAfter input
      (state.1, state.2.2) length record hstop
  · simp only [certificateShadowUpdate, if_neg hcost]
    cases hs : state.2.2 with
    | mk log spent messageCalls proposals creationMass creationCost bank stopped =>
        rw [hs] at hstop
        have hstopped : stopped = true := by simpa using hstop
        subst stopped
        rfl

private theorem pmf_expected_const_of_support {α : Type} (law : PMF α)
    (value : α → ENNReal) (constant : ENNReal)
    (hconstant : ∀ result ∈ law.support, value result = constant) :
    (∑' result, Pr[= result | law] * value result) = constant := by
  calc
    _ = ∑' result, Pr[= result | law] * constant := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ law.support
      · rw [hconstant result hr]
      · have hz : Pr[= result | law] = 0 := by
          rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
          exact hr
        rw [hz, zero_mul, zero_mul]
    _ = constant := by
      simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply,
        PMF.tsum_coe, one_mul]

theorem expected_certificateShadowLengthImpl_potential_le_of_stopped
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState)
    (hstop : state.2.2.stopped = true) :
    (∑' result,
      Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
        input).run state] *
      certificateMonitorPotential key budget required (result.2.1, result.2.2.2)) ≤
    certificateMonitorPotential key budget required (state.1, state.2.2) +
      certificateMonitorCharge key budget required input (state.1, state.2.2) := by
  have hconstant := pmf_expected_const_of_support
    ((certificateShadowLengthImpl key budget required stopAfter input).run state)
    (fun result => certificateMonitorPotential key budget required
      (result.2.1, result.2.2.2))
    (certificateBankCount state.2.2.bank) (by
      intro result hr
      obtain ⟨length, record, _, rfl⟩ := certificateShadowLengthImpl_support
        key budget required stopAfter input state result hr
      change certificateMonitorPotential key budget required
        (record.cache, (certificateShadowUpdate key budget required stopAfter
          input state length record).2) = certificateBankCount state.2.2.bank
      rw [certificateShadowUpdate_stopped key budget required stopAfter input state
        length record hstop]
      simp only [certificateMonitorPotential, hstop, bankedTargetEnvelope_stopped])
  have hinactive : ¬ CertificateMonitorActive key budget input (state.1, state.2.2) := by
    intro hactive
    have h := hactive.1
    rw [hstop] at h
    exact Bool.noConfusion h
  rw [hconstant]
  simp only [certificateMonitorPotential, hstop, bankedTargetEnvelope_stopped,
    certificateMonitorCharge, if_neg hinactive, add_zero]
  exact le_rfl

theorem certificateShadowUpdate_invariant (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hinv : state.2.2 = state.2.1.1.1 ∨ state.2.2.stopped = true) :
    (certificateShadowUpdate key budget required stopAfter input state length record).2 =
      (certificateShadowUpdate key budget required stopAfter input state length record).1.1.1 ∨
    (certificateShadowUpdate key budget required stopAfter input state length record).2.stopped =
      true := by
  rcases hinv with heq | hstop
  · by_cases hbudget : state.2.1.2 + record.trace.hashCalls ≤ budget
    · exact Or.inl (certificateShadowUpdate_good key budget required stopAfter input
        state length record heq hbudget)
    · right
      simp only [certificateShadowUpdate, if_neg hbudget]
  · right
    rw [certificateShadowUpdate_stopped key budget required stopAfter input state
      length record hstop]
    exact hstop

theorem certificateShadowLengthImpl_invariant (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateShadowState)
    (hinv : state.2.2 = state.2.1.1.1 ∨ state.2.2.stopped = true)
    (result : (OracleWorld + SigningSpec).Range input × CertificateShadowState)
    (hr : result ∈ ((certificateShadowLengthImpl key budget required stopAfter input).run
      state).support) :
    result.2.2.2 = result.2.2.1.1.1 ∨ result.2.2.2.stopped = true := by
  obtain ⟨length, record, _, rfl⟩ := certificateShadowLengthImpl_support
    key budget required stopAfter input state result hr
  exact certificateShadowUpdate_invariant key budget required stopAfter input state
    length record hinv

theorem expected_certificateShadowLengthImpl_potential_le
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState)
    (hinv : state.2.2 = state.2.1.1.1 ∨ state.2.2.stopped = true) :
    (∑' result,
      Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
        input).run state] *
      certificateMonitorPotential key budget required (result.2.1, result.2.2.2)) ≤
    certificateMonitorPotential key budget required (state.1, state.2.2) +
      certificateMonitorCharge key budget required input (state.1, state.2.2) := by
  rcases hinv with heq | hstop
  · exact expected_certificateShadowLengthImpl_potential_le_of_equal key budget
      required stopAfter input state heq
  · exact expected_certificateShadowLengthImpl_potential_le_of_stopped key budget
      required stopAfter input state hstop

noncomputable def expectedShadowCharge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    CertificateShadowState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state =>
      certificateMonitorCharge key budget required input (state.1, state.2.2) +
        ∑' result,
          Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
            input).run state] * next result.1 result.2) computation

@[simp] theorem expectedShadowCharge_pure {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (value : α) (state : CertificateShadowState) :
    expectedShadowCharge key budget required stopAfter (pure value) state = 0 := rfl

theorem expectedShadowCharge_query_bind {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) :
    expectedShadowCharge key budget required stopAfter
      (OracleSpec.query input >>= next) state =
    certificateMonitorCharge key budget required input (state.1, state.2.2) +
      ∑' result,
        Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
          input).run state] *
          expectedShadowCharge key budget required stopAfter (next result.1)
            result.2 := rfl

/-- Optional stopping lifts the shadow-bank potential bound through any adaptive
oracle computation, while the actual execution continues after the shadow stops. -/
theorem expected_certificateShadow_potential_le_initial_add_charge {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState)
    (hinv : state.2.2 = state.2.1.1.1 ∨ state.2.2.stopped = true) :
    (∑' result,
      Pr[= result | (simulateQ (certificateShadowLengthImpl key budget required
        stopAfter) computation).run state] *
      certificateMonitorPotential key budget required (result.2.1, result.2.2.2)) ≤
    certificateMonitorPotential key budget required (state.1, state.2.2) +
      expectedShadowCharge key budget required stopAfter computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        expectedShadowCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        tsum_probOutput_bind_mul, expectedShadowCharge_query_bind]
      let law := (certificateShadowLengthImpl key budget required stopAfter input).run
        state
      calc
        _ ≤ ∑' result, Pr[= result | law] *
            (certificateMonitorPotential key budget required
                (result.2.1, result.2.2.2) +
              expectedShadowCharge key budget required stopAfter (next result.1)
                result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ law.support
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2
                (certificateShadowLengthImpl_invariant key budget required
                  stopAfter input state hinv result hr))
          · have hz : Pr[= result | law] = 0 := by
              rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
              exact hr
            dsimp only [law] at hz
            simp only [hz, zero_mul]
            exact zero_le
        _ = (∑' result, Pr[= result | law] *
              certificateMonitorPotential key budget required
                (result.2.1, result.2.2.2)) +
            ∑' result, Pr[= result | law] *
              expectedShadowCharge key budget required stopAfter (next result.1)
                result.2 := by simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (certificateMonitorPotential key budget required
              (state.1, state.2.2) +
            certificateMonitorCharge key budget required input
              (state.1, state.2.2)) +
            ∑' result, Pr[= result | law] *
              expectedShadowCharge key budget required stopAfter (next result.1)
                result.2 :=
          add_le_add
            (expected_certificateShadowLengthImpl_potential_le key budget required
              stopAfter input state hinv) le_rfl
        _ = _ := by rw [add_assoc]

/-- The shadow bank itself is bounded by the adaptive potential charge. This
bound does not assume that the actual execution stays within the budget. -/
private theorem targetCreationMultiplier_le_macroCost (key : SecretKey)
    (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetCreationMultiplier key cache input ≤ signingMacroHashCost input := by
  cases input with
  | inl world =>
      cases world with
      | inl sample => simp [targetCreationMultiplier, freshWorldTargetHashCost,
          signingMacroHashCost]
      | inr hashInput =>
          simp only [targetCreationMultiplier, signingMacroHashCost,
            freshWorldTargetHashCost]
          split_ifs <;> norm_num
  | inr message =>
      simp only [targetCreationMultiplier, signingMacroHashCost]
      simpa only [mul_one] using
        mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)))
          (freshDigestSelectionProbability_le_one key message cache)

/-- A final signing macro may exceed the true hash budget, but its booked
creation mass still fits: activation reserves the macro's minimum cost. -/
theorem certificateMonitorUpdate_creationMass_le_budget (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (hspent : state.2.creationMass ≤ (state.2.spent : ENNReal))
    (hbudget : state.2.creationMass ≤ (budget : ENNReal)) :
    (certificateMonitorUpdate key budget required stopAfter input state
      length record).creationMass ≤ (budget : ENNReal) := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · have hremaining : signingMacroHashCost input ≤ budget - state.2.spent :=
      hactive.2.2.2
    have hspentBudget : state.2.spent ≤ budget := hactive.2.1.2.2
    have hnat : state.2.spent + signingMacroHashCost input ≤ budget := by omega
    calc
      _ = state.2.creationMass + targetCreationMultiplier key state.1 input := by
        simp only [certificateMonitorUpdate, if_pos hactive]
      _ ≤ (state.2.spent : ENNReal) +
          (signingMacroHashCost input : ENNReal) :=
        add_le_add hspent (targetCreationMultiplier_le_macroCost key state.1 input)
      _ = ((state.2.spent + signingMacroHashCost input : Nat) : ENNReal) := by
        rw [Nat.cast_add]
      _ ≤ (budget : ENNReal) := Nat.cast_le.mpr hnat
  · simpa only [certificateMonitorUpdate, if_neg hactive] using hbudget

/-- The monitor's creation mass never exceeds its nominal budget, on any
adaptive transcript, even when the final recorded hash count overshoots. -/
theorem certificateLength_run_creationMass_le_budget {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateMonitorState)
    (hspent : state.2.creationMass ≤ (state.2.spent : ENNReal))
    (hbudget : state.2.creationMass ≤ (budget : ENNReal))
    (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required
      stopAfter) computation).run state).support) :
    result.2.2.creationMass ≤ (budget : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hbudget
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state
          middle hmiddle
      have hnextSpent := certificateMonitorUpdate_mass_le_spent key budget
        required stopAfter input state length record hspent hrecord
      have hnextBudget := certificateMonitorUpdate_creationMass_le_budget key
        budget required stopAfter input state length record hspent hbudget
      exact ih record.output (record.cache,
        certificateMonitorUpdate key budget required stopAfter input state
          length record) hnextSpent hnextBudget result hr

theorem certificateProposal_run_creationMass_le_budget {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateMonitorState)
    (hspent : state.2.2.creationMass ≤ (state.2.2.spent : ENNReal))
    (hbudget : state.2.2.creationMass ≤ (budget : ENNReal))
    (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required
      stopAfter) computation).run state).support) :
    result.2.2.2.creationMass ≤ (budget : ENNReal) := by
  have hprojection := simulateQ_certificateProposalImpl_length key budget
    required stopAfter computation state
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr
    ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, hprojection] at hm
  exact certificateLength_run_creationMass_le_budget key budget required
    stopAfter computation state.2 hspent hbudget _ hm

theorem certificateGame_creationMass_le_budget (adversary : Adversary)
    (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (result : CertificateGameResult)
    (hr : result ∈ (certificateGame adversary budget required stopAfter
      stopped).support) :
    result.2.2.2.creationMass ≤ (budget : ENNReal) := by
  rw [certificateGame, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hresult⟩ := hr
  exact certificateProposal_run_creationMass_le_budget
    generated.1.1.2 budget required (stopAfter generated.1.1.2)
    (FtsProbeSimulation.retainedGameRestComputation adversary
      generated.1.1.1)
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls
      stopped) (by simp only [initialCertificateMonitor, zero_le])
    (by simp only [initialCertificateMonitor, zero_le]) result hresult

/-- The independent terminal proposal word still amortizes creation mass
without any support-wide hash-call cutoff. -/
theorem expected_certificateTerminalGame_mass_payoff_le_unconditionally
    (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (total : Nat) (payoff : List Index → ENNReal) :
    (∑' result,
      Pr[= result | certificateTerminalGame adversary q required stopAfter
        stopped total] *
        (result.1.2.2.2.creationMass * payoff result.2)) ≤
      (q : ENNReal) *
        ∑' word, Pr[= word | independentProposalWord
          (PMF.uniformOfFintype Index) total] * payoff word := by
  have hword := congrArg
    (fun law : PMF (List Index) =>
      ∑' word, Pr[= word | law] * payoff word)
    (certificateTerminalGame_word adversary q required stopAfter stopped total)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hword
  calc
    _ ≤ ∑' result, (q : ENNReal) *
        (Pr[= result | certificateTerminalGame adversary q required stopAfter
          stopped total] * payoff result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hzero : Pr[= result | certificateTerminalGame adversary q
          required stopAfter stopped total] = 0
      · rw [hzero, zero_mul, zero_mul, mul_zero]
      · have hr : result ∈ (certificateTerminalGame adversary q required
            stopAfter stopped total).support := by
          simpa only [PMF.mem_support_iff, PMF.probOutput_eq_apply] using hzero
        have hm := (PMF.mem_support_map_iff Prod.fst _ _).mpr
          ⟨result, hr, rfl⟩
        rw [certificateTerminalGame_game] at hm
        have hmass := certificateGame_creationMass_le_budget adversary q
          required stopAfter stopped result.1 hm
        calc
          _ ≤ Pr[= result | certificateTerminalGame adversary q required
                stopAfter stopped total] *
              ((q : ENNReal) * payoff result.2) :=
            mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)
          _ = _ := by ring
    _ = _ := by rw [ENNReal.tsum_mul_left, hword]

theorem expected_certificateTerminalGame_count_le_q_average_price
    (adversary : Adversary) (q total : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (hbudget : q ≤ 2 ^ 128) :
    (∑' result,
      Pr[= result | certificateTerminalGame adversary q required
        (fun key input state length record =>
          proposalPrefixStop input state length record ||
            stopAfter key input state length record)
        (decide (total < fixedProposalLength)) total] *
          certificateBankCount result.1.2.2.2.bank) ≤
      (q : ENNReal) *
        ∑' word, Pr[= word | independentProposalWord
          (PMF.uniformOfFintype Index) total] *
            terminalCertificatePrice required word := by
  exact (expected_certificateTerminalGame_count_le_mass_price adversary q
    total required stopAfter hbudget).trans
    (expected_certificateTerminalGame_mass_payoff_le_unconditionally adversary
      q required
      (fun key input state length record =>
        proposalPrefixStop input state length record ||
          stopAfter key input state length record)
      (decide (total < fixedProposalLength)) total
      (terminalCertificatePrice required))

theorem expected_certificateCounted_budget_bank_le_game_bank
    (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result,
      Pr[= result | certificateCountedContextGame adversary q required
        stopAfter stopped] * CertificateCountedWeightedBank q result) ≤
      ∑' result,
        Pr[= result | certificateGame adversary q required stopAfter
          stopped] * certificateBankCount result.2.2.2.bank := by
  rw [← certificateCountedContextGame_game, tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  apply mul_le_mul' le_rfl
  by_cases hcost : result.originalCost.2 ≤ q
  · simp only [CertificateCountedWeightedBank, hcost, if_true]
    exact le_rfl
  · simp only [CertificateCountedWeightedBank, hcost, if_false]
    exact zero_le

theorem expected_certificateGame_bank_le_q_terminal_average
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128) :
    (∑' result,
      Pr[= result | certificateGame adversary q Finset.univ
        (fun _ => proposalPrefixStop) false] *
          certificateBankCount result.2.2.2.bank) ≤
      (q : ENNReal) *
        ∑' word, Pr[= word | independentProposalWord
          (PMF.uniformOfFintype Index) fixedProposalLength] *
            terminalCertificatePrice Finset.univ word := by
  rw [← expected_certificateTerminalGame_project adversary q Finset.univ
    (fun _ => proposalPrefixStop) false fixedProposalLength
    (fun result => certificateBankCount result.2.2.2.bank)]
  simpa only [Bool.or_false, Nat.lt_irrefl, decide_false] using
    (expected_certificateTerminalGame_count_le_q_average_price adversary q
      fixedProposalLength Finset.univ
      (fun _ _ _ _ _ => false) hbudget)

theorem uniformWordAverage_full_price_le_total_rate :
    uniformWordAverage fixedProposalLength
      (terminalCertificatePrice Finset.univ) ≤
        fullCertificateTotalRate := by
  let baseline : ENNReal := (2 ^ 144 : ENNReal)⁻¹
  calc
    _ ≤ uniformWordAverage fixedProposalLength
        (fun word => baseline +
          (terminalCertificatePrice Finset.univ word - baseline)) := by
      apply uniformWordAverage_mono
      intro word
      exact le_add_tsub
    _ = baseline + uniformWordAverage fixedProposalLength
        (fun word => terminalCertificatePrice Finset.univ word - baseline) := by
      rw [uniformWordAverage_add, uniformWordAverage_const]
    _ ≤ baseline + fullCertificateExcessRate :=
      add_le_add le_rfl uniformWordAverage_full_price_excess_le
    _ = fullCertificateTotalRate := by
      rw [fullCertificateTotalRate_def]

theorem expected_certificateGame_bank_le_q_total_rate
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128) :
    (∑' result,
      Pr[= result | certificateGame adversary q Finset.univ
        (fun _ => proposalPrefixStop) false] *
          certificateBankCount result.2.2.2.bank) ≤
      (q : ENNReal) * fullCertificateTotalRate := by
  calc
    _ ≤ (q : ENNReal) *
        ∑' word, Pr[= word | independentProposalWord
          (PMF.uniformOfFintype Index) fixedProposalLength] *
            terminalCertificatePrice Finset.univ word :=
      expected_certificateGame_bank_le_q_terminal_average adversary q hbudget
    _ = (q : ENNReal) * uniformWordAverage fixedProposalLength
          (terminalCertificatePrice Finset.univ) := by
      rw [uniformWordAverage_eq_independent]
    _ ≤ (q : ENNReal) * fullCertificateTotalRate :=
      mul_le_mul' le_rfl uniformWordAverage_full_price_le_total_rate

theorem originalCertificate_budget_le_q_total_rate_add_exception
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128) :
    Pr[OriginalBudgetedFullCertificate q |
      originalCertificateCountedSource adversary] ≤
      (q : ENNReal) * fullCertificateTotalRate +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] := by
  calc
    _ ≤ (∑' result,
        Pr[= result | certificateCountedContextGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] *
          CertificateCountedWeightedBank q result) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] :=
      originalCertificateCountedSource_full_budget_le_count_add_exception
        adversary q hbudget
    _ ≤ (∑' result,
        Pr[= result | certificateGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] *
          certificateBankCount result.2.2.2.bank) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] :=
      add_le_add
        (expected_certificateCounted_budget_bank_le_game_bank adversary q
          Finset.univ (fun _ => proposalPrefixStop) false) le_rfl
    _ ≤ _ :=
      add_le_add
        (expected_certificateGame_bank_le_q_total_rate adversary q hbudget)
        le_rfl

private theorem certificateShadowUpdate_balance (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (hbalance : state.2.2.spent = state.2.1.2 ∨ state.2.2.stopped = true) :
    (certificateShadowUpdate key budget required stopAfter input state
      length record).2.spent =
        (certificateShadowUpdate key budget required stopAfter input state
          length record).1.2 ∨
    (certificateShadowUpdate key budget required stopAfter input state
      length record).2.stopped = true := by
  by_cases hcost : state.2.1.2 + record.trace.hashCalls ≤ budget
  · by_cases hactive : CertificateMonitorActive key budget input (state.1, state.2.2)
    · have heq : state.2.2.spent = state.2.1.2 := by
        rcases hbalance with heq | hstop
        · exact heq
        · have hlive := hactive.1
          rw [hstop] at hlive
          exact Bool.noConfusion hlive
      left
      simp only [certificateShadowUpdate, if_pos hcost,
        certificateMonitorUpdate, if_pos hactive, certificateCountedUpdate,
        certificateCacheMonitorUpdate, certificateShadowActualProject]
      omega
    · right
      simp only [certificateShadowUpdate, if_pos hcost,
        certificateMonitorUpdate, if_neg hactive]
  · right
    simp only [certificateShadowUpdate, if_neg hcost]

private theorem certificateShadowStepMass_le_remaining (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateShadowState) (length : Nat)
    (record : ProposalExecutionRecord input)
    (hbalance : state.2.2.spent = state.2.1.2 ∨ state.2.2.stopped = true)
    (hrecord : record ∈ (originalProposalRecord key input state.1).support) :
    certificateMonitorMass key budget input (state.1, state.2.2) +
      ((budget - (certificateShadowUpdate key budget required stopAfter input state
        length record).1.2 : Nat) : ENNReal) ≤
      ((budget - state.2.1.2 : Nat) : ENNReal) := by
  have hmin := signingMacroHashCost_le_record key input state.1 record hrecord
  have hcost : (certificateShadowUpdate key budget required stopAfter input state
      length record).1.2 = state.2.1.2 + record.trace.hashCalls := rfl
  rw [hcost]
  by_cases hactive : CertificateMonitorActive key budget input (state.1, state.2.2)
  · have heq : state.2.2.spent = state.2.1.2 := by
      rcases hbalance with heq | hstop
      · exact heq
      · have hlive := hactive.1
        rw [hstop] at hlive
        exact Bool.noConfusion hlive
    have hspent : state.2.1.2 ≤ budget := by
      rw [← heq]
      exact hactive.2.1.2.2
    have hmacro : signingMacroHashCost input ≤ budget - state.2.1.2 := by
      rw [← heq]
      exact hactive.2.2.2
    have hnat : signingMacroHashCost input +
        (budget - (state.2.1.2 + record.trace.hashCalls)) ≤
        budget - state.2.1.2 := by omega
    have hmass : certificateMonitorMass key budget input (state.1, state.2.2) ≤
        (signingMacroHashCost input : ENNReal) := by
      simpa only [certificateMonitorMass, if_pos hactive] using
        targetCreationMultiplier_le_macroCost key state.1 input
    calc
      _ ≤ (signingMacroHashCost input : ENNReal) +
          ((budget - (state.2.1.2 + record.trace.hashCalls) : Nat) : ENNReal) :=
        add_le_add hmass le_rfl
      _ ≤ ((budget - state.2.1.2 : Nat) : ENNReal) := by
        exact_mod_cast hnat
  · simp only [certificateMonitorMass, if_neg hactive, zero_add]
    exact Nat.cast_le.mpr (by omega)

noncomputable def expectedShadowMass {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    CertificateShadowState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state =>
      certificateMonitorMass key budget input (state.1, state.2.2) +
        ∑' result,
          Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
            input).run state] * next result.1 result.2) computation

@[simp] theorem expectedShadowMass_pure {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (value : α) (state : CertificateShadowState) :
    expectedShadowMass key budget required stopAfter (pure value) state = 0 := rfl

theorem expectedShadowMass_query_bind {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) :
    expectedShadowMass key budget required stopAfter
      (OracleSpec.query input >>= next) state =
    certificateMonitorMass key budget input (state.1, state.2.2) +
      ∑' result,
        Pr[= result | (certificateShadowLengthImpl key budget required stopAfter
          input).run state] *
          expectedShadowMass key budget required stopAfter (next result.1)
            result.2 := rfl

/-- The virtual charge cannot book more than the remaining global hash budget,
even when the last signing macro overshoots it. -/
theorem expectedShadowMass_le_remaining {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState)
    (hbalance : state.2.2.spent = state.2.1.2 ∨ state.2.2.stopped = true) :
    expectedShadowMass key budget required stopAfter computation state ≤
      ((budget - state.2.1.2 : Nat) : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedShadowMass_pure, zero_le]
  | query_bind input next ih =>
      rw [expectedShadowMass_query_bind]
      let law := (certificateShadowLengthImpl key budget required stopAfter input).run
        state
      calc
        _ ≤ certificateMonitorMass key budget input (state.1, state.2.2) +
            ∑' result, Pr[= result | law] *
              ((budget - result.2.2.1.2 : Nat) : ENNReal) := by
          apply add_le_add le_rfl
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ law.support
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2
                (by
                  obtain ⟨length, record, _, rfl⟩ :=
                    certificateShadowLengthImpl_support key budget required
                      stopAfter input state result hr
                  exact certificateShadowUpdate_balance key budget required
                    stopAfter input state length record hbalance))
          · have hz : Pr[= result | law] = 0 := by
              rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
              exact hr
            dsimp only [law] at hz
            simp only [hz, zero_mul]
            exact zero_le
        _ = ∑' result, Pr[= result | law] *
            (certificateMonitorMass key budget input (state.1, state.2.2) +
              ((budget - result.2.2.1.2 : Nat) : ENNReal)) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
            PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
        _ ≤ ((budget - state.2.1.2 : Nat) : ENNReal) := by
          calc
            _ ≤ ∑' _result, Pr[= _result | law] *
                ((budget - state.2.1.2 : Nat) : ENNReal) := by
              apply ENNReal.tsum_le_tsum
              intro result
              by_cases hr : result ∈ law.support
              · obtain ⟨length, record, hrecord, rfl⟩ :=
                  certificateShadowLengthImpl_support key budget required
                    stopAfter input state result hr
                exact mul_le_mul' le_rfl
                  (certificateShadowStepMass_le_remaining key budget required
                    stopAfter input state length record hbalance hrecord)
              · have hz : Pr[= result | law] = 0 := by
                  rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
                  exact hr
                simp only [hz, zero_mul, le_refl]
            _ = _ := by
              simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply,
                PMF.tsum_coe, one_mul]

/-- A uniform upper bound on the creation price converts virtual mass into
the exact adaptive shadow charge, including a final overshooting macro. -/
theorem expectedShadowCharge_le_price_mul_mass {α : Type} (key : SecretKey)
    (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) (price : ENNReal)
    (hprice : ∀ current : CertificateMonitorState,
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - current.2.spent) (signatureLimit - current.2.log.length)
        required (certificateMonitorCoverState current) ≤ price) :
    expectedShadowCharge key budget required stopAfter computation state ≤
      price * expectedShadowMass key budget required stopAfter computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedShadowCharge_pure, expectedShadowMass_pure,
      mul_zero, le_refl]
  | query_bind input next ih =>
      rw [expectedShadowCharge_query_bind, expectedShadowMass_query_bind]
      have hstep : certificateMonitorCharge key budget required input
          (state.1, state.2.2) ≤
          price * certificateMonitorMass key budget input
            (state.1, state.2.2) := by
        by_cases hactive : CertificateMonitorActive key budget input
            (state.1, state.2.2)
        · simp only [certificateMonitorCharge, certificateMonitorMass,
            if_pos hactive]
          calc
            _ ≤ targetCreationMultiplier key state.1 input * price :=
              mul_le_mul' le_rfl (hprice (state.1, state.2.2))
            _ = _ := mul_comm _ _
        · simp only [certificateMonitorCharge, certificateMonitorMass,
            if_neg hactive, mul_zero, le_refl]
      calc
        _ ≤ price * certificateMonitorMass key budget input
              (state.1, state.2.2) +
            ∑' result,
              Pr[= result | (certificateShadowLengthImpl key budget required
                stopAfter input).run state] *
                (price * expectedShadowMass key budget required stopAfter
                  (next result.1) result.2) := by
          apply add_le_add hstep
          apply ENNReal.tsum_le_tsum
          intro result
          exact mul_le_mul' le_rfl (ih result.1 result.2)
        _ = price * (certificateMonitorMass key budget input
              (state.1, state.2.2) +
            ∑' result,
              Pr[= result | (certificateShadowLengthImpl key budget required
                stopAfter input).run state] *
                expectedShadowMass key budget required stopAfter
                  (next result.1) result.2) := by
          rw [mul_add]
          congr 1
          calc
            _ = ∑' result, price *
                (Pr[= result | (certificateShadowLengthImpl key budget required
                  stopAfter input).run state] *
                  expectedShadowMass key budget required stopAfter
                    (next result.1) result.2) := by
              apply tsum_congr
              intro result
              ac_rfl
            _ = _ := by rw [ENNReal.tsum_mul_left]
        _ = _ := rfl

/-- The price bound only needs to hold on an invariant of the shadow run.
This form can use the cache and proposal-prefix invariants of an actual game. -/
theorem expectedShadowCharge_le_price_mul_mass_on_invariant {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) (price : ENNReal)
    (invariant : CertificateShadowState → Prop)
    (hstable : ∀ (input : (OracleWorld + SigningSpec).Domain)
      (current : CertificateShadowState)
      (result : (OracleWorld + SigningSpec).Range input × CertificateShadowState),
      invariant current →
      result ∈ ((certificateShadowLengthImpl key budget required stopAfter input).run
        current).support → invariant result.2)
    (hprice : ∀ current : CertificateShadowState,
      invariant current →
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - current.2.2.spent)
        (signatureLimit - current.2.2.log.length) required
        (certificateMonitorCoverState (current.1, current.2.2)) ≤ price)
    (hstate : invariant state) :
    expectedShadowCharge key budget required stopAfter computation state ≤
      price * expectedShadowMass key budget required stopAfter computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedShadowCharge_pure, expectedShadowMass_pure,
      mul_zero, le_refl]
  | query_bind input next ih =>
      rw [expectedShadowCharge_query_bind, expectedShadowMass_query_bind]
      have hstep : certificateMonitorCharge key budget required input
          (state.1, state.2.2) ≤
          price * certificateMonitorMass key budget input
            (state.1, state.2.2) := by
        by_cases hactive : CertificateMonitorActive key budget input
            (state.1, state.2.2)
        · simp only [certificateMonitorCharge, certificateMonitorMass,
            if_pos hactive]
          calc
            _ ≤ targetCreationMultiplier key state.1 input * price :=
              mul_le_mul' le_rfl (hprice state hstate)
            _ = _ := mul_comm _ _
        · simp only [certificateMonitorCharge, certificateMonitorMass,
            if_neg hactive, mul_zero, le_refl]
      calc
        _ ≤ price * certificateMonitorMass key budget input
              (state.1, state.2.2) +
            ∑' result,
              Pr[= result | (certificateShadowLengthImpl key budget required
                stopAfter input).run state] *
                (price * expectedShadowMass key budget required stopAfter
                  (next result.1) result.2) := by
          apply add_le_add hstep
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ ((certificateShadowLengthImpl key budget
              required stopAfter input).run state).support
          · exact mul_le_mul' le_rfl
              (ih result.1 result.2
                (hstable input state result hstate hr))
          · have hz : Pr[= result | (certificateShadowLengthImpl key budget
                required stopAfter input).run state] = 0 := by
              rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
              exact hr
            simp only [hz, zero_mul, le_refl]
        _ = price * (certificateMonitorMass key budget input
              (state.1, state.2.2) +
            ∑' result,
              Pr[= result | (certificateShadowLengthImpl key budget required
                stopAfter input).run state] *
                expectedShadowMass key budget required stopAfter
                  (next result.1) result.2) := by
          rw [mul_add]
          congr 1
          calc
            _ = ∑' result, price *
                (Pr[= result | (certificateShadowLengthImpl key budget required
                  stopAfter input).run state] *
                  expectedShadowMass key budget required stopAfter
                    (next result.1) result.2) := by
              apply tsum_congr
              intro result
              ac_rfl
            _ = _ := by rw [ENNReal.tsum_mul_left]
        _ = _ := rfl

inductive CertificateShadowReachable (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (initial : CertificateShadowState) : CertificateShadowState → Prop where
  | initial : CertificateShadowReachable key budget required stopAfter initial initial
  | step {current : CertificateShadowState}
      (hcurrent : CertificateShadowReachable key budget required stopAfter
        initial current)
      (input : (OracleWorld + SigningSpec).Domain)
      (result : (OracleWorld + SigningSpec).Range input × CertificateShadowState)
      (hr : result ∈ ((certificateShadowLengthImpl key budget required stopAfter
        input).run current).support) :
      CertificateShadowReachable key budget required stopAfter initial result.2

/-- A price ceiling is required only on states that the actual shadow
interpreter can reach from this initial state. -/
theorem expectedShadowCharge_le_price_mul_mass_reachable {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initial : CertificateShadowState) (price : ENNReal)
    (hprice : ∀ current : CertificateShadowState,
      CertificateShadowReachable key budget required stopAfter initial current →
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - current.2.2.spent)
        (signatureLimit - current.2.2.log.length) required
        (certificateMonitorCoverState (current.1, current.2.2)) ≤ price) :
    expectedShadowCharge key budget required stopAfter computation initial ≤
      price * expectedShadowMass key budget required stopAfter computation initial := by
  exact expectedShadowCharge_le_price_mul_mass_on_invariant key budget required
    stopAfter computation initial price
    (CertificateShadowReachable key budget required stopAfter initial)
    (by
      intro input current result hcurrent hr
      exact CertificateShadowReachable.step hcurrent input result hr)
    hprice CertificateShadowReachable.initial

theorem expectedShadowCharge_le_remaining_mul_price_reachable {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initial : CertificateShadowState) (price : ENNReal)
    (hbalance : initial.2.2.spent = initial.2.1.2 ∨
      initial.2.2.stopped = true)
    (hprice : ∀ current : CertificateShadowState,
      CertificateShadowReachable key budget required stopAfter initial current →
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - current.2.2.spent)
        (signatureLimit - current.2.2.log.length) required
        (certificateMonitorCoverState (current.1, current.2.2)) ≤ price) :
    expectedShadowCharge key budget required stopAfter computation initial ≤
      price * ((budget - initial.2.1.2 : Nat) : ENNReal) := by
  exact (expectedShadowCharge_le_price_mul_mass_reachable key budget required
    stopAfter computation initial price hprice).trans
    (mul_le_mul' le_rfl
      (expectedShadowMass_le_remaining key budget required stopAfter
        computation initial hbalance))

/-- The per-call price already contains the moment of the observed signing
log. Future-query and future-signature terms can only increase it. -/
theorem targetCreationPrice_ge_observed_signing_moment
    (key : SecretKey) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) :
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
      (Fintype.card Index : ENNReal)⁻¹) *
        targetIndexMoments key state.1 state.2 0 required.card *
          targetCertificateScale required ≤
      targetCreationPrice key nearUniformDigestReuseWeight budget signatures
        required state := by
  unfold targetCreationPrice reuseRawEnvelope observedRawIndexShapeVector
    liftTargetIndexVector
  exact mul_le_mul' (mul_le_mul' le_rfl
    (le_targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹
      nearUniformDigestReuseWeight
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
        (Fintype.card Index : ENNReal)⁻¹)
      budget signatures (liftTargetIndexVector
        (targetIndexMoments key state.1 state.2)) ∅ required)) le_rfl

private theorem index_term_le_sum (f : Index → ENNReal) (index : Index) :
    f index ≤ ∑ i : Index, f i := by
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ index)

theorem targetIndexMoments_ge_repeated_index
    (key : SecretKey) (state : CoverLogState) (index : Index)
    (degree count : Nat)
    (hcount : count ≤
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root
          state.2) index).card) :
    (count : ENNReal) ^ degree ≤
      targetIndexMoments key state.1 state.2 0 degree := by
  have hterm : ((signingSlotsAtIndex (observedOptionalSigningViews
      (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2)
      index).card : ENNReal) ^ degree ≤
      targetIndexMoments key state.1 state.2 0 degree := by
    calc
      _ = cachedIndexMultiplicity key.parameter state.1 index ^ 0 *
          ((signingSlotsAtIndex (observedOptionalSigningViews
            (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root
              state.2) index).card : ENNReal) ^ degree := by
          rw [pow_zero, one_mul]
      _ ≤ targetIndexMoments key state.1 state.2 0 degree := by
          exact index_term_le_sum
            (fun index => cachedIndexMultiplicity key.parameter state.1 index ^ 0 *
              ((signingSlotsAtIndex (observedOptionalSigningViews
                (FtsProbeSimulation.messageAnswers key.parameter state.1)
                  key.root state.2) index).card : ENNReal) ^ degree) index
  exact (by gcongr : (count : ENNReal) ^ degree ≤
    ((signingSlotsAtIndex (observedOptionalSigningViews
      (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2)
      index).card : ENNReal) ^ degree).trans hterm

theorem targetCreationPrice_ge_repeated_index
    (key : SecretKey) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState)
    (index : Index) (count : Nat)
    (hcount : count ≤
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root
          state.2) index).card) :
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
      (Fintype.card Index : ENNReal)⁻¹) *
        (count : ENNReal) ^ required.card *
          targetCertificateScale required ≤
      targetCreationPrice key nearUniformDigestReuseWeight budget signatures
        required state := by
  exact (mul_le_mul' (mul_le_mul' le_rfl
    (targetIndexMoments_ge_repeated_index key state index required.card count
      hcount)) le_rfl).trans
    (targetCreationPrice_ge_observed_signing_moment key budget signatures
      required state)

private theorem repeated32_price_constant :
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
      (Fintype.card Index : ENNReal)⁻¹) *
        (32 : ENNReal) ^ (Finset.univ : Finset FtsTree).card *
          targetCertificateScale Finset.univ =
      ((2 ^ 114 : Nat) : ENNReal)⁻¹ := by
  norm_num [targetCertificateScale, ftsTreeHeight, totalHeight, ftsTrees,
    Index, FtsTree, FtsLeaf]
  have hnn :
    (256 : NNReal)⁻¹ * (17179869184 : NNReal)⁻¹ *
      1329227995784915872903807060280344576 *
        (6277101735386680763835789423207666416102355444464034512896 : NNReal)⁻¹ =
      (20769187434139310514121985316880384 : NNReal)⁻¹ := by norm_num
  have he := congrArg (fun x : NNReal => (x : ENNReal)) hnn
  simpa [ENNReal.coe_mul, ENNReal.coe_inv] using he

/-- Thirty-two openings at one index already make the pointwise creation
price exceed the desired 127-bit per-call rate. -/
theorem targetCreationPrice_gt_127_of_repeated32
    (key : SecretKey) (budget signatures : Nat)
    (state : CoverLogState) (index : Index)
    (hcount : 32 ≤
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root
          state.2) index).card) :
    ((2 ^ 127 : Nat) : ENNReal)⁻¹ <
      targetCreationPrice key nearUniformDigestReuseWeight budget signatures
        Finset.univ state := by
  have hlower := targetCreationPrice_ge_repeated_index key budget signatures
    Finset.univ state index 32 hcount
  have hlower' : ((2 ^ 114 : Nat) : ENNReal)⁻¹ ≤
      targetCreationPrice key nearUniformDigestReuseWeight budget signatures
        Finset.univ state := by
    calc
      _ = (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
          (Fintype.card Index : ENNReal)⁻¹) *
            (32 : ENNReal) ^ (Finset.univ : Finset FtsTree).card *
              targetCertificateScale Finset.univ :=
        repeated32_price_constant.symm
      _ ≤ _ := by simpa only [Nat.cast_ofNat] using hlower
  exact (by norm_num : ((2 ^ 127 : Nat) : ENNReal)⁻¹ <
    ((2 ^ 114 : Nat) : ENNReal)⁻¹).trans_le hlower'

theorem no_uniform_127_price_on_reachable_repeated32
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (initial current : CertificateShadowState)
    (index : Index)
    (hreach : CertificateShadowReachable key budget required stopAfter
      initial current)
    (hrequired : required = Finset.univ)
    (hcount : 32 ≤
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter current.1)
          key.root current.2.2.log) index).card) :
    ¬ ∀ state : CertificateShadowState,
      CertificateShadowReachable key budget required stopAfter initial state →
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - state.2.2.spent)
        (signatureLimit - state.2.2.log.length) required
        (certificateMonitorCoverState (state.1, state.2.2)) ≤
          ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
  intro hprice
  have hbound := hprice current hreach
  subst required
  have htooHigh := targetCreationPrice_gt_127_of_repeated32 key
    (budget - current.2.2.spent)
    (signatureLimit - current.2.2.log.length)
    (current.1, current.2.2.log) index hcount
  exact (not_lt_of_ge hbound) htooHigh

theorem expectedShadowCharge_le_remaining_mul_price {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState) (price : ENNReal)
    (hbalance : state.2.2.spent = state.2.1.2 ∨ state.2.2.stopped = true)
    (hprice : ∀ current : CertificateMonitorState,
      targetCreationPrice key nearUniformDigestReuseWeight
        (budget - current.2.spent) (signatureLimit - current.2.log.length)
        required (certificateMonitorCoverState current) ≤ price) :
    expectedShadowCharge key budget required stopAfter computation state ≤
      price * ((budget - state.2.1.2 : Nat) : ENNReal) := by
  exact (expectedShadowCharge_le_price_mul_mass key budget required stopAfter
    computation state price hprice).trans
    (mul_le_mul' le_rfl
      (expectedShadowMass_le_remaining key budget required stopAfter
        computation state hbalance))

theorem expected_certificateShadow_bank_le_initial_add_charge {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateShadowState)
    (hinv : state.2.2 = state.2.1.1.1 ∨ state.2.2.stopped = true) :
    (∑' result,
      Pr[= result | (simulateQ (certificateShadowLengthImpl key budget required
        stopAfter) computation).run state] *
      certificateBankCount result.2.2.2.bank) ≤
    certificateMonitorPotential key budget required (state.1, state.2.2) +
      expectedShadowCharge key budget required stopAfter computation state := by
  apply le_trans ?_
    (expected_certificateShadow_potential_le_initial_add_charge key budget
      required stopAfter computation state hinv)
  apply ENNReal.tsum_le_tsum
  intro result
  exact mul_le_mul' le_rfl
    (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem expected_certificateShadow_bank_le_charge {α : Type}
    (key : SecretKey) (budget spent : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input →
      cache input = none) :
    let initial : CertificateShadowState :=
      (cache, (((initialCertificateMonitor spent stopped, false), spent),
        initialCertificateMonitor spent stopped))
    (∑' result,
      Pr[= result | (simulateQ (certificateShadowLengthImpl key budget required
        stopAfter) computation).run initial] *
      certificateBankCount result.2.2.2.bank) ≤
    expectedShadowCharge key budget required stopAfter computation initial := by
  dsimp only
  have h := expected_certificateShadow_bank_le_initial_add_charge key budget
    required stopAfter computation
    (cache, (((initialCertificateMonitor spent stopped, false), spent),
      initialCertificateMonitor spent stopped)) (Or.inl rfl)
  rw [certificateMonitorPotential_initial key budget spent required cache stopped
    hnone, zero_add] at h
  exact h

theorem simulateQ_certificateShadowProposalImpl_length {α : Type}
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × CertificateShadowState) :
    Prod.map id Prod.snd <$>
      (simulateQ (certificateShadowProposalImpl key budget required stopAfter)
        computation).run state =
    (simulateQ (certificateShadowLengthImpl key budget required stopAfter)
      computation).run state.2 :=
  simulateQ_originalProposalImpl_length _ _ _ _ _ _

theorem expected_certificateShadowProposal_bank_le_charge {α : Type}
    (key : SecretKey) (budget spent : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input →
      cache input = none) :
    let initial : CertificateShadowState :=
      (cache, (((initialCertificateMonitor spent stopped, false), spent),
        initialCertificateMonitor spent stopped))
    (∑' result,
      Pr[= result | (simulateQ (certificateShadowProposalImpl key budget required
        stopAfter) computation).run ([], initial)] *
      certificateBankCount result.2.2.2.2.bank) ≤
    expectedShadowCharge key budget required stopAfter computation initial := by
  dsimp only
  have hmap := simulateQ_certificateShadowProposalImpl_length key budget
    required stopAfter computation
    ([], (cache, (((initialCertificateMonitor spent stopped, false), spent),
      initialCertificateMonitor spent stopped)))
  have hcount := congrArg (fun law : PMF (α × CertificateShadowState) =>
    ∑' result, Pr[= result | law] *
      certificateBankCount result.2.2.2.bank) hmap
  rw [tsum_probOutput_map_mul] at hcount
  simp only [Prod.map] at hcount
  rw [hcount]
  exact expected_certificateShadow_bank_le_charge key budget spent required
    stopAfter computation cache stopped hnone

theorem expected_certificateShadowContext_bank_le_charge
    (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result,
      Pr[= result | certificateShadowContextGame adversary budget required
        stopAfter stopped] * certificateBankCount result.2.2.2.2.2.bank) ≤
    ∑' generated,
      Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedShadowCharge generated.1.1.2 budget required
          (stopAfter generated.1.1.2)
          (FtsProbeSimulation.retainedGameRestComputation adversary
            generated.1.1.1)
          (generated.2, (((initialCertificateMonitor
            generated.1.2.hashCalls stopped, false), generated.1.2.hashCalls),
            initialCertificateMonitor generated.1.2.hashCalls stopped)) := by
  rw [certificateShadowContextGame, tsum_probOutput_bind_mul]
  dsimp only
  simp only [bind_pure_comp, tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  by_cases hg : generated ∈
      (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
  · have hgenerated := hg
    rw [probCompLift_support] at hgenerated
    have hkeygen : (generated.1.1, generated.2) ∈
        support ((simulateQ romImpl scheme.keygen).run ∅) := by
      rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
      exact ⟨generated, hgenerated, rfl⟩
    have hnone := keygen_cache_message_none (generated.1.1, generated.2)
      hkeygen
    exact mul_le_mul' le_rfl
      (expected_certificateShadowProposal_bank_le_charge generated.1.1.2
        budget generated.1.2.hashCalls required
        (stopAfter generated.1.1.2)
        (FtsProbeSimulation.retainedGameRestComputation adversary
          generated.1.1.1) generated.2 stopped hnone)
  · have hzero : Pr[= generated |
        (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hg
    simp only [hzero, zero_mul]
    exact zero_le

/-- On the Q-budget event, the counted game's bank is exactly the stopped
shadow bank; dropping the event can only increase its expected count. -/
theorem expected_certificateCounted_budget_bank_le_shadow
    (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result,
      Pr[= result | certificateCountedContextGame adversary budget required
        stopAfter stopped] * CertificateCountedWeightedBank budget result) ≤
    ∑' result,
      Pr[= result | certificateShadowContextGame adversary budget required
        stopAfter stopped] * certificateBankCount result.2.2.2.2.2.bank := by
  rw [← certificateShadowContextGame_actual, tsum_probOutput_map_mul]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (certificateShadowContextGame adversary budget required
    stopAfter stopped).support
  · apply mul_le_mul' le_rfl
    by_cases hcost : result.actual.originalCost.2 ≤ budget
    · have hgood := certificateShadowContextGame_good adversary budget required
        stopAfter stopped result hr hcost
      change result.2.2.2.2.1.2 ≤ budget at hcost
      simp only [CertificateCountedWeightedBank,
        CertificateShadowContextResult.actual,
        CertificateCountedContextResult.originalCost,
        certificateShadowActualProject, hcost, if_true, hgood]
      exact le_rfl
    · simp only [CertificateCountedWeightedBank, hcost, if_false]
      exact zero_le
  · have hz : Pr[= result | certificateShadowContextGame adversary budget required
        stopAfter stopped] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    simp only [hz, zero_mul]
    exact zero_le

/-- A budgeted full certificate pays either the adaptive shadow charge or the
already isolated exceptional event. The charge still needs a numerical Q-bound. -/
theorem originalCertificate_budget_le_shadow_charge_add_exception
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128) :
    Pr[OriginalBudgetedFullCertificate q |
      originalCertificateCountedSource adversary] ≤
    (∑' generated,
      Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedShadowCharge generated.1.1.2 q Finset.univ proposalPrefixStop
          (FtsProbeSimulation.retainedGameRestComputation adversary
            generated.1.1.1)
          (generated.2, (((initialCertificateMonitor
            generated.1.2.hashCalls false, false), generated.1.2.hashCalls),
            initialCertificateMonitor generated.1.2.hashCalls false))) +
      Pr[CertificateCountedBudgetExceptional q |
        certificateCountedContextGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] := by
  calc
    _ ≤ (∑' result,
        Pr[= result | certificateCountedContextGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] *
          CertificateCountedWeightedBank q result) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] :=
      originalCertificateCountedSource_full_budget_le_count_add_exception
        adversary q hbudget
    _ ≤ (∑' result,
        Pr[= result | certificateShadowContextGame adversary q Finset.univ
          (fun _ => proposalPrefixStop) false] *
          certificateBankCount result.2.2.2.2.2.bank) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] :=
      add_le_add
        (expected_certificateCounted_budget_bank_le_shadow adversary q
          Finset.univ (fun _ => proposalPrefixStop) false) le_rfl
    _ ≤ _ :=
      add_le_add
        (expected_certificateShadowContext_bank_le_charge adversary q
          Finset.univ (fun _ => proposalPrefixStop) false) le_rfl

/-- The actual Q-budget full-certificate probability has a linear Q charge for
any uniform upper bound on the per-call target creation price. -/
theorem originalCertificate_budget_le_q_price_add_exception
    (adversary : Adversary) (q : Nat) (hbudget : q ≤ 2 ^ 128)
    (price : ENNReal)
    (hprice : ∀ key : SecretKey, ∀ current : CertificateMonitorState,
      targetCreationPrice key nearUniformDigestReuseWeight
        (q - current.2.spent) (signatureLimit - current.2.log.length)
        Finset.univ (certificateMonitorCoverState current) ≤ price) :
    Pr[OriginalBudgetedFullCertificate q |
      originalCertificateCountedSource adversary] ≤
      price * (q : ENNReal) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] := by
  calc
    _ ≤ (∑' generated,
        Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
          expectedShadowCharge generated.1.1.2 q Finset.univ proposalPrefixStop
            (FtsProbeSimulation.retainedGameRestComputation adversary
              generated.1.1.1)
            (generated.2, (((initialCertificateMonitor
              generated.1.2.hashCalls false, false), generated.1.2.hashCalls),
              initialCertificateMonitor generated.1.2.hashCalls false))) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] :=
      originalCertificate_budget_le_shadow_charge_add_exception adversary q hbudget
    _ ≤ price * (q : ENNReal) +
        Pr[CertificateCountedBudgetExceptional q |
          certificateCountedContextGame adversary q Finset.univ
            (fun _ => proposalPrefixStop) false] := by
      apply add_le_add_left
      calc
        _ ≤ ∑' generated,
            Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
              (price * (q : ENNReal)) := by
          apply ENNReal.tsum_le_tsum
          intro generated
          apply mul_le_mul' le_rfl
          have hbound := expectedShadowCharge_le_remaining_mul_price
            generated.1.1.2 q Finset.univ proposalPrefixStop
            (FtsProbeSimulation.retainedGameRestComputation adversary
              generated.1.1.1)
            (generated.2, (((initialCertificateMonitor
              generated.1.2.hashCalls false, false), generated.1.2.hashCalls),
              initialCertificateMonitor generated.1.2.hashCalls false))
            price (Or.inl rfl) (hprice generated.1.1.2)
          exact hbound.trans (mul_le_mul' le_rfl
            (Nat.cast_le.mpr (Nat.sub_le q generated.1.2.hashCalls)))
        _ = price * (q : ENNReal) := by
          simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply,
            PMF.tsum_coe, one_mul]


end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.certificateContextGame_mass_le_spent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateContextGame_mass_le_spent

/-- info: 'SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_project

/-- info: 'SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_raw

/-- info: 'SphincsSecurity.Concrete.countedAdversaryPMFImpl_query_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.countedAdversaryPMFImpl_query_count

/-- info: 'SphincsSecurity.Concrete.countedAdversaryPMFImpl_run_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.countedAdversaryPMFImpl_run_count

/-- info: 'SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.simulateQ_certificateCountedProposalImpl_count

/-- info: 'SphincsSecurity.Concrete.certificateCountedProposal_run_spent_le_allCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedProposal_run_spent_le_allCalls

/-- info: 'SphincsSecurity.Concrete.certificateCountedContextGame_mass_le_allCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedContextGame_mass_le_allCalls

/-- info: 'SphincsSecurity.Concrete.certificateCountedContextGame_originalCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedContextGame_originalCost

/-- info: 'SphincsSecurity.Concrete.originalCertificateCountedSource_eq_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalCertificateCountedSource_eq_boundary

/-- info: 'SphincsSecurity.Concrete.simulateQ_certificateCountedLengthImpl_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.simulateQ_certificateCountedLengthImpl_project

/-- info: 'SphincsSecurity.Concrete.certificateCountedContextGame_full_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedContextGame_full_count

/-- info: 'SphincsSecurity.Concrete.originalCertificateCountedSource_full_budget_le_count_add_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalCertificateCountedSource_full_budget_le_count_add_exception

/-- info: 'SphincsSecurity.Concrete.certificateCountedTerminalGame_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateCountedTerminalGame_word

/-- info: 'SphincsSecurity.Concrete.expected_certificateCountedTerminalGame_budget_mass_payoff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateCountedTerminalGame_budget_mass_payoff_le

/-- info: 'SphincsSecurity.Concrete.certificateShadowContextGame_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateShadowContextGame_actual

/-- info: 'SphincsSecurity.Concrete.certificateShadowContextGame_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateShadowContextGame_good

/-- info: 'SphincsSecurity.Concrete.certificateShadowContextGame_mass_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateShadowContextGame_mass_budget

/-- info: 'SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le_of_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le_of_equal

/-- info: 'SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le_of_stopped

/-- info: 'SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateShadowLengthImpl_potential_le

/-- info: 'SphincsSecurity.Concrete.expected_certificateShadow_potential_le_initial_add_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateShadow_potential_le_initial_add_charge

/-- info: 'SphincsSecurity.Concrete.expected_certificateShadowContext_bank_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateShadowContext_bank_le_charge

/-- info: 'SphincsSecurity.Concrete.expected_certificateCounted_budget_bank_le_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateCounted_budget_bank_le_shadow

/-- info: 'SphincsSecurity.Concrete.originalCertificate_budget_le_shadow_charge_add_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalCertificate_budget_le_shadow_charge_add_exception

/-- info: 'SphincsSecurity.Concrete.expectedShadowMass_le_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expectedShadowMass_le_remaining

/-- info: 'SphincsSecurity.Concrete.expectedShadowCharge_le_remaining_mul_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expectedShadowCharge_le_remaining_mul_price

/-- info: 'SphincsSecurity.Concrete.originalCertificate_budget_le_q_price_add_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalCertificate_budget_le_q_price_add_exception

/-- info: 'SphincsSecurity.Concrete.expectedShadowCharge_le_price_mul_mass_on_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expectedShadowCharge_le_price_mul_mass_on_invariant

/-- info: 'SphincsSecurity.Concrete.expectedShadowCharge_le_remaining_mul_price_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expectedShadowCharge_le_remaining_mul_price_reachable

/-- info: 'SphincsSecurity.Concrete.targetCreationPrice_ge_observed_signing_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.targetCreationPrice_ge_observed_signing_moment

/-- info: 'SphincsSecurity.Concrete.targetCreationPrice_gt_127_of_repeated32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.targetCreationPrice_gt_127_of_repeated32

/-- info: 'SphincsSecurity.Concrete.no_uniform_127_price_on_reachable_repeated32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.no_uniform_127_price_on_reachable_repeated32

/-- info: 'SphincsSecurity.Concrete.certificateMonitorUpdate_creationMass_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateMonitorUpdate_creationMass_le_budget

/-- info: 'SphincsSecurity.Concrete.certificateGame_creationMass_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateGame_creationMass_le_budget

/-- info: 'SphincsSecurity.Concrete.expected_certificateTerminalGame_mass_payoff_le_unconditionally' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.expected_certificateTerminalGame_mass_payoff_le_unconditionally

/-- info: 'SphincsSecurity.Concrete.originalCertificate_budget_le_q_total_rate_add_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalCertificate_budget_le_q_total_rate_add_exception
