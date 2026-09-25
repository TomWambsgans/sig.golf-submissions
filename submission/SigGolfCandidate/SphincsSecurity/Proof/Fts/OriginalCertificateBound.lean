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
