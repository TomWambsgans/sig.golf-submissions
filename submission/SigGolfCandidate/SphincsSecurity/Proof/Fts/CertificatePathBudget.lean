import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateMonitor
import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalProposalBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem certificateLengthImpl_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (result : (OracleWorld + SigningSpec).Range input × CertificateMonitorState)
    (hr : result ∈ ((certificateLengthImpl key budget required stopAfter input).run state).support) :
    ∃ length record, record ∈ (originalProposalRecord key input state.1).support ∧
      result = (record.output, originalProposalAdvance
        (certificateMonitorUpdate key budget required stopAfter) input state length record) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk] at hr
  split at hr
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨source, hsource, rfl⟩ := hr
    have hrecord := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source, hsource, rfl⟩
    rw [recordLengthBridge_record] at hrecord
    exact ⟨source.1, source.2, hrecord, rfl⟩
  · rw [PMF.mem_support_map_iff] at hr
    obtain ⟨record, hrecord, rfl⟩ := hr
    exact ⟨0, record, hrecord, rfl⟩

theorem certificateMonitorUpdate_le_hashCalls (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent ≤
        state.2.spent + record.trace.hashCalls ∧
      (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass ≤
        state.2.creationMass + record.trace.hashCalls := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive]
    exact ⟨le_rfl, add_le_add le_rfl (targetCreationMultiplier_le_record_hashCalls key input state.1 record hr)⟩
  · simp only [certificateMonitorUpdate, if_neg hactive]
    exact ⟨Nat.le_add_right _ _, le_self_add⟩

theorem certificateLength_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.1 q) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.spent ≤ state.2.spent + q ∧ result.2.2.creationMass ≤ state.2.creationMass + q := by
  induction computation using OracleComp.inductionOn generalizing q state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨Nat.le_add_right _ _, le_self_add⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, hrecord, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      have hquery := originalProposalRecord_query_bound key input next q state.1 hbound record hrecord
      have hstep := certificateMonitorUpdate_le_hashCalls key budget required stopAfter input state length record hrecord
      have htail := ih record.output _ _ hquery.2 result hr
      simp only [originalProposalAdvance] at htail
      constructor
      · omega
      · calc
          _ ≤ (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass +
              (q - record.trace.hashCalls : Nat) := htail.2
          _ ≤ (state.2.creationMass + record.trace.hashCalls) + (q - record.trace.hashCalls : Nat) :=
            add_le_add hstep.2 le_rfl
          _ = state.2.creationMass + q := by
            rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hquery.1]

theorem certificateProposal_run_cost_le {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (state : List Index × CertificateMonitorState)
    (hbound : HashQueryBound (simulateQ (expandedAdversaryImpl key) computation) state.2.1 q) (result : α × (List Index × CertificateMonitorState))
    (hr : result ∈ ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.2.spent ≤ state.2.2.spent + q ∧
      result.2.2.2.creationMass ≤ state.2.2.creationMass + q := by
  have hprojection := simulateQ_certificateProposalImpl_length key budget required stopAfter computation state
  have hm := (PMF.mem_support_map_iff (Prod.map id Prod.snd) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, hprojection] at hm
  exact certificateLength_run_cost_le key budget required stopAfter computation q state.2 hbound _ hm

theorem originalProposalRecord_counted (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (fun record : ProposalExecutionRecord input =>
      ((record.output, record.trace.hashCalls), record.cache)) <$>
      originalProposalRecord key input cache =
    (liftM ((simulateQ romImpl (countHashQueries (expandedAdversaryImpl key input))).run cache) : PMF _) := by
  let f : ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × QueryCache HashSpec →
      ((OracleWorld + SigningSpec).Range input × Nat) × QueryCache HashSpec :=
    fun result => ((result.1.1, result.1.2.hashCalls), result.2)
  calc
    _ = f <$> ((fun record : ProposalExecutionRecord input =>
        ((record.output, record.trace), record.cache)) <$> originalProposalRecord key input cache) := by
      simp only [Functor.map_map, f]
    _ = f <$> (liftM (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) : PMF _) := by
      exact congrArg (Functor.map f) (originalProposalRecord_boundary key input cache)
    _ = _ := by
      rw [← liftM_map (m := ProbComp) (n := PMF)]
      rw [boundaryRun_count]

theorem certificateMonitorUpdate_mass_le_spent (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hpre : state.2.creationMass ≤ (state.2.spent : ENNReal))
    (hr : record ∈ (originalProposalRecord key input state.1).support) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass ≤
      ((certificateMonitorUpdate key budget required stopAfter input state length record).spent : ENNReal) := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simp only [certificateMonitorUpdate, if_pos hactive]
    rw [Nat.cast_add]
    exact add_le_add hpre (targetCreationMultiplier_le_record_hashCalls key input state.1 record hr)
  · simpa only [certificateMonitorUpdate, if_neg hactive] using hpre

theorem certificateLength_run_mass_le_spent {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateMonitorState)
    (hpre : state.2.creationMass ≤ (state.2.spent : ENNReal))
    (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.creationMass ≤ (result.2.2.spent : ENNReal) := by
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
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      exact ih record.output _
        (certificateMonitorUpdate_mass_le_spent key budget required stopAfter input state length record hpre hrecord)
        result hr

end SphincsSecurity.Concrete

/-- info: 'SphincsSecurity.Concrete.certificateLength_run_mass_le_spent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.certificateLength_run_mass_le_spent

/-- info: 'SphincsSecurity.Concrete.originalProposalRecord_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SphincsSecurity.Concrete.originalProposalRecord_counted
