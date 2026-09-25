import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Preparation
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MemoLog
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameErasure
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TableSigner

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {Request Answer : Type} [DecidableEq Request]

def loggedRun {α : Type} (sign : Request → OracleComp OracleWorld Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) :
    OracleComp OracleWorld (α × QueryLog (Request →ₒ Answer)) :=
  (simulateQ ((fun input => liftM (liftM (OracleWorld.query input) : OracleComp OracleWorld _)) + QueryImpl.withLogging sign) computation).run

omit [DecidableEq Request] in
theorem runSigning_withRequestLog {α : Type} (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) :
    runSigning sign (withRequestLog computation) = loggedRun (fun request => liftM (sign request)) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [withRequestLog_base, runSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inl, loggedRun, WriterT.run_bind, WriterT.run_liftM, bind_map_left]
          change ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _) =
            ((liftM (OracleWorld.query input) : OracleComp OracleWorld _) >>= _)
          apply bind_congr
          intro answer
          simpa [loggedRun, runSigning] using ih answer
      | inr input =>
          simp only [withRequestLog_request, runSigning, simulateQ_bind, simulateQ_spec_query,
            QueryImpl.add_apply_inr, simulateQ_map, loggedRun, WriterT.run_bind,
            QueryImpl.run_withLogging_apply, bind_assoc, pure_bind]
          change (liftM (sign input) >>= _) = (liftM (sign input) >>= _)
          apply bind_congr
          intro answer
          simpa only [runSigning, loggedRun, List.singleton_append] using
            congrArg (fun computation : OracleComp OracleWorld (α × QueryLog (Request →ₒ Answer)) =>
              (fun result => (result.1, ⟨input, answer⟩ :: result.2)) <$> computation) (ih answer)

end SphincsSecurity.Seeded


open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

noncomputable def memoAdversary (adversary : Adversary) : Adversary where
  main := fun publicKey => memoize (adversary.main publicKey) ∅

def transcriptWin (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool) : Bool :=
  decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem transcriptWin_mono (forgery : Forgery) (original forwarded : QueryLog SigningSpec)
    (h : forwarded.Sublist original) (verified : Bool) (hwin : transcriptWin forgery original verified = true) :
    transcriptWin forgery forwarded verified = true := by
  simp only [transcriptWin, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  refine ⟨⟨h.length_le.trans hwin.1.1, ?_⟩, hwin.2⟩
  rintro ⟨entry, hentry, heq⟩
  exact hwin.1.2 ⟨entry, h.subset hentry, heq⟩

noncomputable def finishGame (publicKey : PublicKey) (result : Forgery × QueryLog SigningSpec) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (Concrete.verify publicKey result.1.message result.1.signature : OracleComp HashSpec Bool)
  return transcriptWin result.1 result.2 verified

noncomputable def sourceGame (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) Bool :=
  withRequestLog (adversary.main publicKey) >>= fun result => baseLift (finishGame publicKey result)

noncomputable def transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) (Bool × Bool) := do
  let result ← withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)
  let verified ← baseLift (liftM
    (Concrete.verify publicKey result.1.1.message result.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return (transcriptWin result.1.1 result.1.2 verified, transcriptWin result.1.1 result.2 verified)

theorem runSigning_baseLift {α : Type} (sign : Message → OracleComp HashSpec (Option Signature))
    (computation : OracleComp OracleWorld α) : runSigning sign (baseLift computation) = computation := by
  rw [runSigning, simulateQ_baseLift, simulateQ_ofLift_eq_self]

theorem runSigning_sourceGame (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    runSigning (tableSign randomizers secretKey) (sourceGame publicKey adversary) =
      gameRest (tableScheme randomizers) adversary publicKey secretKey := by
  simp only [sourceGame, runSigning, simulateQ_bind, simulateQ_baseLift, simulateQ_ofLift_eq_self]
  rw [show simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
      fun request => liftM (tableSign randomizers secretKey request : OracleComp HashSpec (Option Signature)))
      (withRequestLog (adversary.main publicKey)) =
        loggedRun (fun request => liftM (tableSign randomizers secretKey request : OracleComp HashSpec (Option Signature)))
          (adversary.main publicKey) from runSigning_withRequestLog _ _]
  unfold loggedRun gameRest finishGame transcriptWin
  rfl

theorem fst_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.fst <$> transcriptReduction publicKey adversary = memoize (sourceGame publicKey adversary) ∅ := by
  unfold transcriptReduction sourceGame
  rw [memoize_baseLift_bind]
  conv_rhs => rw [← fst_withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem snd_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.snd <$> transcriptReduction publicKey adversary = sourceGame publicKey (memoAdversary adversary) := by
  unfold transcriptReduction sourceGame memoAdversary
  rw [← withRequestLog_memoize_forget (adversary.main publicKey) ∅]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem transcriptReduction_win (publicKey : PublicKey) (adversary : Adversary)
    (result : Bool × Bool) (hresult : result ∈ support (transcriptReduction publicKey adversary)) :
    result.1 = true → result.2 = true := by
  simp only [transcriptReduction, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨logs, hlogs, verified, _, rfl⟩ := hresult
  exact transcriptWin_mono _ _ _ (memoize_log_sublist _ ∅ logs hlogs) verified

end SphincsSecurity.Seeded
