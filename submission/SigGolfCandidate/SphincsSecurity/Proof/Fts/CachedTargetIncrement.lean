import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeConditionalCoverage
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ObservedAdaptiveCoverBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def observedOptionalSigningViews (answers : HashInput → Option HashOutput) (root : Digest)
    (log : QueryLog SigningSpec) : Fin log.length → Option FewTimeView :=
  fun slot => observedSigningView? answers root (log.get slot)

theorem observedSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    observedSigningView? (messageAnswers parameter after) root entry = observedSigningView? (messageAnswers parameter before) root entry := by
  cases hresponse : entry.2 with
  | none => simp [observedSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [observedSigningView?, hresponse, houtput, hafter]

theorem observedOptionalSigningViews_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached parameter before root log) :
    observedOptionalSigningViews (messageAnswers parameter after) root log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  exact observedSigningView?_cache_stable parameter root before after hcache (log.get slot) (hsigned _ (List.get_mem _ _))

theorem signingSlotsAtIndex_log_card {α : Type} (log : List α) (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0)).sum := by
  rw [signingSlotsAtIndex, Finset.card_eq_sum_ones, Finset.sum_filter, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0))

theorem signingSlotsAtIndex_log_append_card {α : Type} (log : List α) (entry : α)
    (view : α → Option FewTimeView) (index : Index) :
    (signingSlotsAtIndex (fun slot => view ((log ++ [entry]).get slot)) index).card =
      (signingSlotsAtIndex (fun slot => view (log.get slot)) index).card +
        if ∃ source, view entry = some source ∧ source.1 = index then 1 else 0 := by
  simp only [signingSlotsAtIndex_log_card, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem eligibleSigningViews_fresh_eq_observed (parameter : PublicParameter) (root : Digest)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput)
    (hfresh : before (tweakableHashInput parameter .message payload) = none)
    (hsigned : SigningDigestsCached parameter before root log) :
    eligibleSigningViews (messageAnswers parameter before) root payload log =
      observedOptionalSigningViews (messageAnswers parameter before) root log := by
  funext slot
  simp only [eligibleSigningViews, observedOptionalSigningViews]
  cases hresponse : (log.get slot).2 with
  | none =>
      change Option.bind (log.get slot).2 _ = Option.bind (log.get slot).2 _
      rw [hresponse]
      rfl
  | some signature =>
      have hne : messageDigestPayload root (log.get slot).1 signature.randomness ≠ payload := by
        intro heq
        have hcached := hsigned (log.get slot) (List.get_mem _ _) signature hresponse
        apply hcached
        change before (tweakableHashInput parameter .message (messageDigestPayload root (log.get slot).1 signature.randomness)) = none
        rwa [heq]
      unfold eligibleSigningView?
      rw [hresponse]
      change (if messageDigestPayload root (log.get slot).1 signature.randomness = payload then none else _) = _
      rw [if_neg hne]

end SphincsSecurity.Concrete
