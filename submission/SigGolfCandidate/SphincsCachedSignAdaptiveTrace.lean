import SigGolfCandidate.SphincsCachedSignTraceRequests
import SigGolfCandidate.SphincsSecurity.Statement
import SigGolfCandidate.SphincsRawSecurityBound

namespace SigGolfCandidate.CachedSignerTrace

open OracleComp SphincsSecurity SphincsSecurity.Concrete
open SigGolfCandidate.SphincsCachedSignValue

structure InteractionResult (α : Type) where
  value : α
  hashCalls : Nat
  signingRequests : Nat

def worldCharge (input : OracleWorld.Domain) : Nat :=
  match input with
  | .inl _ => 0
  | .inr _ => 1

def runInteraction {α : Type}
    (world : QueryImpl OracleWorld Id)
    (signer : Message → Option Signature × Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : InteractionResult α :=
  OracleComp.construct
    (fun value => ⟨value, 0, 0⟩)
    (fun input _ next =>
      match input with
      | .inl input =>
        let tail := next (world input)
        ⟨tail.value, worldCharge input + tail.hashCalls,
          tail.signingRequests⟩
      | .inr message =>
        let reply := signer message
        let tail := next reply.1
        ⟨tail.value, reply.2 + tail.hashCalls, tail.signingRequests + 1⟩)
    computation

theorem runInteraction_pure {α : Type} (world : QueryImpl OracleWorld Id)
    (signer : Message → Option Signature × Nat) (value : α) :
    runInteraction world signer (pure value) = ⟨value, 0, 0⟩ := rfl

theorem runInteraction_query_bind {α : Type}
    (world : QueryImpl OracleWorld Id)
    (signer : Message → Option Signature × Nat)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α) :
    runInteraction world signer (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      match input with
      | .inl input =>
        let tail := runInteraction world signer (next (world input))
        ⟨tail.value, worldCharge input + tail.hashCalls,
          tail.signingRequests⟩
      | .inr message =>
        let reply := signer message
        let tail := runInteraction world signer (next reply.1)
        ⟨tail.value, reply.2 + tail.hashCalls, tail.signingRequests + 1⟩ := by
  cases input <;> rfl

noncomputable def rawSigner (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) : Option Signature × Nat :=
  runCount hash (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))

noncomputable def cachedSigner (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) : Option Signature × Nat :=
  runCount hash
    (signWithCache secretKey message (canonicalTopCache hash secretKey))

theorem adaptive_signer_coupling (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (world : QueryImpl OracleWorld Id)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    let raw := runInteraction world (rawSigner hash secretKey) computation
    let cached := runInteraction world (cachedSigner hash secretKey) computation
    raw.value = cached.value ∧
      raw.signingRequests = cached.signingRequests ∧
      raw.hashCalls ≤ cached.hashCalls + raw.signingRequests * 1711698 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [runInteraction_pure]
  | query_bind input next ih =>
    cases input with
    | inl input =>
      simp only [runInteraction_query_bind]
      have htail := ih (world input)
      dsimp only at htail ⊢
      constructor
      · exact htail.1
      constructor
      · exact htail.2.1
      · omega
    | inr message =>
      simp only [runInteraction_query_bind]
      have hsingle := runCount_sign_related hash secretKey message
      have hanswer : (rawSigner hash secretKey message).1 =
          (cachedSigner hash secretKey message).1 := hsingle.1
      have hcost : (rawSigner hash secretKey message).2 ≤
          (cachedSigner hash secretKey message).2 + 1711698 := hsingle.2
      rw [hanswer]
      have htail := ih (cachedSigner hash secretKey message).1
      dsimp only at htail ⊢
      constructor
      · exact htail.1
      constructor
      · exact congrArg Nat.succ htail.2.1
      · omega

/-- Under the contest's request limit, a concrete query bound below 2^127
    keeps the coupled raw execution inside the 2^128 residual-proof range. -/
theorem adaptive_raw_budget_below_128 (hash : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (world : QueryImpl OracleWorld Id)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (q outsideCalls : Nat) (hq : q < 2 ^ 127)
    (hrequests : (runInteraction world (cachedSigner hash secretKey) computation).signingRequests ≤
      signatureLimit)
    (hcost : outsideCalls +
      (runInteraction world (cachedSigner hash secretKey) computation).hashCalls ≤ q) :
    outsideCalls + (runInteraction world (rawSigner hash secretKey) computation).hashCalls ≤
      2 ^ 128 := by
  have hcouple := adaptive_signer_coupling hash secretKey world computation
  dsimp only at hcouple
  have hboundary := SphincsSecurity.Concrete.virtual_query_budget_below_128
    q (outsideCalls + (runInteraction world (rawSigner hash secretKey) computation).hashCalls)
    (runInteraction world (rawSigner hash secretKey) computation).signingRequests
    hq (by omega) (by
      rw [SphincsSecurity.Concrete.cachedSignerOverheadCalls_eq]
      omega)
  exact hboundary

end SigGolfCandidate.CachedSignerTrace

/-- info: 'SigGolfCandidate.CachedSignerTrace.adaptive_signer_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.CachedSignerTrace.adaptive_signer_coupling

/-- info: 'SigGolfCandidate.CachedSignerTrace.adaptive_raw_budget_below_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SigGolfCandidate.CachedSignerTrace.adaptive_raw_budget_below_128
