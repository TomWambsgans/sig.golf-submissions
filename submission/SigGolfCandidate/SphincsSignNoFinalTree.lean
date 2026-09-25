import SigGolfCandidate.SphincsSecurity.Scheme

/-! Erase the seed signer's unused final top-tree recomputation at a fixed oracle. -/

namespace SigGolfCandidate.SphincsSignNoFinalTree
open SphincsSecurity OracleComp
open SphincsSecurity.Concrete
open SphincsSecurity.Seeded

def signNoFinalTree (secretKey : Seeded.SecretKey) (message : Message) :
    OracleComp HashSpec (Option Signature) := do
  let some (randomness, index, leaves) ←
      (Seeded.signDigestLoop secretKey message digestAttemptLimit 0 :
        OracleComp HashSpec _) | return none
  let secrets ← sequenceFin fun tree =>
    (deriveKey secretKey.parameter
      (.fts index tree (leaves (ftsIndexOf tree))) secretKey.seed :
      OracleComp HashSpec _)
  let ftsPath ←
    (Seeded.ftsOpen secretKey.parameter index leaves secretKey.seed :
      OracleComp HashSpec _)
  let some layers ←
      (Concrete.sequenceLayers (fun lay => Seeded.signLayer secretKey index lay) :
        OracleComp HashSpec _) | return none
  return some ⟨randomness, secrets, ftsPath, layers⟩

theorem signNoFinalTree_value
    (hash : SphincsSecurity.HashInput → SphincsSecurity.HashOutput)
    (secretKey : Seeded.SecretKey) (message : Message) :
    evalWithAnswerFn hash
      (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature)) =
      evalWithAnswerFn hash (signNoFinalTree secretKey message) := by
  simp only [Seeded.sign, signNoFinalTree, evalWithAnswerFn_bind]
  cases h : evalWithAnswerFn hash
      (Seeded.signDigestLoop secretKey message digestAttemptLimit 0 :
        OracleComp HashSpec _) with
  | none => simp [evalWithAnswerFn_pure]
  | some data =>
    rcases data with ⟨randomness, index, leaves⟩
    simp only [evalWithAnswerFn_bind]
    cases h2 : evalWithAnswerFn hash
        (Concrete.sequenceLayers
          (fun lay => Seeded.signLayer secretKey index lay) :
          OracleComp HashSpec _) with
    | none => simp [evalWithAnswerFn_pure]
    | some layers => simp [evalWithAnswerFn_pure]

/-- info: 'SigGolfCandidate.SphincsSignNoFinalTree.signNoFinalTree_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms signNoFinalTree_value

end SigGolfCandidate.SphincsSignNoFinalTree
