import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing
import SigGolfCandidate.SphincsCommitment

/-! Candidate domain-separated random-oracle inputs for encrypted public cache. -/

namespace SigGolfCandidate.SphincsCacheSecretDomains
open SphincsSecurity

def padInput (parameter : PublicParameter) (seed : MasterSeed)
    (node : BitVec 32) : HashInput :=
  fieldBytes (tweakFields 14 0 0 node.toNat 0) ++
    bytesLE 20 parameter ++ bytesLE 32 seed

def macInput (parameter : PublicParameter) (seed : MasterSeed)
    (ciphertext : HashInput) : HashInput :=
  fieldBytes (tweakFields 15 0 0 0 0) ++
    bytesLE 20 parameter ++ bytesLE 32 seed ++ ciphertext

theorem padInput_seedHit (parameter : PublicParameter) (seed : MasterSeed)
    (node : BitVec 32) : SeedHit (padInput parameter seed node) seed := by
  simp [SeedHit, DerivationSeedHit, padInput, fieldBytes, tweakFields, bytesLE]

theorem macInput_seedHit (parameter : PublicParameter) (seed : MasterSeed)
    (ciphertext : HashInput) : SeedHit (macInput parameter seed ciphertext) seed := by
  simp [SeedHit, DerivationSeedHit, macInput, fieldBytes, tweakFields, bytesLE]

theorem padInput_injective_node (parameter : PublicParameter)
    (seed : MasterSeed) : Function.Injective (padInput parameter seed) := by
  intro left right heq
  simp only [padInput] at heq
  have hprefix := (List.append_inj' heq (by simp [bytesLE_length])).1
  have htweak := (List.append_inj' hprefix (by simp)).1
  have hfields := fieldBytes_injective htweak
  have hposition := congrArg TweakFields.position hfields
  simpa only [tweakFields, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hposition

theorem macInput_injective_ciphertext (parameter : PublicParameter)
    (seed : MasterSeed) : Function.Injective (macInput parameter seed) := by
  intro left right heq
  simp only [macInput, List.append_assoc] at heq
  have h1 := (List.append_right_injective _) heq
  have h2 := (List.append_right_injective _) h1
  exact (List.append_right_injective _) h2

theorem padInput_ne_keygenHashInput (parameter p : PublicParameter)
    (seed s : MasterSeed) (node : BitVec 32) (domain : KeygenDomain) :
    padInput parameter seed node ≠ keygenHashInput p domain s := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  cases domain <;> simp [padInput, keygenHashInput, fieldBytes,
    keygenDomainFields, tweakFields, bytesLE] at htag
  · exact (by decide : (14 : UInt8) ≠ 5) htag
  · exact (by decide : (14 : UInt8) ≠ 0) htag
  · exact (by decide : (14 : UInt8) ≠ 8) htag

theorem macInput_ne_keygenHashInput (parameter p : PublicParameter)
    (seed s : MasterSeed) (ciphertext : HashInput) (domain : KeygenDomain) :
    macInput parameter seed ciphertext ≠ keygenHashInput p domain s := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  cases domain <;> simp [macInput, keygenHashInput, fieldBytes,
    keygenDomainFields, tweakFields, bytesLE] at htag
  · exact (by decide : (15 : UInt8) ≠ 5) htag
  · exact (by decide : (15 : UInt8) ≠ 0) htag
  · exact (by decide : (15 : UInt8) ≠ 8) htag

theorem padInput_ne_tweakableHashInput (parameter p : PublicParameter)
    (seed : MasterSeed) (node : BitVec 32)
    (domain : HashDomain) (payload : HashInput) :
    padInput parameter seed node ≠ tweakableHashInput p domain payload := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  cases domain <;> simp [padInput, tweakableHashInput, tweakBytes,
    fieldBytes, hashDomainFields, tweakFields, bytesLE] at htag <;>
    exact (by decide : (14 : UInt8) ≠ _) htag

theorem macInput_ne_tweakableHashInput (parameter p : PublicParameter)
    (seed : MasterSeed) (ciphertext : HashInput)
    (domain : HashDomain) (payload : HashInput) :
    macInput parameter seed ciphertext ≠ tweakableHashInput p domain payload := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  cases domain <;> simp [macInput, tweakableHashInput, tweakBytes,
    fieldBytes, hashDomainFields, tweakFields, bytesLE] at htag <;>
    exact (by decide : (15 : UInt8) ≠ _) htag

theorem padInput_ne_macInput (parameter p : PublicParameter)
    (seed s : MasterSeed) (node : BitVec 32) (ciphertext : HashInput) :
    padInput parameter seed node ≠ macInput p s ciphertext := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  simp [padInput, macInput, fieldBytes, tweakFields, bytesLE] at htag
  exact (by decide : (14 : UInt8) ≠ 15) htag

theorem padInput_ne_randomizerHashInput (parameter p : PublicParameter)
    (seed s : MasterSeed) (node : BitVec 32)
    (message : Message) (trial : BitVec 32) :
    padInput parameter seed node ≠ randomizerHashInput p s message trial := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  simp [padInput, randomizerHashInput, fieldBytes, tweakFields, bytesLE] at htag
  exact (by decide : (14 : UInt8) ≠ 7) htag

theorem macInput_ne_randomizerHashInput (parameter p : PublicParameter)
    (seed s : MasterSeed) (ciphertext : HashInput)
    (message : Message) (trial : BitVec 32) :
    macInput parameter seed ciphertext ≠ randomizerHashInput p s message trial := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  simp [macInput, randomizerHashInput, fieldBytes, tweakFields, bytesLE] at htag
  exact (by decide : (15 : UInt8) ≠ 7) htag

theorem padInput_ne_commitmentInput (parameter : PublicParameter)
    (seed : MasterSeed) (node : BitVec 32) (publicKey : PublicKey) :
    padInput parameter seed node ≠ SigGolfCandidate.SphincsWire.commitmentInput publicKey := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  simp [padInput, SigGolfCandidate.SphincsWire.commitmentInput,
    fieldBytes, tweakFields, bytesLE] at htag
  exact (by decide : (14 : UInt8) ≠ 13) htag

theorem macInput_ne_commitmentInput (parameter : PublicParameter)
    (seed : MasterSeed) (ciphertext : HashInput) (publicKey : PublicKey) :
    macInput parameter seed ciphertext ≠ SigGolfCandidate.SphincsWire.commitmentInput publicKey := by
  intro h
  have htag := congrArg (fun input : HashInput => input[1]?.getD 0) h
  simp [macInput, SigGolfCandidate.SphincsWire.commitmentInput,
    fieldBytes, tweakFields, bytesLE] at htag
  exact (by decide : (15 : UInt8) ≠ 13) htag

end SigGolfCandidate.SphincsCacheSecretDomains

/-- info: 'SigGolfCandidate.SphincsCacheSecretDomains.padInput_seedHit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheSecretDomains.padInput_seedHit

/-- info: 'SigGolfCandidate.SphincsCacheSecretDomains.macInput_seedHit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheSecretDomains.macInput_seedHit

/-- info: 'SigGolfCandidate.SphincsCacheSecretDomains.padInput_ne_tweakableHashInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheSecretDomains.padInput_ne_tweakableHashInput
