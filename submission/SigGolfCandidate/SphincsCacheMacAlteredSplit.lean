import SigGolfCandidate.SphincsCacheSecretDomains

/-! Exact deterministic split for an altered authenticated public cache.
The genuine MAC is visible, so changing only the tag never succeeds. -/

namespace SigGolfCandidate.SphincsCacheMacAlteredSplit
open SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

def accepts (hash : HashInput → HashOutput)
    (parameter : PublicParameter) (seed : MasterSeed)
    (candidateBytes : HashInput) (tag : Digest) : Prop :=
  truncateHash (hash (macInput parameter seed candidateBytes)) = tag

theorem changed_accepted_candidateBytes_ne (hash : HashInput → HashOutput)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonicalBytes candidateBytes : HashInput) (tag : Digest)
    (hchanged : (candidateBytes, tag) ≠
      (canonicalBytes,
        truncateHash (hash (macInput parameter seed canonicalBytes))))
    (haccept : accepts hash parameter seed candidateBytes tag) :
    candidateBytes ≠ canonicalBytes := by
  intro heq
  subst candidateBytes
  apply hchanged
  simp only [Prod.mk.injEq, true_and]
  exact haccept.symm

theorem changed_accepted_mac_input_ne (hash : HashInput → HashOutput)
    (parameter : PublicParameter) (seed : MasterSeed)
    (canonicalBytes candidateBytes : HashInput) (tag : Digest)
    (hchanged : (candidateBytes, tag) ≠
      (canonicalBytes,
        truncateHash (hash (macInput parameter seed canonicalBytes))))
    (haccept : accepts hash parameter seed candidateBytes tag) :
    macInput parameter seed candidateBytes ≠
      macInput parameter seed canonicalBytes := by
  exact (macInput_injective_ciphertext parameter seed).ne
    (changed_accepted_candidateBytes_ne hash parameter seed canonicalBytes candidateBytes tag
      hchanged haccept)

end SigGolfCandidate.SphincsCacheMacAlteredSplit

/-- info: 'SigGolfCandidate.SphincsCacheMacAlteredSplit.changed_accepted_mac_input_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsCacheMacAlteredSplit.changed_accepted_mac_input_ne
