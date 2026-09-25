import SigGolfCandidate.SphincsVerifierFtsReadyControls

/-! Connect a loaded honest witness to the first FORS leaf HASH site. -/

namespace SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SphincsSecurity
open SigGolfCandidate.SphincsVerifierFtsReadyControls
open SigGolfCandidate.SphincsVerifierFtsEarlyFrame
open SigGolfCandidate.SphincsVerifierFtsQuery
open SigGolfCandidate.SphincsVerifierFtsSetup
open SigGolfCandidate.SphincsVerifierFtsAdvance
open SigGolfCandidate.SphincsVerifierFtsCopyPointers
open SigGolfCandidate.SphincsVerifierFtsSelect
open SigGolfCandidate.SphincsVerifierFtsTreeHeader
open SigGolfCandidate.SphincsVerifierFtsEntry
open SigGolfCandidate.SphincsVerifierLastLeaf
open SigGolfCandidate.SphincsVerifierLeavesTrace
open SigGolfCandidate.SphincsVerifierIndexStore
open SigGolfCandidate.SphincsVerifierIndexPrefix
open SigGolfCandidate.SphincsVerifierMessageHash
open SigGolfCandidate.SphincsVerifierMessageCopy
open SigGolfCandidate.SphincsVerifierHashSetup
open SigGolfCandidate.SphincsVerifierHashBytes
open SigGolfCandidate.SphincsVerifierFtsWitnessFrame
open SigGolfCandidate.SphincsBridge
open SigGolfCandidate.SphincsVerifierFtsFirstTree
open SigGolfCandidate.SphincsVerifierFtsInitialInvariant
open SigGolfCandidate.SphincsVerifierFtsPathInduction
open SigGolfCandidate.SphincsVerifierFtsPathCost
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem loaded_honest_firstFts_ready
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey) (signature : Signature)
    (state : MachineState) (commitmentAnswer digestAnswer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      commitmentAnswer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest digestAnswer)) :
    ∃ ready final,
      OrdinarySteps SphincsImages.verify
        (writeHash (firstHashState state) commitmentAnswer) 107 ready ∧
      OrdinarySteps SphincsImages.verify
        (writeHash ready digestAnswer) 392 final ∧
      final.pc = 0x18c8 ∧
      final.getReg .x10 = 0x40000 ∧
      final.getReg .x11 = 480 ∧
      final.getReg .x12 = 0x42000 ∧
      final.getReg .x5 = 1 ∧
      final.getMem 0x43028 = 0x22cf0 ∧
      final.getMem 0x43070 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest digestAnswer)
          ⟨0, by decide⟩).val ∧
      final.getMem 0x43000 = 0 ∧
      final.getMem 0x43008 = BitVec.ofNat 64
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest digestAnswer)).val ∧
      hashInput final = toQuery (firstFtsInput inner
        (SphincsSecurity.Concrete.digestIndex
          (SphincsSecurity.truncateMessageDigest digestAnswer))
        (SphincsSecurity.Concrete.digestLeaves
          (SphincsSecurity.truncateMessageDigest digestAnswer)
          ⟨0, by decide⟩)
        (signature.ftsSecret ⟨0, by decide⟩)) ∧
      WitnessPrefix final inner ∧ FtsWitness final signature := by
  obtain ⟨ready, trace, readyPc, messageReady, prefixReady, secretBytes⟩ :=
    loaded_honest_message_ready_with_witness publicKey message inner
      signature state commitmentAnswer loaded answerMatches
  let initial := indexStoredState (indexValueState (writeHash ready digestAnswer))
  let selected := leafStates initial 24 (by decide)
  let accepted := lastAcceptState selected
  let entered := ftsEntryState accepted
  let header := ftsTreeHeaderState entered
  let selection := ftsSelectState header
  let pointers := ftsCopyPointers selection
  let advanced := ftsAdvanceState (SphincsVerifierCopy.copyRootState pointers)
  let final := ftsHashReadyState advanced
  obtain ⟨steps, pc, source, bits, destination, service⟩ :=
    messageReady_admissible_ftsHashReady ready inner message
      signature.randomness messageReady readyPc digestAnswer admissible
  obtain ⟨pointer, selector, tree, index⟩ :=
    messageReady_firstFts_controls ready inner message
      signature.randomness messageReady readyPc digestAnswer admissible
  have pointerPrefix := firstFtsPointers_prefix ready inner digestAnswer
    messageReady.destination prefixReady
  have pointerSecret := firstFtsPointers_secret ready digestAnswer
    (signature.ftsSecret ⟨0, by decide⟩)
    messageReady.destination secretBytes
  obtain ⟨_, _, query⟩ := messageReady_firstFts_hashInput ready inner
    message signature.randomness messageReady readyPc digestAnswer
    admissible pointerPrefix (signature.ftsSecret ⟨0, by decide⟩)
    pointerSecret
  have prefixFinal : WitnessPrefix final inner := by
    simpa only [final, advanced, pointers, firstFtsPointers] using
      firstFtsHashReady_prefix ready digestAnswer inner
        messageReady.destination prefixReady
  have witnessReady := loaded_honest_allFts_at_secondHash publicKey
    message inner signature state commitmentAnswer loaded answerMatches
    ready trace
  have witnessFinal : FtsWitness final signature := by
    simpa only [final, advanced, pointers, firstFtsPointers] using
      firstFtsHashReady_preserve_FtsWitness ready digestAnswer signature
        messageReady.destination witnessReady
  exact ⟨ready, final, trace, steps, pc, source, bits, destination,
    service, pointer, selector, tree, index, query,
    prefixFinal, witnessFinal⟩

theorem loaded_honest_firstFts_abstract_root (hash : Hash)
    (publicKey : SigGolf.PublicKey) (message : SigGolf.Message)
    (inner : SphincsSecurity.PublicKey) (signature : Signature)
    (state : MachineState) (commitmentAnswer digestAnswer : BitVec 256)
    (loaded : initialState SphincsSubmission.submission .verify
      (message, publicKey, SphincsWireEncoding.wire inner signature) =
        some state)
    (answerMatches : ∀ index : Fin 2,
      commitmentAnswer.extractLsb' (64 * index.val) 64 =
        publicKey.extractLsb' (64 * index.val) 64)
    (admissible : SphincsSecurity.Concrete.Admissible
      (SphincsSecurity.truncateMessageDigest digestAnswer)) :
    let index := SphincsSecurity.Concrete.digestIndex
      (SphincsSecurity.truncateMessageDigest digestAnswer)
    let leaf := SphincsSecurity.Concrete.digestLeaves
      (SphincsSecurity.truncateMessageDigest digestAnswer)
      ⟨0, by decide⟩
    ∃ final,
      hashInput final = toQuery
        (firstFtsInput inner index leaf
          (signature.ftsSecret ⟨0, by decide⟩)) ∧
      (let answer := hash (hashInput final)
       let start := firstLeafStartState final answer
       let root := parentPathRun hash inner signature ⟨0, by decide⟩
         index leaf start (truncateHash answer) 8
       root.1.pc = 0x1b84 ∧
         (∀ i, (hi : i < 20) →
           root.1.getByte (BitVec.ofNat 64 (0x44a00 + i)) =
             (SphincsSecurity.Concrete.ftsFoldValue
               (adaptOracle hash) inner.parameter index ⟨0, by decide⟩ leaf
               (signature.ftsPath ⟨0, by decide⟩)
               (truncateHash answer) 8).extractLsb' (8 * i) 8) ∧
         pathCycles hash inner signature ⟨0, by decide⟩ index leaf
           start (truncateHash answer) 8 ≤ 1136) := by
  obtain ⟨ready, final, trace, steps, pc, source, bits, destination, service,
      pointer, selector, tree, index, query, hprefix, witness⟩ :=
    loaded_honest_firstFts_ready publicKey message inner signature
      state commitmentAnswer digestAnswer loaded answerMatches admissible
  have root := firstTree_abstract_root hash final (hash (hashInput final))
    signature inner
    (SphincsSecurity.Concrete.digestIndex
      (SphincsSecurity.truncateMessageDigest digestAnswer))
    (SphincsSecurity.Concrete.digestLeaves
      (SphincsSecurity.truncateMessageDigest digestAnswer)
      ⟨0, by decide⟩)
    pc source bits destination pointer selector tree index hprefix witness
  exact ⟨final, query, root⟩

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree.loaded_honest_firstFts_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFts_ready

/-- info: 'SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree.loaded_honest_firstFts_abstract_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loaded_honest_firstFts_abstract_root

end SigGolfCandidate.SphincsVerifierFtsLoadedFirstTree
