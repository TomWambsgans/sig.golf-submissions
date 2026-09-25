import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Support
import SigGolfCandidate.SphincsCacheSecretDomains

/-! The inherited seeded signer never issues a tag-15 cache-MAC oracle query. -/

namespace SigGolfCandidate.SphincsSeededNoMacQueries
open OracleComp OracleSpec SphincsSecurity
open SigGolfCandidate.SphincsCacheSecretDomains

def AvoidsMac {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) : Prop :=
  ∀ parameter seed candidateBytes,
    macInput parameter seed candidateBytes ∉ queriedInputs f computation

theorem AvoidsMac.pure {α : Type} (f : QueryImpl HashSpec Id) (value : α) :
    AvoidsMac f (pure value) := by
  simp [AvoidsMac]

theorem AvoidsMac.bind {α β : Type} (f : QueryImpl HashSpec Id)
    (first : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β)
    (hfirst : AvoidsMac f first)
    (hnext : AvoidsMac f (next (evalWithAnswerFn f first))) :
    AvoidsMac f (first >>= next) := by
  intro parameter seed candidateBytes hmem
  rw [queriedInputs_bind] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst parameter seed candidateBytes hmem
  · exact hnext parameter seed candidateBytes hmem

theorem AvoidsMac.deriveKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    AvoidsMac f (SphincsSecurity.deriveKey parameter domain seed) := by
  intro p s candidateBytes hmem
  change macInput p s candidateBytes ∈ queriedInputs f
    (liftM (HashSpec.query (keygenHashInput parameter domain seed)) >>=
      fun answer => Pure.pure (truncateHash answer)) at hmem
  simp only [queriedInputs_query_bind, queriedInputs_pure,
    List.mem_singleton] at hmem
  exact macInput_ne_keygenHashInput p parameter s seed candidateBytes domain hmem

theorem AvoidsMac.tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    AvoidsMac f (Concrete.tweakableHash parameter domain payload) := by
  intro p seed candidateBytes hmem
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hmem
  exact macInput_ne_tweakableHashInput p parameter seed candidateBytes domain payload hmem

theorem AvoidsMac.deriveRandomizer (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    AvoidsMac f (SphincsSecurity.deriveRandomizer parameter seed message trial) := by
  intro p s candidateBytes hmem
  change macInput p s candidateBytes ∈ queriedInputs f
    (liftM (HashSpec.query (randomizerHashInput parameter seed message trial)) >>=
      fun answer => Pure.pure (truncateHash answer)) at hmem
  simp only [queriedInputs_query_bind, queriedInputs_pure,
    List.mem_singleton] at hmem
  exact macInput_ne_randomizerHashInput p parameter s seed candidateBytes message trial hmem

theorem AvoidsMac.messageDigest (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    AvoidsMac f (Concrete.messageDigest parameter root message randomness) := by
  intro p seed candidateBytes hmem
  change macInput p seed candidateBytes ∈ queriedInputs f
    (liftM (HashSpec.query (tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness))) >>=
      fun answer => Pure.pure (truncateMessageDigest answer)) at hmem
  simp only [queriedInputs_query_bind, queriedInputs_pure,
    List.mem_singleton] at hmem
  exact macInput_ne_tweakableHashInput p parameter seed candidateBytes .message
    (Concrete.messageDigestPayload root message randomness) hmem

theorem AvoidsMac.sequenceFin {α : Type} {n : Nat}
    (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α)
    (hcomputation : ∀ i, AvoidsMac f (computation i)) :
    AvoidsMac f (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact AvoidsMac.pure f _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      apply AvoidsMac.bind f _ _ (hcomputation 0)
      apply AvoidsMac.bind f _ _
      · exact ih (fun i : Fin n => computation i.succ)
          (fun i => hcomputation i.succ)
      · exact AvoidsMac.pure f _

theorem AvoidsMac.chainWalk (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) :
    AvoidsMac f (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value) := by
  induction steps generalizing value with
  | zero => exact AvoidsMac.pure f _
  | succ steps ih =>
      rw [Concrete.chainWalk]
      apply AvoidsMac.bind f _ _ (ih value)
      split
      · exact AvoidsMac.tweakableHash f parameter _ _
      · exact AvoidsMac.pure f _

theorem AvoidsMac.oneTimePublicKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    AvoidsMac f (Seeded.oneTimePublicKey parameter lay tree leaf seed) := by
  apply AvoidsMac.sequenceFin
  intro chainIdx
  apply AvoidsMac.bind f _ _
    (AvoidsMac.deriveKey f parameter (.ots lay tree leaf chainIdx) seed)
  exact AvoidsMac.chainWalk f parameter lay tree leaf chainIdx 0 _ _

theorem AvoidsMac.treeNode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    AvoidsMac f (Seeded.treeNode parameter lay tree seed level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [Seeded.treeNode]
      apply AvoidsMac.bind f _ _
        (AvoidsMac.oneTimePublicKey f parameter lay tree
          (Concrete.leafOfNat nodeIdx) seed)
      exact AvoidsMac.tweakableHash f parameter _ _
  | succ level ih =>
      rw [Seeded.treeNode]
      apply AvoidsMac.bind f _ _ (ih (2 * nodeIdx))
      apply AvoidsMac.bind f _ _ (ih (2 * nodeIdx + 1))
      exact AvoidsMac.tweakableHash f parameter _ _

theorem AvoidsMac.treeRoot (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) :
    AvoidsMac f (Seeded.treeRoot parameter lay tree seed) := by
  exact AvoidsMac.treeNode f parameter lay tree seed (layerHeight lay) 0

theorem AvoidsMac.treePath (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    AvoidsMac f (Seeded.treePath parameter lay tree seed leaf) := by
  apply AvoidsMac.sequenceFin
  intro level
  exact AvoidsMac.treeNode f parameter lay tree seed level.val _

theorem AvoidsMac.encode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    AvoidsMac f (Concrete.encode parameter lay tree leaf message counter) := by
  rw [Concrete.encode]
  apply AvoidsMac.bind f _ _ (AvoidsMac.tweakableHash f parameter _ _)
  exact AvoidsMac.pure f _

theorem AvoidsMac.otsSignFrom (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest)
    (attempts counter : Nat) :
    AvoidsMac f (Seeded.otsSignFrom parameter lay tree leaf seed message
      attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact AvoidsMac.pure f _
  | succ attempts ih =>
      rw [Seeded.otsSignFrom]
      apply AvoidsMac.bind f _ _
        (AvoidsMac.encode f parameter lay tree leaf message _)
      split
      · apply AvoidsMac.bind f _ _
        · apply AvoidsMac.sequenceFin
          intro chainIdx
          apply AvoidsMac.bind f _ _
            (AvoidsMac.deriveKey f parameter (.ots lay tree leaf chainIdx) seed)
          exact AvoidsMac.chainWalk f parameter lay tree leaf chainIdx 0 _ _
        · exact AvoidsMac.pure f _
      · exact ih (counter + 1)

theorem AvoidsMac.otsSign (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    AvoidsMac f (Seeded.otsSign parameter lay tree leaf seed message) := by
  exact AvoidsMac.otsSignFrom f parameter lay tree leaf seed message
    encodingAttemptLimit 0

theorem AvoidsMac.ftsNode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) (level nodeIdx : Nat) :
    AvoidsMac f (Seeded.ftsNode parameter index tree seed level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [Seeded.ftsNode]
      apply AvoidsMac.bind f _ _
        (AvoidsMac.deriveKey f parameter
          (.fts index tree (Concrete.ftsLeafOfNat nodeIdx)) seed)
      exact AvoidsMac.tweakableHash f parameter _ _
  | succ level ih =>
      rw [Seeded.ftsNode]
      apply AvoidsMac.bind f _ _ (ih (2 * nodeIdx))
      apply AvoidsMac.bind f _ _ (ih (2 * nodeIdx + 1))
      exact AvoidsMac.tweakableHash f parameter _ _

theorem AvoidsMac.ftsKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    AvoidsMac f (Seeded.ftsKey parameter index seed) := by
  rw [Seeded.ftsKey]
  apply AvoidsMac.bind f _ _
  · apply AvoidsMac.sequenceFin
    intro tree
    exact AvoidsMac.ftsNode f parameter index tree seed ftsTreeHeight 0
  · exact AvoidsMac.tweakableHash f parameter _ _

theorem AvoidsMac.ftsOpen (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed) :
    AvoidsMac f (Seeded.ftsOpen parameter index leaves seed) := by
  apply AvoidsMac.sequenceFin
  intro tree
  apply AvoidsMac.sequenceFin
  intro level
  exact AvoidsMac.ftsNode f parameter index tree seed level.val _

theorem AvoidsMac.signAttempt (f : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    AvoidsMac f (Seeded.signAttempt secretKey message randomness) := by
  rw [Seeded.signAttempt]
  apply AvoidsMac.bind f _ _
    (AvoidsMac.messageDigest f secretKey.parameter secretKey.root message randomness)
  split <;> exact AvoidsMac.pure f _

theorem AvoidsMac.signDigestLoop (f : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message)
    (attempts trial : Nat) :
    AvoidsMac f (Seeded.signDigestLoop secretKey message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact AvoidsMac.pure f _
  | succ attempts ih =>
      rw [Seeded.signDigestLoop]
      apply AvoidsMac.bind f _ _
        (AvoidsMac.deriveRandomizer f secretKey.parameter secretKey.seed message _)
      apply AvoidsMac.bind f _ _
        (AvoidsMac.signAttempt f secretKey message _)
      split
      · exact AvoidsMac.pure f _
      · exact ih (trial + 1)

theorem AvoidsMac.layerMessage (f : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) :
    AvoidsMac f (Seeded.layerMessage secretKey index lay) := by
  rw [Seeded.layerMessage]
  split
  · exact AvoidsMac.treeRoot f secretKey.parameter _ _ secretKey.seed
  · exact AvoidsMac.ftsKey f secretKey.parameter index secretKey.seed

theorem AvoidsMac.signLayer (f : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer) :
    AvoidsMac f (Seeded.signLayer secretKey index lay) := by
  rw [Seeded.signLayer]
  apply AvoidsMac.bind f _ _
    (AvoidsMac.layerMessage f secretKey index lay)
  apply AvoidsMac.bind f _ _
    (AvoidsMac.otsSign f secretKey.parameter lay
      (Concrete.treeIndexAt index lay) (Concrete.leafIndexAt index lay)
      secretKey.seed _)
  split
  · apply AvoidsMac.bind f _ _
      (AvoidsMac.treePath f secretKey.parameter lay
        (Concrete.treeIndexAt index lay) secretKey.seed
        (Concrete.leafIndexAt index lay))
    exact AvoidsMac.pure f _
  · exact AvoidsMac.pure f _

theorem AvoidsMac.sequenceLayers {α : Layer → Type}
    (f : QueryImpl HashSpec Id)
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay)))
    (hcomputation : ∀ lay, AvoidsMac f (computation lay)) :
    AvoidsMac f (Concrete.sequenceLayers computation) := by
  unfold Concrete.sequenceLayers
  apply AvoidsMac.bind f _ _ (hcomputation bottomLayer)
  split
  · apply AvoidsMac.bind f _ _ (hcomputation middle4Layer)
    split
    · apply AvoidsMac.bind f _ _ (hcomputation middle3Layer)
      split
      · apply AvoidsMac.bind f _ _ (hcomputation middle2Layer)
        split
        · apply AvoidsMac.bind f _ _ (hcomputation middleLayer)
          split
          · apply AvoidsMac.bind f _ _ (hcomputation topLayer)
            split <;> exact AvoidsMac.pure f _
          · exact AvoidsMac.pure f _
        · exact AvoidsMac.pure f _
      · exact AvoidsMac.pure f _
    · exact AvoidsMac.pure f _
  · exact AvoidsMac.pure f _

theorem seeded_sign_avoids_mac (f : QueryImpl HashSpec Id)
    (secretKey : Seeded.SecretKey) (message : Message) :
    AvoidsMac f (Seeded.sign secretKey message :
      OracleComp HashSpec (Option Signature)) := by
  rw [Seeded.sign]
  apply AvoidsMac.bind f _ _
    (AvoidsMac.signDigestLoop f secretKey message digestAttemptLimit 0)
  split
  · apply AvoidsMac.bind f _ _
      (AvoidsMac.sequenceFin f _ (fun tree =>
        AvoidsMac.deriveKey f secretKey.parameter
          (.fts _ tree _) secretKey.seed))
    apply AvoidsMac.bind f _ _
      (AvoidsMac.ftsOpen f secretKey.parameter _ _ secretKey.seed)
    apply AvoidsMac.bind f _ _
      (AvoidsMac.sequenceLayers f _ (fun lay =>
        AvoidsMac.signLayer f secretKey _ lay))
    split
    · apply AvoidsMac.bind f _ _
        (AvoidsMac.treeRoot f secretKey.parameter topLayer
          Concrete.rootTree secretKey.seed)
      exact AvoidsMac.pure f _
    · exact AvoidsMac.pure f _
  · exact AvoidsMac.pure f _

end SigGolfCandidate.SphincsSeededNoMacQueries

/-- info: 'SigGolfCandidate.SphincsSeededNoMacQueries.seeded_sign_avoids_mac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.SphincsSeededNoMacQueries.seeded_sign_avoids_mac
