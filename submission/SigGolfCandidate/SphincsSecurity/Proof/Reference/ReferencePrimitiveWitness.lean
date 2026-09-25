import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceLayerWitness
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsTwoEdgeProbability
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsDistinctContactProbability
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsMarkerContactPartition
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferenceVerifierInstantiation
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem chainException_contactResult (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (result : ContactResult)
    (hfrontier : ∀ index, result.frontier lay tree leaf index = frontier f parameter words lay tree leaf secret index)
    (hexception : ChainException f parameter words lay tree leaf secret (result.before * result.after)) :
    (∃ index, ForwardChainMatch f (segment parameter words lay tree leaf index) (secret index) (result.before * result.after)) ∨
      result.TwoEdge parameter words ∨ result.TwoContacts parameter words ∨ result.MarkerContact parameter words := by
  have hcontact (index : ChainIndex)
      (h : Seen (segment parameter words lay tree leaf index) (frontier f parameter words lay tree leaf secret index) (result.before * result.after)) :
      (⟨lay, tree, leaf, index⟩ : OtsPrefix.ChainAddress) ∈ contacts parameter words result.frontier (result.before * result.after) := by
    rw [mem_contacts]
    simpa only [hfrontier] using h
  rcases hexception with hf | ⟨index, ht⟩ | ⟨left, right, hne, hl, hr⟩ | ⟨index, hm, hc⟩
  · exact Or.inl hf
  · refine Or.inr (Or.inl ⟨⟨lay, tree, leaf, index⟩, ?_⟩)
    change SeenTwoEdge _ (result.frontier lay tree leaf index) (result.before * result.after)
    rw [hfrontier]
    exact ht
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply Finset.one_lt_card.mpr
    refine ⟨⟨lay, tree, leaf, left⟩, hcontact left hl, ⟨lay, tree, leaf, right⟩, hcontact right hr, ?_⟩
    intro he
    exact hne (congrArg (fun address : OtsPrefix.ChainAddress => address.2.2.2) he)
  · exact Or.inr (Or.inr (Or.inr ⟨⟨lay, tree, leaf, index⟩, hm, hcontact index hc⟩))

end SphincsSecurity.Concrete.OtsVerifierWitness

namespace SphincsSecurity.Concrete.ReferencePrimitiveWitness

open _root_.OracleComp OracleSpec OtsContactTrace OtsVerifierWitness
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalPayloadInputs instFintypePosition frontierRoot chainWalk

def AboveFrontier (words : OtsReferenceWords) : Position → Prop
  | .chain lay tree leaf chain step => (words lay tree leaf chain).val ≤ step.val
  | _ => True

def StructuralMatch (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (trace : Trace) : Prop :=
  ∃ position, AboveFrontier words position ∧ QueriedOutputMatch f key position trace

def Outcome (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (result : ContactResult) : Prop :=
  EncodingOutputMatch key.parameter words messages selections (result.before * result.after) ∨
    StructuralMatch key f words (result.before * result.after) ∨ result.TwoEdge key.parameter words ∨
      result.TwoContacts key.parameter words ∨ result.MarkerContact key.parameter words

theorem tree_match (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (lay : Layer) (tree : TreeIndex) (trace : Trace)
    (h : TreeOutputMatch f key.parameter lay tree (key.otsSecret lay tree) trace) : StructuralMatch key f words trace := by
  obtain ⟨level, index, payload, hp, hl, hi, hb, hrow, hhit⟩ := h
  let position : Position := .node lay tree ⟨level, hl.trans_le (layerHeight_le lay)⟩ ⟨index, hi⟩
  refine ⟨position, trivial, hb, payload, hp, hrow, hhit.1, ?_⟩
  simpa only [position, Position.domain, honestValue_node] using hhit.2

theorem leaf_match (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (trace : Trace)
    (h : LeafOutputMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace) : StructuralMatch key f words trace := by
  obtain ⟨payload, hp, hne, hrow, hvalue⟩ := h
  refine ⟨.leaf lay tree leaf, trivial, trivial, payload, hp, hrow, hne, ?_⟩
  simpa only [Position.domain, honestValue_leaf, canonicalLeaf_eq_honestNode] using hvalue

theorem forward_match (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (trace : Trace)
    (h : ForwardChainMatch f (segment key.parameter words lay tree leaf chain) (key.otsSecret lay tree leaf chain) trace) :
    StructuralMatch key f words trace := by
  obtain ⟨step, payload, habove, hrow, hhit⟩ := h
  refine ⟨.chain lay tree leaf chain step, habove, trivial, digestBytes payload, digestBytes_mem_canonicalPayloadInputs _, hrow, ?_, ?_⟩
  · exact fun he => hhit.1 (digestBytes_injective he)
  · simpa only [Position.domain, honestValue_chain] using hhit.2

theorem fts_exception (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (index : Index) (trace : Trace)
    (h : FtsVerifierWitness.Exception f key index trace) : StructuralMatch key f words trace := by
  obtain ⟨position, hp, hmatch⟩ := h
  refine ⟨position, ?_, hmatch⟩
  cases position <;> simp_all only [FtsVerifierWitness.AtIndex, AboveFrontier]

theorem layer_exception (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (result : ContactResult)
    (hfrontier : ∀ lay tree leaf chain, result.frontier lay tree leaf chain = frontier f key.parameter words lay tree leaf (key.otsSecret lay tree leaf) chain)
    (h : LayerException f key words messages selections (result.before * result.after)) : Outcome key f words messages selections result := by
  rcases h with hencoding | ⟨lay, tree, leaf, htree | hleaf | hchain⟩
  · exact Or.inl hencoding
  · exact Or.inr (Or.inl (tree_match key f words lay tree _ htree))
  · exact Or.inr (Or.inl (leaf_match key f words lay tree leaf _ hleaf))
  · rcases chainException_contactResult f key.parameter words lay tree leaf (key.otsSecret lay tree leaf) result
      (hfrontier lay tree leaf) hchain with ⟨chain, hforward⟩ | htwo | hcontacts | hmarker
    · exact Or.inr (Or.inl (forward_match key f words lay tree leaf chain _ hforward))
    · exact Or.inr (Or.inr (Or.inl htwo))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcontacts)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hmarker)))

end SphincsSecurity.Concrete.ReferencePrimitiveWitness
