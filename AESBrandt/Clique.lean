import Mathlib.Combinatorics.SimpleGraph.Turan
import Mathlib.Order.Minimal
-- NOTE this is all in PR #21479 aes_completeMultipartiteGraph
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α} {x y : α} {n : ℕ}

section PR21479aes_completeMultipartiteGraph

lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

/-- Embedding of the complete graph on `ι` into `completeMultipartiteGraph` on `ι` nonempty parts.-/
def completeMultipartiteGraph.topEmbedding {ι : Type*} (V : ι → Type*) (f : ∀ (i : ι), V i) :
    (⊤ : SimpleGraph ι) ↪g (completeMultipartiteGraph V) where
  toFun := fun i ↦ ⟨i, f i⟩
  inj' := fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

theorem completeMultipartiteGraph.not_CliqueFree_le_card {ι : Type*} [Fintype ι] (V : ι → Type*)
    (f : ∀ (i : ι), V i) (hc : n ≤ Fintype.card ι ) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <|
    (completeMultipartiteGraph.topEmbedding V f).comp
      (Iso.completeGraph (Fintype.equivFin ι).symm).toEmbedding

theorem completeMultipartiteGraph.not_CliqueFree_infinite {ι : Type*} [Infinite ι] (V : ι → Type*)
    (f : ∀ (i : ι), V i) : ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ not_cliqueFree_of_top_embedding (completeMultipartiteGraph.topEmbedding V f |>.comp
            <| Embedding.completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι) hf

end PR21479aes_completeMultipartiteGraph

end SimpleGraph
