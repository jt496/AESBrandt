import Mathlib.Combinatorics.SimpleGraph.Turan
import Mathlib.Order.Minimal
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

lemma IsNClique.exists_not_adj_of_cliqueFree_succ {s : Finset α} (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y := by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

-- lemma exists_isNClique_sup_edge_of_max_cliqueFree (h : Maximal (fun H => H.CliqueFree n) G) (hne : x ≠ y)
--     (hn : ¬ G.Adj x y) : ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t :=
--   let ⟨t, hc⟩ := not_forall_not.1 <| h.not_prop_of_gt <| G.lt_sup_edge _ _ hne hn
--   ⟨t, hc, ⟨h.1.mem_of_sup_edge_isNClique hc, h.1.mem_of_sup_edge_isNClique (edge_comm _ _ ▸ hc)⟩⟩

lemma exists_of_max_cliqueFree_not_adj [DecidableEq α] (h : Maximal (fun H => H.CliqueFree n) G)
    (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧ G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨t, hc, xym⟩: ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t :=
    let ⟨t, hc⟩ := not_forall_not.1 <| h.not_prop_of_gt <| G.lt_sup_edge _ _ hne hn
    ⟨t, hc, ⟨h.1.mem_of_sup_edge_isNClique hc, h.1.mem_of_sup_edge_isNClique (edge_comm _ _ ▸ hc)⟩⟩
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (not_mem_erase _ _), not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  cases n with
  | zero => exact False.elim <| not_cliqueFree_zero h.1
  | succ n =>
    exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem xym.2, hc.erase_of_sup_edge_of_mem xym.1⟩

end SimpleGraph
