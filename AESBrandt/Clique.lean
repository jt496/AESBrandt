import Mathlib.Combinatorics.SimpleGraph.Turan
import Mathlib.Order.Minimal
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α}  {n : ℕ}

lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

lemma IsClique.sdiff_of_sup_edge {v w : α} {s : Set α} (hc : (G ⊔ edge v w).IsClique s) :
    G.IsClique (s \ {v}) := by
  intro x hx y hy hxy
  have := hc hx.1 hy.1 hxy
  rw [sup_adj, edge_adj] at this
  aesop

lemma CliqueFree.mem_of_sup_edge_isNClique {t : Finset α} {n : ℕ} (h : G.CliqueFree n)
    (hc : (G ⊔ edge x y).IsNClique n t) : x ∈ t := by
  by_contra! hf
  classical
  have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr <| Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

lemma IsNClique.erase_of_sup_edge_of_mem [DecidableEq α] {v w : α} {s : Finset α}
    (hc : (G ⊔ edge v w).IsNClique n s) (hx : v ∈ s) : G.IsNClique (n - 1) (s.erase v) where
  isClique := coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq  := by rw [card_erase_of_mem hx, hc.2]

open Classical in
lemma CliqueFree.sup_edge' (h : G.CliqueFree n) (v w : α) : (G ⊔ edge v w).CliqueFree (n + 1) :=
    fun _ hs ↦ (hs.erase_of_sup_edge_of_mem <|
        (h.mono (Nat.le_succ n)).mem_of_sup_edge_isNClique hs).not_cliqueFree h

lemma IsNClique.exists_not_adj_of_cliqueFree_succ [DecidableEq α] (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y := by
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

section PR21479aes_completeMultipartiteGraph
/-- Embedding of the complete graph on ι into completeMultipartite graph on ι nonempty parts-/
noncomputable def CompleteMultipartiteGraph.topEmbedding {ι : Type*} (V : ι → Type*)
    [∀ i, Nonempty (V i)] : (⊤ : SimpleGraph ι) ↪g (completeMultipartiteGraph V) where
  toFun := fun i ↦ ⟨i, Classical.arbitrary (V i)⟩
  inj' := fun i j h ↦ (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

theorem CompleteMultipartiteGraph.notCliqueFree_le_card {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Nonempty (V i)] (hc : n ≤ Fintype.card ι ) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <| (CompleteMultipartiteGraph.topEmbedding V).comp
    (Iso.completeGraph (Fintype.equivFin ι).symm).toEmbedding

theorem CompleteMultipartiteGraph.notCliqueFree_infinite {ι : Type*} [Infinite ι] (V : ι → Type*)
    [∀ i, Nonempty (V i)] : ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ not_cliqueFree_of_top_embedding (CompleteMultipartiteGraph.topEmbedding V |>.comp
            <| Embedding.completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι) hf
end PR21479aes_completeMultipartiteGraph

variable {x y : α} (G)
/-- `G` is not complete iff there exist distinct non-adjacent vertices -/
protected lemma ne_top_iff : G ≠ ⊤ ↔ ∃ x y, x ≠ y ∧ ¬ G.Adj x y := by
  constructor <;> intro h <;> contrapose! h
  · exact eq_top_iff.2 fun _ _ hxy ↦ h _ _ hxy.ne
  · exact fun _ _ hne ↦ h ▸ hne

variable {G} {n : ℕ}
/-- A graph G is maximally Kᵣ-free if it doesn't contain Kᵣ but any supergraph does contain Kᵣ -/
abbrev MaximalCliqueFree (G : SimpleGraph α) (n : ℕ) : Prop := Maximal (fun H => H.CliqueFree n) G

namespace MaximalCliqueFree

lemma le_iff_eq (h : G.MaximalCliqueFree n) (hcf : H.CliqueFree n) : G ≤ H ↔ G = H :=
  ⟨fun hle ↦ h.eq_of_le hcf hle, le_of_eq⟩

variable (h : G.MaximalCliqueFree n) include h

lemma not_cliqueFree_of_gt (h' : G < H) : ¬ H.CliqueFree n := h.not_prop_of_gt h'

protected lemma eq_top_iff [Fintype α] : G = ⊤ ↔ Fintype.card α < n := by
  constructor <;> intro h'
  · have ht := (⊤ : SimpleGraph α).not_cliqueFree_card_of_top_embedding Embedding.refl
    contrapose! ht
    exact h' ▸ h.1.mono ht
  · exact h.le_iff_eq ((⊤ : SimpleGraph α).cliqueFree_of_card_lt h') |>.1 le_top

protected lemma ne_top_iff [Fintype α] : G ≠ ⊤ ↔ n ≤ Fintype.card α := by
  rw [ne_eq, h.eq_top_iff, Nat.not_lt]

protected lemma sup_edge (hne : x ≠ y) (hn : ¬ G.Adj x y) :
   ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t := by
  have := h.not_cliqueFree_of_gt <| G.lt_sup_edge _ _ hne hn
  simp only [CliqueFree, not_forall, not_not] at this
  obtain ⟨t, hc⟩ := this
  use t, hc
  exact ⟨h.1.mem_of_sup_edge_isNClique hc, h.1.mem_of_sup_edge_isNClique (edge_comm _ _ ▸ hc)⟩

variable [DecidableEq α]
lemma exists_of_not_adj (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧ G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨t, hc, xym⟩ := h.sup_edge hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (not_mem_erase _ _), not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  cases n with
  | zero => exact False.elim <| not_cliqueFree_zero h.1
  | succ n =>
    exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem xym.2, hc.erase_of_sup_edge_of_mem xym.1⟩

lemma exists_of_le_card [Fintype α] (h' : n ≤ Fintype.card α) : ∃ x y s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧
  G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨_, _, hne, hna⟩ := G.ne_top_iff.1 <| h.ne_top_iff.2 h'
  exact ⟨_, _, h.exists_of_not_adj hne hna⟩

lemma not_cliqueFree_of_le_card [Fintype α] (hle : n ≤ Fintype.card α) : ¬ G.CliqueFree (n - 1) :=
  have ⟨_,_,_,_,_,hs,_⟩ := h.exists_of_le_card hle
  hs.not_cliqueFree

end MaximalCliqueFree

section Turan
variable [Fintype α] [DecidableRel G.Adj]
lemma IsTuranMaximal.maximalCliqueFree (h : G.IsTuranMaximal n) : G.MaximalCliqueFree (n + 1) :=
  ⟨h.1, fun _ hcf hle ↦ h.le_iff_eq hcf |>.1 hle |>.symm.le⟩

variable [DecidableEq α]
theorem not_cliqueFree_of_isTuranMaximal' (hn : r + 1 ≤ Fintype.card α) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := hG.maximalCliqueFree.not_cliqueFree_of_le_card hn

end Turan
end SimpleGraph
