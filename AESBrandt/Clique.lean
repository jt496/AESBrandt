import Mathlib.Combinatorics.SimpleGraph.Turan
import Mathlib.Order.Minimal
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α}  {n : ℕ}

lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

section classical
open Classical
lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y := by
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

end classical

section PR21479aes_completeMultipartiteGraph

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

-- /-- Embedding of the complete graph on ι into completeMultipartite graph on ι nonempty parts-/
-- noncomputable def completeMultipartiteGraph.topEmbedding {ι : Type*} (V : ι → Type*)
--     [∀ i, Nonempty (V i)] : (⊤ : SimpleGraph ι) ↪g (completeMultipartiteGraph V) where
--   toFun := fun i ↦ ⟨i, Classical.arbitrary (V i)⟩
--   inj' := fun i j h ↦ (Sigma.mk.inj_iff.1 h).1
--   map_rel_iff' := by simp

-- theorem completeMultipartiteGraph.not_CliqueFree_le_card {ι : Type*} [Fintype ι] (V : ι → Type*)
--     [∀ i, Nonempty (V i)] (hc : n ≤ Fintype.card ι ) :
--     ¬ (completeMultipartiteGraph V).CliqueFree n :=
--   fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <| (completeMultipartiteGraph.topEmbedding V).comp
--     (Iso.completeGraph (Fintype.equivFin ι).symm).toEmbedding

-- theorem completeMultipartiteGraph.not_CliqueFree_infinite {ι : Type*} [Infinite ι] (V : ι → Type*)
--     [∀ i, Nonempty (V i)] : ¬ (completeMultipartiteGraph V).CliqueFree n :=
--   fun hf ↦ not_cliqueFree_of_top_embedding (completeMultipartiteGraph.topEmbedding V |>.comp
--            <| Embedding.completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι) hf
end PR21479aes_completeMultipartiteGraph

variable {x y : α} (G)
/-- `G` is not complete iff there exist distinct non-adjacent vertices -/
protected lemma ne_top_iff : G ≠ ⊤ ↔ ∃ x y, x ≠ y ∧ ¬ G.Adj x y := by
  constructor <;> intro h <;> contrapose! h
  · exact eq_top_iff.2 fun _ _ hxy ↦ h _ _ hxy.ne
  · exact fun _ _ hne ↦ h ▸ hne

variable {G} {n : ℕ}
/-- A graph `G` is `MaximalCliqueFree n` if it is maximal wrt to not containing an `n`-clique -/
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

lemma exists_isNClique_sup_edge (hne : x ≠ y) (hn : ¬ G.Adj x y) :
   ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t :=
  let ⟨t, hc⟩ := not_forall_not.1 <| h.not_cliqueFree_of_gt <| G.lt_sup_edge _ _ hne hn
  ⟨t, hc, ⟨h.1.mem_of_sup_edge_isNClique hc, h.1.mem_of_sup_edge_isNClique (edge_comm _ _ ▸ hc)⟩⟩

lemma exists_of_not_adj [DecidableEq α] (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧ G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨t, hc, xym⟩ := h.exists_isNClique_sup_edge hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (not_mem_erase _ _), not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  cases n with
  | zero => exact False.elim <| not_cliqueFree_zero h.1
  | succ n =>
    exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem xym.2, hc.erase_of_sup_edge_of_mem xym.1⟩

lemma not_cliqueFree_of_le_card [Fintype α] (hle : n - 1 ≤ Fintype.card α) :
    ¬ G.CliqueFree (n - 1) := by
  classical
  cases n with
  | zero => exact not_cliqueFree_zero
  | succ n =>
  cases hle.lt_or_eq with
  | inl hlt =>
    intro hf
    obtain ⟨_,_, hne, hn⟩ := G.ne_top_iff.1 <| h.ne_top_iff.2 hlt
    exact (h.not_cliqueFree_of_gt <| G.lt_sup_edge _ _ hne hn) <| hf.sup_edge _ _
  | inr heq =>
    exact heq ▸ (h.eq_top_iff.2 (Nat.lt_succ.2 heq.symm.le) ▸
                 (⊤ : SimpleGraph α).not_cliqueFree_card_of_top_embedding Embedding.refl)

end MaximalCliqueFree

section Turan
variable [Fintype α] [DecidableRel G.Adj]
lemma IsTuranMaximal.maximalCliqueFree (h : G.IsTuranMaximal n) : G.MaximalCliqueFree (n + 1) :=
  ⟨h.1, fun _ hcf hle ↦ h.le_iff_eq hcf |>.1 hle |>.symm.le⟩

theorem not_cliqueFree_of_isTuranMaximal' {r} (hn : r ≤ Fintype.card α) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := hG.maximalCliqueFree.not_cliqueFree_of_le_card hn

end Turan
end SimpleGraph
