import Mathlib.Combinatorics.SimpleGraph.Turan
import Mathlib.Order.Minimal
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α}  {n : ℕ} {s : Finset α} {v w : α}

lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

section DecidableEq
variable[DecidableEq α]

/-- If s is a clique in G ⊔ {xy} then s-{x} is a clique in G -/
lemma IsNClique.erase_of_sup_edge_of_mem  {v w : α} (hc : (G ⊔ edge v w).IsNClique n s)
(hx : v ∈ s) : G.IsNClique (n - 1) (s.erase v) := by
  constructor
  · intro u hu v hv huvne
    push_cast at *
    obtain (h | h):= hc.1 hu.1 hv.1 huvne
    · exact h
    · simp only [edge_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, ne_eq] at h
      exfalso; obtain ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩ := h
      · exact hu.2 <| Set.mem_singleton _
      · exact hv.2 <| Set.mem_singleton _
  · rw [card_erase_of_mem hx, hc.2]

/-- If G is Kₙ₊₁-free and s is an n-clique then every vertex is not adjacent to something in s -/
lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s) (h : G.CliqueFree (n + 1))
(x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y := by
  by_contra! hf
  apply (hc.insert hf).not_cliqueFree h

end DecidableEq
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

lemma eq_top_iff [Fintype α] : G = ⊤ ↔ Fintype.card α < n := by
  constructor <;> intro h'
  · have ht := (⊤ : SimpleGraph α).not_cliqueFree_card_of_top_embedding Embedding.refl
    contrapose! ht
    exact h' ▸ h.1.mono ht
  · exact h.le_iff_eq ((⊤ : SimpleGraph α).cliqueFree_of_card_lt h') |>.1 le_top

protected lemma ne_top_iff [Fintype α] : G ≠ ⊤ ↔ n ≤ Fintype.card α := by
  rw [ne_eq, h.eq_top_iff, Nat.not_lt]

/--
If we add a new edge to a maximally n-clique-free graph we get an n-clique containing x and y -/
protected lemma sup_edge (hne : x ≠ y) (hn : ¬ G.Adj x y) :
   ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t := by
  have := h.not_cliqueFree_of_gt <| G.lt_sup_edge _ _ hne hn
  simp only [CliqueFree, not_forall, not_not] at this
  obtain ⟨t, hc⟩ := this
  use t, hc
  by_contra! hf
  apply h.1 t
  refine ⟨?_, hc.2⟩
  intro _ hu _ hv hne
  obtain (h | h) := hc.1 hu hv hne
  · exact h
  · rw [edge_adj, ne_eq] at h
    exfalso
    obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ := h
    · apply hf hu hv
    · apply hf hv hu

variable [DecidableEq α]
/-- If G is maximally K_n-free and xy ∉ E(G) then there is a set s such that
s ∪ {x} and s ∪ {y} are both (n - 1)-cliques -/
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
  obtain ⟨x, y, hne, hna⟩ := G.ne_top_iff.1 (h.ne_top_iff.2 h')
  use x, y
  apply h.exists_of_not_adj hne hna

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
