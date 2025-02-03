import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Minimal
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α}  {n : ℕ} {s : Finset α} {v w : α}

lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

section DecidableEq
variable[DecidableEq α]
lemma IsNClique.erase_of_mem (hs : G.IsNClique n s) (ha : a ∈ s) :
    G.IsNClique (n - 1) (s.erase a):=by
  constructor
  · apply hs.1.subset; simp
  · rw [card_erase_of_mem ha, hs.2]

lemma IsNClique.insert_erase (hs : G.IsNClique n s) (had: ∀ w ∈ s, w ≠ b → G.Adj a w) (hb : b ∈ s):
    G.IsNClique n (Insert.insert a (erase s b)) := by
  cases n with
  | zero => exact False.elim <| not_mem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ n =>
    apply (hs.erase_of_mem hb).insert
    intro w h; rw [mem_erase] at h
    apply had w h.2 h.1

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

/-- Embedding of the complete graph on ι into completeMultipartite graph on ι nonempty parts-/
noncomputable def CompleteMultipartiteGraph.topEmbedding {ι : Type*} (V : ι → Type*)
    [∀ i, Nonempty (V i)] : (⊤ : SimpleGraph ι) ↪g (completeMultipartiteGraph V)
    where
  toFun := fun i ↦ ⟨i, Classical.arbitrary (V i)⟩
  inj' := fun i j h ↦ (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

theorem notCliqueFree_le_card_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Nonempty (V i)] (hc : n ≤ Fintype.card ι ) : ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <| (CompleteMultipartiteGraph.topEmbedding V).comp
    (Iso.completeGraph (Fintype.equivFin ι).symm).toEmbedding

theorem notCliqueFree_completeMultipartiteGraph_infinite {ι : Type*} [Infinite ι] (V : ι → Type*)
    [∀ i, Nonempty (V i)] : ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ not_cliqueFree_of_top_embedding ((CompleteMultipartiteGraph.topEmbedding V).comp
            <| Embedding.completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι) hf

section MaximalCliqueFree
variable {x y : α} {n : ℕ}

/-- A graph G is maximally Kᵣ-free if it doesn't contain Kᵣ but any supergraph does contain Kᵣ -/
abbrev MaximalCliqueFree (G : SimpleGraph α) (n : ℕ) : Prop :=
  Maximal (fun H => H.CliqueFree n) G

variable (h : G.MaximalCliqueFree n) include h
/-- If we add a new edge to a maximally r-clique-free graph we get a clique -/
protected lemma MaximalCliqueFree.sup_edge (hne : x ≠ y) (hn : ¬ G.Adj x y ) :
    ∃ t, (G ⊔ edge x y).IsNClique n t := by
  rw [MaximalCliqueFree, maximal_iff_forall_gt] at h
  convert h.2  <| G.lt_sup_edge _ _ hne hn
  simp [CliqueFree, not_forall]

variable [DecidableEq α]
/-- If G is maximally K_n-free and xy ∉ E(G) then there is a set s such that
s ∪ {x} and s ∪ {y} are both (n - 1)-cliques -/
lemma MaximalCliqueFree.exists_of_not_adj (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧ G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨t,hc⟩ := h.sup_edge hne hn
  have xym: x ∈ t ∧ y ∈ t := by
    by_contra! hf
    apply h.1 t;
    refine ⟨?_,hc.2⟩
    intro _ hu _ hv hne
    obtain (h | h) := hc.1 hu hv hne
    · exact h
    · rw [edge_adj, ne_eq] at h
      exfalso
      obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ := h
      · apply hf hu hv
      · apply hf hv hu
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (not_mem_erase _ _), not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  cases n with
  | zero => exfalso; exact not_cliqueFree_zero h.1
  | succ n =>
    exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem xym.2, hc.erase_of_sup_edge_of_mem xym.1⟩

end MaximalCliqueFree
end SimpleGraph
