import AESBrandt.Operations
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Minimal
namespace SimpleGraph
open Finset
variable {α : Type*} {G : SimpleGraph α}  {n : ℕ} {s : Finset α} {v w : α}
@[simp] lemma cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α :=by
  constructor
  · simp only [CliqueFree, isNClique_one, not_exists, forall_eq_apply_imp_iff]
    exact fun a => { false := a }
  · intro h t hf; simp_all

section DecidableEq
variable[DecidableEq α]
lemma IsNClique.erase_of_mem (hs : G.IsNClique (n + 1) s) (ha : a ∈ s) :
    G.IsNClique n (s.erase a):=by
  constructor
  · apply hs.1.subset; simp
  · rw [card_erase_of_mem ha,hs.2]
    rfl

lemma IsNClique.insert_erase (hs : G.IsNClique n s) (had: ∀ w ∈ s, w ≠ b → G.Adj w a) (hb : b ∈ s):
    G.IsNClique n (Insert.insert a (erase s b)) := by
  cases n with
  | zero => simp_all
  | succ n =>
    apply (hs.erase_of_mem hb).insert
    intro w h; rw [mem_erase] at h; symm
    apply had w h.2 h.1

/-- If s is a clique in G ⊔ {xy} then s-{x} is a clique in G -/
lemma IsNClique.erase_of_sup_edge_of_mem  {v w : α} (hc: (G ⊔ edge v w).IsNClique (n + 1) s)
(hx : v ∈ s) : G.IsNClique n (s.erase v):=by
  constructor
  · intro u hu v hv huvne
    push_cast at *
    obtain (h | h):= (hc.1 hu.1 hv.1 huvne)
    · exact h
    · simp only [edge_adj, Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, ne_eq] at h
      exfalso; obtain ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩:=h
      · exact hu.2 <| Set.mem_singleton _
      · exact hv.2 <| Set.mem_singleton _
  · rw [card_erase_of_mem hx,hc.2]
    rfl

/-- If G is Kᵣ₊₁-free and s is an r-clique then every vertex is not adjacent to something in s -/
lemma IsNClique.exists_non_adj_of_cliqueFree_succ (hc : G.IsNClique n s) (h: G.CliqueFree (n + 1))
(x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y:= by
  by_contra! hf
  apply (hc.insert hf).not_cliqueFree h

end DecidableEq
section MaxCliqueFree
variable {x y : α} {n : ℕ}

/-- A graph G is maximally Kᵣ-free if it doesn't contain Kᵣ but any supergraph does contain Kᵣ -/
abbrev MaxCliqueFree (G : SimpleGraph α) (r : ℕ) : Prop :=
  Maximal (fun H => H.CliqueFree r) G

/-- If we add a new edge to a maximally r-clique-free graph we get a clique -/
protected lemma MaxCliqueFree.sup_edge (h: G.MaxCliqueFree n) (hne: x ≠ y) (hn: ¬G.Adj x y ):
    ∃ t, (G ⊔ edge x y).IsNClique n t:=by
  rw [MaxCliqueFree, maximal_iff_forall_gt] at h
  convert h.2  <| G.lt_sup_edge hne hn
  simp [CliqueFree, not_forall, not_not]

variable [DecidableEq α]
/-- If G is maximally Kᵣ₊₁-free and xy ∉ E(G) then there is a set s such that
s ∪ {x} and s ∪ {y} are both (r + 1)-cliques -/
lemma MaxCliqueFree.exists_of_not_adj (h: G.MaxCliqueFree (n + 1)) (hne: x ≠ y) (hn: ¬G.Adj x y):
 ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique n (insert x s) ∧ G.IsNClique n (insert y s) := by
  obtain ⟨t,hc⟩:= h.sup_edge hne hn
  have xym: x ∈ t ∧ y ∈ t:= by
    by_contra! hf
    apply h.1 t;
    constructor
    · intro u hu v hv hne
      obtain (h | h):=(hc.1 hu hv hne)
      · exact h
      · simp only [edge_adj, ne_eq] at h
        exfalso
        obtain ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,_⟩:=h
        · apply hf hu hv
        · apply hf hv hu
    · exact hc.2
  use (t.erase x).erase y, erase_right_comm (a:=x) ▸ (not_mem_erase _ _),not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  exact ⟨(edge_comm ▸ hc).erase_of_sup_edge_of_mem xym.2,hc.erase_of_sup_edge_of_mem xym.1⟩

end MaxCliqueFree
end SimpleGraph
