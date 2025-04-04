/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import AESBrandt.Coloring

/-!
# Complete Multipartite Graphs

A graph is complete multipartite iff non-adjacency is transitive.

## Main declarations
* `SimpleGraph.IsCompleteMultipartite`: predicate for a graph to be complete-multi-partite.

* `SimpleGraph.IsCompleteMultipartite.setoid`: the Setoid given by non-adjacency.

* `SimpleGraph.IsCompleteMultipartite.iso`: the graph isomorphism from a graph that
  `IsCompleteMultipartite` to the corresponding `completeMultipartiteGraph`.

* `SimpleGraph.IsP2Complement`: predicate for three vertices to be a witness to
   non-complete-multi-partiteness of a graph G.
   
(The name refers to the fact that the three vertices form the complement of a path of length two.)
-/

universe u
namespace SimpleGraph
variable {α : Type u} {G : SimpleGraph α}

/-- `G` is `IsCompleteMultipartite` iff non-adjacency is transitive. -/
abbrev IsCompleteMultipartite (G : SimpleGraph α) : Prop := Transitive (¬ G.Adj · ·)

/-- The setoid given by non-adjacency -/
abbrev IsCompleteMultipartite.setoid (h : G.IsCompleteMultipartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless , fun h' ↦ by rwa [adj_comm] at h', fun h1 h2 ↦ h h1 h2⟩⟩

/-- Any `completeMultipartiteGraph V` `IsCompleteMultipartite` -/
lemma completeMultipartiteGraph.isCompleteMultipartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompleteMultipartite := by
  intro
  aesop

/-- The graph isomorphism from a graph `G` that `IsCompleteMultipartite` to the corresponding
`completeMultipartiteGraph`. -/
def IsCompleteMultipartite.iso (h : G.IsCompleteMultipartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) ↦ { x // h.setoid.r c.out x}) where
  toFun := fun v ↦ ⟨_, ⟨v, Quotient.mk_out v⟩⟩
  invFun := fun ⟨_, x⟩ ↦  x.1
  left_inv := fun _ ↦ rfl
  right_inv := fun ⟨_, x⟩ ↦ Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros; change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

lemma isCompleteMultipartite_iff : G.IsCompleteMultipartite ↔ ∃ (ι : Type u) (V : ι → Type u)
  (_ : ∀ i, (Nonempty (V i))), Nonempty (G ≃g (completeMultipartiteGraph V)) := by
  constructor <;> intro h
  · exact ⟨_, _, fun _ ↦ ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    intro _ _ _ h1 h2
    rw [← e.map_rel_iff] at *
    exact (completeMultipartiteGraph.isCompleteMultipartite _) h1 h2

lemma IsCompleteMultipartite.colorable_of_cliqueFree {n : ℕ} (h : G.IsCompleteMultipartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) :=
    (completeMultipartiteGraph.colorable_of_cliqueFree (fun _ ↦ ⟨_, h.setoid.refl _⟩)
          <| hc.comap h.iso.symm).of_embedding h.iso.toEmbedding

variable (G) in
/--
The vertices `v, w₁, w₂` form an `IsP2Complement` in the graph `G` iff `w₁w₂` is the only adj
present between these three vertices. It is a witness to the non-complete-multipartite-ness of `G`
-/
structure IsP2Complement (v w₁ w₂ : α) : Prop where
  adj : G.Adj w₁ w₂
  not_adj : ¬ G.Adj v w₁ ∧ ¬ G.Adj v w₂

namespace IsP2Complement

variable {v w₁ w₂ : α}
lemma ne (p2 : G.IsP2Complement v w₁ w₂) : v ≠ w₁ ∧ v ≠ w₂ :=
  ⟨fun hvw1 ↦ p2.not_adj.2 (hvw1.symm ▸ p2.adj),fun hvw2 ↦ p2.not_adj.1 (hvw2 ▸ p2.adj.symm)⟩

lemma symm (h : G.IsP2Complement v w₁ w₂) : G.IsP2Complement v w₂ w₁:= by
  obtain ⟨ed, ⟨n1, n2⟩⟩ := h
  exact ⟨ed.symm, ⟨n2, n1⟩⟩

end IsP2Complement

/-- If `G` is not complete-multipartite then it contains `v, w₁, w₂` such that
`G.IsP2Complement v w₁ w₂` -/
lemma exists_isP2Complement_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite G) :
    ∃ v w₁ w₂, G.IsP2Complement v w₁ w₂ := by
  rw [IsCompleteMultipartite, Transitive] at h
  push_neg at h
  obtain ⟨w₁, v, w₂, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨v, w₁, w₂, h3, h1, h2⟩

lemma not_isCompleteMultipartite_iff_exists_isP2Complement :
  ¬ IsCompleteMultipartite G ↔ ∃ v w₁ w₂, G.IsP2Complement v w₁ w₂ := by
  exact ⟨fun h ↦ G.exists_isP2Complement_of_not_isCompleteMultipartite h,
        fun ⟨v, w₁, w₂, e, m, n⟩ ↦ fun h ↦ h (by rwa [adj_comm] at m) n e⟩

end SimpleGraph
