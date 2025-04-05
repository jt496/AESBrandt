/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph
#check SimpleGraph.completeMultipartiteGraph



/-- Given a family of vertex types indexed by `ι`, pulling back from `H : SimpleGraph ι`
yields the blow-up graph on the family. Two vertices are adjacent if and only if their
indices are adjacent in `H`. -/
abbrev blowupGraph {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  SimpleGraph.comap Sigma.fst H

lemma blowupGraph_adj {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) (x y : Σ i, V i) :
    (blowupGraph H V).Adj x y ↔ H.Adj x.1 y.1 := by rfl

/-- Embedding of `H` into `blowupGraph H V` with nonempty parts.-/
def blowupGraph.selfEmbedding {ι : Type*} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ (i : ι), V i) :
    H ↪g (blowupGraph H V) := ⟨⟨fun i ↦ ⟨i, f i⟩, fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1⟩, by simp⟩

lemma blowupGraph_top {ι : Type*} (V : ι → Type*) :
    blowupGraph ⊤ V = completeMultipartiteGraph V := rfl

lemma blowupGraph_bot {ι : Type*} (V : ι → Type*) : blowupGraph ⊥ V = ⊥ := rfl

lemma blowupGraph_cliqueFree_iff  {ι : Type*} {n : ℕ} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ i, (V i)) :
    H.CliqueFree n ↔ (blowupGraph H V).CliqueFree n := by
  constructor <;> intro h
  · rw [cliqueFree_iff, isEmpty_iff] at *
    intro e
    apply h
    use ⟨Sigma.fst ∘ e, fun a b (h : (e a).fst = (e b).fst) ↦ by
      by_contra!
      rw [← top_adj, ← e.map_adj_iff, blowupGraph_adj, h] at this
      exact H.loopless _ this⟩
    dsimp
    intros
    rw [← blowupGraph_adj, e.map_adj_iff]
  · exact h.comap (blowupGraph.selfEmbedding _ _ f)

lemma blowupGraph_colorable_iff  {ι : Type*} {n : ℕ} (H : SimpleGraph ι) (V : ι → Type*) (f : ∀ i, (V i)) :
    H.Colorable n ↔ (blowupGraph H V).Colorable n := by
  constructor <;> intro ⟨c⟩
  · exact ⟨fun x ↦ c x.fst, fun h1 h2 ↦ c.valid h1 h2⟩
  · exact ⟨fun x ↦ c ⟨x, f x⟩, by intro a b had; exact c.valid (by rwa [blowupGraph_adj])⟩

open ConnectedComponent Subgraph

def coloringOfComponents {α β: Type*} {G : SimpleGraph α}
    (h : ∀ (c : G.ConnectedComponent), (G.induce c.supp).Coloring β) :
    G.Coloring β := by
  exact ⟨fun v ↦ h (G.connectedComponentMk v) ⟨v, rfl⟩, by
    simp only [top_adj]
    intro a b hab heq
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk a).supp).Adj ⟨a, rfl⟩
       ⟨b, ((G.connectedComponentMk a).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    exact (h _).valid hadj (by convert heq)⟩

variable {α : Type*} {n : ℕ} {G : SimpleGraph α}
theorem colorable_iff_forall_connectedComponents  :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c.supp).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
     fun h ↦ ⟨coloringOfComponents (fun c ↦ (h c).some)⟩⟩

/-- `G` is `n`-colorable if all its induced connected subgraphs are `n`-colorable-/
theorem colorable_iff_induced_connected :
    (∀ s, (G.induce s).Connected → (G.induce s).Colorable n) ↔ G.Colorable n := by
  constructor <;> intro h
  · rw [colorable_iff_forall_connectedComponents]
    intro c
    apply h
    rw [connected_induce_iff, connected_iff_forall_exists_walk_subgraph]
    refine ⟨c.nonempty_supp,?_⟩
    intro u v hu hv
    simp_rw [induce_verts, mem_supp_iff] at hu hv
    have : G.connectedComponentMk u = G.connectedComponentMk v := by
      rw [hv, hu]
    obtain ⟨w⟩ := ConnectedComponent.exact this
    use w
    induction w with
    | nil => simpa
    | cons h p ih =>
      simp_rw [Walk.toSubgraph, sup_le_iff]
      constructor
      · apply subgraphOfAdj_le_of_adj
        simpa using ⟨hu, hu.symm ▸ connectedComponentMk_eq_of_adj h.symm, h⟩
      · exact ih (hu.symm ▸ connectedComponentMk_eq_of_adj h.symm)
                hv (ConnectedComponent.sound ⟨p⟩)
  · intro s _
    obtain ⟨C⟩ := h
    exact ⟨fun v ↦ (C v.1), fun a ↦ Hom.map_adj C a⟩


end SimpleGraph
