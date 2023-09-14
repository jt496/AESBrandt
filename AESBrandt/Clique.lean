import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

/-
Useful facts about (building) cliques
-/

namespace SimpleGraph
open Finset
variable {α : Type _} {G : SimpleGraph α} [Fintype α] [DecidableEq α] [DecidableRel G.Adj]


/-- If xy ∉ E(G) then G < G ⊔ {xy} -/
lemma lt_of_insert_newedge {G: SimpleGraph α} (hne: x ≠ y) (hnadj: ¬G.Adj x y ) : G < G ⊔ (fromEdgeSet {⟦(x,y)⟧}):=
by
  sorry



--- If we add a vertex to a subset of its nbhd that is a clique we get a new (bigger) clique
lemma isClique_insert_vertex (hB :∀ b, b ∈ B → G.Adj v b) (hBc: IsClique G B): 
 IsClique G (insert v B) :=
by
  sorry


/-- If s is a clique in G ⊔ {xy} but not in G then x ∈ s and y ∈ s -/
lemma mem_of_new_clique (hc: (G ⊔ (fromEdgeSet {⟦(x,y)⟧})).IsClique s) (hnc : ¬G.IsClique s) : x ∈ s ∧ y ∈ s:=
by
  sorry

/-- If s is a clique in G ⊔ {xy} then s-{x}-/
lemma clique_erase_insert_edge (hc: (G ⊔ (fromEdgeSet {⟦(x,y)⟧})).IsClique (s:Finset α)) :
 G.IsClique (s.erase x):=
by
  sorry
/-
The next lemma describes a simple situation when a clique can be altered by erasing one vertex and 
inserting another to give a new clique of the same size.

More precisely, if s ∪ {v} is a clique (with v ∉ s), a ∈ s and v ≠ x  and every member of the 
clique (except possibly a) is adjacent to x, then we can form a new clique by removing a and 
inserting x (and the new clique has the same size)
-/
  
/-- Given an (r+1)-clique under certain simple conditions we can swap a vertex from the clique with a new vertex to build
a new (r+1)-clique -/
lemma clique_iie (hc: IsNClique G (r+1) (insert v s)) (has: a ∈ s) (hvs: v ∉ s) (hvx: v ≠ x)
(had: ∀ w ∈ (insert v s), w ≠ a → G.Adj x w)
: IsNClique G (r+1) (insert v (insert x (erase s a))):=
by
  sorry
end SimpleGraph