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
  apply edgeSet_ssubset_edgeSet.1
  constructor
  · intro E
    intro in_edgeset
    simp
    left
    exact in_edgeset
  · intro h
    rw [edgeSet_subset_edgeSet ] at h
    nth_rw 1 [ ← fromEdgeSet_edgeSet G  ] at h
    rw [fromEdgeSet_sup] at h
    apply hnadj
    apply h
    apply (fromEdgeSet_adj (edgeSet G ∪ {Quotient.mk (Sym2.Rel.setoid α) (x, y)})).2
    constructor
    · right
      exact rfl
    · exact hne
 

--- If we add a vertex to a subset of its nbhd that is a clique we get a new (bigger) clique
lemma isClique_insert_vertex (hB :∀ b, b ∈ B → G.Adj v b) (hBc: IsClique G B): 
 IsClique G (insert v B) :=
by
  unfold IsClique
  unfold Set.Pairwise
  rintro x  xmem y ymem xney
  by_cases (x = v) 
  · rw [h]
    apply hB
    rw [h] at xney
    exact Set.mem_of_mem_insert_of_ne ymem xney.symm
  · have hx : ¬ x = v := by 
      exact h
    by_cases (y = v) 
    · symm
      rw [h]
      apply hB 
      rw [h] at xney
      exact Set.mem_of_mem_insert_of_ne xmem xney
    · apply hBc
      · exact Set.mem_of_mem_insert_of_ne xmem hx
      · exact Set.mem_of_mem_insert_of_ne ymem h
      exact xney


/-- If s is a clique in G ⊔ {xy} but not in G then x ∈ s and y ∈ s -/
lemma mem_of_new_clique (hc: (G ⊔ (fromEdgeSet {⟦(x,y)⟧})).IsClique s) (hnc : ¬G.IsClique s) : x ∈ s ∧ y ∈ s:=
by
  contrapose! hnc 
  unfold IsClique
  unfold Set.Pairwise
  rintro u umems v vmems unev
  rw [← fromEdgeSet_edgeSet G , fromEdgeSet_sup] at hc 
  have : Adj (fromEdgeSet (edgeSet G ∪ {Quotient.mk (Sym2.Rel.setoid α) (x, y)})) u v := by
    apply hc 
    · exact umems
    · exact vmems
    · exact unev
  rw [fromEdgeSet_adj] at this  
  rcases this with ⟨memedge , unev2⟩  
  rcases memedge with h1 | h2
  · rw[mem_edgeSet] at h1
    exact h1
  · rw [Set.mem_singleton_iff] at h2
    simp at h2
    rcases h2 with ⟨ux , vy⟩ | ⟨uy , vx⟩ 
    by_cases (x = u)
    · rw [← h] at umems
      have : ¬y ∈ s := by
        exact hnc umems
      rw [vy] at vmems  
      contradiction
    · symm at ux
      contradiction
    by_cases (x = v) 
    · rw [h] at hnc 
      rw [← uy] at hnc
      have : ¬u ∈ s := by
        exact hnc vmems
      contradiction
    · symm at vx
      contradiction
    
  
        




/-- If s is a clique in G ⊔ {xy} then s-{x}-/
lemma clique_erase_insert_edge (hc: (G ⊔ (fromEdgeSet {⟦(x,y)⟧})).IsClique (s:Finset α)) :
 G.IsClique (s.erase x):=
by
  unfold IsClique
  unfold Set.Pairwise
  rintro u umem v vmem unev 
  rw [mem_coe] at umem 
  rw [mem_erase] at umem 
  rw [mem_coe] at vmem
  rw [mem_erase] at vmem 
  rcases umem with ⟨ unex , umems ⟩
  rcases vmem with ⟨ vnex , vmems ⟩ 
  rw [← fromEdgeSet_edgeSet G , fromEdgeSet_sup] at hc 
  have : Adj (fromEdgeSet (edgeSet G ∪ {Quotient.mk (Sym2.Rel.setoid α) (x, y)})) u v := by
    apply hc 
    · exact umems
    · exact vmems
    · exact unev
  rw [fromEdgeSet_adj] at this  
  rcases this with memG | nmemG
  · exact (mem_edgeSet G).1 memG
  · rw [Set.mem_singleton_iff] at nmemG
    simp at nmemG
    rcases nmemG with ⟨ux , vy⟩ | ⟨uy , vx⟩ 
    · contradiction
    · contradiction  
 

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
  /-rw [isNClique_iff]
  constructor
  · unfold IsClique
    unfold Set.Pairwise
    rintro a amem b bmem aneb-/

end SimpleGraph