import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic
import AESBrandt.Chromatic
import AESBrandt.Clique
import AESBrandt.Subgraphs

namespace SimpleGraph
open Finset
variable {α : Type _} {G : SimpleGraph α} [Fintype α] [DecidableEq α][DecidableRel G.Adj]

/-- A graph G is maximal K_r-free if it doesn't contain K_r but any supergraph does contain 
K_r -/
def MaxCliqueFree (G : SimpleGraph α) (r : ℕ): Prop:= G.CliqueFree r ∧  ∀ H,
 G < H → ¬ H.CliqueFree r
 

/-- If G is K_r-free then there exists  H, maximally K_r-free such that G is a subgraph of H -/
lemma exists_maxcf_super (hcf: G.CliqueFree r) : ∃ H, G ≤ H ∧ H.MaxCliqueFree r:=
by 
  exact pred_graph_maximal hcf


/-- If G is maximal K_r+2 - free and xy ∉ E(G) then there is a set s (of card r) such that s∪{x} and s∪{y} are both 
(r+1)-cliques -/
lemma non_edge_maxcf (h: G.MaxCliqueFree (r+1)) (hne: x ≠ y) (hnadj: ¬G.Adj x y ) :
 ∃ (s:Finset α), x ∉ s ∧ y ∉ s ∧ G.IsNClique r (insert x s) ∧ G.IsNClique r (insert y s) :=
by
  have Gxy_nclique_free : ¬ (G ⊔ (fromEdgeSet {⟦(x,y)⟧})).CliqueFree (r+1) := by
    apply (h.2 (G ⊔ (fromEdgeSet {⟦(x,y)⟧}))) 
    exact lt_of_insert_newedge hne hnadj
  unfold CliqueFree at Gxy_nclique_free
  push_neg at Gxy_nclique_free
  rcases Gxy_nclique_free with ⟨t , t_clique⟩
  have t_not_Gclique :  ¬IsClique G ↑t := by
    have : ¬G.IsNClique (r+1) t  := by
      exact h.1 t
    rw [isNClique_iff G] at this
    push_neg at this
    intro isClique
    apply this isClique
    exact t_clique.2
  have yint : y ∈ t := by
    rw [← mem_coe]
    exact (mem_of_new_clique t_clique.1 t_not_Gclique).2
  have xint : x ∈ t := by
    rw [← mem_coe]
    exact (mem_of_new_clique t_clique.1 t_not_Gclique).1
  have  xinty : x ∈ erase t y := by
    apply mem_erase.2
    exact ⟨ hne, xint⟩  
  use erase (erase t x) y
  have yintx : y ∈ erase t x := by
    apply mem_erase.2
    exact ⟨hne.symm , yint⟩   
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [erase_right_comm]
    exact not_mem_erase x (erase t y)
  · exact not_mem_erase y (erase t x) 
  · rw [erase_right_comm, insert_erase xinty ]
    refine ⟨?_, ?_⟩
    · apply clique_erase_insert_edge 
      rw [Sym2.eq_swap] at t_clique
      exact t_clique.1
    · have add_one: card (erase t y) = r ↔ card (erase t y) + 1 = r + 1 := by
        exact Iff.symm Nat.add_right_cancel_iff 
      rw [add_one]
      rw [card_erase_add_one yint]
      exact t_clique.2
  · rw [insert_erase yintx]
    apply clique_erase_insert_edge 
    exact t_clique.1
  · rw [insert_erase yintx]
    have add_one: card (erase t x) = r ↔ card (erase t x) + 1 = r + 1 := by
      exact Iff.symm Nat.add_right_cancel_iff 
    rw [add_one]
    rw [card_erase_add_one xint]
    exact t_clique.2

 


end SimpleGraph