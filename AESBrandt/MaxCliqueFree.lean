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
  sorry


/-- If G is maximal K_r+2 - free and xy ∉ E(G) then there is a set s (of card r) such that s∪{x} and s∪{y} are both 
(r+1)-cliques -/
lemma non_edge_maxcf (h: G.MaxCliqueFree (r+1)) (hne: x ≠ y) (hnadj: ¬G.Adj x y ) :
 ∃ (s:Finset α), x ∉ s ∧ y ∉ s ∧ G.IsNClique r (insert x s) ∧ G.IsNClique r (insert y s) :=
by
  sorry



end SimpleGraph