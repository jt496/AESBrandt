import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic
import AESBrandt.P3bar
import AESBrandt.MaxCliqueFree


namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]



/-- If non-adjacency is Transitive, then (since it is automatically Reflexive and Symmetric) it is an equivalence relation-/
def completeMultiPartite (G : SimpleGraph α) : Prop := Transitive (λ u v ↦ ¬G.Adj u v)

lemma completeMultiPartite.equiv (hc: G.completeMultiPartite) : Equivalence (λ u v ↦ ¬G.Adj u v):=
by  
  sorry

/-- If G is not complete-multi-partite then it contains an induced P3bar-/
lemma P3bar_of_not_completeMultiPartite (h : ¬ completeMultiPartite G): ∃ v w₁ w₂, G.P3bar v w₁ w₂:=
by
  sorry

/-- If G contains no induced P3bar then it must be complete-multi-partite -/
lemma P3barFree  (p3f: ¬ ∃ v w₁ w₂, G.P3bar v w₁ w₂) : 
G.completeMultiPartite:=
by
  sorry
  
/--  Complete r -partite = Complete-multi-partite + χ(G) = r -/
def completeMultiPartiteR (G : SimpleGraph α) (r : ℕ) : Prop := G.completeMultiPartite ∧ G.chromaticNumber = r 

/-- If G is complete-multi-paritite then it must be complete-χ(G)-partite -/
lemma complete_chrom_partite (hc: G.completeMultiPartite) : G.completeMultiPartiteR (G.chromaticNumber):=
by
  sorry
/-- If G is complete-r-partite then for every r-coloring C, if C x ≠ C y then xy must be an edge-/
lemma completeMultiPartiteR_adj_ne_col (hcpr : G.completeMultiPartiteR r) (C: G.Coloring (Fin r)) (x y: α):  
C x ≠ C y → G.Adj x y:=
by
  sorry
  
/-- If G is complete r-partite then it contains a copy of K_r -/
lemma not_cliquefree_of_complete_multi_partite (hcpr: G.completeMultiPartiteR r) : ¬ G.CliqueFree r:=
by
  sorry

end SimpleGraph