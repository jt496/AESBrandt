import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic


namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

/-- If non-adjacency is Transitive, then (since it is automatically Reflexive and Symmetric) it is an equivalence relation-/
def completeMultiPartite (G : SimpleGraph α) : Prop := Transitive (λ u v ↦ ¬G.Adj u v)


/--  Complete r -partite = Complete-multi-partitie + χ(G) = r -/
def completeMultiPartiteR (G : SimpleGraph α) (r : ℕ) : Prop := G.completeMultiPartite ∧ G.chromaticNumber = r 


end SimpleGraph