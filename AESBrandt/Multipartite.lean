import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic


namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

def CompleteMulti (G : SimpleGraph α) : Prop := Transitive (fun u v => ¬G.Adj u v)

def CompleteKPartite  (G : SimpleGraph α) (k : ℕ): Prop := G.CompleteMulti ∧ G.chromaticNumber = k

end SimpleGraph