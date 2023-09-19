import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

open BigOperators

namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

/--P3bar is a 3-set with one edge and 2 non-edges -/
structure P3bar (v w₁ w₂ : α): Prop where 
  edge : G.Adj w₁ w₂  -- w₁w₂ ∈ E(G) 
  nonedge : ¬G.Adj v w₁ ∧ ¬G.Adj v w₂ -- vw₁, vw₂ ∉ E(G)

#check P3bar.nonedge


lemma P3bar.ne  (p3: G.P3bar v w₁ w₂) : v ≠ w₁ ∧ v ≠ w₂  :=
by
  sorry
/--  we can swap w₁ and w₂ in the definition of P3bar-/
lemma P3bar.comm  (p3: G.P3bar v w₁ w₂) : G.P3bar v w₁ w₂ ↔ G.P3bar v w₂ w₁ :=
by
  -- have hne:=p3.ne
  -- have hedge:=p3.edge
  sorry

end SimpleGraph
