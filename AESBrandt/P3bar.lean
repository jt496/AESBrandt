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
  constructor
  · intro veqw1
    apply p3.nonedge.2
    rw [veqw1]
    exact p3.edge
  · intro veqw2
    apply p3.nonedge.1
    rw [veqw2]
    symm
    exact p3.edge

/--  we can swap w₁ and w₂ in the definition of P3bar-/
lemma P3bar.comm  (p3: G.P3bar v w₁ w₂) : G.P3bar v w₁ w₂ ↔ G.P3bar v w₂ w₁ :=
by
  --have hne:=p3.ne
  --have hedge:=p3.edge
  constructor
  all_goals
  · intro p3_12
    refine {edge := p3_12.edge.symm , nonedge := ⟨ p3_12.nonedge.2 , p3_12.nonedge.1 ⟩ }
  

end SimpleGraph
