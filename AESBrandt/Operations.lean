import Mathlib.Combinatorics.SimpleGraph.Operations
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α} {s t : α}

lemma edge_comm : edge s t = edge t s := by
  simp [edge, Sym2.eq_swap]

lemma lt_sup_edge (hne: s ≠ t) (hnadj: ¬G.Adj s t ) : G < G ⊔ edge s t :=
  left_lt_sup.2 fun h => hnadj <| h (by tauto)

end SimpleGraph
