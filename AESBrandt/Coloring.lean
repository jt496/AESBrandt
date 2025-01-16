import AESBrandt.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
@[simp]
theorem colorable_of_cliqueFree_one (h : G.CliqueFree 1) : G.Colorable n :=by
  have :=isEmpty_of_cliqueFree_one h
  exact colorable_of_isEmpty G n

end SimpleGraph
