import AESBrandt.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}
@[simp]
lemma colorable_zero_iff : G.Colorable 0 ↔ IsEmpty α :=
   ⟨fun h => G.isEmpty_of_colorable_zero h, fun _ => G.colorable_of_isEmpty 0⟩

end SimpleGraph
