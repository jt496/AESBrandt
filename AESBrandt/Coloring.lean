import Mathlib.Combinatorics.SimpleGraph.Coloring
import AESBrandt.Clique

namespace SimpleGraph
/-- The canonical coloring of a completeMultiPartiteGraph. -/
def CompleteMultipartiteGraph.coloring {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).Coloring ι := Coloring.mk (fun v => v.1) (by simp)

lemma CompleteMultipartiteGraph.colorable {ι : Type*} [Fintype ι] (V : ι → Type*) :
    (completeMultipartiteGraph V).Colorable (Fintype.card ι) :=
  (CompleteMultipartiteGraph.coloring V).colorable

theorem CompleteMultipartiteGraph.chromaticNumber {ι : Type*} [Fintype ι] (V : ι → Type*)
    [∀ i, Nonempty (V i)] : (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι := by
  apply le_antisymm (CompleteMultipartiteGraph.colorable V).chromaticNumber_le
  by_contra! h
  apply notCliqueFree_le_card_completeMultipartiteGraph V (le_rfl)
            <| cliqueFree_of_chromaticNumber_lt h

theorem CompleteMultipartiteGraph.colorable_of_cliqueFree {ι : Type*} {V : ι → Type*}
    [∀ i, Nonempty (V i)] (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => apply False.elim <| not_cliqueFree_zero hc
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf ↦ notCliqueFree_completeMultipartiteGraph_infinite V hc
  apply (CompleteMultipartiteGraph.coloring V).colorable.mono
  have := notCliqueFree_le_card_completeMultipartiteGraph V (le_rfl)
  contrapose! this
  apply hc.mono this
end SimpleGraph
