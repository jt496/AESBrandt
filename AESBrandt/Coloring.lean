import Mathlib.Combinatorics.SimpleGraph.Coloring
import AESBrandt.Clique
-- NOTE this is all in PR #21479 aes_completeMultipartiteGraph
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
  apply CompleteMultipartiteGraph.notCliqueFree_le_card V le_rfl
            <| cliqueFree_of_chromaticNumber_lt h

theorem CompleteMultipartiteGraph.colorable_of_cliqueFree {ι : Type*} {V : ι → Type*}
    [∀ i, Nonempty (V i)] (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => apply absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf ↦ CompleteMultipartiteGraph.notCliqueFree_infinite V hc
  apply (CompleteMultipartiteGraph.coloring V).colorable.mono
  have := CompleteMultipartiteGraph.notCliqueFree_le_card V le_rfl
  contrapose! this
  apply hc.mono this
end SimpleGraph
