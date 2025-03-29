import Mathlib.Combinatorics.SimpleGraph.Coloring
import AESBrandt.Clique
-- NOTE this is all in PR #21479 aes_completeMultipartiteGraph
namespace SimpleGraph
/-- The canonical coloring of a completeMultiPartiteGraph. -/
def completeMultipartiteGraph.coloring {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).Coloring ι := Coloring.mk (fun v => v.1) (by simp)

lemma completeMultipartiteGraph.colorable {ι : Type*} [Fintype ι] (V : ι → Type*) :
    (completeMultipartiteGraph V).Colorable (Fintype.card ι) :=
  (completeMultipartiteGraph.coloring V).colorable

theorem completeMultipartiteGraph.chromaticNumber {ι : Type*} [Fintype ι] (V : ι → Type*)
    (f : ∀ (i : ι), V i) : (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι := by
  apply le_antisymm (completeMultipartiteGraph.colorable V).chromaticNumber_le
  by_contra! h
  apply completeMultipartiteGraph.not_CliqueFree_le_card V f le_rfl
            <| cliqueFree_of_chromaticNumber_lt h

theorem completeMultipartiteGraph.colorable_of_cliqueFree {ι : Type*} {V : ι → Type*}
    (f : ∀ (i : ι), V i) (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => apply absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf ↦ completeMultipartiteGraph.not_CliqueFree_infinite V f hc
  apply (completeMultipartiteGraph.coloring V).colorable.mono
  have := completeMultipartiteGraph.not_CliqueFree_le_card V f le_rfl
  contrapose! this
  apply hc.mono this
end SimpleGraph
