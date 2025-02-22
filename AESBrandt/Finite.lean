import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Minimal
namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V]
/--If `V` is finite and `P G` holds then there exists a maximal supergraph `H` of `G`
for which `P H` holds. -/
lemma exists_maximal_supergraph (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H, G ≤ H ∧ Maximal P H :=
  let ⟨_ , ⟨h1, h2⟩, hm⟩ := wellFounded_gt.has_min {H | G ≤ H ∧ P H} ⟨_, ⟨le_rfl, hG⟩⟩
  ⟨_, ⟨h1, h2, fun _ hk hf ↦ (eq_of_ge_of_not_gt hf (hm _ ⟨h1.trans hf, hk⟩)).le⟩⟩


lemma exists_maximal_supergraph' (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H, G ≤ H ∧ Maximal P H := by
  simp_rw [maximal_iff_forall_gt]
  classical
  revert hG
  apply WellFounded.recursion (measure fun H  => Hᶜ.edgeFinset.card).wf G
  intro c hc _
  by_cases hm: ∀ d, c < d → ¬P d
  · use c
  · push_neg at hm
    obtain ⟨d, hd1, hd2⟩ := hm
    obtain ⟨e, hle, he⟩:= hc d ((fun h ↦ Finset.card_lt_card
        <| edgeFinset_ssubset_edgeFinset.2 <| compl_lt_compl_iff_lt.2 h) hd1) hd2
    use e, hd1.le.trans hle
end SimpleGraph
