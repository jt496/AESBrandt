import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Minimal
namespace SimpleGraph
variable {V : Type*} {G H: SimpleGraph V}
variable {v : V} [Fintype (G.neighborSet v)] [Fintype (H.neighborSet v)]

/-- If G is a subgraph of H then d_G(v) ≤ d_H(v) for any vertev v -/
lemma degree_le_of_le (hle : G ≤ H) :
    G.degree v ≤ H.degree v:= by
  simp only [← card_neighborSet_eq_degree]
  apply Set.card_le_card fun v hv  => by exact hle hv

section fintypeV
variable [Fintype V]
/--If V is finite and `P G` holds then there exists a maximal supergraph H of G
for which `P H` holds. -/
lemma exists_maximal_supergraph (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H, G ≤ H ∧ Maximal P H :=by
  simp_rw [maximal_iff_forall_gt]
  classical
  revert hG
  apply WellFounded.recursion (measure fun H  => Hᶜ.edgeFinset.card).wf G
  intro c hc _
  by_cases hm: ∀ d, c < d → ¬P d
  · use c
  · push_neg at hm
    obtain ⟨d,hd1,hd2⟩:=hm
    obtain ⟨e,hle,he⟩:= hc d ((fun h => Finset.card_lt_card <| edgeFinset_ssubset_edgeFinset.2
        <| compl_lt_compl_iff_lt.2 h) hd1) hd2
    use e, hd1.le.trans hle

/-- If there are no vertices then the minDegree is zero -/
@[simp]
lemma minDegree_eq_zero [DecidableRel G.Adj] [IsEmpty V] : G.minDegree = 0:= by
  rw [minDegree,WithTop.untop'_eq_self_iff]
  right
  simp

/--If G is a subgraph of H then δ(G) ≤ δ(H) -/
lemma minDegree_le_minDegree (hle : G ≤ H) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    G.minDegree  ≤ H.minDegree := by
  by_cases hne : Nonempty V
  · apply le_minDegree_of_forall_le_degree;
    intro v; apply (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)
  · rw [not_nonempty_iff] at hne
    simp

end fintypeV
