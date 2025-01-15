import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Minimal
namespace SimpleGraph
variable {V : Type*} {G H: SimpleGraph V}

variable {v : V} [Fintype (G.neighborSet v)] [Fintype (H.neighborSet v)]
/-- If G is a subgraph of H then d_G(v) ≤ d_H(v) for any vertev v -/
lemma degree_le (hle : G ≤ H) :
    G.degree v ≤ H.degree v:= by
  simp only [← card_neighborSet_eq_degree]
  apply Set.card_le_card fun v hv  => by exact hle hv
/-- If `P G` holds and `G` has finitely many edges then there exists an edge minimal
subgraph H of G for which `P H` holds. -/
lemma exists_minimal_subgraph (P : SimpleGraph V → Prop) (hG : P G) [Fintype G.edgeSet] :
    ∃ H, H ≤ G ∧ Minimal P H:=by
  let p : ℕ → Prop := fun n => ∃ H, ∃ _ : Fintype (H.edgeSet), H ≤ G ∧ P H ∧ H.edgeFinset.card ≤ n
  have h : p G.edgeFinset.card := by
    use G, inferInstance
  classical
  obtain ⟨H,_,hH⟩:=Nat.find_spec ⟨_,h⟩
  use H, hH.1
  rw [minimal_iff_forall_lt]
  use hH.2.1
  intro K hK
  have hFin : Fintype K.edgeSet :=
    Set.fintypeSubset G.edgeSet (edgeSet_subset_edgeSet.2 <| hK.le.trans hH.1)
  have hKc: K.edgeFinset.card < H.edgeFinset.card :=
    (Finset.card_lt_card <| edgeFinset_ssubset_edgeFinset.2 hK)
  have := Nat.find_min ⟨_,h⟩ (lt_of_lt_of_le hKc hH.2.2)
  dsimp [p] at this
  push_neg at this
  intro hF
  apply Nat.lt_irrefl K.edgeFinset.card
  exact this K hFin (lt_of_lt_of_le hK hH.1).le hF

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
    intro v; apply (G.minDegree_le_degree v).trans (G.degree_le hle)
  · rw [not_nonempty_iff] at hne
    simp

/--If G is a subgraph of H then Δ(G) ≤ Δ(H) -/
lemma maxDegree_le_maxDegree (hle : G ≤ H)[DecidableRel G.Adj] [DecidableRel H.Adj] :
    G.maxDegree  ≤ H.maxDegree := by
  apply maxDegree_le_of_forall_degree_le
  intro v
  apply (G.degree_le hle).trans <| H.degree_le_maxDegree v

end fintypeV
