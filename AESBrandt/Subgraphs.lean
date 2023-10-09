import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

open BigOperators

namespace SimpleGraph
open Finset
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]


  
  
lemma degree_le [DecidableRel H.Adj](hle : G ≤ H) (x : α) : G.degree x ≤ H.degree x:=
by
  have subgraph : IsSubgraph G H := by
    exact hle
  unfold IsSubgraph at subgraph
  have Gsubset : neighborFinset G x ⊆ neighborFinset H x := by
    intro a
    intro adjG
    rw [mem_neighborFinset]
    rw [mem_neighborFinset] at adjG
    exact subgraph adjG
  rw [degree, degree]
  apply card_le_of_subset
  exact Gsubset    

lemma degree_le_edges : G.degree x ≤ G.edgeFinset.card:=
by
  have : incidenceFinset G x ⊆ (edgeFinset G) := by
    intro e
    intro emem
    rcases e with ⟨ u , v⟩ 
    apply mem_coe.2
    rw [mem_edgeFinset]
    apply (mem_edgeSet G).2
    rw [mem_incidenceFinset] at emem
    exact ((mk'_mem_incidenceSet_iff G).1 emem).1
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_of_subset this

    
      
    
    

lemma minDegree_le_of_le [DecidableRel H.Adj][Nonempty α] (hle : G ≤ H) : G.minDegree  ≤ H.minDegree :=
by
  have h : ∀ v, G.minDegree ≤ H.degree v := by
    by_contra p
    push_neg at p
    rcases p with ⟨ v , deg_lt ⟩
    have : H.degree v < G.degree v := by
      calc
        H.degree v < minDegree G := by 
          exact deg_lt
        _≤ G.degree v := by
          exact minDegree_le_degree G v
    have contra : ¬ H.degree v < G.degree v := by
      push_neg
      exact degree_le hle v
    contradiction
  exact le_minDegree_of_forall_le_degree H (G.minDegree) h       


/-- If G < H then Hᶜ < Gᶜ -/
lemma gt_compl_of_lt (hlt: G < H) [DecidableRel H.Adj] : Hᶜ < Gᶜ:=
by 
  have subsetGH : edgeFinset G ⊂ edgeFinset H := by
    exact edgeFinset_ssubset_edgeFinset.2 hlt
  have subsetHG : edgeFinset Hᶜ ⊂ edgeFinset Gᶜ := by
    rcases subsetGH with ⟨a ,b⟩
    constructor
    · intro x
      intro xmemHc
      rw [mem_edgeFinset]
      rw [mem_edgeFinset] at xmemHc
      rcases x with ⟨u , v⟩
      have adjuv : Adj Hᶜ u v := by
        exact (mem_edgeSet Hᶜ).1 xmemHc
      apply (mem_edgeSet Gᶜ).2
      apply (compl_adj G u v).2
      constructor 
      exact ((compl_adj H u v).2 adjuv).1
      intro adjGuv
      have : Adj H u v := by
        apply (mem_edgeSet H).1
        apply (mem_edgeFinset).1
        apply a
        apply (mem_edgeFinset).2
        apply (mem_edgeSet G).2
        exact adjGuv
      have nadjHuv : ¬ Adj H u v := by
        exact ((compl_adj H u v).2 adjuv).2
      contradiction
    contrapose! b
    intro x
    intro memH
    apply (mem_edgeFinset).2
    rcases x with ⟨u , v⟩  
    apply (mem_edgeSet G).2
    rw [mem_edgeFinset] at memH
    have : Adj H u v := by
      exact (mem_edgeSet H).1 memH
    have ne : u ≠ v := by
      exact ne_of_adj H this 
    contrapose this
    have memHc : Adj Hᶜ u v := by
      apply (mem_edgeSet Hᶜ).1
      apply mem_edgeFinset.1
      apply b
      apply mem_edgeFinset.2
      apply (mem_edgeSet Gᶜ).2
      exact (compl_adj G u v).2 ⟨ne , this⟩
    exact ((compl_adj H u v).1 memHc).2  
  exact edgeFinset_ssubset_edgeFinset.1 subsetHG

    
/-- If G is a strict subgraph of H then Hᶜ contains more edges than Gᶜ -/
lemma wf_edge_compl (hlt: G < H) [DecidableRel H.Adj] : card (Hᶜ.edgeFinset) < card (Gᶜ.edgeFinset):=
by
  have hcltgc : Hᶜ < Gᶜ := by
    exact gt_compl_of_lt hlt
  apply card_lt_card
  exact edgeFinset_ssubset_edgeFinset.2 hcltgc


/-- Given a member G of a set of graphs on a fintype α there exists a maximal element of the set
that is a supergraph of G -/
lemma pred_graph_maximal {P : SimpleGraph α → Prop } (hG: P G) : 
∃ H, G ≤ H ∧  P H  ∧ ∀ {K}, H < K →¬ P K :=
by
  classical
  revert hG
  apply WellFounded.recursion (InvImage.wf (λ F ↦ card (Fᶜ.edgeFinset)) Nat.lt_wfRel.wf) G
  intro A hA
  by_cases hm : ∀ {K}, A < K → ¬ P K 
  · intro hPA
    use A
  · intro _
    push_neg at hm
    obtain ⟨K,hK1,hK2⟩:= hm
    have := wf_edge_compl hK1
    obtain ⟨H,hH1,hH2⟩:= hA K this hK2
    use H 
    exact ⟨hK1.le.trans hH1,hH2⟩
    

end SimpleGraph