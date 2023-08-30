import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

open BigOperators

namespace SimpleGraph
open Finset
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

#check card_neighborFinset_eq_degree
#check card_eq_sum_ones
#check sum_comm'

/-- Basic double counting: given a Finset of vertices s we have: 
 ∑ v ∈ V, |Γ(v)∩ s| = ∑ v ∈ s, d(v)  -/
lemma double_counting (s : Finset α) :
    ∑ v, (G.neighborFinset v ∩ s).card = ∑ v in s, G.degree v :=
by
  sorry
lemma degree_le [DecidableRel H.Adj](hle : G ≤ H) (x : α) : G.degree x ≤ H.degree x:=
by
  sorry

lemma degree_le_edges : G.degree x ≤ G.edgeFinset.card:=
by
  sorry

lemma minDegree_le_of_le [DecidableRel H.Adj][Nonempty α] (hle : G ≤ H) : G.minDegree  ≤ H.minDegree :=
by
  sorry

/-- If G < H then Hᶜ < Gᶜ -/
lemma gt_compl_of_lt (hlt: G < H) [DecidableRel H.Adj] : Hᶜ < Gᶜ:=
by 
  sorry

/-- If G is a strict subgraph of H then Hᶜ contains more edges than Gᶜ -/
lemma wf_edge_compl (hlt: G < H) [DecidableRel H.Adj] : card (Hᶜ.edgeFinset) < card (Gᶜ.edgeFinset):=
by
  sorry

end SimpleGraph