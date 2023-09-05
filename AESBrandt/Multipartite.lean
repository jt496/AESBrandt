import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

open BigOperators

namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

lemma not_col_of_chrom_succ (h : G.chromaticNumber = k + 1) : ¬ G.Colorable k:=
by 
  sorry


lemma chromatic_succ_verts (h : G.chromaticNumber = k + 1) (C : G.Coloring (Fin (k+1))) : ∀ i, ∃ v, C v = i :=
by
  by_contra hc
  push_neg at hc
  apply G.not_col_of_chrom_succ h
  sorry


lemma chromatic_succ_edges (h : G.chromaticNumber = k + 1) (C : G.Coloring (Fin (k+1))) : ∀ i j, i ≠ j →  ∃ u v, C u = i ∧ C v = j ∧ G.Adj u v:=
by
  sorry


def CompleteMulti (G : SimpleGraph α) : Prop := Transitive (fun u v => ¬G.Adj u v)

def CompleteKPartite  (G : SimpleGraph α) (k : ℕ): Prop := G.CompleteMulti ∧ G.chromaticNumber = k

end SimpleGraph