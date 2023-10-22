import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic

open BigOperators

namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]

lemma not_col_of_chrom_succ (h : G.chromaticNumber = k + 1) : ¬ G.Colorable k:=
by 
  intro kcolourable
  have : 1 ≤ 0 := by 
    apply (add_le_add_iff_left k).1
    rw [add_zero]
    rw [← h ]
    apply chromaticNumber_le_of_colorable
    exact kcolourable
  contradiction

     
lemma chrom_imp_nat_col_self  (hcrom: G.chromaticNumber = k + 1) (C : G.Coloring ℕ): ∃ v, k ≤ C v :=
by 
  by_contra h
  push_neg at h
  have kcol : G.Colorable k := by
    apply (colorable_iff_exists_bdd_nat_coloring k).2
    use C
  exact not_col_of_chrom_succ hcrom kcol



lemma chromatic_imp_verts (h : G.chromaticNumber = k + 1) (C : G.Coloring (Fin (k+1))) : 
∀ i, ∃ v, C v = i :=
by
  by_contra hc
  push_neg at hc
  apply G.not_col_of_chrom_succ h
  rcases hc with ⟨i , cneqi⟩
  let CN : α → ℕ := fun v => ite (C v = Fin.last k) (i) (C v)
  have valid :  ∀ {a b : α}, Adj G a b → Adj ⊤ (CN a) (CN b) := 
  by
    intro a b adjab 
    dsimp; split_ifs with h1 h2 h3
    all_goals intro eq; rw [Fin.val_eq_val] at eq
    · apply C.valid adjab; rw [h1,h2]
    · apply cneqi b eq.symm
    · apply cneqi _ eq
    · apply C.valid adjab eq
  let CN' : G.Coloring ℕ :=⟨CN,valid⟩
  have Clt : ∀ v, CN v < k
  · intro v; dsimp; split_ifs with h1
    · by_contra hl
      rw [←Fin.eq_last_of_not_lt hl] at h1
      apply cneqi _ h1
    · apply Fin.val_lt_last h1
  contrapose! Clt;  
  exact chrom_imp_nat_col_self h CN'
    -- by_cases hi: C a = Fin.last k
    -- --rcases em (C a = Fin.last k) with i | ni
    -- · dsimp at eq
    --   rw [if_pos hi] at eq
    --   rcases em (C b = Fin.last k) with ib | nib
    --   · have : C a = C b := by
    --       rw [hi , ib]
    --     exact Coloring.valid C adjab this
    --   rw [if_neg nib] at eq
    --   symm at eq
    --   exact cneqi b eq
     
 -- let CN' : G.Coloring ℕ := ⟨CN, by intro a b adjab si ⟩
 #check Fin.val_lt_last
  #check Fin.eq_last_of_not_lt
 variable (a : Fin n)
 



lemma chromatic_imp_edges (h : G.chromaticNumber = k + 1) (C : G.Coloring (Fin (k+1))) : ∀ i j, i ≠ j →  ∃ u v, C u = i ∧ C v = j ∧ G.Adj u v:=
by
  intro i j hij
  by_contra hc
  push_neg at hc
  let D : α → Fin (k+1) := fun v => ite (C v = j) (i) (C v)
  let D' : G.Coloring (Fin (k+1)) :=⟨D,
  by
    intro a b
    intro adjab
    dsimp 
    split_ifs with h1 h2 h3
    · intro _
      apply C.valid adjab
      rw [h1 ,h2]
    · intro eq
      exact hc b a eq.symm h1 adjab.symm
    · intro eq
      exact hc a b eq h3 adjab
    · intro eq
      exact C.valid adjab eq ⟩
  
  have  hj : ∀ v, D v ≠ j
  · intro v
    dsimp
    split_ifs with h1
    · exact hij
    · exact h1
  have : ∀ i, ∃ v, D' v = i := by
    exact chromatic_imp_verts h D'
  have contr : ¬ ∀ i, ∃ v, D v = i := by
    push_neg
    use j 
  contradiction


end SimpleGraph