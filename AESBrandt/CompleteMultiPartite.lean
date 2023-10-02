import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Core
import Mathlib.Data.Fin.Basic
import AESBrandt.P3bar
import AESBrandt.MaxCliqueFree
import AESBrandt.Chromatic


namespace SimpleGraph
variable {α β: Type _} {G : SimpleGraph α} [Fintype α] [Fintype (Sym2 α)] [DecidableEq α][Fintype β] [DecidableEq β] [DecidableRel G.Adj]



/-- If non-adjacency is Transitive, then (since it is automatically Reflexive and Symmetric) it is an equivalence relation-/
def completeMultiPartite (G : SimpleGraph α) : Prop := Transitive (λ u v ↦ ¬G.Adj u v)

lemma completeMultiPartite.equiv (hc: G.completeMultiPartite) : Equivalence (λ u v ↦ ¬G.Adj u v):=
by  
  refine { refl := ?_, symm := ?symm, trans := ?_ }
  · intro x ; exact SimpleGraph.irrefl G
  · rintro x y ; contrapose! ; exact (adj_comm G x y).2
  · unfold completeMultiPartite at hc ; unfold Transitive at hc ; simp at hc ; exact @hc


/-- If G is not complete-multi-partite then it contains an induced P3bar-/
lemma P3bar_of_not_completeMultiPartite (h : ¬ completeMultiPartite G): ∃ v w₁ w₂, G.P3bar v w₁ w₂:=
by
  contrapose! h
  unfold completeMultiPartite ; unfold Transitive ; simp
  intro a b c nadjab nadjbc adjac
  have nP3barbac : ¬P3bar b a c := by exact h b a c
  have nP3barbac2 : ¬( G.Adj a c ∧ (¬ G.Adj b a ∧ ¬ G.Adj b c )) := by
    contrapose! nP3barbac
    refine {edge := ?_ , nonedge := ?_}
    exact nP3barbac.1
    exact nP3barbac.2
  push_neg at nP3barbac2
  rw [adj_comm] at nadjab
  have : Adj G b c := by
    exact nP3barbac2 adjac nadjab
  contradiction

/-- If G contains no induced P3bar then it must be complete-multi-partite -/
lemma P3barFree  (p3f: ¬ ∃ v w₁ w₂, G.P3bar v w₁ w₂) : 
G.completeMultiPartite:=
by
  rintro x y z nadjxy nadjyz
  intro adjxz
  have p3t : ∃ v w₁ w₂, G.P3bar v w₁ w₂ := by
    use y ; use x ; use z
    refine {edge := adjxz , nonedge := ?_ }
    constructor
    · intro adjyx
      symm at adjyx
      contradiction
    · exact nadjyz
  contradiction
  
/--  Complete r -partite = Complete-multi-partite + χ(G) = r -/
def completeMultiPartiteR (G : SimpleGraph α) (r : ℕ) : Prop := G.completeMultiPartite ∧ G.chromaticNumber = r 

/-- If G is complete-multi-paritite then it must be complete-χ(G)-partite -/
lemma complete_chrom_partite (hc: G.completeMultiPartite) : G.completeMultiPartiteR (G.chromaticNumber):=
by
  constructor
  · exact hc
  · rfl
 
/-- If G is complete-r-partite then for every r-coloring C, if C x ≠ C y then xy must be an edge-/
lemma completeMultiPartiteR_adj_ne_col (hcpr : G.completeMultiPartiteR (r + 1)) (C: G.Coloring (Fin (r + 1))) (x y: α):  
C x ≠ C y → G.Adj x y:=
by
  rcases hcpr with ⟨multipartG , chromG⟩  
  intro cxnecy
  by_contra nadjxy
  let CN : α → ℕ := fun v => ite (¬ Adj G v y) (C x) (C v)
  have validCN : ∀ {a b : α}, Adj G a b → Adj ⊤ (CN a) (CN b) := by
    intro a b adjab 
    dsimp
    split_ifs with h1 h2 h3
    · intro caeqcb
      rw [Fin.val_eq_val] at caeqcb
      have caneqcb : C a ≠ C b := by
        apply Coloring.valid 
        exact adjab
      contradiction
    · have adjax : Adj G a x := by
        by_contra nadjax
        have nadjay : ¬ Adj G a y := by
          apply multipartG nadjax nadjxy
        contradiction
      intro caeqcx
      have caneqcx : C a ≠ C x := by
        apply Coloring.valid
        exact adjax
      rw [Fin.val_eq_val] at caeqcx
      contradiction
    · have adjbx : Adj G b x := by
        by_contra nadjbx
        have nadjay : ¬ Adj G b y := by
          apply multipartG nadjbx nadjxy
        contradiction
      intro cbeqcx
      have caneqcx : C b ≠ C x := by
        apply Coloring.valid
        exact adjbx
      rw [Fin.val_eq_val] at cbeqcx
      symm at cbeqcx
      contradiction
    · have nadjab : ¬ Adj G a b := by
        apply multipartG h1 
        intro adjby
        symm at adjby
        contradiction
      contradiction
  let CN' : G.Coloring ℕ :=⟨CN,validCN⟩
  by_cases (r = C y )
  · have Clt : ∀ v, CN v < r := by    
      intro v
      dsimp
      split_ifs with h1 
      · apply lt_iff_le_and_ne.2
        constructor
        · apply Fin.le_last
        · intro cveqr
        --rw [ h ] at cveqr
          have : C v = C y := by
            rw [← Fin.val_eq_val , cveqr , ← h]
          have nadjvy : C v ≠ C y  := by
            apply Coloring.valid
            exact h1
          contradiction
      · by_contra rlecv
        have reqcx : C x = r := by
          have : Fin.last r = r := by 
            exact Eq.symm (Fin.cast_nat_eq_last r)
          rw [← this ]
          apply Fin.eq_last_of_not_lt rlecv
        rw [Fin.eq_iff_veq ] at reqcx
        have : (↑(↑(r : ℕ) : Fin (r + 1)) : ℕ)  = r := by
          rw [Fin.cast_nat_eq_last r]
          exact rfl
        rw [this] at reqcx
        have cxeqcy : C x = C y := by
          rw [← Fin.val_eq_val , reqcx , ← h] 
        contradiction
    contrapose! Clt
    exact chrom_imp_nat_col_self chromG CN' 
  · let CN2 : α → ℕ := fun v => ite (CN v = r) (C y) (CN v)
    have validCN2 : ∀ {a b : α}, Adj G a b → Adj ⊤ (CN2 a) (CN2 b) := by
      rintro a b adjab cn2eq
      by_cases (CN a = r)
      · dsimp at cn2eq
        rcases em (CN b = r) with h2 | h2
        · rw [← h ] at h2
          have : CN a ≠ CN b := by
            apply Coloring.valid CN'
            exact adjab
          symm at h2
          contradiction
        · dsimp at h
          dsimp at h2
          rw [if_pos h , if_neg h2] at cn2eq
          simp at cn2eq
          rcases em (Adj G b y) with h3| h3
          · rw [if_pos h3 , Fin.val_eq_val] at cn2eq 
            have : C b ≠ C y := by
              apply Coloring.valid
              exact h3
            symm at cn2eq
            contradiction
          · rw [if_neg h3 , Fin.val_eq_val] at cn2eq  
            symm at cn2eq
            contradiction
      · dsimp at cn2eq 
        dsimp at h
        rw [if_neg h] at cn2eq
        rcases em (CN b = r) with h2| h2
        · dsimp at h2
          rw [if_pos h2] at cn2eq
          · rcases em (¬ Adj G a y) with h3| h3 
            · rw [if_pos h3 , Fin.val_eq_val] at cn2eq
              contradiction
            · rw [if_neg h3 , Fin.val_eq_val] at cn2eq
              push_neg at h3
              have : C a ≠ C y := by
                apply Coloring.valid
                exact h3
              contradiction
        · dsimp at h2 
          rw [if_neg h2] at cn2eq   
          have CNa : (if ¬Adj G a y then ((C x) : ℕ) else ((C a) : ℕ) ) = CN a := by 
            simp 
          have CNb : (if ¬Adj G b y then ((C x) : ℕ)  else ((C b) : ℕ )) = CN b := by 
            simp
          rw [CNa , CNb] at cn2eq
          have : CN a ≠ CN b := by
            apply Coloring.valid CN'
            exact adjab 
          contradiction
    let CN2' : G.Coloring ℕ :=⟨CN2,validCN2⟩
    have Clt2 : ∀ v, CN2 v < r := by  
      intro v
      dsimp 
      rcases em ((if ¬Adj G v y then (C x : ℕ ) else (C v : ℕ )) = r) with pos | neg
      · rw [if_pos pos]
        apply lt_iff_le_and_ne.2
        constructor
        · apply Fin.le_last
        · symm
          push_neg at h
          exact h
      · rw [if_neg neg]
        rcases em (¬ Adj G v y) with nadjvy | adjvy
        · rw [if_pos nadjvy]
          apply lt_iff_le_and_ne.2
          constructor
          · apply Fin.le_last
          · rw [if_pos nadjvy] at neg
            push_neg at neg
            exact neg
        rw [if_neg adjvy]
        apply lt_iff_le_and_ne.2
        constructor
        · apply Fin.le_last
        · rw [if_neg adjvy] at neg
          push_neg at neg
          exact neg
    contrapose! Clt2
    exact chrom_imp_nat_col_self chromG CN2'
  
/-- If G is complete r-partite then it contains a copy of K_r -/
lemma not_cliquefree_of_complete_multi_partite (hcpr: G.completeMultiPartiteR r) : ¬ G.CliqueFree r:=
by
  sorry

end SimpleGraph