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
  intro a b c nadjab nadjbc adjac
  have nP3barbac : ¬P3bar b a c := h b a c
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
lemma completeMultiPartiteR_adj_ne_col (hcpr : G.completeMultiPartiteR r) (C: G.Coloring (Fin r)) (x y: α):
C x ≠ C y → G.Adj x y:=
by
  cases r with
  | zero => exfalso; apply Fin.elim0 (C x)
  | succ n =>
    intro Cneq
    obtain ⟨u , v , ⟨h1 , h2 , h3⟩⟩ := chromatic_imp_edges hcpr.2 C (C x) (C y) Cneq
    by_contra nadj
    have : ¬ Adj G u v
    · have nadjux : ¬ Adj G u x
      · exact Coloring.not_adj_of_mem_colorClass C h1 rfl
      have nadjxv : ¬ Adj G x v
      · apply hcpr.1
        · exact nadj
        · exact Coloring.not_adj_of_mem_colorClass C (id (Eq.symm h2)) rfl
      apply hcpr.1
      · exact nadjux
      · exact nadjxv
    contradiction



open Finset
/-- If G is complete r-partite then it contains a copy of K_r -/
lemma not_cliquefree_of_complete_multi_partite (hcpr: G.completeMultiPartiteR r) : ¬ G.CliqueFree r:=
by
  cases r with
  | zero =>
    intro cliquefree ;
    apply cliquefree ∅
    constructor
    · intro i hi; exfalso; rw [coe_empty] at hi; exact hi
    · simp only [card_empty, Nat.zero_eq]
  | succ r =>
    intro hcf
    -- Get an (r+1)-coloring C of G
    have C : G.Coloring (Fin (r+1))
    · have : G.Colorable (r+1) := by
        rw [← Nat.succ_eq_add_one , ← hcpr.2]
        apply colorable_of_chromaticNumber_pos
        rw [hcpr.2 , Nat.succ_eq_add_one]
        exact Nat.succ_pos r
      apply Colorable.toColoring
      · exact this
      · simp only [Fintype.card_fin, le_refl]

    -- assert that ∀ colors i, ∃ v such that C v = i
    have Csurj: ∀ i, ∃ v , C v = i
    · exact chromatic_imp_verts hcpr.2 C
    let f: Fin (r+1) → α := fun i => (Csurj i).choose
    have hf: ∀ i, (C (f i))= i := fun i => (Csurj i).choose_spec
    let S: Finset α:= (univ : Finset (Fin (r+1))).image (fun i => f i)
    apply hcf S
    constructor
    · intro u hu v hv hne
      apply completeMultiPartiteR_adj_ne_col hcpr C
      contrapose! hne
      rw [mem_coe , mem_image] at hu
      rw [mem_coe , mem_image] at hv
      rcases hu with ⟨ a , ⟨ amemuniv , faequ⟩⟩
      rcases hv with ⟨ b , ⟨ bmemuniv , fbeqv⟩⟩
      rw [←faequ , ← fbeqv ]
      have finj : ∀ x₁ x₂ , f x₁ = f x₂ → x₁ = x₂ := by
        intro x₁ x₂ fx1eqfx2
        rw [← hf x₁ , ←hf x₂]
        exact congrArg (↑C) fx1eqfx2
      have aeqcu : C (f a) = C u := by
        exact congrArg (↑C) faequ
      rw [hf a] at aeqcu
      have beqcv : C (f b) = C v := by
        exact congrArg (↑C) fbeqv
      rw [hf b] at beqcv
      rw [←aeqcu , ← beqcv ] at hne
      exact congrArg f hne
    · rw [Nat.succ_eq_add_one, ← Fintype.card_fin (r+1)]
      apply card_image_of_injective
      intro a b faeqfb
      rw [← hf a , ←hf b]
      exact congrArg (↑C) faeqfb


end SimpleGraph
