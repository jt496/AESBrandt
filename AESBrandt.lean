import AESBrandt.Chromatic
import AESBrandt.Clique
import AESBrandt.MaxCliqueFree
import AESBrandt.P3bar
import AESBrandt.Subgraphs
import AESBrandt.CompleteMultiPartite
import AESBrandt.Wheel
import Mathlib.Algebra.BigOperators.Order



namespace SimpleGraph
open Finset
open BigOperators
variable {α : Type _} {G : SimpleGraph α}  [DecidableEq α]  [Fintype α] [DecidableRel G.Adj] [Nonempty α]

lemma double_counting (s : Finset α) :
    ∑ v , (G.neighborFinset v ∩ s).card = ∑ v in s, G.degree v :=
by
  simp only [Finset.card_eq_sum_ones]
  have comm : ∀ (x y : α), x ∈ univ ∧ y ∈ neighborFinset G x ∩ s ↔ x ∈ neighborFinset G y ∧ y ∈ s
  · intro x y ; constructor
    · intro h
      rw [mem_inter] at h
      exact ⟨by apply (mem_neighborFinset G y x).2 ; rw [adj_comm] ; exact (mem_neighborFinset G x y).1 h.2.1,h.2.2 ⟩
    · intro h
      refine ⟨by exact mem_univ x, ?_⟩
      · rw [mem_inter]
        refine ⟨by rw [mem_neighborFinset] ; rw [adj_comm] ; exact (mem_neighborFinset G y x).1 h.1 , by exact h.2⟩
  rw [sum_comm' comm ]
  simp only [ ← Finset.card_eq_sum_ones , card_neighborFinset_eq_degree]

lemma nonadj_adj (s : Finset α) (hx: i ≤ card (s.filter (λ z ↦ ¬ G.Adj x z))):
card (s.filter (λ z ↦ G.Adj x z)) ≤ s.card - i :=
by
  have aux : i ≤ card s :=
    calc
      i ≤ card (filter (fun z => ¬Adj G x z) s) := by
        exact hx
      _ ≤ card s := by
        apply card_filter_le
  rw [Nat.le_sub_iff_right aux]
  have i_le_sum_card : card (filter (fun z => Adj G x z) s) + i ≤ card (filter (fun z => Adj G x z) s) + card (filter (fun z => ¬ Adj G x z) s)
  · apply add_le_add_left ; exact hx
  apply le_trans i_le_sum_card
  have disjoint : Disjoint (filter (fun z => Adj G x z) s) (filter (fun z => ¬Adj G x z) s)
  · exact disjoint_filter_filter_neg s s fun z => Adj G x z
  rw [← card_disjoint_union disjoint] ; apply card_le_of_subset ; intro y ymem ; rw [mem_union] at ymem
  rcases ymem with h | h
  · rw [mem_filter] at h ; exact h.1
  · rw [mem_filter] at h ; exact h.1

lemma deg_bound (W X : Finset α) (hx: ∀x, x ∈ X → i  ≤ card (W.filter (λ z ↦ ¬ G.Adj  x z)))
(hy: ∀y, j ≤ card (W.filter (λ z ↦ ¬ G.Adj  y z))) : ∑ w in W, G.degree w ≤ (X.card) * (W.card - i) + Xᶜ.card* (W.card - j) :=
by
  rw [← double_counting , ← sum_add_sum_compl X]
  have sum_eq_card : ∑ x in X, (card W - i) = card X * (card W - i)
  · rw [← sum_const_nat]
    intro x _ ; rfl
  have sum_bound : ∑ x in X, card (neighborFinset G x ∩ W) ≤ ∑ x in X, (card W - i)
  · have : ∀ (x : α), x ∈ X → card (neighborFinset G x ∩ W) ≤ (card W - i)
    · intro x x_memX
      have : (filter (fun z => Adj G x z) W) = neighborFinset G x ∩ W
      · ext v ; rw [mem_filter , mem_inter , mem_neighborFinset , and_comm]
      rw [← this] ; exact nonadj_adj W (hx x x_memX)
    apply sum_le_sum
    intro j jmem
    exact this j jmem
  have sum_eq_card2 : ∑ x in Xᶜ , (card W - j) = card Xᶜ  * (card W - j)
  · rw [← sum_const_nat]
    intro x _  ; rfl
  have sum_bound2 : ∑ x in Xᶜ , card (neighborFinset G x ∩ W) ≤ ∑ x in Xᶜ , (card W - j)
  · have : ∀ (x : α), x ∈ Xᶜ → card (neighborFinset G x ∩ W) ≤ (card W - j)
    · intro x _
      have : (filter (fun z => Adj G x z) W) = neighborFinset G x ∩ W
      · ext v ; rw [mem_filter , mem_inter , mem_neighborFinset , and_comm]
      rw [← this] ; exact nonadj_adj W (hy x)
    apply sum_le_sum
    intro i imem
    exact this i imem
  rw [sum_eq_card] at sum_bound ; rw [sum_eq_card2] at sum_bound2
  exact Nat.add_le_add sum_bound sum_bound2

lemma abc {a : ℕ } {b : ℕ } {c : ℕ } {n : ℕ } (h : a ≤ c) (hab : 0 < a + b ): a * n / (a + b) ≤ c * n / (c + b) := by
  have cb_pos : 0 < c + b
  · calc
      0 < a + b := by
        exact hab
      _ ≤ c + b := by
        apply Nat.add_le_add_right  
        exact h 
  rw [← one_mul (a * n / (a + b)) ,← Nat.div_self cb_pos , mul_comm]
  have : a * n / (a + b) * ((c + b) / (c + b)) ≤ (a * n / (a + b) * (c + b)) / (c + b)
  · exact Nat.mul_div_le_mul_div_assoc (a * n / (a + b)) (c + b) (c + b)
  apply le_trans this
  apply Nat.div_le_div_right
  rw [mul_comm]
  have aux : (c + b) * (a * n / (a + b)) ≤ ((c + b) * (a * n)) / (a + b)
  · exact Nat.mul_div_le_mul_div_assoc (c + b) (a * n) (a + b)
  apply le_trans aux
  apply Nat.div_le_of_le_mul'
  rw [add_mul , add_mul , ← mul_assoc c , mul_comm c a , ← mul_assoc a , Nat.add_le_add_iff_left ]
  apply Nat.mul_le_mul (by rfl)
  apply Nat.mul_le_mul_right
  exact h

lemma kr_bound {k : ℕ} {r : ℕ}  (h : k ≤ r) (n : ℕ) : (2 * r + 2 + k) * n / (2 * r + 2 + k + 3) ≤  (3 * r + 2) *n / (3 * r + 5) := by
  have aux : (2 * r + 2 + k) ≤ (3 * r + 2)
  · rw [add_comm , ← add_assoc , add_le_add_iff_right]
    rw [← two_add_one_eq_three , add_comm, add_mul , add_le_add_iff_left , one_mul]
    exact h
  have : 0 < (2 * r + 2 + k) + 3
  · exact Nat.succ_pos (2 * r + 2 + k + 2)
  exact abc aux this

theorem aes_brandt (hf: G.CliqueFree (r+2)) (md: (3*r - 1)* (Fintype.card α)/(3*r + 2) < G.minDegree) : G.Colorable (r+1) := by
  classical
  rcases exists_maxcf_super hf with ⟨H , ⟨H_subgraph ,H_max_cf⟩⟩
  apply Colorable.mono_left H_subgraph
  by_cases (H.chromaticNumber ≤ r + 1)
  · apply Colorable.mono h
    exact colorable_chromaticNumber (colorable_of_fintype H)
  · push_neg at h ; rw [← add_lt_add_iff_right 1 , ← Nat.succ_eq_add_one (chromaticNumber H) , Nat.lt_succ_iff , add_assoc , one_add_one_eq_two] at h
    have not_completeMP : ¬ H.completeMultiPartiteR (chromaticNumber H)
    · intro completeMP
      apply not_cliquefree_of_complete_multi_partite (completeMP)
      apply CliqueFree.mono _ H_max_cf.1
      exact h
    have exists_p3 : ∃ v w₁ w₂, P3bar v w₁ w₂
    · by_contra n_p3
      apply not_completeMP ; constructor
      · exact P3barFree n_p3
      · rfl
    rcases exists_p3 with ⟨v , w₁ , w₂ , p3⟩
    rcases exists_MaxWheel H_max_cf p3 with ⟨s , t , hw , hsf⟩
    have boundW : ∑ w in (wheelVerts hw), degree H w ≤ card (H.WheelCore hw)  * (card (wheelVerts hw) - 3) + card (H.WheelCore hw)ᶜ  * (card (wheelVerts hw) - 1)
    · have dXle : ∀ x : α , x ∈ H.WheelCore hw → 3 ≤ card (filter (fun z => ¬Adj H x z) (wheelVerts hw))
      · intro x xmem_core ; exact three_le_wheel_nonadj H_max_cf p3 hw hsf xmem_core
      have dnXle : ∀ v : α , 1 ≤ card (filter (fun z => ¬Adj H v z) (wheelVerts hw))
      · intro v ; exact degle_noncore H_max_cf.1 hw v
      exact deg_bound (wheelVerts hw) (H.WheelCore hw) dXle dnXle
    have boundX : ∑ w in s ∩ t, degree H w ≤  card (H.WheelCore hw)ᶜ  * (card (s ∩ t) - 1) + card (H.WheelCore hw) * card (s ∩ t)
    · have dXle : ∀ x : α , x ∈ (H.WheelCore hw)ᶜ  → 1 ≤ card (filter (fun z => ¬Adj H x z) (s ∩ t))
      · intro x xmem_n_core ; exact degcore_compl H_max_cf.1 hw xmem_n_core
      have dnXle : ∀ v : α , 0 ≤ card (filter (fun z => ¬Adj H v z) (s ∩ t))
      · intro v ; exact Nat.zero_le (card (filter (fun z => ¬Adj H v z) (s ∩ t)))
      have : ∑ w in s ∩ t, degree H w ≤ card (H.WheelCore hw)ᶜ * (card (s ∩ t) - 1) + card (H.WheelCore hw)ᶜᶜ   * (card (s ∩ t) - 0)
      · exact deg_bound (s ∩ t) (H.WheelCore hw)ᶜ  dXle dnXle
      rw [compl_compl (WheelCore hw) , Nat.sub_zero (card (s ∩ t)) ] at this
      exact this
    have card_wheel_inter : card (wheelVerts hw) + card (s ∩ t) = 2 * r + 3
    · exact card_wheelVerts hw
    have card_inter : card (s ∩ t) < r
    · exact card_of_IsWheel_cf H_max_cf.1 hw
    have mdH : (3 * r - 1) * (Fintype.card α)/(3 * r + 2) < H.minDegree :=
      calc
        (3 * r - 1) * (Fintype.card α)/(3 * r + 2) < minDegree G := by
          exact md
        _ ≤ minDegree H := by
          exact minDegree_le_of_le H_subgraph

    have krle : (2 * r + card (s ∩ t)) * (Fintype.card α) /(2 * r + card (s ∩ t) + 3) ≤ (3 * r - 1) * (Fintype.card α) /(3 * r + 2)
    · cases r with
      | zero => contradiction;
      | succ r =>
        rw [Nat.succ_eq_add_one , mul_add , mul_add , mul_one , mul_one]
        have aux : 3 * r + 3 - 1 = 3 * r + 2
        · exact rfl 
        rw [aux]
        have aux2 : 3 * r + 3 + 2 = 3 * r + 5
        · exact rfl
        rw [aux2]
        apply kr_bound ; apply Nat.le_of_lt_succ ; exact card_inter
    have min_degree_le : minDegree H ≤ (3 * r - 1) * Fintype.card α / (3 * r + 2)
    · apply le_trans _ krle
      have aux : 0 < (2 * r + card (s ∩ t) + 3) 
      · exact Nat.succ_pos (2 * r + card (s ∩ t) + 2)
      apply (Nat.le_div_iff_mul_le aux).2
      have min_deg_W : H.minDegree * card (wheelVerts hw) ≤ card (WheelCore hw) * (card (wheelVerts hw) - 3) + card (WheelCore hw)ᶜ * (card (wheelVerts hw) - 1)
      · apply le_trans _ boundW
        rw [mul_comm]
        have aux2 : card (wheelVerts hw) * minDegree H = ∑ v in (wheelVerts hw) , minDegree H
        · symm ; apply sum_const_nat ; intro _ _ ; rfl
        rw [aux2] ; apply sum_le_sum ; intro i _ ; exact minDegree_le_degree H i
      rcases Nat.eq_zero_or_eq_succ_pred (card (s ∩ t)) with k_eq_zero | one_le_K
      · rw [k_eq_zero , add_zero] ; rw [k_eq_zero , add_zero] at card_wheel_inter ; rw [card_wheel_inter] at min_deg_W
        have core_eq_n : WheelCore hw = univ 
        · ext y ; constructor
          · intro _ ; exact mem_univ y
          · intro _ ; rw [mem_WheelCore_iff] ; intro l contra
            rw [card_eq_zero.1 k_eq_zero] at contra
            contradiction
        rw [(card_eq_iff_eq_univ (WheelCore hw)).2 core_eq_n] at min_deg_W
        have comple_core_empty : (WheelCore hw)ᶜ = ∅  
        · exact Iff.mpr (compl_eq_empty_iff (WheelCore hw)) core_eq_n 
        rw [comple_core_empty , card_empty , zero_mul , add_zero , mul_comm (Fintype.card α) , Nat.add_sub_assoc (Nat.le_refl 3) , Nat.sub_self , add_zero] at min_deg_W
        exact min_deg_W
      · have min_deg_K : H.minDegree * card (s ∩ t) ≤ card (WheelCore hw)ᶜ * (card (s ∩ t) - 1) + card (WheelCore hw) * card (s ∩ t)
        · apply le_trans _ boundX
          rw [mul_comm]
          have aux2 : card (s ∩ t) * minDegree H = ∑ v in (s ∩ t) , minDegree H
          · symm ; apply sum_const_nat ; intro _ _ ; rfl
          rw [aux2] ; apply sum_le_sum ; intro i _ ; exact minDegree_le_degree H i
        have two_min_deg_K : 2 * (H.minDegree * card (s ∩ t)) ≤ 2 * (card (WheelCore hw)ᶜ * (card (s ∩ t) - 1) + card (WheelCore hw) * card (s ∩ t))
        · exact (mul_le_mul_left (Nat.succ_pos 1)).2 min_deg_K
        have result : H.minDegree * card (wheelVerts hw) + 2 * (H.minDegree * card (s ∩ t)) ≤ 
        (card (WheelCore hw) * (card (wheelVerts hw) - 3) + card (WheelCore hw)ᶜ * (card (wheelVerts hw) - 1)) + (2 * (card (WheelCore hw)ᶜ * (card (s ∩ t) - 1) + card (WheelCore hw) * card (s ∩ t)))
        · exact Nat.add_le_add min_deg_W two_min_deg_K 
        have lhs : minDegree H * card (wheelVerts hw) + 2 * (minDegree H * card (s ∩ t)) = minDegree H * (2 * r + card (s ∩ t) + 3)
        · rw [← mul_assoc , mul_comm 2 , mul_assoc , ← mul_add] ; nth_rw 1 [← one_add_one_eq_two , add_mul , one_mul , one_mul]
          rw [← add_assoc , card_wheelVerts] ; nth_rw 1 [add_assoc] ; rw [add_comm 3 , ← add_assoc ]
        rw [lhs] at result
        have rhs : card (WheelCore hw) * (card (wheelVerts hw) - 3) + card (WheelCore hw)ᶜ * (card (wheelVerts hw) - 1) +
      2 * (card (WheelCore hw)ᶜ * (card (s ∩ t) - 1) + card (WheelCore hw) * card (s ∩ t)) = (2 * r + card (s ∩ t)) * Fintype.card α 
        · rw [add_assoc , add_comm , mul_add , ← add_assoc , ← mul_assoc , mul_comm 2 , mul_assoc , ← mul_add ]
          have three_le_card_wheel : 3 ≤ card (wheelVerts hw)
          · rw [wheelVerts]
            have n_v : ¬ v ∈ (insert w₁ (insert w₂ (s ∪ t)))
            · rw [mem_insert , mem_insert , mem_union] ; push_neg
              exact ⟨by exact (P3bar.ne p3).1 ,by exact (P3bar.ne p3).2 , by exact hw.disj.1 , by exact hw.disj.2.1⟩
            rw [card_insert_eq_ite , if_neg n_v]
            have n_w₁ : ¬ w₁ ∈ insert w₂ (s ∪ t)
            · rw [mem_insert , mem_union] ; push_neg
              refine ⟨?_,by exact hw.2.2.2.1 ,by exact (IsWheel_disj_ext hw).1 ⟩
              · intro eq ; apply SimpleGraph.irrefl H ; rw [eq] at p3 ; exact p3.edge 
            rw [card_insert_eq_ite , if_neg n_w₁ , add_assoc , one_add_one_eq_two]
            have n_w₂ : ¬ w₂ ∈ s ∪ t
            · rw [mem_union] ; push_neg
              exact ⟨by exact (IsWheel_disj_ext hw).2 , by exact hw.2.2.2.2 ⟩ 
            rw [card_insert_eq_ite , if_neg n_w₂ , add_assoc , add_comm 1 , two_add_one_eq_three ]
            nth_rw 1 [← zero_add 3 ] ; apply add_le_add_right ; exact Nat.zero_le (card (s ∪ t))    
          have one_le_card_wheel : 1 ≤ card (wheelVerts hw)
          · calc 
              1 ≤ 3 := by
                norm_num
              _ ≤ card (wheelVerts hw) := by
                exact three_le_card_wheel
          have one_le_card_inter : 1 ≤ card (s ∩ t)
          · rw [Nat.one_eq_succ_zero , one_le_K] ; apply Nat.succ_le_succ ; exact Nat.zero_le (Nat.pred (card (s ∩ t)))
          rw [Nat.mul_sub_left_distrib 2 (card (s ∩ t)) 1 , mul_one , ← Nat.sub_add_comm one_le_card_wheel ,←  Nat.add_sub_assoc (Nat.mul_le_mul_left 2 one_le_card_inter)]
          rw [mul_one] ; nth_rw 1 [← one_add_one_eq_two , add_mul] ; rw [one_mul , ← add_assoc , card_wheel_inter , add_assoc (2 * r) , add_comm 3 , ← add_assoc]
          have three_sub_two : 3 - 2 = 1
          · norm_num 
          rw [Nat.add_sub_assoc (by norm_num) , three_sub_two , Nat.add_sub_assoc (by norm_num) , Nat.sub_self , add_zero]
          rw [add_assoc , mul_comm 2 ((card (WheelCore hw) * card (s ∩ t))) , mul_assoc , ← Nat.mul_add ]
          nth_rw 2 [←one_add_one_eq_two] ; rw [Nat.mul_add (card (s ∩ t)) , mul_one , add_assoc , ← Nat.add_sub_assoc (three_le_card_wheel)]
          rw [add_comm (card (s ∩ t)) (card (wheelVerts hw)) , card_wheel_inter , Nat.add_sub_assoc (by norm_num) , Nat.sub_self , add_zero]
          rw [add_comm (card (s ∩ t)) (2 * r) , ← Nat.add_mul , add_comm (card (WheelCore hw)ᶜ) , card_compl]
          rw [← Nat.add_sub_assoc (by exact card_le_univ (WheelCore hw)) , add_comm , Nat.add_sub_assoc (by norm_num) ,Nat.sub_self , add_zero , mul_comm] 
        rw [rhs] at result ; exact result
    have contra : ¬ (3 * r - 1) * Fintype.card α / (3 * r + 2) < minDegree H
    · push_neg ; exact min_degree_le
    contradiction

end SimpleGraph
