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
    -- rw [← sum_to_list , ← sum_to_list]
    -- apply List.sum_le_sum
    intro j jmem
    --rw [mem_toList] at jmem ;
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
    rw [← sum_to_list , ← sum_to_list]
    apply List.sum_le_sum
    intro i imem
    rw [mem_toList] at imem ; exact this i imem
  rw [sum_eq_card] at sum_bound ; rw [sum_eq_card2] at sum_bound2
  exact Nat.add_le_add sum_bound sum_bound2
#check Nat.div
lemma abc {a : ℕ } {b : ℕ } {c : ℕ } {n : ℕ } (h : a ≤ c) (hab : 0 < a + b ): a * n / (a + b) ≤ c * n / (c + b) := by
  sorry

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
    cases r with
      | zero => contradiction;
      | succ r =>
      have krle : (2 * r + 2+ card (s ∩ t)) * (Fintype.card α) /(2 * r + 2+ card (s ∩ t) + 3) ≤ (3 * r - 1) * (Fintype.card α) /(3 * r + 2)
      ·
        sorry
      -- I think you may also need to do a case split on whether or not `k = card(s ∩ t)` is zero
      sorry











      #check P3barFree
























end SimpleGraph
