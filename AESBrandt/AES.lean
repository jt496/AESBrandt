/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v , w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
 `t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k  = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

The first interesting cases of such structures are `W₁,₀` and `W₂,₁`: `W₁,₀` is a 5-cycle,
while `W₂,₁` is a 5-cycle with an extra central hub vertex adjacent to all other vertices
(i.e. `W₂,₁` resembles a wheel with five spokes).

                 `W₁,₀`       v                 `W₂,₁`      v
                           /     \                       /  |  \
                          s       t                     s ─ u ─ t
                           \     /                       \ / \ /
                           w₁ ─ w₂                       w₁ ─ w₂

## Main definitions

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of
  `G` with `r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
  `#(s ∩ t) = k`.

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## Implementation notes
The definitions of `IsFiveWheelLike` and `IsFiveWheelLikeFree` in this file have `r` shifted by two
compared to the definitions in Brandt **On the structure of graphs with bounded clique number**

The definition of `IsFiveWheelLike` does not contain the facts that `#s = r ` and `#t = r` but we
deduce these later as `card_left` and `card_right`.

Although `#(s ∩ t)` can easily be derived from `s` and `t` we include the `IsFiveWheelLike` field
`card_inter : #(s ∩ t) = k` to match the informal / paper definitions and to simplify some
statements of results and match our definition of `IsFiveWheelLikeFree`.

## References

* B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2

* S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z
-/
local notation "‖" x "‖" => Fintype.card x

open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : ℕ}

namespace SimpleGraph

variable {i j n : ℕ} {d x : α}

section Counting

private lemma kr_bound (hk : k ≤ r) :
    (2 * (r + 1) + k) * n / (2 * (r + 1) + k + 3) ≤ (3 * r + 2) * n / (3 * r + 5) := by
  apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
    <| (mul_le_mul_left (2 * r + 2 + k + 2).succ_pos).1 _
  rw [← mul_assoc, mul_comm (2 * r + 2 + k + 3), mul_comm _ (_ * n)]
  apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
  nlinarith

variable [DecidableRel G.Adj]

/-- Transform a lower bound on non-adjacencies into an upper bound on adjacencies. -/
private lemma card_adj_le_of_le_card_not_adj (hx : i ≤ #(s.filter fun z ↦ ¬ G.Adj x z)) :
    #(s.filter fun z ↦ G.Adj x z) ≤ #s - i := by
  rw [← filter_card_add_filter_neg_card_eq_card (s := s) (fun z ↦ G.Adj x z),
      add_tsub_assoc_of_le hx]
  exact Nat.le_add_right ..

variable [DecidableEq α]

/-- Useful trivial fact about when `|{a, b, c, d}| ≤ 2` given `a ≠ b` , `a ≠ d`, `b ≠ c`. -/
private lemma eq_of_card_le_two_of_ne (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c)
    (hc2 : #{a, b, c, d} ≤ 2) : c = a ∧ d = b := by
  by_contra! hf
  apply Nat.le_lt_asymm hc2 <| two_lt_card_iff.2 _
  by_cases h : a = c <;> aesop

/--
Given lower bounds on non-adjacencies from `W` into `X`,`Xᶜ` we can bound the degree sum over `W`.
-/
private lemma sum_degree_le_of_le_not_adj [Fintype α] {W X : Finset α}
    (hx : ∀ x, x ∈ X → i  ≤ #(W.filter fun z ↦ ¬ G.Adj x z))
    (hxc : ∀ y, y ∈ Xᶜ → j ≤ #(W.filter fun z ↦ ¬ G.Adj y z)) :
    ∑ w ∈ W, G.degree w ≤ #X * (#W - i) + #Xᶜ * (#W - j) := calc
   _ = ∑ v, #(G.neighborFinset v ∩ W) := by
      simp_rw [degree, card_eq_sum_ones]
      exact sum_comm' (fun _ _ ↦ by simp [and_comm, adj_comm])
   _ ≤ _ := by
    rw [← union_compl X, sum_union disjoint_compl_right]
    simp_rw [neighborFinset_eq_filter, filter_inter, univ_inter, card_eq_sum_ones X,
      card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    apply add_le_add <;> apply sum_le_sum <;> intro x hx1
    · exact card_adj_le_of_le_card_not_adj <| hx x hx1
    · exact card_adj_le_of_le_card_not_adj <| hxc x hx1

end Counting

namespace IsFiveWheelLike

variable [DecidableEq α] {v w₁ w₂ : α} {s t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

lemma exist_not_adj_of_adj_inter (h : G.CliqueFree (r + 2)) (hW : ∀ {y}, y ∈ s ∩ t → G.Adj x y) :
    ∃ a b c d, a ∈ insert w₁ s ∧ ¬ G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬ G.Adj x b ∧ c ∈ insert v s ∧
    ¬ G.Adj x c ∧ d ∈ insert v t ∧ ¬ G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨_, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hd, hdj⟩ := hw.isNClique_right.exists_not_adj_of_cliqueFree_succ h x
  refine ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, ?_, ?_, ?_, ?_, ?_⟩
    <;> rw [mem_insert] at * <;> try rintro rfl
  · obtain (rfl | ha) := ha
    · obtain (rfl | hb) := hb
      · exact hw.isPathGraph3Compl.fst_ne_snd rfl
      · exact hw.fst_not_mem_right hb
    · obtain (rfl | hb) := hb
      · exact hw.symm.fst_not_mem_right ha
      · exact haj <| hW <| mem_inter_of_mem ha hb
  · obtain (rfl | ha) := ha
    · obtain (rfl | hd) := hd
      · exact hw.isPathGraph3Compl.ne_fst rfl
      · exact hw.fst_not_mem_right  hd
    · obtain (rfl | hd) := hd
      · exact hw.not_mem_left ha
      · exact haj <| hW <| mem_inter_of_mem ha hd
  · obtain (rfl | hb) := hb
    · obtain (rfl | hc) := hc
      · exact hw.isPathGraph3Compl.ne_snd rfl
      · exact hw.symm.fst_not_mem_right  hc
    · obtain (rfl | hc) := hc
      ·  exact hw.not_mem_right hb
      ·  exact hbj <| hW <| mem_inter_of_mem hc hb
  · intro hat
    obtain (rfl | ha) := ha
    · exact hw.fst_not_mem_right hat
    · exact haj <| hW <| mem_inter_of_mem ha hat
  · intro hbs
    obtain (rfl | hb) := hb
    · exact hw.symm.fst_not_mem_right hbs
    · exact hbj <| hW <| mem_inter_of_mem hbs hb

lemma card_add_card_inter : #(insert v (insert w₁ (insert w₂ (s ∪ t)))) + k = 2 * r + 3 := by
  rw [add_comm, card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem]
  · simp [← add_assoc, ← hw.card_inter, card_inter_add_card_union, two_mul,
          hw.card_left, hw.card_right]
  · simpa using ⟨hw.symm.fst_not_mem_right, hw.snd_not_mem⟩
  · simpa using ⟨hw.isPathGraph3Compl.fst_ne_snd, hw.fst_not_mem, hw.fst_not_mem_right⟩
  · simpa using ⟨hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd,
                 hw.not_mem_left, hw.not_mem_right⟩

variable [DecidableRel G.Adj]

lemma exists_isFiveWheelLike_succ_of_not_adj_le_two (h : G.CliqueFree (r + 2))
    (hW : ∀ {y}, y ∈ s ∩ t → G.Adj x y)
    (h2 : #(({v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))).filter (fun z ↦ ¬ G.Adj x z)) ≤ 2) :
    ∃ a b, a ∉ t ∧ b ∉ s ∧
    G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter h hW
  let W := insert v <| insert w₁ <| insert w₂ (s ∪ t)
  have hfst := hw.isPathGraph3Compl.ne_fst
  have hsnd := hw.isPathGraph3Compl.ne_snd
  have ca_db : c = a ∧ d = b := by
    apply eq_of_card_le_two_of_ne hab had hbc <| h2.trans' <| card_le_card _
    intro z; simp_rw [mem_filter, mem_insert, mem_singleton] at *
    aesop
  simp_rw [ca_db.1, ca_db.2, mem_insert] at *
  have has : a ∈ s := by
    obtain (rfl | ha) := ha
    · obtain (rfl | hc) := hc <;> trivial
    · exact ha
  have hbt: b ∈ t := by
    obtain (rfl | hb) := hb;
    · obtain (rfl | hd) := hd <;> trivial
    · exact hb
  have habv : v ≠ a ∧ v ≠ b := ⟨fun h ↦ hw.not_mem_left (h ▸ has), fun h ↦ hw.not_mem_right (h ▸ hbt)⟩
  have haw2 : a ≠ w₂ := fun hf ↦ hw.symm.fst_not_mem_right (hf ▸ has)
  have hbw1 : b ≠ w₁ := fun hf ↦ hw.fst_not_mem_right (hf ▸ hbt)
  have hxvw12 : x ≠ v ∧ x ≠ w₁ ∧ x ≠ w₂ := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.not_mem_left (hax ▸ has)
      · exact haj <| hw.isNClique_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.fst_not_mem (hax ▸ has)
      · exact haj <| hw.isNClique_fst_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · exact hw.snd_not_mem (hbx ▸ hbt)
      · exact hbj <| hw.isNClique_snd_right.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  have wadj : ∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x := by
    intro z hz haz hbz
    by_contra! hf
    apply Nat.lt_le_asymm _ h2
    refine two_lt_card.2 ⟨a, ?_, b, ?_, z, ?_, hab, haz.symm, hbz.symm⟩ <;> rw [mem_filter]
    · exact ⟨mem_insert_of_mem <| mem_insert_of_mem
                <| mem_insert_of_mem <| mem_union_left _ has, hcj⟩
    · exact ⟨mem_insert_of_mem <| mem_insert_of_mem
                <| mem_insert_of_mem <| mem_union_right _ hbt, hdj⟩
    · exact ⟨hz, by rwa [adj_comm] at hf⟩
  -- We now prove that the new 5-wheel is indeed a 5-wheel
  have hc1 : insert v s ⊆ W := insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  have hc2 : insert w₁ s ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm]
    exact insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  have hc3 : insert v t ⊆ W := insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  have hc4 : insert w₂ t ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm w₁, insert_comm v]
    exact insert_subset_insert _ fun _ hx ↦ (by simp [hx])
  refine ⟨_, _, hat, hbs, ⟨hw.isPathGraph3Compl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    <;> try rw [mem_insert, not_or]
  · exact ⟨hxvw12.1.symm, fun hv ↦ hw.not_mem_left (mem_erase.1 hv).2⟩
  · exact ⟨hxvw12.1.symm, fun hv ↦ hw.not_mem_right (mem_erase.1 hv).2⟩
  · exact ⟨hxvw12.2.1.symm, fun hw1 ↦ hw.fst_not_mem (mem_erase.1 hw1).2⟩
  · exact ⟨hxvw12.2.2.symm, fun hv ↦ hw.snd_not_mem (mem_erase.1 hv).2⟩
  · apply hw.isNClique_left.insert_insert_erase has hw.not_mem_left
                      fun z hz hZ ↦ wadj _ (hc1 hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact habv.2.symm <| hz.resolve_right hbs
  · apply hw.isNClique_fst_left.insert_insert_erase has hw.fst_not_mem
                      fun z hz hZ ↦ wadj _ (hc2 hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact hbw1 <| hz.resolve_right hbs
  · apply hw.isNClique_right.insert_insert_erase hbt hw.not_mem_right
                      fun z hz hZ ↦ wadj _ (hc3 hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact habv.1.symm <| hz.resolve_right hat
  · apply hw.isNClique_snd_right.insert_insert_erase hbt hw.snd_not_mem
                      fun z hz hZ ↦ wadj _ (hc4 hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact haw2 <| hz.resolve_right hat
  · rw [← insert_inter_distrib, erase_inter, inter_erase, erase_eq_of_not_mem <|
        not_mem_mono inter_subset_left hbs, erase_eq_of_not_mem <|
        not_mem_mono inter_subset_right hat,
        card_insert_of_not_mem (fun h ↦ G.loopless x (hW h)), hw.card_inter]

lemma one_le_not_adj_of_cliqueFree (hc : G.CliqueFree (r + 2)) (x : α) :
    1 ≤ #((({v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))))).filter (fun z ↦ ¬ G.Adj x z)) := by
  apply card_pos.2
  obtain ⟨_, hz⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hc x
  exact ⟨_, mem_filter.2 ⟨by aesop, hz.2⟩⟩

/--
If `G` is a `Kᵣ₊₂`-free graph with `n` vertices containing a `Wᵣ,ₖ` but no `Wᵣ,ₖ₊₁`
then `G.minDegree ≤ (2 * r + k) * n / (2 * r + k + 3)`
-/
lemma minDegree_le_of_cliqueFree_FiveWheelLikeFree_succ [Fintype α] (hc : G.CliqueFree (r + 2))
    (hm : G.FiveWheelLikeFree r (k + 1)) : G.minDegree ≤ (2 * r + k) * ‖α‖ / (2 * r + k + 3) := by
  let X := {x | ∀ {y}, y ∈ s ∩ t → G.Adj x y}.toFinset
  let W := insert v <| insert w₁ <| insert w₂ (s ∪ t)
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : ∀ x, x ∈ X → 3 ≤ #(W.filter fun z ↦ ¬ G.Adj x z) := by
    intro z hx
    by_contra! h
    obtain ⟨_, _, _, _, hW⟩ := hw.exists_isFiveWheelLike_succ_of_not_adj_le_two hc
      (by simpa [X] using hx) <| Nat.le_of_succ_le_succ h
    exact hm hW
  -- Every vertex has at least 1 non-neighbor in `W`, so we have a bound on the degree sum over `W`
  -- `∑ w ∈ W, H.degree w ≤  |X| * (|W| - 3) + |Xᶜ| * (|W| - 1)`
  have bdW := sum_degree_le_of_le_not_adj dXle (fun y _ ↦ (hw.one_le_not_adj_of_cliqueFree hc) y)
  -- By the definition of `X`, any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : ∀ x, x ∈ Xᶜ → 1 ≤ #((s ∩ t).filter fun z ↦ ¬ G.Adj x z) := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : ∃ y ∈ s ∩ t, ¬ G.Adj x y := by
      contrapose! hx
      rw [mem_compl, not_not, Set.mem_toFinset]
      exact hx _
    exact ⟨_, mem_filter.2 hy⟩
  -- So we also have a bound on the degree sum over `s ∩ t`
  -- `∑ w ∈ s ∩ t, H.degree w ≤  |Xᶜ| * (|s ∩ t| - 1) + |X| * |s ∩ t|`
  have bdX := sum_degree_le_of_le_not_adj xcle (fun x _ ↦ Nat.zero_le _)
  rw [compl_compl, tsub_zero, add_comm] at bdX
  rw [Nat.le_div_iff_mul_le (Nat.add_pos_right _ zero_lt_three)]
  have Wc : #W + k = 2 * r + 3 := hw.card_add_card_inter
  have w3 : 3 ≤ #W := two_lt_card.2 ⟨_, mem_insert_self .., _, by simp [W], _, by simp [W],
    hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩
  -- 1st case: `s ∩ t = ∅`
  by_cases hst : k = 0
  · rw [hst, add_zero] at Wc ⊢
    rw [← Wc, ← tsub_eq_of_eq_add Wc]
    have Xu : X = univ := by
      apply eq_univ_of_forall
      rw [← hw.card_inter, card_eq_zero] at hst
      intro x; simp [X, hst]
    rw [Xu, card_univ, compl_univ, card_empty, zero_mul, add_zero, mul_comm] at bdW
    apply bdW.trans'
    rw [card_eq_sum_ones, mul_sum, mul_one]
    exact sum_le_sum (fun i _ ↦ G.minDegree_le_degree i)
  -- 2nd case `s ∩ t ≠ ∅`
  · have hap :  #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by omega
    calc
    minDegree G * (2 * r + k + 3) ≤ ∑ w ∈ W, G.degree w +  2 * ∑ w ∈ s ∩ t, G.degree w := by
        rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add]
        simp_rw [← hw.card_inter, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one]
        apply add_le_add <;> apply sum_le_sum <;> intro i _
        · exact minDegree_le_degree ..
        · exact mul_comm 2 _ ▸ (Nat.mul_le_mul_left _ <| G.minDegree_le_degree _)
    _ ≤ #X * (#W - 3) + #Xᶜ * (#W - 1) + 2 * (#X * k + #Xᶜ * (k - 1)) :=
          add_le_add bdW <| Nat.mul_le_mul_left _ (hw.card_inter ▸ bdX)
    _ = #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by ring_nf
    _ ≤ (2 * r + k) * ‖α‖ := by
        rw [hap, ← add_mul, card_compl, add_tsub_cancel_of_le (card_le_univ _), mul_comm]
        apply Nat.mul_le_mul_right
        rw [two_mul, ← add_assoc]
        apply Nat.add_le_add_right
        rw [tsub_add_eq_add_tsub w3, Wc, Nat.add_sub_cancel_right]

end IsFiveWheelLike

variable [DecidableEq α]

/-- **Andrasfái-Erdős-Sós**
If `G` is a `Kᵣ₊₁` - free graph with `n` vertices and `(3r - 4)n / (3r - 1) < G.minDegree` then `G`
is `(r + 1)` - colorable, e.g. if `G` is `K₃` - free and `2 * n / 5 < G.minDegree` then `G`
is `2` - colorable.
-/
theorem colorable_of_cliqueFree_lt_minDegree [Fintype α] [DecidableRel G.Adj]
    (hf : G.CliqueFree (r + 1)) (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) :
    G.Colorable r := by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    -- There is an edge maximal Kᵣ₊₃-free supergraph H
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H ↦ H.CliqueFree (r + 3)) G hf
    -- If we can (r + 2) - color H then we can (r + 2) - color G
    apply Colorable.mono_left hle
    by_contra! hnotcol
    -- If H is complete-multipartite and Kᵣ₊₃-free then it is (r + 2) - colorable
    have hn : ¬ H.IsCompleteMultipartite := fun hc ↦ hnotcol <| hc.colorable_of_cliqueFree hmcf.1
    -- H contains `Wᵣ₊₁,ₖ` but not `Wᵣ₊₁,ₖ₊₁`, for some `k ≤ r`
    obtain ⟨_, _, _, _, _, _, hw, hlt, hm⟩ :=
      exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite hmcf hn
    classical
    have hD := hw.minDegree_le_of_cliqueFree_FiveWheelLikeFree_succ hmcf.1 <| hm _ <| lt_add_one _
    exact (hd.trans_le <| minDegree_le_minDegree hle).not_le
             <| hD.trans (kr_bound <| Nat.le_of_succ_le_succ <| hlt)

end SimpleGraph
--end PR4
