/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
 such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Putting these together gives the definition of an `IsFiveWheelLike` structure
which can be found in any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite`).

These play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem.

Main definition:

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s₁ s₂` to form a 5-wheel-like subgraph of
 `G` with `r`-sets `s₁` and `s₂`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl`. -/

open Finset
variable {α : Type*} {a b c d x y : α} {G : SimpleGraph α} {r : ℕ} [DecidableEq α]
/-- Useful trivial fact about when `|{a, b, c, d}| ≤ 2` given `a ≠ b` , `a ≠ d`, `b ≠ c`. -/
private lemma eq_of_card_le_two_of_ne (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c)
    (hc2 : #{a, b, c, d} ≤ 2) : c = a ∧ d = b := by
  by_contra! hf
  apply (#{a, b, c, d}).le_lt_asymm hc2 <| two_lt_card_iff.2 _
  by_cases h : a = c <;> simp_rw [mem_insert, mem_singleton]
  · exact ⟨a, b, d, Or.inl rfl, Or.inr <| Or.inl rfl, Or.inr <| Or.inr <| Or.inr rfl, hab, had,
      fun hbd ↦ (hf h.symm) hbd.symm⟩
  · exact ⟨a, b, c, Or.inl rfl, Or.inr <| Or.inl rfl, Or.inr <| Or.inr <| Or.inl rfl, hab, h, hbc⟩

namespace SimpleGraph
variable {s : Finset α}
private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (ha : G.Adj a b) :
    G.IsNClique (r + 1) (insert b (insert a s)) := by
  apply h1.insert (fun b hb ↦ ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
  · exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) <| fun h' ↦ (h3 (h' ▸ h)).elim

private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c ∈ s)
    (ha : a ∉ s) (hd : ∀ w ∈ insert a s, w ≠ c → G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  have : a ≠ c := fun h ↦ (ha (h ▸ hc)).elim
  rw [insert_comm, ← erase_insert_of_ne this]
  simp_rw [adj_comm, ← not_mem_singleton] at hd
  exact hs.insert_erase (fun _ h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

/--
An `IsFiveWheelLike r v w₁ w₂ s₁ s₂` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets
`s₁` and `s₂` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they form an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s₁ ∪ s₂` and `s₁ ∪ {v}, s₂ ∪ {v}, s₁ ∪ {w₁}, s₂ ∪ {w₂}` are all
`(r + 1)`- cliques.
(If `G` is maximally `(r + 2)`-cliquefree and not complete multipartite then `G` will contain such
 a structure: see
`exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite`.)
-/
structure IsFiveWheelLike (G : SimpleGraph α) (r : ℕ) (v w₁ w₂ : α) (s₁ s₂ : Finset α) : Prop where
  isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
  not_mem_fst : v ∉ s₁
  not_mem_snd : v ∉ s₂
  fst_not_mem : w₁ ∉ s₁
  snd_not_mem : w₂ ∉ s₂
  isNClique_fst : G.IsNClique (r + 1) (insert v s₁)
  isNClique_fst_fst : G.IsNClique (r + 1) (insert w₁ s₁)
  isNClique_snd : G.IsNClique (r + 1) (insert v s₂)
  isNClique_snd_snd : G.IsNClique (r + 1) (insert w₂ s₂)

lemma exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r v w₁ w₂ s₁ s₂ := by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s₁, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨s₂, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact  ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8⟩

/--
`G.IsFiveWheelLikeFree r k` iff the sets `s₁` and `s₂` in any `G.IsFiveWheelLiker v w₁ w₂ s₁ s₂`
structure meet in fewer than `k` vertices.
-/
def IsFiveWheelLikeFree (G : SimpleGraph α) (r k : ℕ) : Prop :=
    ∀ v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r v w₁ w₂ s₁ s₂ → #(s₁ ∩ s₂) < k

namespace IsFiveWheelLike
variable {v w₁ w₂ : α} {s₁ s₂ : Finset α} (hw : G.IsFiveWheelLike r v w₁ w₂ s₁ s₂)

include hw

@[symm] lemma symm : G.IsFiveWheelLike r v w₂ w₁ s₂ s₁ :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2⟩

lemma fst_not_mem_snd : w₁ ∉ s₂ :=
  fun h ↦ hw.isPathGraph3Compl.not_adj_fst <| hw.isNClique_snd.1 (mem_insert_self ..)
  (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

lemma card_isNClique_erase : s₁.card = r := by
  have := hw.isNClique_fst.2
  rwa [card_insert_of_not_mem hw.not_mem_fst, Nat.succ_inj] at this

lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : #(s₁ ∩ s₂) < r := by
  contrapose! h
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_isNClique_erase ▸ h)
  have ht := eq_of_subset_of_card_le inter_subset_right (hw.symm.card_isNClique_erase ▸ h)
  exact (hw.isNClique_fst_fst.insert_insert (hs ▸ ht.symm ▸ hw.isNClique_snd_snd)
    hw.symm.fst_not_mem_snd hw.isPathGraph3Compl.adj).not_cliqueFree

lemma exist_not_adj_of_adj_inter (h : G.CliqueFree (r + 2)) (hW : ∀ {y}, y ∈ s₁ ∩ s₂ → G.Adj x y) :
    ∃ a b c d, a ∈ insert w₁ s₁ ∧ ¬ G.Adj x a ∧ b ∈ insert w₂ s₂ ∧ ¬ G.Adj x b ∧ c ∈ insert v s₁ ∧
      ¬ G.Adj x c ∧ d ∈ insert v s₂ ∧ ¬ G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ s₂ ∧ b ∉ s₁ := by
  obtain ⟨_, ha, haj⟩ := hw.isNClique_fst_fst.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hb, hbj⟩ := hw.isNClique_snd_snd.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hc, hcj⟩ := hw.isNClique_fst.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨_, hd, hdj⟩ := hw.isNClique_snd.exists_not_adj_of_cliqueFree_succ h x
  refine ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, ?_, ?_, ?_, ?_, ?_⟩
  <;> rw [mem_insert] at *
  · rintro rfl
    obtain (rfl | ha) := ha
    · obtain (rfl | hb) := hb
      · exact hw.isPathGraph3Compl.fst_ne_snd rfl
      · exact hw.fst_not_mem_snd hb
    · obtain (rfl | hb) := hb
      · exact hw.symm.fst_not_mem_snd ha
      · exact haj <| hW <| mem_inter_of_mem ha hb
  · rintro rfl
    obtain (rfl | ha) := ha
    · obtain (rfl | hd) := hd
      · exact hw.isPathGraph3Compl.ne_fst rfl
      · exact hw.fst_not_mem_snd  hd
    · obtain (rfl | hd) := hd
      · exact hw.not_mem_fst ha
      · exact haj <| hW <| mem_inter_of_mem ha hd
  · rintro rfl;
    obtain (rfl | hb) := hb
    · obtain (rfl | hc) := hc
      · exact hw.isPathGraph3Compl.ne_snd rfl
      · exact hw.symm.fst_not_mem_snd  hc
    · obtain (rfl | hc) := hc
      ·  exact hw.not_mem_snd hb
      ·  exact hbj <| hW <| mem_inter_of_mem hc hb
  · intro hat
    obtain (rfl | ha) := ha
    · exact hw.fst_not_mem_snd hat
    · exact haj <| hW <| mem_inter_of_mem ha hat
  · intro hbs
    obtain (rfl | hb) := hb
    · exact hw.symm.fst_not_mem_snd hbs
    · exact hbj <| hW <| mem_inter_of_mem hbs hb

lemma card_add_card_inter :
    #(insert v <| insert w₁ <| insert w₂ (s₁ ∪ s₂)) + #(s₁ ∩ s₂) = 2 * r + 3 := by
  rw [add_comm, card_insert_of_not_mem, card_insert_of_not_mem, card_insert_of_not_mem]
  · simp_rw [← add_assoc, card_inter_add_card_union, two_mul, hw.card_isNClique_erase,
    hw.symm.card_isNClique_erase]
  · rw [mem_union, not_or]
    exact ⟨hw.symm.fst_not_mem_snd, hw.snd_not_mem⟩
  · rw [mem_insert, mem_union, not_or, not_or]
    exact ⟨hw.isPathGraph3Compl.fst_ne_snd, hw.fst_not_mem, hw.fst_not_mem_snd⟩
  · simp_rw [mem_insert, mem_union]
    push_neg
    exact ⟨hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd,
           hw.not_mem_fst, hw.not_mem_snd⟩

-- Note that `{v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂)))` is `insert v <| insert w₁ <| insert w₂ (s₁ ∪ s₂)`
lemma three_le_card : 3 ≤ #({v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂)))) :=
  two_lt_card.2 ⟨_, mem_insert_self .., _, by simp, _, by simp, hw.isPathGraph3Compl.ne_fst,
                hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩

variable [DecidableRel G.Adj]

lemma exists_isFiveWheelLike_insert_of_not_adj_le_two (h : G.CliqueFree (r + 2))
    (hW : ∀ {y}, y ∈ s₁ ∩ s₂ → G.Adj x y)
    (h2 : #(({v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂)))).filter (fun z ↦ ¬ G.Adj x z)) ≤ 2) :
    ∃ a b, a ∉ s₂ ∧ b ∉ s₁ ∧
    G.IsFiveWheelLike r v w₁ w₂ (insert x (s₁.erase a)) (insert x (s₂.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter h hW
  let W := insert v <| insert w₁ <| insert w₂ (s₁ ∪ s₂)
  have hfst := hw.isPathGraph3Compl.ne_fst
  have hsnd := hw.isPathGraph3Compl.ne_snd
  have ca_db : c = a ∧ d = b := by
    apply eq_of_card_le_two_of_ne hab had hbc <| h2.trans' <| card_le_card _
    intro z; simp_rw [mem_filter, mem_insert, mem_singleton] at *
    aesop
  simp_rw [ca_db.1, ca_db.2, mem_insert] at *
  have has : a ∈ s₁ := by
    obtain (rfl | ha) := ha
    · obtain (rfl | hc) := hc <;> trivial
    · exact ha
  have hbt: b ∈ s₂ := by
    obtain (rfl | hb) := hb;
    · obtain (rfl | hd) := hd <;> trivial
    · exact hb
  have habv : v ≠ a ∧ v ≠ b := ⟨fun h ↦ hw.not_mem_fst (h ▸ has), fun h ↦ hw.not_mem_snd (h ▸ hbt)⟩
  have haw2 : a ≠ w₂ := fun hf ↦ hw.symm.fst_not_mem_snd (hf ▸ has)
  have hbw1 : b ≠ w₁ := fun hf ↦ hw.fst_not_mem_snd (hf ▸ hbt)
  have hxvw12 : x ≠ v ∧ x ≠ w₁ ∧ x ≠ w₂ := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.not_mem_fst (hax ▸ has)
      · exact haj <| hw.isNClique_fst.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.fst_not_mem (hax ▸ has)
      · exact haj <| hw.isNClique_fst_fst.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · exact hw.snd_not_mem (hbx ▸ hbt)
      · exact hbj <| hw.isNClique_snd_snd.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
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
  have hc1 : insert v s₁ ⊆ W := by apply insert_subset_insert; intro x hx; simp [hx]
  have hc2 : insert w₁ s₁ ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm]
    apply insert_subset_insert
    intro x hx; simp [hx]
  have hc3 : insert v s₂ ⊆ W := by apply insert_subset_insert; intro x hx; simp [hx]
  have hc4 : insert w₂ s₂ ⊆ W := by
    change _ ⊆ insert _ _
    rw [insert_comm w₁, insert_comm v]
    apply insert_subset_insert
    intro x hx; simp [hx]
  refine ⟨_, _, hat, hbs, ⟨hw.isPathGraph3Compl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    <;> try rw [mem_insert, not_or]
  · exact ⟨hxvw12.1.symm, fun hv ↦ hw.not_mem_fst (mem_erase.1 hv).2⟩
  · exact ⟨hxvw12.1.symm, fun hv ↦ hw.not_mem_snd (mem_erase.1 hv).2⟩
  · exact ⟨hxvw12.2.1.symm, fun hw1 ↦ hw.fst_not_mem (mem_erase.1 hw1).2⟩
  · exact ⟨hxvw12.2.2.symm, fun hv ↦ hw.snd_not_mem (mem_erase.1 hv).2⟩
  · apply hw.isNClique_fst.insert_insert_erase has hw.not_mem_fst
                      fun z hz hZ ↦ wadj _ (hc1 hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact habv.2.symm <| hz.resolve_right hbs
  · apply hw.isNClique_fst_fst.insert_insert_erase has hw.fst_not_mem
                      fun z hz hZ ↦ wadj _ (hc2 hz) hZ ?_
    rintro rfl; rw [mem_insert] at hz
    exact hbw1 <| hz.resolve_right hbs
  · apply hw.isNClique_snd.insert_insert_erase hbt hw.not_mem_snd
                      fun z hz hZ ↦ wadj _ (hc3 hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact habv.1.symm <| hz.resolve_right hat
  · apply hw.isNClique_snd_snd.insert_insert_erase hbt hw.snd_not_mem
                      fun z hz hZ ↦ wadj _ (hc4 hz) ?_ hZ
    rintro rfl; rw [mem_insert] at hz
    exact haw2 <| hz.resolve_right hat

lemma one_le_not_adj_of_cliqueFree (hcf : G.CliqueFree (r + 2)) (x : α) :
    1 ≤ #((({v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂))))).filter (fun z ↦ ¬ G.Adj  x z)) := by
  apply card_pos.2
  obtain ⟨_, hz⟩ := hw.isNClique_fst_fst.exists_not_adj_of_cliqueFree_succ hcf x
  exact ⟨_, mem_filter.2 ⟨by aesop, hz.2⟩⟩

/--
If G is Kᵣ₊₂-free and contains a maximal `IsFiveWheelLike` structure (in terms of the size of the
intersection of the cliques) then every vertex that is adjacent to all of the common
clique vertices is non-adjacent to at least 3 vertices of the wheel.
-/
lemma three_le_not_adj_of_cliqueFree_max (hcf : G.CliqueFree (r + 2))
    (hW : ∀ {y}, y ∈ s₁ ∩ s₂ → G.Adj x y)
    (hmax : ∀ s₁' s₂', G.IsFiveWheelLike r v w₁ w₂ s₁' s₂' → #(s₁' ∩ s₂') ≤ #(s₁ ∩ s₂)) :
    3 ≤ #(({v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂)))).filter fun z ↦ ¬ G.Adj x z) := by
  by_contra! hc
  obtain ⟨c, d, hw1 , hw2, hbW⟩ := hw.exists_isFiveWheelLike_insert_of_not_adj_le_two hcf hW
                                        <| Nat.succ_le_succ_iff.1 hc
  apply Nat.not_succ_le_self #(s₁ ∩ s₂)
  rw [Nat.succ_eq_add_one, ← card_insert_of_not_mem fun hx ↦ G.loopless x <| hW hx] at *
  apply ((insert_inter_distrib _ _ x).symm ▸ hmax _ _ hbW).trans'
              <| card_le_card <| insert_subset_insert ..
  rw [erase_inter, inter_erase, erase_eq_of_not_mem <| not_mem_mono inter_subset_left hw2,
        erase_eq_of_not_mem fun hf ↦ hw1 <| mem_inter.1 hf|>.2]

end IsFiveWheelLike

lemma exists_max_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ v w₁ w₂ s₁ s₂, G.IsFiveWheelLike r v w₁ w₂ s₁ s₂ ∧ ∀ s₁' s₂',
    G.IsFiveWheelLike r v w₁ w₂ s₁' s₂' → #(s₁' ∩ s₂') ≤ #(s₁ ∩ s₂) := by
  obtain ⟨v, w₁, w₂, s₁, s₂, hw⟩ :=
    exists_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite h hnc
  let P : ℕ → Prop := fun k ↦ ∃ s₁ s₂, G.IsFiveWheelLike r v w₁ w₂ s₁ s₂ ∧ #(s₁ ∩ s₂) = k
  have : P #(s₁ ∩ s₂) := by use s₁, s₂
  classical
  obtain ⟨s₁, s₂, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le this
  use v, w₁, w₂, s₁, s₂, hw.1
  intro s₁' s₂' hw'
  exact (Nat.le_findGreatest (hw'.card_inter_lt_of_cliqueFree h.1).le (by use s₁', s₂')).trans
            hw.2.symm.le

end SimpleGraph
