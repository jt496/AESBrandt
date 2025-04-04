/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import AESBrandt.Clique
import AESBrandt.CompleteMultipartite

/-!
If `G` is maximally Kᵣ₊₂-free and xy is a non-edge then there exists an r-set such that
s ∪ {x} and s ∪ {y} are both r + 1 cliques.

If G is not complete-multipartite then it contains an edge w₁w₂ and a vertex v such that vw₁ and
vw₂ are non-edges. We call this three vertex graph with a single edge a `P₂-complement`.

Putting these together gives the definition of a 5-wheel-like subgraph which can be found in any
maximally Kᵣ₊₂-free graph that is not complete-multipartite.

FiveWheel-like subgraphs plays a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem.

Main definition:
* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of `G` with
`r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsP2Complement`. -/

open Finset
variable {α : Type*} {a b c d x y : α} {G : SimpleGraph α} {r n : ℕ} {s : Finset α} [DecidableEq α]
/-- Useful trivial fact about when `|{a, b, c, d}| ≤ 2` given `a ≠ b` , `a ≠ d`, `b ≠ c`. -/
private lemma eq_of_card_le_two_of_ne (hab : a ≠ b) (had : a ≠ d) (hbc : b ≠ c) (hc2 : #{a, b, c, d} ≤ 2) :
    c = a ∧ d = b := by
  by_contra! hf
  apply (#{a, b, c, d}).le_lt_asymm hc2 <| two_lt_card_iff.2 _
  by_cases hac : a = c <;> simp_rw [mem_insert, mem_singleton]
  · exact ⟨a, b, d, Or.inl rfl, Or.inr <| Or.inl rfl, Or.inr <| Or.inr <| Or.inr rfl, hab, had,
      fun hbd ↦ (hf hac.symm) hbd.symm⟩
  · exact ⟨a, b, c, Or.inl rfl, Or.inr <| Or.inl rfl, Or.inr <| Or.inr <| Or.inl rfl, hab, hac, hbc⟩

namespace SimpleGraph

lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) :  ∃ y, y ∈ s ∧ ¬G.Adj x y := by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

lemma exists_of_max_cliqueFree_not_adj (h : Maximal (fun H ↦ H.CliqueFree n) G) (hne : x ≠ y)
    (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique (n - 1) (insert x s) ∧ G.IsNClique (n - 1) (insert y s) := by
  obtain ⟨t, hc, xym⟩: ∃ t, (G ⊔ edge x y).IsNClique n t ∧ x ∈ t ∧ y ∈ t :=
    let ⟨t, hc⟩ := not_forall_not.1 <| h.not_prop_of_gt <| G.lt_sup_edge _ _ hne hn
    ⟨t, hc, ⟨h.1.mem_of_sup_edge_isNClique hc, h.1.mem_of_sup_edge_isNClique (edge_comm _ _ ▸ hc)⟩⟩
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (not_mem_erase _ _), not_mem_erase _ _
  rw [insert_erase (mem_erase_of_ne_of_mem hne.symm xym.2), erase_right_comm,
      insert_erase (mem_erase_of_ne_of_mem hne xym.1)]
  cases n with
  | zero => exact False.elim <| not_cliqueFree_zero h.1
  | succ n =>
    exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem xym.2, hc.erase_of_sup_edge_of_mem xym.1⟩

private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (hadj : G.Adj a b) :
    G.IsNClique (r + 1) (insert b ((insert a) s)) := by
  apply h1.insert
  intro b hb
  obtain (rfl | h) := mem_insert.1 hb
  · exact hadj.symm
  · exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) <| fun h' ↦ False.elim <| h3 (h' ▸ h)

private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c ∈ s)
    (ha : a ∉ s) (hd : ∀ w ∈ insert a s, w ≠ c → G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  have : a ≠ c := fun h ↦ False.elim <| ha (h ▸ hc)
  rw [insert_comm, ← erase_insert_of_ne this]
  simp_rw [adj_comm, ← not_mem_singleton] at hd
  exact hs.insert_erase (fun x h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

variable (G)
/-- A `IsFiveWheelLike r` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets `s` and `t`
such that: `v w₁ w₂` form an `IsP2Complement`; `v, w₁, w₂ ∉ s ∪ t` and
`v ∪ s, v ∪ t, w₁ ∪ s, w₂ ∪ t` are `(r + 1)`- cliques. -/
structure IsFiveWheelLike (r : ℕ) (v w₁ w₂ : α) (s t : Finset α) : Prop where
  isP2Complement : G.IsP2Complement v w₁ w₂
  not_mem   : v ∉ s ∧ v ∉ t ∧ w₁ ∉ s ∧ w₂ ∉ t
  cliques : G.IsNClique (r + 1) (insert v s) ∧ G.IsNClique (r + 1) (insert w₁ s)
              ∧ G.IsNClique (r + 1) (insert v t) ∧ G.IsNClique (r + 1) (insert w₂ t)

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {G} {t : Finset α} (hw : G.IsFiveWheelLike r v w₁ w₂ s t) include hw

lemma symm :  G.IsFiveWheelLike r v w₂ w₁ t s :=
  let ⟨p2, ⟨d1, d2, d3, d4⟩, ⟨c1, c2, c3, c4⟩⟩ := hw
  ⟨p2.symm, ⟨d2, d1, d4, d3⟩, ⟨c3, c4, c1, c2⟩⟩

lemma not_mem' : w₁ ∉ t ∧ w₂ ∉ s :=
  ⟨fun hf ↦ hw.isP2Complement.not_adj.1 <| hw.cliques.2.2.1.1 (mem_insert_self ..)
    (mem_insert_of_mem hf) hw.isP2Complement.ne.1,
   fun hf ↦ hw.isP2Complement.not_adj.2 <| hw.cliques.1.1 (mem_insert_self ..)
    (mem_insert_of_mem hf) hw.isP2Complement.ne.2⟩

lemma card_cliques : s.card = r ∧ t.card = r :=by
  constructor
  · have := hw.cliques.1.2
    rwa [card_insert_of_not_mem hw.not_mem.1, Nat.succ_inj] at this
  · have := hw.cliques.2.2.1.2
    rwa [card_insert_of_not_mem hw.not_mem.2.1, Nat.succ_inj] at this

/-- The size of a 5-wheel-like strucutre will vary depending on how large |s ∩ t| is, so a useful
identity is  `|{v, w₁, w₂} ∪ s ∪ t| = 2r + 3 - |s ∩ t|`, which we express as follows .-/
lemma card_add_card_inter : #(insert v (insert w₁ (insert w₂ (s ∪ t)))) + #(s ∩ t) = 2 * r + 3 := by
  rw [card_insert_of_not_mem, add_comm, card_insert_of_not_mem, card_insert_of_not_mem]
  · simp_rw [← add_assoc, card_inter_add_card_union, two_mul, hw.card_cliques.1, hw.card_cliques.2]
  · rw [mem_union, not_or]
    exact ⟨hw.not_mem'.2, hw.not_mem.2.2.2⟩
  · rw [mem_insert, mem_union, not_or, not_or]
    exact ⟨hw.isP2Complement.adj.ne, hw.not_mem.2.2.1, hw.not_mem'.1⟩
  · rw [mem_insert, mem_insert, mem_union]
    push_neg
    exact ⟨hw.isP2Complement.ne.1, hw.isP2Complement.ne.2, hw.not_mem.1, hw.not_mem.2.1⟩

/-- Every 5-wheel contains at least 3 vertices: v w₁ w₂-/
lemma three_le_card : 3 ≤ #(insert v (insert w₁ (insert w₂ (s ∪ t)))) := two_lt_card.2
  ⟨v, mem_insert_self .., w₁, by simp, w₂, by simp, hw.isP2Complement.ne.1,
    hw.isP2Complement.ne.2, hw.isP2Complement.adj.ne⟩

/-- If s ∩ t contains an r-set then then s ∪ {w₁,w₂} is Kᵣ₊₂ so -/
lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : #(s ∩ t) < r := by
  contrapose! h
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_cliques.1 ▸ h)
  have ht := eq_of_subset_of_card_le inter_subset_right (hw.card_cliques.2 ▸ h)
  exact (hw.cliques.2.1.insert_insert (hs ▸ ht.symm ▸ hw.cliques.2.2.2)
    hw.not_mem'.2 hw.isP2Complement.adj).not_cliqueFree

omit hw in
/-- If G is maximally Kᵣ₊₂-free and not complete-multi-partite then it contains a
   5-wheel-like structure that is maximal in the sense that the intersection of its
   cliques has maximum size. -/
lemma _root_.SimpleGraph.exists_max_isFiveWheelLike (h : Maximal (fun H => H.CliqueFree (r + 2)) G)
    (hnc : ¬ G.IsCompleteMultipartite) : ∃ v w₁ w₂ s t, G.IsFiveWheelLike r v w₁ w₂ s t ∧ ∀ s' t',
    G.IsFiveWheelLike r v w₁ w₂ s' t' → #(s' ∩ t') ≤ #(s ∩ t) := by
  classical
  obtain ⟨v, w₁, w₂, h3⟩ := exists_isP2Complement_of_not_isCompleteMultipartite hnc
  obtain ⟨s, hvs, hw1s, hcsv, hcsw1⟩ := exists_of_max_cliqueFree_not_adj h h3.ne.1 h3.not_adj.1
  obtain ⟨t, hvt, hw2t, hctv, hctw2⟩ := exists_of_max_cliqueFree_not_adj h h3.ne.2 h3.not_adj.2
  let hw : G.IsFiveWheelLike r v w₁ w₂ s t :=  ⟨h3, ⟨hvs, hvt, hw1s, hw2t⟩, ⟨hcsv, hcsw1, hctv, hctw2⟩⟩
  let P : ℕ → Prop := fun k ↦ ∃ s t, G.IsFiveWheelLike r v w₁ w₂ s t ∧ #(s ∩ t) = k
  have : P #(s ∩ t) := by use s, t
  obtain ⟨s, t, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le this
  use v, w₁, w₂, s, t, hw.1
  intro s' t' hw'
  exact (Nat.le_findGreatest (hw'.card_inter_lt_of_cliqueFree h.1).le (by use s', t')).trans hw.2.symm.le

/-- This is a warmup for the main lemma `exists_isFiveWheelLike_of_not_adj_le_two` where we use it with
`eq_of_card_le_two_of_ne` to help build a bigger 5-wheel. -/
lemma exist_non_adj_of_adj_inter (h : G.CliqueFree (r + 2)) (hWc : ∀ {y}, y ∈ s ∩ t → G.Adj x y ) :
    ∃ a b c d, a ∈ insert w₁ s ∧ ¬G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬G.Adj x b ∧ c ∈ insert v s ∧
      ¬G.Adj x c ∧ d ∈ insert v t ∧ ¬G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨a, ha, haj⟩ := hw.cliques.2.1.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨b, hb, hbj⟩ := hw.cliques.2.2.2.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨c, hc, hcj⟩ := hw.cliques.1.exists_not_adj_of_cliqueFree_succ h x
  obtain ⟨d, hd, hdj⟩ := hw.cliques.2.2.1.exists_not_adj_of_cliqueFree_succ h x
  have := hw.isP2Complement.adj.ne
  have := hw.isP2Complement.ne
  have := hw.not_mem'
  refine ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, ?_, ?_, ?_, ?_, ?_⟩
  <;> rw [mem_insert] at *
  · rintro rfl
    obtain (rfl | ha) := ha
    · obtain (rfl | hb) := hb
      · contradiction
      · exact this.1 hb
    · obtain (rfl | hb) := hb
      · exact this.2 ha
      · exact haj (hWc <| mem_inter_of_mem ha hb)
  · rintro rfl
    obtain (rfl | ha) := ha
    · obtain (rfl | hd) := hd
      · exact hw.isP2Complement.ne.1 rfl
      · exact hw.not_mem'.1  hd
    · obtain (rfl | hd ) := hd
      · exact hw.not_mem.1 ha
      · exact haj <| hWc <| mem_inter_of_mem ha hd
  · rintro rfl;
    obtain (rfl | hb) := hb
    · obtain (rfl | hc ) := hc
      · exact hw.isP2Complement.ne.2 rfl
      · exact hw.not_mem'.2  hc
    · obtain (rfl | hc ) := hc
      ·  exact hw.not_mem.2.1 hb
      ·  exact hbj <| hWc <|  mem_inter_of_mem hc hb
  · intro hat
    obtain (rfl | ha) := ha
    · exact this.1 hat
    · exact haj (hWc <| mem_inter_of_mem ha hat)
  · intro hbs
    obtain (rfl | hb) := hb
    · exact this.2 hbs
    · exact hbj (hWc <| mem_inter_of_mem hbs hb)

open Classical
/-- We can build a 5-wheel with a larger common clique set if there is a core vertex that is
 adjacent to all but at most 2 of the vertices of the 5-wheel -/
lemma exists_isFiveWheelLike_of_not_adj_le_two (h : G.CliqueFree (r + 2)) (hWc : ∀ {y}, y ∈ s ∩ t → G.Adj x y)
(hsmall : #((insert v (insert w₁ (insert w₂ (s ∪ t)))).filter (fun z ↦ ¬ G.Adj x z)) ≤ 2) :
    ∃ a b, a ∉ t ∧ b ∉ s ∧
    G.IsFiveWheelLike r v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_non_adj_of_adj_inter h hWc
  let W := insert v <| insert w₁ <| insert w₂ (s ∪ t)
  have ⟨_,_⟩ := hw.isP2Complement.ne
  have ca_db : c = a ∧ d = b := by
    apply eq_of_card_le_two_of_ne hab had hbc <| hsmall.trans' <| card_le_card _
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
  have habv : v ≠ a ∧ v ≠ b := ⟨fun hf ↦ hw.not_mem.1 (hf ▸ has), fun hf ↦ hw.not_mem.2.1 (hf ▸ hbt)⟩
  have haw2 : a ≠ w₂ := fun hf ↦ hw.not_mem'.2 (hf ▸ has)
  have hbw1 : b ≠ w₁ := fun hf ↦ hw.not_mem'.1 (hf ▸ hbt)
  have hxvw12 : x ≠ v ∧ x ≠ w₁ ∧ x ≠ w₂ := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.not_mem.1 (hax ▸ has)
      · exact haj <| hw.cliques.1.1 (mem_insert_self _ _) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · exact hw.not_mem.2.2.1 (hax ▸ has)
      · exact haj <| hw.cliques.2.1.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · exact hw.not_mem.2.2.2 (hbx ▸ hbt)
      · exact hbj <| hw.cliques.2.2.2.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  have wadj : ∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x := by
    intro z hz haz hbz
    by_contra! hf
    have gt2 : 2 < #(W.filter (fun z ↦ ¬ G.Adj x z)) := by
      refine two_lt_card.2 ⟨a, ?_, b , ?_, z, ?_, hab, haz.symm, hbz.symm⟩ <;> rw [mem_filter]
      · exact ⟨by aesop, hcj⟩
      · exact ⟨by aesop, hdj⟩
      · rw [adj_comm] at hf
        exact ⟨hz, hf⟩
    apply Nat.lt_le_asymm gt2 hsmall
-- Below we prove that the new 5-wheel is indeed a 5-wheel
  refine ⟨a, b, hat, hbs, ⟨hw.isP2Complement, ?_, ?_⟩⟩
-- We first prove `v w₁ w₂` are not in the various new cliques
  · simp_rw [mem_insert, not_or]
    exact ⟨⟨hxvw12.1.symm, fun hv ↦ hw.not_mem.1 (mem_erase.1 hv).2 ⟩,
           ⟨hxvw12.1.symm, fun hv ↦ hw.not_mem.2.1 (mem_erase.1 hv).2⟩,
           ⟨hxvw12.2.1.symm, fun hw1 ↦ hw.not_mem.2.2.1 (mem_erase.1 hw1).2⟩,
           ⟨hxvw12.2.2.symm, fun hv ↦ hw.not_mem.2.2.2 (mem_erase.1 hv).2⟩⟩
-- Finally we prove that the new cliques are indeed (r + 1)-cliques
  · refine ⟨hw.cliques.1.insert_insert_erase has hw.not_mem.1
                      fun z hz hZ ↦ wadj _ (by aesop) hZ ?_,
            hw.cliques.2.1.insert_insert_erase has hw.not_mem.2.2.1
                      fun z hz hZ ↦  wadj _ (by aesop) hZ ?_,
            hw.cliques.2.2.1.insert_insert_erase hbt hw.not_mem.2.1
                      fun z hz hZ ↦  wadj _ (by aesop)  ?_ hZ,
            hw.cliques.2.2.2.insert_insert_erase hbt hw.not_mem.2.2.2
                      fun z hz hZ ↦ wadj _ (by aesop) ?_ hZ⟩
    <;> rintro rfl <;> rw [mem_insert] at hz
    · exact habv.2.symm (hz.resolve_right hbs)
    · exact hbw1 (hz.resolve_right hbs)
    · exact habv.1.symm (hz.resolve_right hat)
    · exact haw2 (hz.resolve_right hat)

/-- For any x there is a 5-wheel vertex that is not adjacent to x (in fact there is one in s ∪ {w₁}) -/
lemma one_le_not_adj_of_cliqueFree (hcf : G.CliqueFree (r + 2)) (x : α) :
    1 ≤ #(((insert v (insert w₁ (insert w₂ (s ∪ t))))).filter (fun z ↦ ¬ G.Adj  x z)) := by
  apply card_pos.2
  obtain ⟨_, hz⟩ := hw.cliques.2.1.exists_not_adj_of_cliqueFree_succ hcf x
  exact ⟨_, mem_filter.2 ⟨by aesop, hz.2⟩⟩

/-- If G is Kᵣ₊₂-free and contains a maximal FiveWheel (in terms of the size of the
intersection of the cliques) then every vertex that is adjacent to all of the common
clique vertices is non-adjacent to at least 3 vertices in W -/
lemma three_le_not_adj_of_cliqueFree_max (hcf : G.CliqueFree (r + 2)) (hWc : ∀ {y}, y ∈ s ∩ t → G.Adj x y)
(hmax : ∀ s' t', G.IsFiveWheelLike r v w₁ w₂ s' t' → #(s' ∩ t') ≤ #(s ∩ t)) :
    3 ≤ #(((insert v (insert w₁ (insert w₂ (s ∪ t))))).filter fun z ↦ ¬ G.Adj x z) := by
  by_contra! hc
  obtain ⟨c, d, hw1 , hw2, hbW⟩ := hw.exists_isFiveWheelLike_of_not_adj_le_two hcf hWc
          <| Nat.succ_le_succ_iff.1 hc
  apply Nat.not_succ_le_self #(s ∩ t)
  rw [Nat.succ_eq_add_one, ← card_insert_of_not_mem fun hx ↦ G.loopless x <| hWc hx] at *
  apply ((insert_inter_distrib _ _ x).symm ▸ hmax _ _ hbW).trans'
              <| card_le_card <| insert_subset_insert ..
  rw [erase_inter, inter_erase, erase_eq_of_not_mem <| not_mem_mono inter_subset_left hw2,
        erase_eq_of_not_mem fun hf ↦ hw1 <| mem_inter.1 hf|>.2]

end SimpleGraph.IsFiveWheelLike
