import AESBrandt.P3bar
import AESBrandt.MaxCliqueFree

namespace SimpleGraph
open Finset
variable {α : Type _} {G : SimpleGraph α}  [DecidableEq α] 

section Wheel

/-- A IsWheel r structure in G is 3 vertices and two sets such that... -/
structure IsWheel (r : ℕ) (v w₁ w₂ : α) (s t : Finset α) : Prop where
  P3 : G.P3bar v w₁ w₂ -- w₁w₂ ∈ E(G) but vw₁,vw₂ ∉ E(G) 
  disj : v ∉ s ∧ v ∉ t ∧ w₁ ∉ s ∧ w₂ ∉ t
  cliques : G.IsNClique (r+1) (insert v s) ∧ G.IsNClique (r+1) (insert w₁ s) ∧ G.IsNClique (r+1) (insert v t) ∧ G.IsNClique (r+1) (insert w₂ t)
  
/-- The vertex set of the Wheel -/  
@[reducible]
def wheelVerts  (_hw: G.IsWheel r v w₁ w₂ s t) : Finset α :=(insert v (insert w₁ (insert w₂ (s ∪ t) )))

/-- Helper lemma to show x ∈ W -/
lemma mem_wheelVerts (hw: G.IsWheel r v w₁ w₂ s t) :
 x ∈ insert w₁ s ∨ x ∈ insert w₂ t ∨ x ∈ insert v s ∨ x ∈ insert v t ↔ x ∈ wheelVerts hw:=
by
  rw [mem_insert, mem_insert, mem_insert, mem_insert, mem_insert, mem_insert , mem_insert]
  constructor
  · intro h 
    rcases h with (xw1 | xs) | (xw2 | xt) | (xv |xs) | (xv | xt)
    · right ; left ; exact xw1
    · right ; right ; right ; rw [mem_union] ; left ;exact xs 
    · right ; right ; left ; exact xw2
    · right ; right ; right ; rw [mem_union] ; right ; exact xt
    · left ; exact xv
    · right ; right ; right ; rw [mem_union] ; left ;exact xs 
    · left ; exact xv
    · right ; right ; right ; rw [mem_union] ; right ; exact xt
  · intro h
    rcases h with xv | xw1 | xw2 | xsu
    · right ; right ; left ; left ; exact xv
    · left ; left ; exact xw1 
    · right ; left ; left ; exact xw2
    · rw [mem_union] at xsu 
      rcases xsu with xs | xt
      · left ; right ; exact xs
      · right ; left ; right ; exact xt

/-- We automatically have w₁ ∉ t and w₂ ∉ s for any wheel -/
lemma IsWheel_disj_ext (h: G.IsWheel r v w₁ w₂ s t ): w₁ ∉ t ∧ w₂ ∉ s:=
by
  constructor
  · intro w1t
    apply h.P3.nonedge.1
    apply h.cliques.2.2.1.clique
    · rw [mem_coe , mem_insert] ; left ; rfl
    · rw [mem_coe , mem_insert] ; right ; exact w1t 
    · exact (P3bar.ne h.P3).1
  · intro w2t
    apply h.P3.nonedge.2
    apply h.cliques.1.clique
    · rw [mem_coe , mem_insert] ; left ; rfl
    · rw [mem_coe , mem_insert] ; right ; exact w2t 
    · exact (P3bar.ne h.P3).2


    /-have w1_mem_clique : w₁ ∈ insert v t 
    · rw [mem_insert] ; right ; exact w1t-/
    
     

/-- A wheel consists of the 3 vertices v, w₁, w₂, and the r-sets s , t but the size will vary 
depending on how large |s ∩ t| is, so a useful identity is
#verts in Wheel =  |s ∪ t| + 3 = 2r+3 - |s∩t|, which we express without subtraction -/
lemma card_wheelVerts  (hw: G.IsWheel r v w₁ w₂ s t) : card (wheelVerts hw) + card (s ∩ t) = 2*r+3:=
by
  have v_not_mem : ¬ v ∈ insert w₁ (insert w₂ (s ∪ t)) := by
    rw [mem_insert] ; push_neg
    constructor
    · exact (P3bar.ne hw.P3).1
    · rw [mem_insert] ; push_neg
      constructor
      · exact (P3bar.ne hw.P3).2
      · rw [mem_union] ; push_neg
        constructor
        · exact hw.disj.1
        · exact hw.disj.2.1  
  rw [add_comm , wheelVerts , card_insert_eq_ite , if_neg v_not_mem ]
  have w1_not_mem : ¬ w₁ ∈ insert w₂ (s ∪ t) := by
    rw [mem_insert] ; push_neg
    constructor
    · apply Adj.ne 
      exact hw.P3.edge
    · rw [mem_union] ; push_neg
      constructor
      · exact hw.disj.2.2.1
      · exact (IsWheel_disj_ext hw).1
  rw [card_insert_eq_ite , if_neg w1_not_mem ]
  have w2_not_mem : ¬ w₂ ∈ s ∪ t := by
    rw [mem_union] ; push_neg
    constructor
    · exact (IsWheel_disj_ext hw).2
    · exact hw.disj.2.2.2
  rw [card_insert_eq_ite , if_neg w2_not_mem , add_assoc (card (s ∪ t)) 1 , one_add_one_eq_two]
  rw [add_assoc (card (s ∪ t)) 2 , two_add_one_eq_three , ← add_assoc ,add_comm (card (s ∩ t)), card_union_add_card_inter]
  have card_s_t : card s = r ∧ card t = r := by
    constructor
    · have : card (insert v s) = r + 1 := by
        exact hw.cliques.1.card_eq
      rw [card_insert_eq_ite , if_neg hw.disj.1 , Nat.add_right_cancel_iff ] at this
      exact this
    · have : card (insert v t) = r + 1 := by
        exact hw.cliques.2.2.1.card_eq
      rw [card_insert_eq_ite , if_neg hw.disj.2.1 , Nat.add_right_cancel_iff ] at this
      exact this
  rw [card_s_t.1 , card_s_t.2 ,Nat.add_right_cancel_iff]
  exact Eq.symm (Nat.two_mul r)

/-- vertices of P3 are in W -/
lemma mem_wheelVerts_P3 (hw: G.IsWheel r v w₁ w₂ s t) : v ∈ wheelVerts hw ∧ w₁ ∈ wheelVerts hw ∧ w₂ ∈ wheelVerts hw:=
by
  rw [wheelVerts]
  refine ⟨?_,?_,?_⟩  
  · rw [mem_insert] ; left ; rfl
  · rw [mem_insert] ; right ; rw [mem_insert] ; left ; rfl
  · rw [mem_insert] ; right ; rw [mem_insert] ; right ; rw [mem_insert] ; left ; rfl
  
/-- we can swap the labels of w₁ ↔ w₂ and s ↔ t -/
lemma IsWheel_comm : G.IsWheel r v w₁ w₂ s t ↔ G.IsWheel r v w₂ w₁ t s:=
by
  constructor 
  all_goals intro wheel
  all_goals refine {P3 :=  ?_ , disj :=  ?_ , cliques := ?_}
  · exact (P3bar.comm wheel.P3).1 wheel.P3
  · exact ⟨ wheel.disj.2.1 ,wheel.disj.1 , wheel.disj.2.2.2 , wheel.disj.2.2.1⟩   
  · exact ⟨wheel.cliques.2.2.1 , wheel.cliques.2.2.2 , wheel.cliques.1 ,wheel.cliques.2.1 ⟩
  · exact (P3bar.comm wheel.P3).1 wheel.P3
  · exact ⟨ wheel.disj.2.1 ,wheel.disj.1 , wheel.disj.2.2.2 , wheel.disj.2.2.1⟩   
  · exact ⟨wheel.cliques.2.2.1 , wheel.cliques.2.2.2 , wheel.cliques.1 ,wheel.cliques.2.1 ⟩

/-- If G contains a P3bar and is maximal K_r+2 -free then we have a wheel like graph -/
lemma exists_IsWheel (h: G.MaxCliqueFree (r+2)) (h3: G.P3bar v w₁ w₂) :
∃ (s t: Finset α), G.IsWheel r v w₁ w₂ s t :=
by
  rcases non_edge_maxcf h (P3bar.ne h3).1 h3.nonedge.1 with ⟨s , ⟨nvs , ⟨nw1s , ⟨cliquevs , cliquew1s ⟩⟩⟩⟩
  rcases non_edge_maxcf h (P3bar.ne h3).2 h3.nonedge.2 with ⟨t , ⟨nvt , ⟨nw2t , ⟨cliquevt , cliquew2t ⟩⟩⟩⟩
  use s ; use t
  refine {P3 :=  ?_ , disj :=  ?_ , cliques := ?_}
  · exact h3
  · exact ⟨nvs , nvt , nw1s ,nw2t⟩    
  · exact ⟨cliquevs ,cliquew1s,cliquevt,cliquew2t⟩

/-- 
If s ∩ t contains an r-set then together with w₁ and w₂ it contains a copy of K_r+2.
This implies a bound on k for any W_r,k in a K_r+2 - free graph -/
lemma card_of_IsWheel_cf (h : G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) : card (s ∩ t) < r:=
by
  by_contra H
  push_neg at H
  apply h (insert w₂ (insert w₁ (s ∩ t)))
  refine {clique := ?_ , card_eq := ?_}
  intro x xmem y ymem xney
  rw [mem_coe , mem_insert , mem_insert] at xmem
  rw [mem_coe , mem_insert , mem_insert] at ymem
  rcases xmem with xw₂ | (xw₁ | xinter)
  rcases ymem with yw₂ | (yw₁ | yinter)
  · rw [← yw₂] at xw₂ ; contradiction
  · rw [xw₂ , yw₁] ; exact Adj.symm hw.P3.edge
  · rw [mem_inter] at yinter ; apply hw.cliques.2.2.2.clique
    · rw [mem_coe , mem_insert] ; left ; exact xw₂
    · rw [mem_coe , mem_insert] ; right ; exact yinter.2
    · exact xney  
  rcases ymem with yw₂ | (yw₁ | yinter)
  · rw [yw₂ , xw₁] ; exact hw.P3.edge
  · rw [← yw₁] at xw₁ ; contradiction
  · rw [mem_inter] at yinter ; apply hw.cliques.2.1.clique
    · rw [mem_coe , mem_insert] ; left ; exact xw₁
    · rw [mem_coe , mem_insert] ; right ; exact yinter.1
    · exact xney  
  rcases ymem with yw₂ | (yw₁ | yinter)
  · rw [mem_inter] at xinter ; apply hw.cliques.2.2.2.clique
    · rw [mem_coe , mem_insert] ; right ; exact xinter.2
    · rw [mem_coe , mem_insert] ; left ; exact yw₂
    · exact xney  
  · rw [mem_inter] at xinter ; apply hw.cliques.2.1.clique
    · rw [mem_coe , mem_insert] ; right ; exact xinter.1
    · rw [mem_coe , mem_insert] ; left ; exact yw₁
    · exact xney  
  · rw [mem_inter] at xinter ; rw [mem_inter] at yinter ; apply hw.cliques.2.1.clique
    · rw [mem_coe , mem_insert] ; right ; exact xinter.1
    · rw [mem_coe , mem_insert] ; right ; exact yinter.1
    · exact xney 
  · have aux : ¬ w₂ ∈ insert w₁ (s ∩ t) := by
      rw [mem_insert] ; push_neg ; constructor
      · symm ; intro weq ; apply SimpleGraph.irrefl G ; rw [weq] at hw ; exact hw.P3.edge
      · rw [mem_inter] ; push_neg ; intro _ ; exact hw.disj.2.2.2
    rw [card_insert_eq_ite , if_neg aux]
    have aux2 : ¬ w₁ ∈ s ∩ t := by
      rw [mem_inter] ; push_neg ; intro _ ; exact (IsWheel_disj_ext hw).1
    rw [card_insert_eq_ite , if_neg aux2 , add_assoc , one_add_one_eq_two , Nat.add_right_cancel_iff]
    have card_s : card s = r := by
      have card_insert_vs : card (insert v s) = r + 1 := by
        exact hw.cliques.1.card_eq
      rw [card_insert_eq_ite , if_neg hw.disj.1 , Nat.add_right_cancel_iff] at card_insert_vs
      exact card_insert_vs
    rw [← card_s ] at H
    have inter_eq_s : s ∩ t = s := by
      exact (subset_iff_eq_of_card_le H).1 (inter_subset_left s t)
    rw [inter_eq_s]
    exact card_s
    
    


/-- Any x ∈ V(G) is not adjacent to at least one vertex in s + w₁ -/
lemma nonadj_w1s (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): ∃ y, y ∈ insert w₁ s ∧ ¬G.Adj x y:=
by
  by_contra contra
  push_neg at contra
  apply h (insert x (insert w₁ s))
  refine {clique := ?_ , card_eq := ?_}
  · have : (insert x (insert w₁ s)).toSet = insert x ((insert w₁ s).toSet) := by
      ext y
      rw [mem_coe , ← mem_insert_coe] 
    rw [this]
    apply isClique_insert_vertex
    · simp only [mem_coe]
      exact contra
    · exact hw.cliques.2.1.clique 
  · have xnin : ¬ x ∈ insert w₁ s := by
      by_contra contra2
      apply SimpleGraph.irrefl
      exact contra x contra2
    rw [card_insert_eq_ite , if_neg xnin]
    rw [hw.cliques.2.1.card_eq , add_assoc, one_add_one_eq_two]


/-- Any x ∈ V(G) is not adjacent to at least one vertex in s + v -/
lemma nonadj_vs (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): ∃ y, y ∈ insert v s ∧ ¬G.Adj x y:=
by
  by_contra contra
  push_neg at contra
  apply h (insert x (insert v s))
  refine {clique := ?_ , card_eq := ?_}
  · have : (insert x (insert v s)).toSet = insert x ((insert v s).toSet) := by
      ext y
      rw [mem_coe , ← mem_insert_coe] 
    rw [this]
    apply isClique_insert_vertex
    · simp only [mem_coe]
      exact contra
    · exact hw.cliques.1.clique 
  · have xnin : ¬ x ∈ insert v s := by
      by_contra contra2
      apply SimpleGraph.irrefl
      exact contra x contra2
    rw [card_insert_eq_ite , if_neg xnin]
    rw [hw.cliques.1.card_eq , add_assoc, one_add_one_eq_two]

/- If x ∈ V(G) there exist a b c d non-neighbours of x such that ... (note a,b,c,d are not necessarily distinct)  -/
lemma nonadj_IsWheel (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): 
∃ a b c d, a ∈ insert w₁ s ∧ ¬G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬G.Adj x b ∧ c ∈ insert v s ∧ ¬G.Adj x c ∧  d ∈ insert v t ∧ ¬G.Adj x d:=
by
  rcases nonadj_w1s h hw x with ⟨a , ha⟩  
  have hw_comm : G.IsWheel r v w₂ w₁ t s := by
    exact IsWheel_comm.1 hw
  have nonadj_w2t : ∃ y, y ∈ insert w₂ t ∧ ¬G.Adj x y := by
    apply nonadj_w1s
    · exact h
    · exact hw_comm
  rcases nonadj_w2t with ⟨b , hb⟩
  rcases nonadj_vs h hw x with ⟨c , hc⟩      
  have nonadj_vt : ∃ y, y ∈ insert v t ∧ ¬G.Adj x y := by
    apply nonadj_vs
    · exact h
    · exact hw_comm
  rcases nonadj_vt with ⟨d , hd⟩
  use a ; use b ; use c ; use d
  refine ⟨ha.1 , ha.2 , hb.1 , hb.2 , hc.1 , hc.2 , hd.1 , hd.2⟩

/-- Useful trivial fact about when |{a,b,c,d}| ≤ 2 given a ≠ b , a ≠ d, b ≠ c  -/

lemma card_eq_two_of_four {a b c d :α} (hab: a ≠ b) (had: a ≠ d) (hbc : b ≠ c) : 
2 ≤ card {a, b, c, d} ∧ (card {a,b,c,d} ≤ 2 → a = c ∧ b = d):=
by
  constructor
  · let f : ℕ → α := fun n => ite (n >= 2) (a) (ite (n = 0) (a) (b))
    have f_inj : ∀ (i : ℕ), i < 2 → ∀ (j : ℕ), j < 2 → f i = f j → i = j := by
      intro i ilt2 j jlt2 fieqfj
      have not_i_ge_2 : ¬ i ≥ 2 := by
        push_neg ; exact ilt2
      have not_j_ge_2 : ¬ j ≥ 2 := by
        push_neg ; exact jlt2 
      dsimp at fieqfj
      rw [if_neg not_j_ge_2 , if_neg not_i_ge_2] at fieqfj
      have two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
        cases m; contradiction
        case succ m =>
          cases m; contradiction
          repeat' apply Nat.succ_le_succ
          apply zero_le
      have lt_two : ∀ m : ℕ , m < 2 → m = 0 ∨ m = 1 := by
        intro m 
        contrapose ; push_neg
        intro mne
        exact two_le mne.1 mne.2    
      rcases lt_two i ilt2 with i0 | i1 
      · rcases lt_two j jlt2 with j0 | j1 
        · rw [i0 , j0]
        · rw [if_pos i0 ] at fieqfj
          have nj0 : ¬ j = 0 := by
            intro j0
            rw [j0] at j1
            contradiction
          rw [if_neg nj0] at fieqfj 
          contradiction
      · rcases lt_two j jlt2 with j0 | j1 
        · have ni0 : ¬ i = 0 := by
            intro i0
            rw [i0] at i1
            contradiction
          rw [if_neg ni0 , if_pos j0] at fieqfj
          symm at fieqfj
          contradiction
        · rw [i1 , j1]
    apply le_card_of_inj_on_range f
    · intro i ilt2 
      have not_i_ge_2 : ¬ i ≥ 2 := by
        push_neg ; exact ilt2
      dsimp
      rw [if_neg not_i_ge_2] 
      split_ifs 
      · exact mem_insert_self a {b, c, d} 
      · rw [mem_insert] ; right ; exact mem_insert_self b {c , d}
    · exact f_inj
  · rw [card_insert_eq_ite]
    split_ifs with h1 
    · rw [card_insert_eq_ite]
      · split_ifs with h3 
        · rw [mem_insert , mem_singleton] at h3
          rw [mem_insert , mem_insert , mem_singleton] at h1  
          intro _
          refine ⟨(h1.resolve_left hab).resolve_right had,h3.resolve_left hbc⟩
        · rw [card_insert_eq_ite]
          split_ifs with h4 
          rw [mem_insert , mem_insert , mem_singleton] at h1  
          · have aeqd : a = d := by
              rw [mem_singleton] at h4
              rw [← h4]
              exact (h1.resolve_left hab).resolve_right had
            contradiction
          · rw [add_assoc , one_add_one_eq_two ]
            intro card_le
            rw [card_singleton , add_comm, two_add_one_eq_three] at card_le
            contradiction
    · rw [card_insert_eq_ite]
      split_ifs with h2
      · rw [card_insert_eq_ite]
        split_ifs with h3
        · have beqc : b = c := by
            rw [mem_singleton] at h3
            rw [mem_insert , mem_singleton] at h2
            rw [h3]
            exact h2.resolve_left hbc
          contradiction
        · intro card_le
          rw [card_singleton , one_add_one_eq_two , two_add_one_eq_three] at card_le
          contradiction
      · rw [card_insert_eq_ite]
        split_ifs
        · intro card_eq
          rw [card_singleton , one_add_one_eq_two , two_add_one_eq_three] at card_eq  
          contradiction
        · intro card_eq
          rw [card_singleton , one_add_one_eq_two , two_add_one_eq_three , three_add_one_eq_four] at card_eq
          contradiction
  
/-- If G is maximally K_r+2-free and contains a P3bar then it certainly contains a Wheel.
Given these two hypotheses we let MaxWheel be the largest |s ∩ t| of any such wheel in G 
(Note: this does not necessarily correspond to the largest wheel in G it is simply the size
of |s ∩ t| for the largest wheel in G using a given copy of P3bar) -/
noncomputable
def MaxWheel (h: G.MaxCliqueFree (r+2)) (h3: G.P3bar v w₁ w₂) : ℕ :=
by
  classical
  let F:= ((range r).filter (fun k => ∃ s t, G.IsWheel r v w₁ w₂ s t ∧ card (s ∩ t) = k)) 
  let s:= (exists_IsWheel h h3).choose
  let t:= (exists_IsWheel h h3).choose_spec.choose
  have ltr: card (s ∩ t) < r:=
    card_of_IsWheel_cf h.1 (exists_IsWheel h h3).choose_spec.choose_spec
  have Fne: F.Nonempty
  · use (card (s ∩ t)); rw [mem_filter,mem_range]
    exact ⟨ltr,s,t,(exists_IsWheel h h3).choose_spec.choose_spec,rfl⟩
  exact F.max' Fne

/-- If we have any wheel in G using the same P3bar then it cannot be larger than the MaxWheel-/
lemma le_MaxWheel (h: G.MaxCliqueFree (r+2))(p3: G.P3bar v w₁ w₂) (hw: G.IsWheel r v w₁ w₂ s' t') :
card (s' ∩ t') ≤ MaxWheel h p3:=
by
  classical
  rw [MaxWheel]
  simp only [mem_range, not_exists, not_and]
  apply le_max'
  rw [mem_filter]
  constructor
  · rw [mem_range]
    exact card_of_IsWheel_cf h.1 hw
  · use s' ; use t'

/-- Since G is maximally K_r+2-free and contains P3bar it must contain a wheel using P3bar
and since any wheel has size at most r there must exist a wheel of size exactly MaxWheel-/
lemma exists_MaxWheel (h: G.MaxCliqueFree (r+2)) (p3: G.P3bar v w₁ w₂): 
∃ s t, G.IsWheel r v w₁ w₂ s t ∧ (card (s ∩ t)) = MaxWheel h p3:=
by
  classical
  rw [MaxWheel]
  simp only [mem_range, not_exists, not_and]
  let F:= ((range r).filter (fun k => ∃ s t, G.IsWheel r v w₁ w₂ s t ∧ card (s ∩ t) = k)) 
  let s:= (exists_IsWheel h p3).choose
  let t:= (exists_IsWheel h p3).choose_spec.choose
  have ltr: card (s ∩ t) < r:=
    card_of_IsWheel_cf h.1 (exists_IsWheel h p3).choose_spec.choose_spec
  have Fne: F.Nonempty
  · use (card (s ∩ t)); rw [mem_filter,mem_range]
    exact ⟨ltr,s,t,(exists_IsWheel h p3).choose_spec.choose_spec,rfl⟩
  have max_F : max' F Fne ∈ F := by
    exact max'_mem F Fne
  dsimp at max_F
  rw [mem_filter] at max_F
  rcases max_F.2 with ⟨s_max , t_max , ⟨ WheelMax , card_inter⟩ ⟩ 
  use s_max ; use t_max  

/- Need Fintype α + DecidableRel G.Adj to form WheelCore : Finset α -/
variable [Fintype α] [DecidableRel G.Adj]

/-- The core nbhd of a Wheel is the set of vertices in α that are adjacent to all vertices in s ∩ t 
Note this can be all vertices (for example if s ∩ t = ∅ )-/
@[reducible]
def WheelCore (_hw : G.IsWheel r v w₁ w₂ s t) : Finset α := 
(univ : Finset α).filter (fun x => ∀ y, y ∈ s ∩ t → G.Adj x y)

/-- if x is in the core then it adjacent to every y ∈ s ∩ t -/
lemma mem_WheelCore {hw : G.IsWheel r v w₁ w₂ s t} (hx: x ∈ G.WheelCore hw) {y : α} (hy: y ∈ s ∩ t): G.Adj x y:=
by
  rw [WheelCore , mem_filter] at hx
  exact hx.2 y hy

/--  x is in the core iff it adjacent to every y ∈ s ∩ t -/
lemma mem_WheelCore_iff {hw : G.IsWheel r v w₁ w₂ s t} : x ∈ G.WheelCore hw ↔ ∀ y, y ∈ s ∩ t → G.Adj x y:=
by
  rw [WheelCore , mem_filter]
  constructor
  · intro H
    exact H.2
  · intro H
    refine ⟨by exact mem_univ x, H⟩
  
/-- If s ∩ t is empty then the core is the whole vertex set -/
lemma WheelCoreUniv (hw: G.IsWheel r v w₁ w₂ s t) (hem: s ∩ t = ∅ ) : ∀ x, x ∈ WheelCore hw :=
by
  intro x
  rw [WheelCore , mem_filter]
  constructor
  · exact mem_univ x 
  · intro y ymem ; rw [hem] at ymem ; exfalso ; exact not_mem_empty y ymem

/--This is a warmup for the next lemma `BiggerWheel` where we use it with `card_eq_two_of_four` to help build a
bigger wheel -/ 
lemma nonadj_core_IsWheel (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hWc: x ∈ G.WheelCore hw ): 
∃ a b c d , a ∈ insert w₁ s ∧ ¬G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬G.Adj x b ∧ c ∈ insert v s ∧ ¬G.Adj x c ∧  d ∈ insert v t ∧ ¬G.Adj x d
∧ ( a ≠ b ) ∧ (a ≠ d) ∧ ( b ≠ c ) ∧ (a ∉ t) ∧ (b ∉ s):=
by
  rcases nonadj_IsWheel h hw x with ⟨a , b , c , d , ⟨amem , naadj , bmem , bnadj , cmem , cnadj , dmem , dnadj⟩⟩  
  use a ; use b ; use c ; use d
  refine ⟨amem , naadj, bmem , bnadj , cmem , cnadj , dmem , dnadj , ?_ , ?_ , ?_ , ?_ ⟩
  rw [mem_insert] at amem
  rw [mem_insert] at bmem
  · rcases amem with ax₁ | as
    · rcases bmem with bx₂ | bt
      · rw [ax₁ , bx₂]
        intro eq
        apply SimpleGraph.irrefl
        have adjw₁ : G.Adj w₁ w₁ := by
          nth_rw 2 [eq] 
          exact hw.P3.edge
        exact adjw₁
      · have anint : ¬ a ∈ t := by
          rw [ax₁] ; exact (IsWheel_disj_ext hw).1
        exact Ne.symm (ne_of_mem_of_not_mem bt anint)
    · rcases bmem with bx₂ | bt
      · have bnint : ¬ b ∈ s := by
          rw [bx₂] ; exact (IsWheel_disj_ext hw).2
        exact ne_of_mem_of_not_mem as bnint
      · intro aeqb
        · rw [aeqb] at as
          apply bnadj
          have bmeminter : b ∈ s ∩ t := by
            rw [mem_inter] ; exact ⟨as , bt⟩
          rw [WheelCore , mem_filter] at hWc ; exact hWc.2 b bmeminter
  rw [mem_insert] at amem
  rw [mem_insert] at dmem
  · rcases amem with ax₁ | as
    · rcases dmem with dx₂ | dt
      · rw [ax₁ , dx₂]
        symm
        exact (P3bar.ne hw.P3).1
      · have anint : ¬ a ∈ t := by
          rw [ax₁] ; exact (IsWheel_disj_ext hw).1
        exact Ne.symm (ne_of_mem_of_not_mem dt anint)
    · rcases dmem with dx₂ | dt
      · have dnins : ¬ d ∈ s := by
          rw [dx₂] ; exact hw.disj.1
        exact ne_of_mem_of_not_mem as dnins
      · intro aeqd
        · rw [aeqd] at as
          apply dnadj
          have dmeminter : d ∈ s ∩ t := by
            rw [mem_inter] ; exact ⟨as , dt⟩
          rw [WheelCore , mem_filter] at hWc ; exact hWc.2 d dmeminter
  rw [mem_insert] at bmem
  rw [mem_insert] at cmem
  · rcases bmem with bx₂ | bt
    · rcases cmem with cx₁ | cs
      · rw [cx₁ , bx₂]
        symm
        exact (P3bar.ne hw.P3).2
      · have bnins : ¬ b ∈ s := by
          rw [bx₂] ; exact (IsWheel_disj_ext hw).2
        exact Ne.symm (ne_of_mem_of_not_mem cs bnins)
    · rcases cmem with cx₁ | cs
      · have cnint : ¬ c ∈ t := by
          rw [cx₁] ; exact hw.disj.2.1
        exact ne_of_mem_of_not_mem bt cnint
      · intro beqc
        · rw [beqc] at bt
          apply cnadj
          have cmeminter : c ∈ s ∩ t := by
            rw [mem_inter] ; exact ⟨cs , bt⟩
          rw [WheelCore , mem_filter] at hWc ; exact hWc.2 c cmeminter
  constructor
  · rw [mem_insert] at amem
    rcases amem with ax₁ | amems
    · rw [ax₁] ; exact (IsWheel_disj_ext hw).1
    · intro amemt 
      have ameminter : a ∈ s ∩ t := by
        rw [mem_inter] ; exact ⟨amems , amemt⟩   
      apply naadj
      rw [WheelCore , mem_filter] at hWc
      exact hWc.2 a ameminter
  · rw [mem_insert] at bmem
    rcases bmem with bx₂ | bmemt
    · rw [bx₂] ; exact (IsWheel_disj_ext hw).2
    · intro bmems 
      have bmeminter : b ∈ s ∩ t := by
        rw [mem_inter] ; exact ⟨bmems , bmemt⟩   
      apply bnadj
      rw [WheelCore , mem_filter] at hWc
      exact hWc.2 b bmeminter
                 
 
/-
If we have a K_r+2-free graph with a wheel W and there is a vertex x that is adjacent to all of the 
common vertices of the cliques that is adjacent to all but two of the vertices in W then we can build
a bigger wheel (where the size of a wheel is the number of common vertices of the cliques)
-/
/-- We can build a wheel with a larger common clique set if there is a core verted that is adjacent to all but
at most 2 of the vertices of the wheel 
-/
lemma BiggerWheel (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hWc: x ∈ G.WheelCore hw) 
(hsmall : card ((G.wheelVerts hw).filter (fun z => ¬ G.Adj  x z)) ≤ 2) :
 ∃ a b, a ∈ s ∧ b ∈ t ∧ a ∉ t ∧ b ∉ s ∧ (G.IsWheel r v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b))) :=
by
  rcases nonadj_core_IsWheel h hw hWc with ⟨a , b , c , d ,⟨amem , naadj , bmem , nbadj , cmem , ncadj , dmem , ndadj, aneb , aned , bnec , anint , bnins⟩⟩
  use a ; use b
  have amemfilter : a ∈ filter (fun z => ¬Adj G x z) (wheelVerts hw) := by
    rw [mem_insert] at amem
    rcases amem with aw₁|as
    · rw [aw₁ , mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert] ; right ; left ; rfl
      · rw [←aw₁] ; exact naadj 
    · rw [mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert , mem_insert ,  mem_union] ; right ; right ; right ; left ; exact as
      · exact naadj  
  have bmemfilter : b ∈ filter (fun z => ¬Adj G x z) (wheelVerts hw) := by
    rw [mem_insert] at bmem
    rcases bmem with bw₂|bt
    · rw [bw₂ , mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert , mem_insert] ; right ; right ; left ; rfl
      · rw [←bw₂] ; exact nbadj 
    · rw [mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert , mem_insert ,  mem_union] ; right ; right ; right ; right ; exact bt
      · exact nbadj  
  have cmemfilter : c ∈ filter (fun z => ¬Adj G x z) (wheelVerts hw) := by
    rw [mem_insert] at cmem
    rcases cmem with cv|cs
    · rw [cv , mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert] ; left ; rfl
      · rw [←cv] ; exact ncadj 
    · rw [mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert , mem_insert ,  mem_union] ; right ; right ; right ; left ; exact cs
      · exact ncadj  
  have dmemfilter : d ∈ filter (fun z => ¬Adj G x z) (wheelVerts hw) := by
    rw [mem_insert] at dmem
    rcases dmem with dv|dt
    · rw [dv , mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert] ; left ; rfl
      · rw [←dv] ; exact ndadj 
    · rw [mem_filter]
      constructor 
      · rw [wheelVerts , mem_insert , mem_insert , mem_insert ,  mem_union] ; right ; right ; right ; right ; exact dt
      · exact ndadj 
  have filter_eq : (filter (fun z => ¬Adj G x z) (wheelVerts hw)) = {a,b,c,d} := by
    have card_abcd : 2 ≤ card {a,b,c,d} := by
      exact (card_eq_two_of_four aneb aned bnec).1
    have card_le_card : card (filter (fun z => ¬Adj G x z) (wheelVerts hw)) ≤ card {a,b,c,d} := by
      exact le_trans hsmall card_abcd
    symm
    apply (subset_iff_eq_of_card_le card_le_card).1
    intro y ymem
    rw [mem_insert , mem_insert , mem_insert , mem_singleton] at ymem
    rcases ymem with ya | (yb | (yc | yd))
    · rw [ya] ; exact amemfilter
    · rw [yb] ; exact bmemfilter
    · rw [yc] ; exact cmemfilter
    · rw [yd] ; exact dmemfilter
  rw [filter_eq] at hsmall
  have ac_bd : a = c ∧ b = d := by
    exact (card_eq_two_of_four aneb aned bnec).2 hsmall
  rw [← ac_bd.1] at cmem
  rw [← ac_bd.2] at dmem
  have ains : a ∈ s 
  · rw [mem_insert] at amem
    rcases amem with aw₁ | as
    · rw [aw₁ , mem_insert] at cmem  
      rcases cmem with w₁v |w₁s 
      · exfalso ; symm at w₁v ; exact (P3bar.ne hw.P3).1 w₁v
      · exfalso ; exact hw.disj.2.2.1 w₁s
    exact as
  have bint : b ∈ t
  · rw [mem_insert] at bmem
    rcases bmem with bw₂ | bt
    · rw [bw₂ , mem_insert] at dmem  
      rcases dmem with w₂v |w₂t
      · exfalso ; symm at w₂v ; exact (P3bar.ne hw.P3).2 w₂v
      · exfalso ; exact hw.disj.2.2.2 w₂t
    exact bt
  refine ⟨?_,?_,?_,?_,?_⟩ 
  · exact ains
  · exact bint  
  · exact anint
  · exact bnins
  have vnex : v ≠ x := by
        intro veqx
        have vnmemabcd : ¬ v ∈ {a ,b,c,d} := by
          intro vmem
          rw [mem_insert ,mem_insert , mem_insert , mem_singleton , ac_bd.1 , ac_bd.2] at vmem  
          rw [← or_assoc , or_self] at vmem
          rcases vmem with vc |vd
          · rw [←ac_bd.1] at vc
            rw [← vc , mem_insert] at amem
            rcases amem with vw₁ |vs
            · exact (P3bar.ne hw.P3).1 vw₁
            · exact hw.disj.1 vs 
          · rw [←ac_bd.2] at vd
            rw [← vd , mem_insert] at bmem
            rcases bmem with vw₂ |vt
            · exact (P3bar.ne hw.P3).2 vw₂
            · exact hw.disj.2.1 vt
        apply vnmemabcd
        rw [← filter_eq , mem_filter]
        constructor   
        · rw [wheelVerts , mem_insert] ; left ; rfl
        · rw [veqx] ; exact SimpleGraph.irrefl G
  have w₁nex : w₁ ≠ x := by
        intro w₁eqx
        have w₁nmemabcd : ¬ w₁ ∈ {a ,b,c,d} := by
          intro w₁mem
          rw [mem_insert ,mem_insert , mem_insert , mem_singleton , ac_bd.1 , ac_bd.2] at w₁mem  
          rw [← or_assoc , or_self] at w₁mem
          rcases w₁mem with w₁c |w₁d
          · rw [←ac_bd.1] at w₁c
            rw [← w₁c , mem_insert] at cmem
            rcases cmem with w₁v |w₁s
            · symm at w₁v ; exact (P3bar.ne hw.P3).1 w₁v
            · exact hw.disj.2.2.1 w₁s
          · rw [←ac_bd.2] at w₁d
            rw [← w₁d , mem_insert] at dmem
            rcases dmem with w₁v |w₁t
            · exact (P3bar.ne hw.P3).1 w₁v.symm
            · exact (IsWheel_disj_ext hw).1 w₁t
        apply w₁nmemabcd
        rw [← filter_eq , mem_filter]
        constructor   
        · rw [wheelVerts , mem_insert , mem_insert] ;right ; left ; rfl
        · rw [w₁eqx] ; exact SimpleGraph.irrefl G
  have w₂nex : w₂ ≠ x := by
        intro w₂eqx
        have w₂nmemabcd : ¬ w₂ ∈ {a ,b,c,d} := by
          intro w₂mem
          rw [mem_insert ,mem_insert , mem_insert , mem_singleton , ac_bd.1 , ac_bd.2] at w₂mem  
          rw [← or_assoc , or_self] at w₂mem
          rcases w₂mem with w₂c |w₂d
          · rw [←ac_bd.1] at w₂c
            rw [← w₂c , mem_insert] at cmem
            rcases cmem with w₂v |w₂s
            · exact (P3bar.ne hw.P3).2 w₂v.symm
            · exact (IsWheel_disj_ext hw).2 w₂s
          · rw [←ac_bd.2] at w₂d
            rw [← w₂d , mem_insert] at dmem
            rcases dmem with w₂v |w₂t
            · exact (P3bar.ne hw.P3).2 w₂v.symm
            · exact hw.disj.2.2.2 w₂t
        apply w₂nmemabcd
        rw [← filter_eq , mem_filter]
        constructor   
        · rw [wheelVerts , mem_insert , mem_insert , mem_insert] ;right ;right ; left ; rfl
        · rw [w₂eqx] ; exact SimpleGraph.irrefl G
  · refine {P3 := ?_ , disj := ?_ , cliques := ?_}
    · exact hw.P3
    · refine ⟨?_,?_,?_,?_⟩
      · rw [mem_insert] ; push_neg ; refine ⟨vnex , by rw [mem_erase] ; push_neg ; intro _ ; exact hw.disj.1⟩
      · rw [mem_insert] ; push_neg ; refine ⟨vnex , by rw [mem_erase] ; push_neg ; intro _ ; exact hw.disj.2.1⟩
      · rw [mem_insert] ; push_neg ; refine ⟨w₁nex , by rw [mem_erase] ; push_neg ; intro _ ; exact hw.disj.2.2.1⟩
      · rw [mem_insert] ; push_neg ; refine ⟨w₂nex , by rw [mem_erase] ; push_neg ; intro _ ; exact hw.disj.2.2.2⟩
    · refine ⟨?_,?_,?_,?_⟩
      · apply clique_iie hw.cliques.1 ains hw.disj.1 vnex
        intro w wmem wnea
        have not_w_in_abcd : ¬ w ∈ {a ,b, c ,d} := by
          rw [mem_insert , mem_insert , mem_insert , mem_singleton ] 
          intro w_ab
          rw [← ac_bd.1 , ← ac_bd.2 ,← or_assoc , or_self ] at w_ab
          rcases w_ab with wa |wb
          · contradiction
          · rw [wb , mem_insert] at wmem
            rcases wmem with bv |bs
            · rw [bv] at bint ; exact hw.disj.2.1 bint
            · contradiction  
        rw [←filter_eq , mem_filter] at not_w_in_abcd ; push_neg at not_w_in_abcd
        apply not_w_in_abcd
        rw [mem_insert] at wmem ; rcases wmem with wv | ws
        · rw [wv] ; exact (mem_wheelVerts_P3 hw).1
        · rw [wheelVerts , mem_insert , mem_insert , mem_insert , mem_union] ; right ;right ; right ;left ;exact ws
      · apply clique_iie hw.cliques.2.1 ains hw.disj.2.2.1 w₁nex
        intro w wmem wnea
        have not_w_in_abcd : ¬ w ∈ {a ,b, c ,d} := by
          rw [mem_insert , mem_insert , mem_insert , mem_singleton ] 
          intro w_ab
          rw [← ac_bd.1 , ← ac_bd.2 ,← or_assoc , or_self ] at w_ab
          rcases w_ab with wa |wb
          · contradiction
          · rw [wb , mem_insert] at wmem
            rcases wmem with bv |bs
            · rw [bv] at bint ; exact (IsWheel_disj_ext hw).1 bint
            · contradiction  
        rw [←filter_eq , mem_filter] at not_w_in_abcd ; push_neg at not_w_in_abcd
        apply not_w_in_abcd
        rw [mem_insert] at wmem ; rcases wmem with wv | ws
        · rw [wv] ; exact (mem_wheelVerts_P3 hw).2.1
        · rw [wheelVerts , mem_insert , mem_insert , mem_insert , mem_union] ; right ;right ; right ;left ;exact ws
      · apply clique_iie hw.cliques.2.2.1 bint hw.disj.2.1 vnex
        intro w wmem wnea
        have not_w_in_abcd : ¬ w ∈ {a ,b, c ,d} := by
          rw [mem_insert , mem_insert , mem_insert , mem_singleton ] 
          intro w_ab
          rw [← ac_bd.1 , ← ac_bd.2 ,← or_assoc , or_self ] at w_ab
          rcases w_ab with wa |wb
          · rw [mem_insert] at wmem 
            rcases wmem with wv |wt
            · rw [wa] at wv ; rw [wv] at ains ; exact hw.disj.1 ains
            · rw [wa] at wt ; contradiction
          · contradiction
        rw [←filter_eq , mem_filter] at not_w_in_abcd ; push_neg at not_w_in_abcd
        apply not_w_in_abcd
        rw [mem_insert] at wmem ; rcases wmem with wv | ws
        · rw [wv] ; exact (mem_wheelVerts_P3 hw).1
        · rw [wheelVerts , mem_insert , mem_insert , mem_insert , mem_union] ; right ;right ; right ;right ;exact ws
      · apply clique_iie hw.cliques.2.2.2 bint hw.disj.2.2.2 w₂nex
        intro w wmem wnea
        have not_w_in_abcd : ¬ w ∈ {a ,b, c ,d} := by
          rw [mem_insert , mem_insert , mem_insert , mem_singleton ] 
          intro w_ab
          rw [← ac_bd.1 , ← ac_bd.2 ,← or_assoc , or_self ] at w_ab
          rcases w_ab with wa |wb
          · rw [mem_insert] at wmem 
            rcases wmem with wv |wt
            · rw [wa] at wv ; rw [wv] at ains ; exact (IsWheel_disj_ext hw).2 ains
            · rw [wa] at wt ; contradiction
          · contradiction
        rw [←filter_eq , mem_filter] at not_w_in_abcd ; push_neg at not_w_in_abcd
        apply not_w_in_abcd
        rw [mem_insert] at wmem ; rcases wmem with wv | ws
        · rw [wv] ; exact (mem_wheelVerts_P3 hw).2.2
        · rw [wheelVerts , mem_insert , mem_insert , mem_insert , mem_union] ; right ;right ; right ;right ;exact ws
      

/-- If we have a BiggerWheel then it is bigger -/
lemma card_BiggerWheel {s t : Finset α} (hab: a ∉ t ∧ b ∉ s) (hx: x ∉ s ∩ t): 
card ((insert x (s.erase a)) ∩ (insert x (t.erase b))) = card (s ∩ t) + 1:=
by 
  apply card_inter

/-- For any vertex x there is a wheelvertex that is not adjacent to x (in fact there is one in s+w₁) -/
lemma degle_noncore  (hcf: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): 
1 ≤ card ((G.wheelVerts hw).filter (fun z => ¬ G.Adj  x z)):=
by
  sorry

/-- If x is not in the core then there is at least one vertex in s ∩ t that is non-adj to x -/
lemma degcore_compl (hcf: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hx: x ∈ (G.WheelCore hw)ᶜ) :
 1 ≤  card ((s∩t).filter (fun z => ¬ G.Adj  x z)) :=
by
  sorry

/-- If G is K_r+2 -free contains a MaxWheel W then every vertex that is adjacent to all of the common
clique vertices is not adjacent to at least 3 vertices in W -/
lemma three_le_wheel_nonadj (hmcf: G.MaxCliqueFree (r+2)) (p3: G.P3bar v w₁ w₂) (hw: G.IsWheel r v w₁ w₂ s t) 
(hsf: card (s ∩ t) = G.MaxWheel hmcf p3) (hWc: x ∈ G.WheelCore hw) :
 3 ≤ card ((G.wheelVerts hw).filter (fun z => ¬ G.Adj  x z)) :=
by
  sorry


