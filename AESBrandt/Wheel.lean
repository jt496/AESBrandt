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
    
    

 
      
