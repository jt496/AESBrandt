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
  sorry

/-- We automatically have w₁ ∉ t and w₂ ∉ s for any wheel -/
lemma IsWheel_disj_ext (h: G.IsWheel r v w₁ w₂ s t ): w₁ ∉ t ∧ w₂ ∉ s:=
by
  sorry

/-- A wheel consists of the 3 vertices v, w₁, w₂, and the r-sets s , t but the size will vary 
depending on how large |s ∩ t| is, so a useful identity is
#verts in Wheel =  |s ∪ t| + 3 = 2r+3 - |s∩t|, which we express without subtraction -/
lemma card_wheelVerts  (hw: G.IsWheel r v w₁ w₂ s t) : card (wheelVerts hw) + card (s ∩ t) = 2*r+3:=
by
  sorry

/-- vertices of P3 are in W -/
lemma mem_wheelVerts_P3 (hw: G.IsWheel r v w₁ w₂ s t) : v ∈ wheelVerts hw ∧ w₁ ∈ wheelVerts hw ∧ w₂ ∈ wheelVerts hw:=
by
  sorry

/-- we can swap the labels of w₁ ↔ w₂ and s ↔ t -/
lemma IsWheel_comm : G.IsWheel r v w₁ w₂ s t ↔ G.IsWheel r v w₂ w₁ t s:=
by
  sorry

/-- If G contains a P3bar and is maximal K_r+2 -free then we have a wheel like graph -/
lemma exists_IsWheel (h: G.MaxCliqueFree (r+2)) (h3: G.P3bar v w₁ w₂) :
∃ (s t: Finset α), G.IsWheel r v w₁ w₂ s t :=
by
  sorry


/-- 
If s ∩ t contains an r-set then together with w₁ and w₂ it contains a copy of K_r+2.
This implies a bound on k for any W_r,k in a K_r+2 - free graph -/
lemma card_of_IsWheel_cf (h : G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) : card (s ∩ t) < r:=
by
  sorry
