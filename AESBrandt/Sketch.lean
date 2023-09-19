/-
  
  **Sketch of Andrasfai--Erdos--Sos proof due to Brandt in Lean** 

`Chromatic` (results about chromatic numbers) 
no imports

1. If r < χ(G) then G is not r-colorable `not_col_lt_chrom`

2. If χ(G)= r+1 then G is not r-colorable`not_col_chrom_succ`

3. If χ(G) = r and C is an r-coloring of G then `chrom_imp_verts` says that 
for any color i there is a vertex v such that C v = i

4. If χ(G) = r, C is an r-coloring of G and i ≠ j are distinct colors then `chrom_imp_edges`
says that there exist x,y vertices, such that C x = i and C y = j and xy ∈ E(G)


`Clique` (results about cliques) 
no imports

1. If x ≠ y are vertices and xy ∉ E(G) then G < G ⊔ {xy} `lt_of_insert_newedge`

2. If s is a clique, v ∉ s and ∀ x ∈ s, G.Adj x v then (insert s v) is a clique `isClique_insert_vertex`

3. If s is a clique in G ⊔ {xy} but not in G then x ∈ s and y ∈ s `mem_of_new_clique`

4. If s is a clique in G ⊔ {xy} then (erase s x) is a clique in G `clique_erase_insert_edge`

5. If (insert v s)  is an (r+1)-clique in G, a ∈ s , v ∉ s, v ≠ x and ∀ w ∈ (insert v s), w ≠ a → G.Adj x w
then (insert v (insert x (erase s a))) is an (r+1)-clique in G. `clique_iie` 


`Subgraphs` (results about subgraphs and maximal graphs subject to conditions) 
no imports

1.  If G ≤ H then for any vertex x, G.degree x ≤ H.degree x `degree_le` 

2.  If G ≤ H then δ(G) ≤ δ(H) `minDegree_le_of_le`

3. If G is a strict subgraph of H  (G < H) then Hᶜ is a strict subgraph of Gᶜ, `gt_compl_of_lt`

4. If G < H then |E(Hᶜ)| < |E(Gᶜ)|, `wf_edge_compl`

5. If P G holds (where P: SimpleGraph α → Prop) then ∃ H, G ≤ H ∧  P H  ∧ ∀ {K}, H < K →¬ P K 
i.e. if there is a graph G with property P then there is a maximal supergraph of G with this property
  `pred_graph_maximal `

`P3bar` (results about P3bar) 
no imports

0. P3bar is a 3-set with one edge and 2 non-edges 

structure P3bar (v w₁ w₂ : α): Prop where 
  edge : G.Adj w₁ w₂  -- w₁w₂ ∈ E(G) 
  nonedge : ¬G.Adj v w₁ ∧ ¬G.Adj v w₂ -- vw₁, vw₂ ∉ E(G)

1.  (G.P3bar: v w₁ w₂) : v ≠ w₁ ∧ v ≠ w₂  `ne`-- v ≠ w₁ and v ≠ w₂

2. `P3bar_comm` we can swap w₁ and w₂ in the definition of P3bar
 G.P3bar v w₁ w₂ ↔ G.P3bar v w₂ w₁


`MaxCliqueFree` (results about maximally clique free graphs) 
imports `Chromatic, Clique, Subgraphs`

1. MaxCliqueFree defines a graph G to be maximally r-clique-free  if G is r-clique free but if G < H then 
H is not r-cliqueFree `MaxCliqueFree`

2.  If  G.CliqueFree r then ∃ H, G ≤ H ∧ H.MaxCliqueFree r `exists_maxcf_super`

3.  If G.MaxCliqueFree (r+1)), x ≠ y and ¬G.Adj x y then `non_edge_maxcf ` says that
∃ (s:Finset α), x ∉ s ∧ y ∉ s ∧ G.IsNClique r (insert x s) ∧ G.IsNClique r (insert y s) 


`CompleteMultiPartite` (results about complete (r) multi-partite graphs) 
imports `P3bar, MaxCliqueFree`

1. A graph is complete multi partite iff non-adjacency is an equiv rel. Since it
is always reflexive and symmetric this comes down to transitivity:
def `completeMultiPartite` (G : SimpleGraph α) : Prop := Transitive (λ u v ↦ ¬G.Adj u v)

2. If G is not completeMultiPartite then ∃ v w₁ w₂, G.P3bar v w₁ w₂, `P3bar_of_not_completeMultiPartite`

3. If there is no P3bar in G then G is complete multi partite `P3barFree`

4. A graph G is `completeMultiPartiteR` r iff G is complete multi paritite and χ(G)=r

5. If G is complete multipartite then it is complete-χ(G)-partite `complete_chrom_partite`

6.  If G is complete-r-partite and C is an r-coloring of G with C x ≠ C y then xy ∈ E(G) 
    `completeMultiPartiteR_adj_ne_col`

7. If G is complete-r-partite then it is not r-cliquefree `not_cliquefree_of_complete_multi_partite`

`Wheel` (results about wheel like graphs)
imports `P3bar MaxCliqueFree`

1. Definition of a wheel in a graph G: `IsWheel`
structure IsWheel (r : ℕ) (v w₁ w₂ : α) (s t : Finset α) : Prop where
  P3 : G.P3bar v w₁ w₂ -- so w₁w₂ ∈ E(G) but vw₁,vw₂ ∉ E(G) 
  disj : v ∉ s ∧ v ∉ t ∧ w₁ ∉ s ∧ w₂ ∉ t
  cliques : G.IsNClique (r+1) (insert v s) ∧ G.IsNClique (r+1) (insert w₁ s) 
              ∧ G.IsNClique (r+1) (insert v t) ∧ G.IsNClique (r+1) (insert w₂ t)
  
2. The vertices of a wheel are s ∪ t ∪ {v, w₁, w₂}  `wheelVerts` 
  insert v (insert w₁ (insert w₂ (s ∪ t) )))

3.  Helper lemma to prove x ∈ W, `mem_wheelVerts` :
 x ∈ insert w₁ s ∨ x ∈ insert w₂ t ∨ x ∈ insert v s ∨ x ∈ insert v t ↔ x ∈ wheelVerts hw:=

4. We automatically have w₁ ∉ t and w₂ ∉ s for any wheel  `IsWheel_disj_ext` : w₁ ∉ t ∧ w₂ ∉ s

 A wheel consists of the 3 vertices v, w₁, w₂, and the r-sets s , t but the size will vary 
depending on how large |s ∩ t| is, so a useful identity is
#verts in Wheel =  |s ∪ t| + 3 = 2r+3 - |s∩t|, which we express without subtraction 
`card_wheelVerts` : card (wheelVerts hw) + card (s ∩ t) = 2*r+3:=

5. The vertices of the P3bar belong to W: `mem_wheelVerts_P3`
v ∈ wheelVerts hw ∧ w₁ ∈ wheelVerts hw ∧ w₂ ∈ wheelVerts hw:=

6. Given a wheel we can swap the labels of w₁ ↔ w₂ and s ↔ t : `IsWheel_comm`  
G.IsWheel r v w₁ w₂ s t ↔ G.IsWheel r v w₂ w₁ t s

7. If G contains a P3bar and is maximal K_r+2 -free then we have a wheel like graph: `exists_IsWheel`
 (h: G.MaxCliqueFree (r+2)) (h3: G.P3bar v w₁ w₂) : ∃ (s t: Finset α), G.IsWheel r v w₁ w₂ s t 

8. In any wheel we have |s ∩ t| < r : `card_of_IsWheel_cf`
 (h : G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) : card (s ∩ t) < r

9. If x ∈ V(G) then x is not adjacent to at least one vertex in s + w₁ : `nonadj_w1s`
 (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): ∃ y, y ∈ insert w₁ s ∧ ¬G.Adj x y

10. Similarly for s+v: `nonadj_vs`
 (h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): ∃ y, y ∈ insert v s ∧ ¬G.Adj x y

11. If x ∈ V(G) there exist a b c d (not necessarily distinct) such that : `nonadj_IsWheel` 
 a ∈ insert w₁ s ∧ ¬G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬G.Adj x b ∧ c ∈ insert v s ∧ ¬G.Adj x c ∧  d ∈ insert v t ∧ ¬G.Adj x d

12. The core nbhd of a Wheel is the set of vertices in α that are adjacent to all vertices in s ∩ t 
Note this can be all vertices (for example if s ∩ t = ∅ ) 
def `WheelCore` (_hw : G.IsWheel r v w₁ w₂ s t) : Finset α := 
(univ : Finset α).filter (λ x ↦ ∀ y, y ∈ s ∩ t → G.Adj x y)

13. If x ∈ WheelCore and y ∈ s ∩ t then xy ∈ E(G): `mem_WheelCore`

14. x ∈ G.WheelCore hw ↔ ∀ y, y ∈ s ∩ t → G.Adj x y: `mem_WheelCore_iff`

15. If s ∩ t = ∅ then the core is all vertices: `WheelCoreUniv`

16. If a, b, c, d are vertices and a ≠ b, a ≠ d and b ≠ c then: `card_eq_two_of_four`  
2 ≤ |{a,b,c,d}| and |{a,b,c,d}| ≤ 2 → (a = c and b = d) 

17. If x ∈ WheelCore then `nonadj_core_IsWheel` says
(h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hWc: x ∈ G.WheelCore hw ): 
∃ a b c d , a ∈ insert w₁ s ∧ ¬G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬G.Adj x b ∧ c ∈ insert v s ∧ ¬G.Adj x c ∧  
d ∈ insert v t  ∧ ¬G.Adj x d ∧ ( a ≠ b ) ∧ (a ≠ d) ∧ ( b ≠ c ) ∧ (a ∉ t) ∧ (b ∉ s)

18. If G is K_r+2-free with a wheel W and there is a vertex x ∈ WheelCore that is adjacent to all but 
two of the vertices in W then we can build a bigger wheel (where the size of a wheel is the number of common 
vertices of the cliques |s ∩ t|): `BiggerWheel` 
(h: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hWc: x ∈ G.WheelCore hw) 
(hsmall : card ((G.wheelVerts hw).filter (λ z ↦ ¬ G.Adj  x z)) ≤ 2) :
 ∃ a b, a ∈ s ∧ b ∈ t ∧ a ∉ t ∧ b ∉ s ∧ (G.IsWheel r v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)))

19. If we built a bigger wheel then it is indeed bigger: `card_BiggerWheel`
(hab: a ∉ t ∧ b ∉ s) (hx: x ∉ s ∩ t): card ((insert x (s.erase a)) ∩ (insert x (t.erase b))) = card (s ∩ t) + 1

20. If G is maximally K_r+2-free and contains a P3bar then it certainly contains a Wheel.
Given these two hypotheses we let MaxWheel be the largest |s∩ t| of any such wheel in G 
(Note: this does not necessarily correspond to the largest wheel in G it is simply the size
of |s ∩ t| for the largest wheel in G using the given copy of P3bar) 
def MaxWheel (h: G.MaxCliqueFree (r+2)) (h3: G.P3bar v w₁ w₂) : ℕ :=
by
  classical
  let F:= ((range r).filter (λ k ↦ ∃ s t, G.IsWheel r v w₁ w₂ s t ∧ card (s ∩ t) = k)) 
  let s:= (exists_IsWheel h h3).choose
  let t:= (exists_IsWheel h h3).choose_spec.choose
  have ltr: card (s ∩ t) < r:=
    card_of_IsWheel_cf h.1 (exists_IsWheel h h3).choose_spec.choose_spec
  have Fne: F.Nonempty
  · use (card (s ∩ t)); rw [mem_filter,mem_range]
    exact ⟨ltr,s,t,(exists_IsWheel h h3).choose_spec.choose_spec,rfl⟩
  exact F.max' Fne

21.  If we have any wheel in G using the same P3bar then it cannot be larger than the MaxWheel: `le_MaxWheel` 
(h: G.MaxCliqueFree (r+2))(p3: G.P3bar v w₁ w₂) (hw: G.IsWheel r v w₁ w₂ s' t') : card (s' ∩ t') ≤ MaxWheel h p3

22. If G is maximally K_r+2-free and contains a P3bar then there is a wheel of size MaxWheel: `exists_MaxWheel` 
(h: G.MaxCliqueFree (r+2)) (p3: G.P3bar v w₁ w₂): ∃ s t, G.IsWheel r v w₁ w₂ s t ∧ (card (s ∩ t)) = MaxWheel h p3


23. For any vertex x there is a Wheelvertex that is not adjacent to x (in fact there is one in s+w₁)
`degle_noncore`  (hcf: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (x : α): 
1 ≤ card ((G.wheelVerts hw).filter (λ z ↦ ¬ G.Adj  x z))

24.  If x is not in the core then there is at least one vertex in s ∩ t that is non-adj to x:
`degcore_compl` (hcf: G.CliqueFree (r+2)) (hw: G.IsWheel r v w₁ w₂ s t) (hx: x ∈ (G.WheelCore hw)ᶜ) :
 1 ≤  card ((s∩t).filter (λ z ↦ ¬ G.Adj  x z))

25.  If G is K_r+2 -free contains a MaxWheel W then every vertex that is adjacent to all of the common
clique vertices is not adjacent to at least 3 vertices in W: `three_le_wheel_nonadj` 
(hmcf: G.MaxCliqueFree (r+2)) (p3: G.P3bar v w₁ w₂) (hw: G.IsWheel r v w₁ w₂ s t) 
(hsf: card (s ∩ t) = G.MaxWheel hmcf p3) (hWc: x ∈ G.WheelCore hw) :
 3 ≤ card ((G.wheelVerts hw).filter (λ z ↦ ¬ G.Adj  x z))


`AES` (main result)
imports `Wheel CompleteMultiPartite`

1. Basic double counting given a Finset of vertices s we have: `double_counting` 
 ∑ v ∈ V, |Γ(v)∩ s| = ∑ v ∈ s, d(v) 

2. Transform lower bound on non-edges into upper bound on edges: `nonadj_adj`
 (s : Finset α) (hx: i ≤ card (s.filter (λ z ↦ ¬ G.Adj x z))):
card (s.filter (λ z ↦ G.Adj x z)) ≤ s.card - i 

3.  Given lower bounds on degrees from W into X and into α we can bound degrees over W: `deg_bound`
(W X : Finset α) (hx: ∀x, x ∈ X → i  ≤ card (W.filter (λ z ↦ ¬ G.Adj  x z)))
(hy: ∀y, j ≤ card (W.filter (λ z ↦ ¬ G.Adj  y z))):
∑ w in W, G.degree w ≤ (X.card) * (W.card - i) + Xᶜ.card* (W.card - j) 

4. Trivial but tedious bound on fractions:  `abc` 
if a ≤ c then  a*n/(a+b) ≤ c*n/(c+b)

5. Bound used in AES proof: `kr_bound` if k ≤ r then
 (2 * r + 2 + k) * n / (2 * r + 2 + k + 3) ≤  (3 * r + 2) *n / (3 * r + 5)


6.   
 **Andrasfai-Erdos-Sos**   
If G is K_r+2 - free and (3r-1)‖α‖/(3r+2)< δ(G) then G is (r+1)-colorable: `aes_brandt`
(hf: G.CliqueFree (r+2)) (md: (3*r - 1)*‖α‖/(3*r + 2) < G.minDegree) : G.Colorable (r+1)


**Proof of AES**
Let G be K_r+2-free, and take a maximally K_r+2-free supergraph H `exists_maxcf_super`. 
If H is (r+1)-colorable then so is G, `Colorable.mono_left` thus it suffices to show that H is (r+1)-colorable.

If χ(H) ≤ r + 1 then H is (r+1)-colorable so can suppose r + 2 ≤  χ(H)
Since any complete k-partite graph contains K_k `not_cliquefree_of_complete_multi_partite` this implies that 
H is not complete multipartite. 

Hence, using `P3barFree`, we find that H contains a copy of P3bar v w₁ w₂.

Since H is maximally K_r+2-free and contains a P3bar `exists_MaxWheel` implies that H contains a wheel with the
given P3bar and cliques s, t  with |s ∩ t| = MaxWheel (ie of maximum size) 

Let W be the vertices of this wheel and X be its core (the vertices in G adjacent to every vertex in s ∩ t)

By `three_le_wheel_nonadj` any vertex in X has at least 3 non-neighbors in W  `dXle`

By `degle_noncore` any vertex in α has at least 1 non-neighbor in W `dnXle`

So using `deg_bound` we have a bound on the degree sum over W 
  ∑ w in W, degree H w ≤  |X| * (|W| - 3) + |Xᶜ| * (|W| - 1)  `boundW`

By the definition of the core, any vertex in Xᶜ has at least one non-neighbor in s ∩ t `degcore_compl`
So we also have a bound on degree sum over s ∩ t (again using `deg_bound`)
   ∑ w in s ∩ t, degree H w ≤  |Xᶜ| * (|s ∩ t| - 1) + |X| * |s ∩ t| `boundX`

If |s ∩ t| = k then we have |W| + k = 2r + 3 by `card_wheelVerts` and k < r `card_of_IsWheel_cf`

Note that, since G ≤ H `minDegree_le_of_le` implies that
             (3r-1)‖α‖/(3r+2)< δ(H) `mdH`

Using k < r  and `kr_bound` we have (2*r + k)*‖α‖/(2*r+k + 3) ≤ (3*r - 1)*‖α‖/(3*r + 2) `krle`

The remainder of the proof is combining `boundW`, `boundX`, `krle` and `mdH` to show that

      δ(H) ≤  (3r-1)‖α‖/(3r+2) < δ(H), a contradiction.

This in turn follows by noting 3 ≤ |W| (count the vertices in P3bar) and |W| + k = 2r + 3 and considering

δ(H) * (2 * r + k + 3) ≤  ∑ w in W, degree H w +  2*∑ w in s ∩ t, degree H w

                       ≤ ∣X∣ * (∣W∣ - 3) + ∣Xᶜ∣ * (∣W∣ - 1) + 2 * (∣X∣ * k + ∣Xᶜ∣ * (k - 1))

                       ≤ (2 * r + k) * ‖α‖ 


-/