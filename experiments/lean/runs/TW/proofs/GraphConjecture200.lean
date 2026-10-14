import FormalConjectures.WrittenOnTheWallII.GraphConjecture200

/-!
# A counterexample to WrittenOnTheWallII.GraphConjecture200

The graph `G200` below is connected, has 11 vertices and 24 edges, and satisfies
`largestInducedTreeSize G200 = ⌈1 + averageIndepNeighbors G200⌉ = 4`, yet it has
three leaves (vertices 0, 3, 9), so it admits no Hamiltonian path. This disproves
the conjecture.
-/

open SimpleGraph WrittenOnTheWallII.GraphConjecture200

set_option maxRecDepth 16000

/-- The edge set of the counterexample graph on `Fin 11`. -/
def G200adjN : Nat → Nat → Bool :=
  fun a b =>
    (a == 0 && b == 1) || (a == 1 && b == 2) || (a == 1 && b == 4) ||
    (a == 1 && b == 5) || (a == 1 && b == 6) || (a == 1 && b == 8) ||
    (a == 1 && b == 10) || (a == 2 && b == 4) || (a == 2 && b == 5) ||
    (a == 2 && b == 6) || (a == 2 && b == 8) || (a == 2 && b == 9) ||
    (a == 2 && b == 10) || (a == 3 && b == 5) || (a == 4 && b == 5) ||
    (a == 4 && b == 6) || (a == 4 && b == 7) || (a == 4 && b == 10) ||
    (a == 5 && b == 6) || (a == 5 && b == 8) || (a == 5 && b == 10) ||
    (a == 6 && b == 8) || (a == 7 && b == 8) || (a == 8 && b == 10)

/-- The counterexample graph: a 7-vertex core (`K 7` minus the two edges `4-8`, `6-10`)
with a path `4-7-8` bridging one missing edge and leaves `0-1`, `3-5`, `9-2`. -/
def G200 : SimpleGraph (Fin 11) where
  Adj u v := G200adjN (min u.val v.val) (max u.val v.val)
  symm := ⟨fun (u v : Fin 11)
      (h : G200adjN (min u.val v.val) (max u.val v.val) = true) => by
    show G200adjN (min v.val u.val) (max v.val u.val) = true
    rw [Nat.min_comm, Nat.max_comm]
    exact h⟩
  loopless := ⟨fun (u : Fin 11) h => by
    simp only [Nat.min_self, Nat.max_self, G200adjN, Bool.and_eq_true, beq_iff_eq,
      Bool.or_eq_true] at h
    omega⟩

instance : DecidableRel G200.Adj :=
  fun u v => instDecidableEqBool (G200adjN (min u.val v.val) (max u.val v.val)) true

instance (s : Set (Fin 11)) : DecidableRel ((G200.induce s).Adj) :=
  fun a b => decidable_of_iff (G200.Adj a.val b.val) (by simp)

theorem g200_connected : G200.Connected := by decide

/-- Vertices 0, 3 and 9 are leaves, with unique neighbors 1, 5, 2. -/
theorem g200_leaf0 : ∀ x : Fin 11, G200.Adj 0 x → x = 1 := by decide
theorem g200_leaf3 : ∀ x : Fin 11, G200.Adj 3 x → x = 5 := by decide
theorem g200_leaf9 : ∀ x : Fin 11, G200.Adj 9 x → x = 2 := by decide

/-- A vertex of degree one in a Hamiltonian walk must be an endpoint. -/
theorem leaf_endpoint {a b w w' : Fin 11} (p : G200.Walk a b) (hp : p.IsHamiltonian)
    (ha : w ≠ a) (hb : w ≠ b) (huni : ∀ x : Fin 11, G200.Adj w x → x = w') : False := by
  have hmem : w ∈ p.support := hp.mem_support w
  obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp hmem
  have hl : p.support.length = p.length + 1 := p.length_support
  have hgv : p.getVert i = w := by
    have h1 := p.support_getElem_eq_getVert hi_lt
    rw [hi] at h1
    exact h1.symm
  have hge1 : 1 ≤ i := by
    by_contra h
    push_neg at h
    have h0 : i = 0 := by omega
    rw [h0] at hgv
    rw [p.getVert_zero] at hgv
    exact ha hgv.symm
  have hilt : i < p.length := by
    by_contra h
    push_neg at h
    have hl' : i = p.length := by omega
    rw [hl'] at hgv
    rw [p.getVert_length] at hgv
    exact hb hgv.symm
  have hp1 : G200.Adj (p.getVert (i - 1)) (p.getVert i) := by
    have h' := p.adj_getVert_succ (show i - 1 < p.length by omega)
    rwa [show i - 1 + 1 = i from by omega] at h'
  have hp2 : G200.Adj (p.getVert i) (p.getVert (i + 1)) := p.adj_getVert_succ hilt
  rw [hgv] at hp1 hp2
  have x1 : p.getVert (i - 1) = w' := huni _ hp1.symm
  have x2 : p.getVert (i + 1) = w' := huni _ hp2
  have hnd : p.support.Nodup := hp.isPath.support_nodup
  have e : p.getVert (i - 1) = p.getVert (i + 1) := by rw [x1, x2]
  have e' : p.support[i - 1]'(by omega) = p.support[i + 1]'(by omega) := by
    rw [p.support_getElem_eq_getVert (by omega), p.support_getElem_eq_getVert (by omega)]
    exact e
  have hkey : i - 1 = i + 1 := hnd.getElem_inj_iff.mp e'
  omega

theorem g200_no_hamiltonian {a b : Fin 11} (p : G200.Walk a b) (hp : p.IsHamiltonian) :
    False := by
  have h0 : (0 : Fin 11) = a ∨ (0 : Fin 11) = b := by
    by_contra hc
    push_neg at hc
    exact leaf_endpoint p hp hc.1 hc.2 g200_leaf0
  have h3 : (3 : Fin 11) = a ∨ (3 : Fin 11) = b := by
    by_contra hc
    push_neg at hc
    exact leaf_endpoint p hp hc.1 hc.2 g200_leaf3
  have h9 : (9 : Fin 11) = a ∨ (9 : Fin 11) = b := by
    by_contra hc
    push_neg at hc
    exact leaf_endpoint p hp hc.1 hc.2 g200_leaf9
  rcases h0 with h0 | h0
  · rcases h3 with h3 | h3
    · exact absurd (h0.trans h3.symm) (by decide)
    · rcases h9 with h9 | h9
      · exact absurd (h0.trans h9.symm) (by decide)
      · exact absurd (h3.trans h9.symm) (by decide)
  · rcases h3 with h3 | h3
    · rcases h9 with h9 | h9
      · exact absurd (h3.trans h9.symm) (by decide)
      · exact absurd (h0.trans h9.symm) (by decide)
    · exact absurd (h0.trans h3.symm) (by decide)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
/-- No induced subgraph of `G200` on 5 or more vertices is a tree. -/
theorem g200_no_big_tree : ∀ s : Finset (Fin 11), 5 ≤ s.card →
    ¬ ((G200.induce (s : Set (Fin 11))).edgeFinset.card + 1
        = Fintype.card ↥(s : Set (Fin 11)) ∧
      (G200.induce (s : Set (Fin 11))).Connected) := by decide

theorem g200_tree4 : largestInducedTreeSize G200 = 4 := by
  have hT : (G200.induce (({0, 1, 4, 7} : Finset (Fin 11)) : Set (Fin 11))).IsTree := by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card, ← edgeFinset_card,
      Nat.card_eq_fintype_card]
    decide
  apply le_antisymm
  · unfold largestInducedTreeSize
    refine csSup_le ⟨4, {0, 1, 4, 7}, rfl, hT⟩ ?_
    rintro n ⟨s, rfl, hT'⟩
    by_contra h4
    push_neg at h4
    exact g200_no_big_tree s (by omega) ⟨hT'.card_edgeFinset, hT'.connected⟩
  · have h4 := card_le_largestInducedTreeSize hT
    simpa using h4

theorem g200_sum : ∑ v : Fin 11, indepNeighborsCard G200 v = 24 := by
  unfold indepNeighborsCard
  simp only [indep_num_eq_computable]
  decide

theorem g200_eq : (largestInducedTreeSize G200 : ℝ) = ⌈1 + averageIndepNeighbors G200⌉ := by
  have havg : averageIndepNeighbors G200 = (24 : ℝ) / 11 := by
    unfold averageIndepNeighbors indepNeighbors
    rw [← Nat.cast_sum, g200_sum]
    norm_num
  rw [havg, g200_tree4]
  have hnum : (1 : ℝ) + (24 : ℝ) / 11 = (35 : ℝ) / 11 := by norm_num
  have e1 : ((35 : ℝ) / 11) ≤ 4 := by norm_num
  have e2 : (3 : ℝ) < ((35 : ℝ) / 11) := by norm_num
  have c1 : (⌈((35 : ℝ) / 11)⌉ : ℤ) ≤ 4 := Int.ceil_le.mpr e1
  have c2 : (4 : ℤ) ≤ ⌈((35 : ℝ) / 11)⌉ := by
    by_contra hcon
    push_neg at hcon
    have h3 : (⌈((35 : ℝ) / 11)⌉ : ℤ) ≤ 3 := by omega
    have hle : ((35 : ℝ) / 11) ≤ 3 := Int.ceil_le.mp h3
    exact absurd hle (by rw [not_le]; exact e2)
  have hceil : (⌈((35 : ℝ) / 11)⌉ : ℤ) = 4 := by omega
  rw [hnum, hceil]
  push_cast
  norm_num

theorem swarm_proof : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (largestInducedTreeSize G : ℝ) = ⌈1 + averageIndepNeighbors G⌉ →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  constructor
  · intro h
    exact h.elim
  · intro h
    obtain ⟨a, b, p, hp⟩ :=
      h (Fin 11) G200 g200_connected g200_eq
    exact g200_no_hamiltonian p hp
