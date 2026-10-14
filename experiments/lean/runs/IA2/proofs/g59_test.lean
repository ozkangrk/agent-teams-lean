import FormalConjectures.WrittenOnTheWallII.GraphConjecture59
open SimpleGraph

abbrev Gc : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4), s(2, 3)}

private lemma connG : Gc.Connected := by decide

private lemma hh1 : havelHakimiStep [3, 3, 3, 3, 2] = [2, 2, 2, 2] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl
private lemma hh2 : havelHakimiStep [2, 2, 2, 2] = [2, 1, 1] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl
private lemma hh3 : havelHakimiStep [2, 1, 1] = [0, 0] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl
private lemma resG : residue Gc = 2 := by
  rw [residue]
  have hm : (Finset.univ.val.map fun v => Gc.degree v)
      = (([3, 3, 3, 3, 2] : List ℕ) : Multiset ℕ) := by decide
  rw [hm, Multiset.coe_sort, List.mergeSort_eq_insertionSort]
  have h0 : List.insertionSort GE.ge [3, 3, 3, 3, 2] = [3, 3, 3, 3, 2] := rfl
  rw [h0]
  rw [SimpleGraph.residueAux.eq_3 3 [3, 3, 3, 2] (by decide), hh1]
  rw [SimpleGraph.residueAux.eq_3 2 [2, 2, 2] (by decide), hh2]
  rw [SimpleGraph.residueAux.eq_3 2 [1, 1] (by decide), hh3]
  rw [SimpleGraph.residueAux.eq_2 [0]]
  rfl

set_option maxRecDepth 100000 in
private lemma bG : b Gc = ((4 : ℕ) : ℝ) := by
  rw [b, largestInducedBipartiteSubgraphSize_eq_computable]
  have hv : Gc.computableLargestInducedBipartiteSubgraphSize = 4 := by decide
  rw [hv]

private lemma fG : Gc.largestInducedForestSize ≤ 3 := by
  have hcover : ∀ t : Finset (Fin 5), 4 ≤ t.card →
      t = {0, 1, 2, 3} ∨ t = {0, 1, 2, 4} ∨ t = {0, 1, 3, 4} ∨ t = {0, 2, 3, 4} ∨ t = {1, 2, 3, 4} ∨ t = {0, 1, 2, 3, 4} := by decide
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro v
    exact absurd v.property (by simp)
  rintro m ⟨s, hsacy, rfl⟩
  by_contra hle
  have hcard : 4 ≤ s.card := by omega
  rcases hcover s hcard with heq | heq | heq | heq | heq | heq
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({0, 1, 2, 3} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(0 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 3} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(3 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 3} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(2 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide) Walk.nil)))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({0, 1, 2, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(0 : Fin 5), by decide⟩ ⟨(4 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(4 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(1 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(2 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide) Walk.nil))))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({0, 1, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(0 : Fin 5), by decide⟩ ⟨(4 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(4 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(1 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(3 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide) Walk.nil))))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({0, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(0 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(3 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(2 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide) Walk.nil)))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(1 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(3 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(2 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide) Walk.nil)))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw
  · subst heq
    have hw : ((Walk.cons (show (Gc.induce (({0, 1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(0 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(3 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide) (Walk.cons (show (Gc.induce (({0, 1, 2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))).Adj ⟨(2 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide) Walk.nil)))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy _ hw

private lemma bridge (R B F : ℕ) (h : (F : ℝ) ^ 2 < (R : ℝ) * (B : ℝ))
    (hg : (⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ : ℝ) ≤ (F : ℝ)) : False := by
  have hz : (F : ℤ) < ⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ := by
    rw [Int.lt_ceil]
    rw [Real.lt_sqrt (by positivity)]
    exact h
  have h1 : (F : ℝ) < (⌈Real.sqrt ((R : ℝ) * (B : ℝ))⌉ : ℝ) := by
    exact_mod_cast hz
  linarith

theorem swarm_proof : type_of% @WrittenOnTheWallII.GraphConjecture59.conjecture59 := by
  refine ⟨?_, ?_⟩
  · intro h; exact h.elim
  · intro h
    have hg : (⌈Real.sqrt ((residue Gc : ℝ) * b Gc)⌉ : ℝ) ≤ (Gc.largestInducedForestSize : ℝ) :=
      h (Fin 5) Gc connG
    rw [resG, bG] at hg
    have hle : (⌈Real.sqrt ((2 : ℝ) * ((4 : ℕ) : ℝ))⌉ : ℝ) ≤ (3 : ℝ) := by
      have hcast : (Gc.largestInducedForestSize : ℝ) ≤ ((3 : ℕ) : ℝ) := by exact_mod_cast fG
      linarith
    exact bridge 2 4 3 (by norm_num) hle
