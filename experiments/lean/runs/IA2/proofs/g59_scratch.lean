import FormalConjectures.WrittenOnTheWallII.GraphConjecture59
open SimpleGraph

abbrev G59 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 4), s(2, 3)
  }

private lemma hh1 : havelHakimiStep [3, 3, 3, 3, 2] = [2, 2, 2, 2] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl
private lemma hh2 : havelHakimiStep [2, 2, 2, 2] = [2, 1, 1] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl
private lemma hh3 : havelHakimiStep [2, 1, 1] = [0, 0] := by
  simp only [havelHakimiStep]; rw [List.mergeSort_eq_insertionSort]; rfl

private lemma resG : residue G59 = 2 := by
  rw [residue]
  have hm : (Finset.univ.val.map fun v => G59.degree v)
      = (([3, 3, 3, 3, 2] : List ℕ) : Multiset ℕ) := by decide
  rw [hm, Multiset.coe_sort, List.mergeSort_eq_insertionSort,
    show [3, 3, 3, 3, 2] = List.insertionSort GE.ge [3, 3, 3, 3, 2] from rfl,
    SimpleGraph.residueAux.eq_3 3 [3, 3, 3, 2] (by decide), hh1,
    SimpleGraph.residueAux.eq_3 2 [2, 2, 2] (by decide), hh2,
    SimpleGraph.residueAux.eq_3 2 [1, 1] (by decide), hh3,
    SimpleGraph.residueAux.eq_2 [0]]
  rfl

set_option maxRecDepth 100000 in
private lemma bG : G59.largestInducedBipartiteSubgraphSize = 4 := by
  rw [largestInducedBipartiteSubgraphSize_eq_computable]
  decide

set_option maxRecDepth 100000 in
private lemma notBip5 : ¬ (G59.induce ((Finset.univ : Finset (Fin 5)) :
    Set (Fin 5))).IsBipartite := by
  rw [induce_isBipartite_iff_exists_coloring]
  rintro ⟨c, hc⟩
  have h1 := hc 0 (by decide) 2 (by decide) (by decide)
  have h2 := hc 2 (by decide) 3 (by decide) (by decide)
  have h3 := hc 3 (by decide) 0 (by decide) (by decide)
  fin_cases c 0 <;> fin_cases c 2 <;> fin_cases c 3 <;> simp_all

private lemma bGle : G59.largestInducedBipartiteSubgraphSize ≤ 4 := by
  rw [largestInducedBipartiteSubgraphSize_eq_computable]
  apply Finset.sup_le
  rintro s ⟨-, ⟨c, hc⟩⟩
  by_contra hle
  have h5 : 5 ≤ s.card := by omega
  have hu : s = Finset.univ := Finset.eq_univ_of_card_eq_n
    (by omega : s.card = Fintype.card (Fin 5))
  subst hu
  exact notBip5 (induce_isBipartite_iff_exists_coloring G59 _).mpr ⟨c, hc⟩

-- concrete cycle lemmas: triangle {0,2,3}
private lemma triNotAcyc : ¬ (G59.induce ({0, 2, 3} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({0, 2, 3} : Set (Fin 5))).Adj
      ⟨(0 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 2, 3} : Set (Fin 5))).Adj
      ⟨(2 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 2, 3} : Set (Fin 5))).Adj
      ⟨(3 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide)
    Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma c4aNotAcyc : ¬ (G59.induce ({0, 1, 2, 4} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({0, 1, 2, 4} : Set (Fin 5))).Adj
      ⟨(0 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 2, 4} : Set (Fin 5))).Adj
      ⟨(2 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 2, 4} : Set (Fin 5))).Adj
      ⟨(1 : Fin 5), by decide⟩ ⟨(4 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 2, 4} : Set (Fin 5))).Adj
      ⟨(4 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide)
    Walk.nil)))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma c4bNotAcyc : ¬ (G59.induce ({0, 1, 3, 4} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({0, 1, 3, 4} : Set (Fin 5))).Adj
      ⟨(0 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 3, 4} : Set (Fin 5))).Adj
      ⟨(3 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 3, 4} : Set (Fin 5))).Adj
      ⟨(1 : Fin 5), by decide⟩ ⟨(4 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 3, 4} : Set (Fin 5))).Adj
      ⟨(4 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide)
    Walk.nil)))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma triNotAcyc0123 : ¬ (G59.induce ({0, 1, 2, 3} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({0, 1, 2, 3} : Set (Fin 5))).Adj
      ⟨(0 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 2, 3} : Set (Fin 5))).Adj
      ⟨(2 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 1, 2, 3} : Set (Fin 5))).Adj
      ⟨(3 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide)
    Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma triNotAcyc1234 : ¬ (G59.induce ({1, 2, 3, 4} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({1, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(1 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({1, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(2 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({1, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(3 : Fin 5), by decide⟩ ⟨(1 : Fin 5), by decide⟩ from by decide)
    Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma triNotAcyc0234 : ¬ (G59.induce ({0, 2, 3, 4} : Set (Fin 5))).IsAcyclic := by
  intro hacy
  have hw : (Walk.cons (show (G59.induce ({0, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(0 : Fin 5), by decide⟩ ⟨(2 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(2 : Fin 5), by decide⟩ ⟨(3 : Fin 5), by decide⟩ from by decide)
    (Walk.cons (show (G59.induce ({0, 2, 3, 4} : Set (Fin 5))).Adj
      ⟨(3 : Fin 5), by decide⟩ ⟨(0 : Fin 5), by decide⟩ from by decide)
    Walk.nil))).IsCycle := by
    rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  exact hacy _ hw

private lemma fG : G59.largestInducedForestSize ≤ 3 := by
  have hcover : ∀ t : Finset (Fin 5), 4 ≤ t.card →
      t = {0, 1, 2, 3} ∨ t = {0, 1, 2, 4} ∨ t = {0, 1, 3, 4} ∨ t = {0, 2, 3, 4} ∨
      t = {1, 2, 3, 4} ∨ t = (Finset.univ : Finset (Fin 5)) := by decide
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro v
    exact absurd v.property (by simp)
  rintro n ⟨s, hsacy, rfl⟩
  by_contra hle
  have h4 : 4 ≤ s.card := by omega
  rcases hcover s h4 with heq | heq | heq | heq | heq | heq
  · subst heq; exact triNotAcyc0123 hsacy
  · subst heq; exact c4aNotAcyc hsacy
  · subst heq; exact c4bNotAcyc hsacy
  · subst heq; exact triNotAcyc0234 hsacy
  · subst heq; exact triNotAcyc1234 hsacy
  · subst heq
    have h0 : (0 : Fin 5) ∈ ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by decide
    have h2 : (2 : Fin 5) ∈ ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by decide
    have h3 : (3 : Fin 5) ∈ ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by decide
    have hw : (Walk.cons (show (G59.induce ((Finset.univ : Finset (Fin 5)) :
        Set (Fin 5))).Adj ⟨(0 : Fin 5), h0⟩ ⟨(2 : Fin 5), h2⟩ from by decide)
      (Walk.cons (show (G59.induce ((Finset.univ : Finset (Fin 5)) :
        Set (Fin 5))).Adj ⟨(2 : Fin 5), h2⟩ ⟨(3 : Fin 5), h3⟩ from by decide)
      (Walk.cons (show (G59.induce ((Finset.univ : Finset (Fin 5)) :
        Set (Fin 5))).Adj ⟨(3 : Fin 5), h3⟩ ⟨(0 : Fin 5), h0⟩ from by decide)
      Walk.nil))).IsCycle := by
      rw [Walk.isCycle_def]; refine ⟨?_, ?_, ?_⟩
      · rw [Walk.isTrail_def]; decide
      · simp
      · decide
    exact hsacy ⟨(0 : Fin 5), h0⟩ _ hw
