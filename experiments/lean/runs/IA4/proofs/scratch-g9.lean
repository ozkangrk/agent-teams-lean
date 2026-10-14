import FormalConjectures.Arxiv.«2507.17780».«2»
/-! List-based forcing machinery for GP. -/

open SimpleGraph Arxiv.«2507.17780»

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Boolean adjacency table. -/
def adjB : Fin 10 → Fin 10 → Bool := fun u v =>
  match u.val, v.val with
  | 0, 1 => true
  | 0, 4 => true
  | 0, 5 => true
  | 1, 0 => true
  | 1, 2 => true
  | 1, 6 => true
  | 2, 1 => true
  | 2, 3 => true
  | 2, 7 => true
  | 3, 2 => true
  | 3, 4 => true
  | 3, 8 => true
  | 4, 0 => true
  | 4, 3 => true
  | 4, 9 => true
  | 5, 0 => true
  | 5, 7 => true
  | 5, 8 => true
  | 6, 1 => true
  | 6, 8 => true
  | 6, 9 => true
  | 7, 2 => true
  | 7, 5 => true
  | 7, 9 => true
  | 8, 3 => true
  | 8, 5 => true
  | 8, 6 => true
  | 9, 4 => true
  | 9, 6 => true
  | 9, 7 => true
  | _, _ => false

/-- The graph. -/
def GP : SimpleGraph (Fin 10) := SimpleGraph.mk' ⟨adjB, by decide, by decide⟩

instance : DecidableRel GP.Adj := fun u v => by
  dsimp only [GP]
  exact instDecidableEqBool (adjB u v) true

lemma adj_iff {a b : Fin 10} : GP.Adj a b ↔ adjB a b = true := Iff.rfl

/-- Computable replica of `zeroForcingStep` on finsets. -/
def zfStepC (S : Finset (Fin 10)) : Finset (Fin 10) :=
  S ∪ Finset.univ.filter fun w =>
    decide (w ∉ S ∧ ∃ v ∈ S, GP.Adj v w ∧ ∀ u, GP.Adj v u → u ∉ S → u = w)

theorem step_eq (S : Finset (Fin 10)) : zeroForcingStep GP S = zfStepC S := by
  unfold zeroForcingStep zfStepC
  ext w
  simp only [Finset.mem_union, Finset.mem_filter, decide_eq_true_eq]

/-- List version. -/
def stepL (l : List (Fin 10)) : List (Fin 10) :=
  l ++ (List.finRange 10).filter (fun w =>
    !(l.elem w) && (l.any (fun v => adjB v w && (List.finRange 10).all (fun u =>
      !(adjB v u) || l.elem u || (u == w)))))

theorem mem_step_iff {S : Finset (Fin 10)} {l : List (Fin 10)}
    (h : ∀ v, v ∈ S ↔ v ∈ l) (w : Fin 10) :
    w ∈ zfStepC S ↔ w ∈ stepL l := by
  constructor
  · rintro (hS | hF)
    · exact List.mem_append.mpr (Or.inl (h w).mp hS)
    · rw [Finset.mem_filter, decide_eq_true_eq] at hF
      obtain ⟨hw1, v, hv, hAdj, hAll⟩ := hF
      refine List.mem_append.mpr (Or.inr ?_)
      rw [List.mem_filter]
      refine ⟨List.mem_finRange.2 (by omega), ?_⟩
      simp only [Bool.not_eq_true', decide_eq_true_eq, List.mem_elem] at *
      refine ⟨(h w).not.mp hw1, ?_⟩
      rw [List.any_eq_true]
      exact ⟨v, (h v).mp hv, hAdj, ?_⟩
      rw [List.all_eq_true]
      intro u hu
      by_cases hAdj2 : GP.Adj v u
      · have := hAll u hAdj2
        rcases this with hu1 | rfl
        · exact Or.inr (Or.inl ((h u).not.mpr hu1))
        · exact Or.inr (Or.inr (by simpa using congrArg Fin.val rfl) ▸ (by
            simpa [Fin.ext_iff] using rfl))
      · exact Or.inl hAdj2
  · rintro (hS | hF)
    · exact Or.inl ((h w).mpr hS)
    · rw [List.mem_filter] at hF
      obtain ⟨-, hF2⟩ := hF
      simp only [Bool.not_eq_true', decide_eq_true_eq, List.mem_elem] at hF2
      obtain ⟨hw1, hv⟩ := hF2
      rw [List.any_eq_true] at hv
      obtain ⟨v, hv1, hAdj, hAll⟩ := hv
      refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ w, by
        simp only [decide_eq_true_eq]⟩)⟩
      sorry


example : True := trivial
