import FormalConjectures.Arxiv.«2507.17780».«2»
/-! List-based forcing machinery. -/

open SimpleGraph Arxiv.«2507.17780»

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def v0 : Fin 10 := ⟨0, by omega⟩
def v1 : Fin 10 := ⟨1, by omega⟩
def v2 : Fin 10 := ⟨2, by omega⟩
def v3 : Fin 10 := ⟨3, by omega⟩
def v4 : Fin 10 := ⟨4, by omega⟩
def v5 : Fin 10 := ⟨5, by omega⟩
def v6 : Fin 10 := ⟨6, by omega⟩
def v7 : Fin 10 := ⟨7, by omega⟩
def v8 : Fin 10 := ⟨8, by omega⟩
def v9 : Fin 10 := ⟨9, by omega⟩

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

def zfStepC (S : Finset (Fin 10)) : Finset (Fin 10) :=
  S ∪ Finset.univ.filter fun w =>
    decide (w ∉ S ∧ ∃ v ∈ S, GP.Adj v w ∧ ∀ u, GP.Adj v u → u ∉ S → u = w)

theorem step_eq (S : Finset (Fin 10)) : zeroForcingStep GP S = zfStepC S := by
  unfold zeroForcingStep zfStepC
  ext w
  simp only [Finset.mem_union, Finset.mem_filter, decide_eq_true_eq]

def stepL (l : List (Fin 10)) : List (Fin 10) :=
  l ++ (List.finRange 10).filter (fun w =>
    decide (w ∉ l ∧ ∃ v ∈ l, GP.Adj v w ∧ ∀ u, GP.Adj v u → u ∉ l → u = w))

theorem closure_eq (S : Finset (Fin 10)) : zeroForcingClosure GP S = (zfStepC)^[10] S := by
  have key : ∀ (k : ℕ) (T : Finset (Fin 10)), (zeroForcingStep GP)^[k] T = (zfStepC)^[k] T := by
    intro k
    induction k with
    | zero => intro T; rfl
    | succ k ih =>
        intro T
        rw [Function.iterate_succ_apply, step_eq, ih, Function.iterate_succ_apply]
  rw [zeroForcingClosure]
  exact key 10 S

theorem mem_step_iff {S : Finset (Fin 10)} {l : List (Fin 10)}
    (h : ∀ v, v ∈ S ↔ v ∈ l) (w : Fin 10) :
    w ∈ zfStepC S ↔ w ∈ stepL l := by
  simp only [zfStepC, stepL, Finset.mem_union, Finset.mem_filter,
    decide_eq_true_eq, List.mem_append, List.mem_filter]
  constructor
  · rintro (hS | ⟨_, hw1, v, hv, hAdj, hAll⟩)
    · exact Or.inl ((h w).mp hS)
    · refine Or.inr ⟨List.mem_finRange w, ⟨(h w).not.mp hw1, v, (h v).mp hv,
        adj_iff.mp hAdj, fun u hAdj2 huNotl => hAll u hAdj2 ((h u).not.mpr huNotl)⟩⟩
  · rintro (hS | ⟨_, hw1, v, hv1, hAdj, hAll⟩)
    · exact Or.inl ((h w).mpr hS)
    · exact Or.inr ⟨Finset.mem_univ w, ⟨(h w).not.mpr hw1, v, (h v).mpr hv1, hAdj,
        fun u hAdj2 huNotS => hAll u hAdj2 ((h u).not.mp huNotS)⟩⟩

def sortedOf (S : Finset (Fin 10)) : List (Fin 10) :=
  (List.finRange 10).filter (fun v => decide (v ∈ S))

lemma mem_sortedOf {S : Finset (Fin 10)} {v : Fin 10} :
    v ∈ sortedOf S ↔ v ∈ S := by
  rw [sortedOf, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange v, h⟩⟩

@[reducible]
def coversL (l : List (Fin 10)) : Prop := ∀ v : Fin 10, v ∈ (stepL)^[10] l

theorem mem_iter_iff {S : Finset (Fin 10)} {k : ℕ} :
    ∀ w, w ∈ (zfStepC)^[k] S ↔ w ∈ (stepL)^[k] (sortedOf S) := by
  induction k with
  | zero => intro w; exact (mem_sortedOf : w ∈ sortedOf S ↔ w ∈ S).symm
  | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact mem_step_iff (ih) w

def S₅ : Finset (Fin 10) := {0, 1, 2, 3, 4}
def Iₐ : Finset (Fin 10) := {0, 3, 6, 7}

theorem S₅_forces : IsZeroForcingSet GP S₅ := by
  rw [IsZeroForcingSet, closure_eq]
  ext w
  have hdec : coversL (sortedOf S₅) := of_decide_eq_true (p := coversL (sortedOf S₅)) (by decide)
  exact ⟨fun _ => Finset.mem_univ w, fun _ => (mem_iter_iff w).mpr (hdec w)⟩

theorem sortedOf_mem_sublists (S : Finset (Fin 10)) :
    sortedOf S ∈ (List.finRange 10).sublists :=
  List.mem_sublists.2 List.filter_sublist

theorem sortedOf_length (S : Finset (Fin 10)) : (sortedOf S).length = S.card := by
  have hnd : (sortedOf S).Nodup := List.Nodup.filter _ (List.nodup_finRange 10)
  have hts : (sortedOf S).toFinset = S := by
    ext w
    rw [List.mem_toFinset, mem_sortedOf]
  rw [← List.toFinset_card_of_nodup hnd, hts]

theorem no_small_forcing :
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 10))), S.card ≤ 4 →
      ¬ IsZeroForcingSet GP S := by
  have hd : ∀ l ∈ (List.finRange 10).sublists, l.length ≤ 4 → ¬ coversL l := by sorry
  intro S hS hcard hforce
  rw [IsZeroForcingSet, closure_eq] at hforce
  have hcov : coversL (sortedOf S) := by
    intro v
    have h1 := congrArg (fun t => v ∈ t) hforce
    exact (mem_iter_iff v).mp (h1 ▸ Finset.mem_univ v)
  exact hd (sortedOf S) (sortedOf_mem_sublists S) (by rw [sortedOf_length]; exact hcard) hcov

theorem znum_le : zeroForcingNumber GP ≤ 5 := by
  apply Nat.sInf_le
  exact ⟨S₅, by decide, S₅_forces⟩

theorem znum_ge : 5 ≤ zeroForcingNumber GP := by
  by_contra h
  push Not at h
  obtain ⟨S, hcard, hforce⟩ : ∃ S : Finset (Fin 10), S.card ≤ 4 ∧ IsZeroForcingSet GP S := by
    have hne : {k | ∃ S : Finset (Fin 10), S.card = k ∧ IsZeroForcingSet GP S}.Nonempty :=
      ⟨5, S₅, by decide, S₅_forces⟩
    have hs := Nat.sInf_mem hne
    rw [Set.mem_setOf_eq] at hs
    obtain ⟨S, hk, hforce⟩ := hs
    have hk2 : S.card = zeroForcingNumber GP := hk
    exact ⟨S, by omega, hforce⟩
  exact no_small_forcing S (Finset.mem_powerset.2 (Finset.subset_univ S)) hcard hforce

def indepB (l : List (Fin 10)) : Bool :=
  l.all (fun v => l.all (fun w => !(adjB v w) || (v == w)))

theorem alpha_le : GP.indepNum ≤ 4 := by
  have hd : ∀ l ∈ (List.finRange 10).sublists, l.length = 5 → ¬ (indepB l = true) := by sorry
  obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum GP
  rw [isNIndepSet_iff] at hs
  by_contra hgt
  push Not at hgt
  have hscard : 5 ≤ s.card := by omega
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (n := 5) hscard
  have hpair0 := hs.1
  rw [isIndepSet_iff] at hpair0
  have hpair : (↑t : Set (Fin 10)).Pairwise (fun v w => ¬GP.Adj v w) :=
    hpair0.mono (fun x hx => Finset.mem_coe.mpr (hts hx))
  apply hd (sortedOf t) (sortedOf_mem_sublists t) (by rw [sortedOf_length, htcard])
  rw [indepB, List.all_eq_true]
  intro v hv w hw
  by_cases heq : v = w
  · rw [heq]; simp
  · rw [Bool.or_eq_true]
    exact Or.inl (by
      by_cases hb : adjB v w = true
      · exact absurd (adj_iff.mpr hb) (hpair (mem_sortedOf.mp hv) (mem_sortedOf.mp hw) heq)
      · simp [hb])

theorem alpha_ge : 4 ≤ GP.indepNum := by
  have hall : ∀ v w : Fin 10, v ∈ Iₐ → w ∈ Iₐ → adjB v w = false := by decide
  have hIs : GP.IsIndepSet (Iₐ : Finset (Fin 10)) := by
    rw [isIndepSet_iff]
    intro v hv w hw _
    rw [Finset.mem_coe] at hv hw
    exact fun hAdj => Bool.noConfusion ((adj_iff.mp hAdj).trans (hall v hv hw).symm)
  have hle : Iₐ.card ≤ GP.indepNum := hIs.card_le_indepNum
  have hcard : Iₐ.card = 4 := by decide
  omega

theorem G_conn : GP.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨v0, fun v => ?_⟩
  match v with
  | ⟨0, _⟩ => exact ⟨(Walk.nil : GP.Walk v0 v0)⟩
  | ⟨1, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v1 from by decide) Walk.nil) : GP.Walk v0 v1)⟩
  | ⟨2, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v1 from by decide) (Walk.cons (show GP.Adj v1 v2 from by decide) Walk.nil)) : GP.Walk v0 v2)⟩
  | ⟨3, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v4 from by decide) (Walk.cons (show GP.Adj v4 v3 from by decide) Walk.nil)) : GP.Walk v0 v3)⟩
  | ⟨4, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v4 from by decide) Walk.nil) : GP.Walk v0 v4)⟩
  | ⟨5, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v5 from by decide) Walk.nil) : GP.Walk v0 v5)⟩
  | ⟨6, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v1 from by decide) (Walk.cons (show GP.Adj v1 v6 from by decide) Walk.nil)) : GP.Walk v0 v6)⟩
  | ⟨7, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v5 from by decide) (Walk.cons (show GP.Adj v5 v7 from by decide) Walk.nil)) : GP.Walk v0 v7)⟩
  | ⟨8, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v5 from by decide) (Walk.cons (show GP.Adj v5 v8 from by decide) Walk.nil)) : GP.Walk v0 v8)⟩
  | ⟨9, _⟩ => exact ⟨((Walk.cons (show GP.Adj v0 v4 from by decide) (Walk.cons (show GP.Adj v4 v9 from by decide) Walk.nil)) : GP.Walk v0 v9)⟩
