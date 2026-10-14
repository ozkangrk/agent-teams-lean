import FormalConjectures.Arxiv.«2507.17780».«2»
/-! Scaffold for tx_graffiti_conjecture_2 machinery. -/

open SimpleGraph Arxiv.«2507.17780»

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

/-- Computable replica of `zeroForcingStep`. -/
def zfStepC (S : Finset (Fin 10)) : Finset (Fin 10) :=
  S ∪ Finset.univ.filter fun w =>
    decide (w ∉ S ∧ ∃ v ∈ S, GP.Adj v w ∧ ∀ u, GP.Adj v u → u ∉ S → u = w)

theorem step_eq (S : Finset (Fin 10)) : zeroForcingStep GP S = zfStepC S := by
  unfold zeroForcingStep zfStepC
  ext w
  simp only [Finset.mem_union, Finset.mem_filter, decide_eq_true_eq]

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

def Iₐ : Finset (Fin 10) := {0, 3, 6, 7}

def S₅ : Finset (Fin 10) := {0, 1, 2, 3, 4}

theorem S₅_forces : IsZeroForcingSet GP S₅ := by
  rw [IsZeroForcingSet, closure_eq]
  decide

theorem no_small_forcing :
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 10))), S.card ≤ 4 →
      ¬ IsZeroForcingSet GP S := by
  have hd := of_decide_eq_true (p :=
    ∀ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 10))), S.card ≤ 4 →
      ¬ ((zfStepC)^[10] S = Finset.univ)) (by decide)
  intro S hS hcard hforce
  rw [IsZeroForcingSet, closure_eq] at hforce
  exact hd S hS hcard hforce

theorem znum_ge : 5 ≤ zeroForcingNumber GP := by
  by_contra h
  push_neg at h
  obtain ⟨S, hcard, hforce⟩ : ∃ S : Finset (Fin 10), S.card ≤ 4 ∧ IsZeroForcingSet GP S := by
    have hne : {k | ∃ S : Finset (Fin 10), S.card = k ∧ IsZeroForcingSet GP S}.Nonempty :=
      ⟨5, S₅, by decide, S₅_forces⟩
    obtain ⟨k, S, hk, hforce⟩ := Nat.sInf_mem hne
    exact ⟨S, by omega, hforce⟩
  exact no_small_forcing S (Finset.mem_powerset.mpr (Finset.subset_univ S)) hcard hforce

theorem znum_le : zeroForcingNumber GP ≤ 5 := by
  apply Nat.sInf_le
  exact ⟨5, S₅, by decide, S₅_forces⟩

theorem alpha_le : GP.indepNum ≤ 4 := by
  have hd := of_decide_eq_true (p :=
    ∀ t ∈ Finset.powersetLen 5 (Finset.univ : Finset (Fin 10)), ¬ GP.IsIndepSet t) (by decide)
  apply Nat.sSup_le
  rintro n' ⟨s, hs⟩
  simp only [Set.mem_setOf_eq] at hs
  rw [← hs.card_eq]
  by_contra hscard
  push_neg at hscard
  obtain ⟨t, hts, htcard⟩ := Finset.exists_smaller_set s 5 hscard
  exact hd t (Finset.mem_powersetLen.2 ⟨5, htcard, hts⟩) (hs.isIndepSet.subset hts)

theorem alpha_ge : 4 ≤ GP.indepNum := by
  have hI : GP.IsIndepSet Iₐ := by decide
  apply le_csSup ⟨10, ?_⟩ ⟨4, Iₐ, ⟨hI, by decide⟩⟩
  rintro n' ⟨s, hs⟩
  simp only [Set.mem_setOf_eq] at hs
  rw [← hs.card_eq]
  exact le_trans (Finset.card_le_univ s) (by decide)

theorem G_conn : GP.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  match v with
  | ⟨0, _⟩ => exact ⟨Walk.nil⟩
  | ⟨1, _⟩ => exact ⟨Walk.cons Walk.nil (by decide)⟩
  | ⟨2, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩
  | ⟨3, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩
  | ⟨4, _⟩ => exact ⟨Walk.cons Walk.nil (by decide)⟩
  | ⟨5, _⟩ => exact ⟨Walk.cons Walk.nil (by decide)⟩
  | ⟨6, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩
  | ⟨7, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩
  | ⟨8, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩
  | ⟨9, _⟩ => exact ⟨Walk.cons Walk.cons Walk.nil (by decide) (by decide)⟩

theorem G_deg : GP.maxDegree ≤ 3 := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  match v with
  | ⟨0, _⟩ => decide
  | ⟨1, _⟩ => decide
  | ⟨2, _⟩ => decide
  | ⟨3, _⟩ => decide
  | ⟨4, _⟩ => decide
  | ⟨5, _⟩ => decide
  | ⟨6, _⟩ => decide
  | ⟨7, _⟩ => decide
  | ⟨8, _⟩ => decide
  | ⟨9, _⟩ => decide

theorem znum_eq : zeroForcingNumber GP = 5 := le_antisymm znum_le znum_ge
theorem alpha_eq : GP.indepNum = 4 := le_antisymm alpha_le alpha_ge
