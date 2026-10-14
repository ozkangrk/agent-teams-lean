import FormalConjectures.Arxiv.«2507.17780».«2»
/-! Machinery scaffold. -/

open SimpleGraph Arxiv.«2507.17780»

set_option maxRecDepth 1000000

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

by omega⟩
local instance : Std.Associative (· ||| ·) := ⟨fun x y z => by omega⟩
local instance : Std.IdempotentOp (· ||| ·) := ⟨fun x => by omega⟩

def nbrM : Fin 10 → ℕ := fun v =>
  (List.range 10).foldl (fun acc i => if adjB v ⟨i, by omega⟩ then acc ||| 2 ^ i else acc) 0

def whiteOf (v : Fin 10) (S : ℕ) : ℕ := nbrM v &&& ~~~S

def forcesB (v : Fin 10) (S : ℕ) : Bool :=
  S.testBit v.val && Nat.popcount (whiteOf v S) == 1

def newForced (S : ℕ) : ℕ :=
  (List.finRange 10).foldl (fun acc v => if forcesB v S then acc ||| whiteOf v S else acc) 0

def stepM (S : ℕ) : ℕ := S ||| newForced S

/-- Mask of a finset. -/
def m (S : Finset (Fin 10)) : ℕ := S.fold (· ||| ·) 0 (fun v => 2 ^ v.val)

lemma testBit_two_pow_lt {a i : ℕ} (h : i ≠ a) : (2 ^ a).testBit i = false := by
  rw [Nat.testBit_two_pow]
  omega

lemma testBit_two_pow_eq (a : ℕ) : (2 ^ a).testBit a = true := by
  simp [Nat.testBit_two_pow]

lemma testBit_m_of_lt {S : Finset (Fin 10)} {i : ℕ} (hi : i < 10) :
    (m S).testBit i ↔ (⟨i, hi⟩ : Fin 10) ∈ S := by
  induction S using Finset.induction_on with
  | empty => simp [m]
  | insert a s ha ih =>
      have hbits : ∀ j : ℕ, (2 ^ a.val).testBit j ↔ j = a.val := by
        intro j
        by_cases h : j = a.val <;> simp [h, testBit_two_pow_lt, testBit_two_pow_eq]
      simp only [Finset.fold_insert_idem, Finset.mem_insert]
      rw [Nat.testBit_bor]
      rw [Nat.testBit_congr (by omega)]
      constructor
      · rintro (h | h)
        · exact Or.inr (by simp [Finset.ext_iff, hbits, h] at *)
        · exact Or.inl ih.mpr h
      · rintro (rfl | h)
        · exact Or.inr (hbits i).mpr rfl
        · exact Or.inl ih.mp h

lemma m_lt (S : Finset (Fin 10)) : m S < 1024 := by
  have : ∀ j : ℕ, j > 10 → (m S).testBit j = false := by
    intro j hj
    have := (testBit_m_of_lt (by omega)).not.mpr (by
      intro hc
      have := Finset.mem_univ (⟨j, by omega⟩ : Fin 10)
      exact absurd hc (by simp))
    exact this
  exact Nat.lt_of_testBit_eq_false this (by omega)

lemma popcount_m (S : Finset (Fin 10)) : Nat.popcount (m S) = S.card := by
  sorry

lemma step_bridge (S : Finset (Fin 10)) : m (zfStepC S) = stepM (m S) := by
  sorry

theorem M_all : ∀ mm : ℕ, mm < 1024 → Nat.popcount mm ≤ 4 → (stepM)^[10] mm ≠ 1023 := by
  intro mm hmm hpc
  exact of_decide_eq_true (p := ∀ mm : ℕ, mm < 1024 → Nat.popcount mm ≤ 4 →
      ¬ ((stepM)^[10] mm = 1023)) (by decide) mm hmm hpc
