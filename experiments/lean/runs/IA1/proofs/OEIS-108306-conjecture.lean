
import FormalConjectures.OEIS.«108306»

open OeisA108306

theorem swarm_proof (a_val b_val n : ℕ) :
    invertSeqD a_val b_val n = (genMatrix a_val b_val ^ n) 0 0 := by
  classical
  have hc1 : invertSeqC a_val b_val 1 = 1 := rfl
  have hc2 : ∀ k, invertSeqC a_val b_val (k + 2) = a_val * b_val ^ k := fun k => rfl
  have hMbase : genMatrix a_val b_val ^ 2 + b_val • (1 : Matrix (Fin 2) (Fin 2) ℕ)
      = genMatrix a_val b_val + b_val • genMatrix a_val b_val
        + a_val • (1 : Matrix (Fin 2) (Fin 2) ℕ) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [pow_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, genMatrix]
    all_goals simp
    all_goals try (first | rfl | ring)
  have hMrel : ∀ k : ℕ, genMatrix a_val b_val ^ (k + 2) + b_val • genMatrix a_val b_val ^ k
      = genMatrix a_val b_val ^ (k + 1) + b_val • genMatrix a_val b_val ^ (k + 1)
        + a_val • genMatrix a_val b_val ^ k := by
    intro k
    have h1 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℕ => X * genMatrix a_val b_val ^ k) hMbase
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_mul] at h1
    simp only [smul_mul_assoc, Matrix.one_mul] at h1
    have e2 : genMatrix a_val b_val ^ 2 * genMatrix a_val b_val ^ k
        = genMatrix a_val b_val ^ (k + 2) := by
      rw [show k + 2 = 2 + k from by omega, pow_add]
    have e1 : genMatrix a_val b_val * genMatrix a_val b_val ^ k
        = genMatrix a_val b_val ^ (k + 1) := by
      rw [show k + 1 = 1 + k from by omega, pow_add, pow_one]
    rw [e2, e1] at h1
    exact h1
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℕ, u = fun k => (genMatrix a_val b_val ^ k) 0 0 := ⟨_, rfl⟩
  have hchar : ∀ k, u (k + 2) + b_val * u k
      = u (k + 1) + b_val * u (k + 1) + a_val * u k := by
    intro k
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℕ => X 0 0) (hMrel k)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [hu]
    exact h
  have u0 : u 0 = 1 := by rw [hu]; simp [pow_zero]
  have u1 : u 1 = 1 := by rw [hu]; simp [pow_one, genMatrix]
  have u2 : u 2 = 1 + a_val := by
    have h9 : (genMatrix a_val b_val ^ 2) 0 0 = 1 + a_val := by
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, genMatrix]
    simp only [hu]
    exact h9
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℕ,
      S = fun m => ∑ i ∈ Finset.range m, invertSeqC a_val b_val (m - i) * u i := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℕ,
      T = fun j => ∑ i ∈ Finset.range j, a_val * b_val ^ (j - 1 - i) * u i := ⟨_, rfl⟩
  have hST : ∀ j, S (j + 1) = T j + u j := by
    intro j
    have hterm : ∀ i ∈ Finset.range j,
        invertSeqC a_val b_val (j + 1 - i) * u i = a_val * b_val ^ (j - 1 - i) * u i := by
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      have hexp : j + 1 - i = (j - 1 - i) + 2 := by omega
      rw [hexp, hc2]
    simp only [hSdef, hTdef, Finset.sum_range_succ, Finset.sum_congr rfl hterm,
      Nat.add_sub_cancel_left, hc1, one_mul]
  have hT : ∀ j, T (j + 1) = b_val * T j + a_val * u j := by
    intro j
    have hterm : ∀ i ∈ Finset.range j,
        a_val * b_val ^ (j + 1 - 1 - i) * u i = b_val * (a_val * b_val ^ (j - 1 - i) * u i) := by
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      have hexp : j + 1 - 1 - i = (j - 1 - i) + 1 := by omega
      rw [hexp, pow_succ]; ring
    have hz : j + 1 - 1 - j = 0 := by omega
    simp only [hTdef, Finset.sum_range_succ, Finset.sum_congr rfl hterm,
      ← Finset.mul_sum, hz, pow_zero, mul_one]
  have hS : ∀ m, 1 ≤ m → S m = u m := by
    intro m
    induction m with
    | zero => intro h; exact absurd h (by omega)
    | succ k ih =>
      intro _
      rcases k with _ | k'
      · simp only [hSdef, Finset.sum_range_one, Nat.sub_zero, hc1, one_mul, u0, u1,
          Nat.zero_add]
      · have h1 : S (k' + 2) = T (k' + 1) + u (k' + 1) := hST (k' + 1)
        have h2 : T (k' + 1) = b_val * T k' + a_val * u k' := hT k'
        have h3 : S (k' + 1) = T k' + u k' := hST k'
        have h4 : u (k' + 2) + b_val * u k'
            = u (k' + 1) + b_val * u (k' + 1) + a_val * u k' := hchar k'
        have ih' := ih (show 1 ≤ k' + 1 by omega)
        have h5 : b_val * T k' + b_val * u k' = b_val * u (k' + 1) := by
          have hx := congrArg (b_val * ·) ((h3.symm).trans ih')
          rw [Nat.mul_add] at hx
          exact hx
        show S (k' + 2) = u (k' + 2)
        omega
  have hbetaEq : ∀ m, invertSeqD a_val b_val m
      = if m = 0 then 1 else ∑ i ∈ Finset.range m,
          if h : i < m then invertSeqC a_val b_val (m - i) * invertSeqD a_val b_val i else 0 := by
    intro m
    show Nat.strongRecOn m (fun m ih =>
        if m = 0 then 1 else ∑ i ∈ Finset.range m,
          if h : i < m then invertSeqC a_val b_val (m - i) * ih i h else 0)
      = if m = 0 then 1 else ∑ i ∈ Finset.range m,
          if h : i < m then invertSeqC a_val b_val (m - i) * invertSeqD a_val b_val i else 0
    rw [Nat.strongRecOn.eq_def, WellFounded.fix_eq]
    rfl
  have hD : ∀ m, invertSeqD a_val b_val m = u m := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [hbetaEq, if_pos rfl, u0]
      · rw [hbetaEq, if_neg (show ¬ (m = 0) by omega)]
        have hinner : ∀ i ∈ Finset.range m,
            (if h : i < m then invertSeqC a_val b_val (m - i) * invertSeqD a_val b_val i else 0)
              = invertSeqC a_val b_val (m - i) * u i := by
          intro i hi
          rw [dif_pos (Finset.mem_range.mp hi), ih i (Finset.mem_range.mp hi)]
        rw [Finset.sum_congr rfl hinner]
        have hs := hS m hm
        simp only [hSdef] at hs
        exact hs
  rw [hD n, hu]
