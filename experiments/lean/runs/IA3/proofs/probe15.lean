import Mathlib
open Finset Nat Finsupp
theorem sum_restrict (n m : ℕ) (hm : m ≤ n) : ∑ k ∈ Finset.Icc 1 n, k * (m / k) = ∑ k ∈ Finset.Icc 1 m, k * (m / k) := by
  have hsub : (Finset.Icc 1 m) ⊆ (Finset.Icc 1 n) := by
    intro x hx
    have h := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨h.1, Nat.le_trans h.2 hm⟩
  sorry
theorem gpos (n : ℕ) (m : ℕ) (hm : m ≤ n) (h3 : 3 ≤ m) :
    ∑ k ∈ Finset.Icc 1 n, k * (m / k) + 1 ≤ m * m := by
  rw [sum_restrict n m hm]
  have hset : Finset.Icc 1 m = insert 1 (insert (m-1) (insert m (Finset.Ico 2 (m-1)))) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hset]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega)]
  have hmid : m / (m - 1) * (m - 1) ≤ m := Nat.div_mul_le_self m (m - 1)
  have hcomm : (m - 1) * (m / (m - 1)) = m / (m - 1) * (m - 1) := Nat.mul_comm _ _
  have hmid2 : m / (m - 1) ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ m / (m - 1) := by omega
    have h3' : (m - 1) * 2 ≤ (m - 1) * (m / (m - 1)) := Nat.mul_le_mul_left _ h2
    have h4 : 2 * (m - 1) = (m - 1) + (m - 1) := by ring
    omega
  have h2b : (m - 1) * (m / (m - 1)) ≤ m - 1 :=
    Nat.le_trans (Nat.mul_le_mul_left _ hmid2) (by omega)
  have hb3 : m * (m / m) ≤ m := by
    rw [Nat.div_self (by omega)]
    omega
  have hb1 : 1 * (m / 1) ≤ m := by rw [Nat.div_one]; omega
  have hrest : ∀ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ m := fun k _ => by
    calc k * (m / k) = (m / k) * k := Nat.mul_comm _ _
      _ ≤ m := Nat.div_mul_le_self m k
  have hrestsum : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ m * (m - 3) := by
    have h1 : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ ∑ k ∈ Finset.Ico 2 (m-1), m :=
      Finset.sum_le_sum hrest
    have h2 : ∑ k ∈ Finset.Ico 2 (m-1), m = m * #(Finset.Ico 2 (m-1)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm, Nat.cast_id]
    rw [h2] at h1
    have h3c : #(Finset.Ico 2 (m-1)) = m - 3 := by rw [Nat.card_Ico]; omega
    rw [h3c] at h1
    exact h1
  have hring : m * (m - 3) = m * m - 3 * m := by rw [Nat.mul_sub, Nat.mul_comm m 3]
  have hrestsum' : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ m * m - 3 * m :=
    hrestsum.trans (le_of_eq hring)
  have hm0 : 0 < m := by omega
  trace_state
  sorry

