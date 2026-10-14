import FormalConjectures.OEIS.«237271»

/-! Swarm proof for OEIS A237271 a_odd_prime_pow: a (p^k) = k + 1 for odd prime p.
Sorted divisors of p^k are powers of p; every adjacent pair (p^j, p^j') has
j' >= j + 1, so p^j' >= 3 * p^j > 2 * p^j and is odd. -/

namespace S237271A

open Nat List Finset

theorem mem_zip_tail : ∀ (l : List ℕ) (p : ℕ × ℕ), p ∈ l.zip l.tail → p.1 ∈ l ∧ p.2 ∈ l := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    rcases xs with _ | ⟨y, ys⟩
    · simp at hp
    · have hp' : p ∈ (x, y) :: (y :: ys).zip ys := by simpa [List.zip] using hp
      rcases List.mem_cons.mp hp' with hp2 | hp2
      · subst hp2; exact ⟨by simp, by simp⟩
      · exact ⟨List.mem_cons_of_mem _ (ih p hp2).1, List.mem_cons_of_mem _ (ih p hp2).2⟩

theorem zip_lt : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) → l.Nodup →
    ∀ pr ∈ l.zip l.tail, pr.1 < pr.2 := by
  intro l
  induction l with
  | nil => intro _ _ pr hp; simp at hp
  | cons x xs ih =>
    intro hsort hnodup pr hp
    rcases xs with _ | ⟨y, ys⟩
    · simp at hp
    · have hp' : pr ∈ (x, y) :: (y :: ys).zip ys := by simpa [List.zip] using hp
      have hxy : x ≤ y := (List.pairwise_cons.mp hsort).1 y (by simp)
      have hne : x ≠ y := by
        intro hc
        exact (List.nodup_cons.mp hnodup).1 (hc ▸ by simp)
      rcases List.mem_cons.mp hp' with hp2 | hp2
      · subst hp2; omega
      · exact ih ((List.pairwise_cons.mp hsort).2) ((List.nodup_cons.mp hnodup).2) pr hp2

theorem odd_pow_of_odd {p : ℕ} (ho : Odd p) (j : ℕ) : Odd (p ^ j) := by
  induction j with
  | zero => rw [Nat.pow_zero]; exact ⟨0, by omega⟩
  | succ n ih => rw [pow_succ]; exact Nat.odd_mul.mpr ⟨ih, ho⟩

theorem a_odd_prime_pow_core (p k : ℕ) (hp : p.Prime) (ho : Odd p) :
    OeisA237271.a (p ^ k) = k + 1 := by
  have hp3 : 3 ≤ p := by
    rcases ho with ⟨m, rfl⟩
    have h1 : 1 < 2 * m + 1 := hp.one_lt
    omega
  set L : List ℕ := (Nat.divisors (p ^ k)).sort (· ≤ ·) with hL
  have hsort : L.Pairwise (· ≤ ·) := Finset.pairwise_sort _ (· ≤ ·)
  have hnodup : L.Nodup := Finset.sort_nodup _ _
  have hmemiff : ∀ x : ℕ, x ∈ L ↔ ∃ j, j ≤ k ∧ x = p ^ j := by
    intro x
    rw [hL]
    constructor
    · intro hx
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact (Nat.dvd_prime_pow hp).mp hdvd
    · rintro ⟨j, hj, rfl⟩
      refine (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨?_, by positivity⟩)
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr hj
  have hcard : L.length = k + 1 := by
    rw [hL, Finset.length_sort]
    have hset : Nat.divisors (p ^ k) = Finset.image (fun j => p ^ j) (Finset.range (k + 1)) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · intro hx
        obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hx
        obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
        exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact Nat.mem_divisors.mpr ⟨
          (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr (by omega), by positivity⟩
    rw [hset, Finset.card_image_of_injOn, Finset.card_range]
    intro j _ j' _ h
    exact Nat.pow_right_injective (by omega) h
  -- every adjacent pair is good
  have hgood : ∀ pr ∈ L.zip L.tail, Odd pr.2 ∧ pr.2 ≥ 2 * pr.1 := by
    intro pr hpr
    obtain ⟨h1, h2⟩ := mem_zip_tail L pr hpr
    obtain ⟨j, -, hj⟩ := (hmemiff _).mp h1
    obtain ⟨j', -, hj'⟩ := (hmemiff _).mp h2
    have hlt : pr.1 < pr.2 := zip_lt L hsort hnodup pr hpr
    have hjj : j + 1 ≤ j' := by
      by_contra hc
      push_neg at hc
      have hc2 : j' ≤ j := Nat.le_of_lt_succ hc
      have hle : p ^ j' ≤ p ^ j := Nat.pow_le_pow_right (by omega) hc2
      omega
    rw [hj, hj']
    refine ⟨odd_pow_of_odd ho j', ?_⟩
    have hkey : p ^ (j + 1) ≤ p ^ j' := Nat.pow_le_pow_right (by omega) hjj
    have hsplit : p ^ (j + 1) = p * p ^ j := by rw [pow_succ, Nat.mul_comm]
    have hle2 : 2 * p ^ j ≤ p * p ^ j := Nat.mul_le_mul_right (p ^ j) (show 2 ≤ p by omega)
    have hfin : p ^ j' ≥ 2 * p ^ j := by omega
    exact hfin
  -- count all pairs
  have hcount : (L.zip L.tail).countP (fun pr => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1))
      = (L.zip L.tail).length := by
    refine List.countP_eq_length.mpr fun pr hpr => ?_
    exact decide_eq_true (hgood pr hpr)
  have hlen : (L.zip L.tail).length = k := by
    have h1 : (L.zip L.tail).length = min L.length L.tail.length := List.length_zip
    have ht : L.tail.length = L.length - 1 := by simp
    omega
  -- unfold a and conclude
  have ha : OeisA237271.a (p ^ k) = 1 + (L.zip L.tail).countP
      (fun pr => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)) := rfl
  rw [ha, hcount, hlen]
  omega

end S237271A

theorem swarm_proof (p k : ℕ) (hp : p.Prime) (ho : Odd p) :
    OeisA237271.a (p ^ k) = k + 1 :=
  S237271A.a_odd_prime_pow_core p k hp ho