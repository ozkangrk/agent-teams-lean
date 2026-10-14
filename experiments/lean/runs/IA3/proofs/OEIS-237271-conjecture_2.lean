import FormalConjectures.OEIS.«237271»

/-! Swarm proof for OEIS A237271 conjecture_2: a n = num2DenseSublists n.
Key fact: for consecutive divisors d < d' of n, if d' > 2*d then d' is odd
(else d'/2 would be a divisor strictly between).  Hence the two countP
predicates agree pointwise. -/

namespace S237271

open List Finset Nat

theorem countP_eq_of_forall : ∀ {α : Type} (l : List α) (p q : α → Bool),
    (∀ x ∈ l, p x = q x) → l.countP p = l.countP q := by
  intro α l p q h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = q x := h x (List.mem_cons_self ..)
    simp only [List.countP_cons, hx]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

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

theorem no_between : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) → ∀ p : ℕ × ℕ, p ∈ l.zip l.tail →
    ∀ m ∈ l, p.1 < m → m < p.2 → False := by
  intro l
  induction l with
  | nil => intro _ p hp; simp at hp
  | cons x xs ih =>
    intro hl p hp m hm h1 h2
    rcases xs with _ | ⟨y, ys⟩
    · simp at hp
    · have hyy : ∀ a ∈ ys, y ≤ a :=
        (List.pairwise_cons.mp ((List.pairwise_cons.mp hl).2)).1
      have hp' : p ∈ (x, y) :: (y :: ys).zip ys := by simpa [List.zip] using hp
      rcases List.mem_cons.mp hp' with hp2 | hp2
      · subst hp2
        have hm' : m ∈ y :: ys := by
          rcases List.mem_cons.mp hm with rfl | hm
          · omega
          · exact hm
        have hle : y ≤ m := by
          rcases List.mem_cons.mp hm' with rfl | hm''
          · exact le_refl _
          · exact hyy m hm''
        omega
      · refine ih ((List.pairwise_cons.mp hl).2) p hp2 m ?_ h1 h2
        rcases List.mem_cons.mp hm with rfl | hm
        · obtain ⟨hp1, -⟩ := mem_zip_tail _ p hp2
          have hy1 : y ≤ p.1 := by
            rcases List.mem_cons.mp hp1 with rfl | hp1'
            · exact le_refl _
            · exact hyy p.1 hp1'
          have hxy : _ ≤ y := (List.pairwise_cons.mp hl).1 y (by simp)
          omega
        · exact hm

theorem odd_of_adj {n : ℕ} (p : ℕ × ℕ)
    (hp : p ∈ (OeisA237271.sortedDivisorsList n).zip ((OeisA237271.sortedDivisorsList n).tail))
    (hgt : p.2 > 2 * p.1) : Odd p.2 := by
  by_contra hE
  rw [Nat.odd_iff] at hE
  have hmem2 : p.2 ∈ OeisA237271.sortedDivisorsList n := (mem_zip_tail _ p hp).2
  have hd2 : p.2 ∈ Nat.divisors n := (Finset.mem_sort (· ≤ ·)).mp hmem2
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd2
  obtain ⟨m, hpe⟩ : ∃ m, p.2 = 2 * m := ⟨p.2 / 2, by omega⟩
  have hmp2 : m ∣ p.2 := ⟨2, by omega⟩
  have hmd : m ∈ Nat.divisors n := Nat.mem_divisors.mpr ⟨Nat.dvd_trans hmp2 hdvd, hn0⟩
  have hmL : m ∈ OeisA237271.sortedDivisorsList n := (Finset.mem_sort (· ≤ ·)).mpr hmd
  exact no_between _ (Finset.pairwise_sort _ (· ≤ ·)) p hp m hmL (by omega) (by omega)

theorem pred_iff {n : ℕ} (p : ℕ × ℕ)
    (hp : p ∈ (OeisA237271.sortedDivisorsList n).zip ((OeisA237271.sortedDivisorsList n).tail)) :
    (Odd p.2 ∧ p.2 ≥ 2 * p.1) ↔ p.2 > 2 * p.1 := by
  constructor
  · rintro ⟨hodd, hge⟩
    rw [Nat.odd_iff] at hodd
    omega
  · intro hgt
    exact ⟨odd_of_adj p hp hgt, by omega⟩

theorem main (n : ℕ) : OeisA237271.a n = OeisA237271.num2DenseSublists n := by
  have key : List.countP (fun p : ℕ × ℕ => decide (Odd p.2 ∧ p.2 ≥ 2 * p.1))
        ((OeisA237271.sortedDivisorsList n).zip ((OeisA237271.sortedDivisorsList n).tail))
      = List.countP (fun p : ℕ × ℕ => decide (p.2 > 2 * p.1))
        ((OeisA237271.sortedDivisorsList n).zip ((OeisA237271.sortedDivisorsList n).tail)) := by
    refine countP_eq_of_forall _ _ _ ?_
    intro p hp
    by_cases h : Odd p.2 ∧ p.2 ≥ 2 * p.1
    · rw [decide_eq_true h, decide_eq_true ((pred_iff p hp).mp h)]
    · rw [decide_eq_false h, decide_eq_false (mt (pred_iff p hp).mpr h)]
  calc OeisA237271.a n = 1 + List.countP (fun p : ℕ × ℕ => decide (Odd p.2 ∧ p.2 ≥ 2 * p.1))
        ((OeisA237271.sortedDivisorsList n).zip ((OeisA237271.sortedDivisorsList n).tail)) := rfl
    _ = OeisA237271.num2DenseSublists n := by rw [key]; rfl

end S237271

theorem swarm_proof : ∀ (n : ℕ), OeisA237271.a n = OeisA237271.num2DenseSublists n :=
  S237271.main

