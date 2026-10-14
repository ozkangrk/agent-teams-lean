import FormalConjectures.OEIS.«93456»
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Infinite

/-! Helpers -/

private theorem sum_Icc_two (f : ℕ → ℕ) (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    ∑ j ∈ Finset.Icc a c, f j = ∑ j ∈ Finset.Icc a b, f j + ∑ j ∈ Finset.Icc (b+1) c, f j := by
  have hu : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b+1) c := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc a b) (Finset.Icc (b+1) c) :=
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [Finset.mem_Icc] at hx1 hx2
      omega
  rw [hu, Finset.sum_union hdis]

private theorem count_mult (d x y : ℕ) (hd : 0 < d) :
    ((Finset.Icc (x+1) y).filter (fun c => d ∣ c)).card = y / d - x / d := by
  classical
  have hkey : (Finset.Icc (x+1) y).filter (fun c => d ∣ c)
      = (Finset.Icc (x/d+1) (y/d)).image (fun j => j * d) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hc⟩
      have hcm : c = (c/d) * d := (Nat.div_mul_cancel hc).symm
      have hxd : (x/d) * d ≤ x := Nat.div_mul_le_self x d
      have hlt : (x/d) * d < (c/d) * d := by omega
      have hlt2 : x/d < c/d := Nat.lt_of_mul_lt_mul_right hlt
      exact ⟨c/d, ⟨by omega, Nat.div_le_div_right h2⟩, Nat.div_mul_cancel hc⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      have hxle : (x/d) * d ≤ x := Nat.div_mul_le_self x d
      have hmd : x % d + (x/d) * d = x := by rw [Nat.mul_comm (x/d) d]; exact Nat.mod_add_div x d
      have hmlt : x % d < d := Nat.mod_lt x hd
      have hmj : (x/d+1)*d ≤ j*d := Nat.mul_le_mul_right _ hj1
      have hadd : (x/d+1)*d = (x/d)*d + d := by rw [Nat.add_mul, Nat.one_mul]
      have hyle : (y/d)*d ≤ y := Nat.div_mul_le_self y d
      have hyj : j*d ≤ (y/d)*d := Nat.mul_le_mul_right _ hj2
      refine ⟨⟨?_, ?_⟩, j, by ring⟩
      · omega
      · omega
  rw [hkey, Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]
    omega
  · intro j1 _ j2 _ heq
    exact Nat.eq_of_mul_eq_mul_right hd heq

private theorem not_prime_of_two_dvd {k : ℕ} (h2 : (2:ℕ) ∣ k) (hk : 4 ≤ k) : ¬ k.Prime := by
  intro hpr
  have hm : k % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
  have htk : k / 2 ≠ 0 := by omega
  have hkd : k ∣ 2 * (k/2) := ⟨1, by omega⟩
  obtain hdl | hdr := hpr.dvd_mul.mp hkd
  · have := Nat.le_of_dvd (by norm_num : (0:ℕ) < 2) hdl
    omega
  · have := Nat.le_of_dvd (Nat.pos_of_ne_zero htk) hdr
    omega

private theorem row_ne (L R : ℕ) :
    ((Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime)).prod id ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  have hik : id k = k := rfl
  omega

private theorem v2_row (L R : ℕ) (hLR : L ≤ R) (hL4 : 4 ≤ L) :
    (((Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime)).prod id).factorization 2
      = ∑ j ∈ Finset.Icc 1 R, (R / 2^j - (L-1) / 2^j) := by
  have hne : ∀ k ∈ (Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime), id k ≠ 0 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    have hik : id k = k := rfl
    omega
  rw [Nat.factorization_prod_apply hne]
  have hid : ∀ x ∈ (Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime),
      (id x).factorization 2 = x.factorization 2 := fun x _ => rfl
  rw [Finset.sum_congr rfl hid]
  have hcard : ∀ k ∈ (Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime),
      k.factorization 2 = ((Finset.Icc 1 R).filter (fun i => 2^i ∣ k)).card := by
    intro k hk
    have hk0 : k ≠ 0 := hne k hk
    have hkR : k ≤ R := by
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk; exact hk.1.2
    have hk2R : k ≤ 2^R := le_trans hkR (le_of_lt (Nat.lt_pow_self (by norm_num)))
    rw [Nat.factorization_eq_card_pow_dvd k Nat.prime_two,
      Nat.Ico_filter_pow_dvd_eq Nat.prime_two hk0 hk2R]
  rw [Finset.sum_congr rfl fun k hk => hcard k hk]
  have hcs : ∀ k ∈ (Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime),
      ((Finset.Icc 1 R).filter (fun i => 2^i ∣ k)).card
        = ∑ i ∈ Finset.Icc 1 R, (if 2^i ∣ k then (1:ℕ) else 0) := by
    intro k _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun k hk => hcs k hk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  have h2jpos : 0 < 2^j := Nat.two_pow_pos _
  have hsf : ((Finset.Icc L R).filter (fun k => 1 < k ∧ ¬ k.Prime)).filter (fun k => 2^j ∣ k)
      = (Finset.Icc L R).filter (fun k => 2^j ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    by_cases hk2 : 2^j ∣ k
    · have hd2 : (2:ℕ) ∣ 2^j :=
        ⟨2^(j-1), by
          conv_lhs => rw [show j = Nat.succ (j-1) from by omega, Nat.pow_succ']⟩

      have hk2' : (2:ℕ) ∣ k := Nat.dvd_trans hd2 hk2
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, _⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨⟨h1, h2⟩, ⟨by omega, not_prime_of_two_dvd hk2' (by omega : 4 ≤ k)⟩⟩, h3⟩
    · simp [hk2]
  have hcardj : ((Finset.Icc L R).filter (fun k => 2^j ∣ k)).card = R / 2^j - (L-1) / 2^j := by
    have hcm := count_mult (2^j) (L-1) R h2jpos
    rw [show (L-1)+1 = L from by omega] at hcm
    exact hcm
  rw [← hcardj, ← hsf]
  simp only [Finset.card_filter]

private def A9 (m : ℕ) : ℕ := 2^(2*m-1) - 2^(m-1)
private def B9 (m : ℕ) : ℕ := 2^(2*m-1) + 2^(m-1)
private def C9 (m : ℕ) : ℕ := 2^(2*m-1) + 3*2^(m-1) + 1
private def S9 (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (m-1), 2^(m-j)

private theorem div_of_eq (d q n : ℕ) (hd : 0 < d) (h : n = q * d) : n / d = q := by
  rw [h, Nat.mul_comm q d, Nat.mul_div_cancel_left q hd]

theorem swarm_proof : ¬ Set.Finite {n : ℕ | 1 < n ∧ ¬ (OeisA93456.a (n - 1) ∣ OeisA93456.a n)} := by
  intro hf
  have hfam : ∀ m : ℕ, 2 ≤ m → 1 < 2^m + 1 ∧ ¬ (OeisA93456.a (2^m + 1 - 1) ∣ OeisA93456.a (2^m + 1)) := by
    intro m hm
    have hm2 : 2^m = 2 * 2^(m-1) := by
      conv_lhs => rw [show m = (m-1) + 1 from by omega, Nat.pow_succ]
      ring
    have hp2m1 : 2^(2*m-1) = 2^(m-1)*2^m := by
      rw [show 2*m-1 = (m-1)+m from by omega, Nat.pow_add]
    have hp2m : 2^(2*m) = 2 * 2^(2*m-1) := by
      conv_lhs => rw [show 2*m = (2*m-1) + 1 from by omega, Nat.pow_succ]
      ring
    have hp1ge2 : 2 ≤ 2^(m-1) := by
      have := Nat.one_lt_two_pow (by omega : m - 1 ≠ 0)
      omega
    have hpmge4 : 4 ≤ 2^m := by omega
    have hp2m1' : 2^(2*m-1) = 2^m * 2^(m-1) := by rw [hp2m1, Nat.mul_comm]
    have hp4p : 4 * 2^(m-1) ≤ 2^(2*m-1) := by rw [hp2m1']; exact Nat.mul_le_mul_right _ hpmge4
    have hp1m : m ≤ 2^(m-1) := by
      have := Nat.lt_pow_self (by norm_num : (1:ℕ) < 2) (n := m-1)
      omega
    refine ⟨by omega, ?_⟩
    intro hdvd
    rw [show 2^m + 1 - 1 = 2^m from by omega] at hdvd
    -- choose values
    have hc1 : Nat.choose (2^m) 2 = 2^(2*m-1) - 2^(m-1) := by
      rw [Nat.choose_two_right]
      rw [show 2^m * (2^m - 1) = 2^(m-1) * (2^m - 1) * 2 from by rw [hm2]; ring]
      rw [Nat.mul_comm (2^(m-1) * (2^m - 1)) (2:ℕ)]
      rw [Nat.mul_div_cancel_left _ (by omega : (0:ℕ) < 2)]
      rw [hp2m1, Nat.mul_comm]
      rw [Nat.sub_mul, one_mul, Nat.mul_comm (2^(m-1)) (2^m)]
    have hc2 : Nat.choose (2^m + 1) 2 = 2^(2*m-1) + 2^(m-1) := by
      rw [show 2^m + 1 = Nat.succ (2^m) from by omega, Nat.choose_succ_succ, Nat.choose_one_right,
        hc1]
      omega
    have hc3 : Nat.choose (2^m + 2) 2 = 2^(2*m-1) + 3*2^(m-1) + 1 := by
      rw [show 2^m + 2 = Nat.succ (2^m + 1) from by omega, Nat.choose_succ_succ, Nat.choose_one_right,
        hc2]
      omega
    have hrow1 : OeisA93456.a (2^m) =
        ((Finset.Icc (A9 m + 1) (B9 m)).filter fun k => 1 < k ∧ ¬ k.Prime).prod id := by
      simp only [OeisA93456.a]
      rw [hc1, hc2]
      rfl
    have hrow2 : OeisA93456.a (2^m + 1) =
        ((Finset.Icc (B9 m + 1) (C9 m)).filter fun k => 1 < k ∧ ¬ k.Prime).prod id := by
      simp only [OeisA93456.a]
      rw [hc2, hc3]
      rfl
    -- atom equalities
    have hA : A9 m = 2^(2*m-1) - 2^(m-1) := rfl
    have hB : B9 m = 2^(2*m-1) + 2^(m-1) := rfl
    have hC : C9 m = 2^(2*m-1) + 3*2^(m-1) + 1 := rfl
    -- v2 of a(2^m)
    have hv1 : (OeisA93456.a (2^m)).factorization 2 = S9 m + m := by
      rw [hrow1]
      have hL4 : 4 ≤ A9 m + 1 := by omega
      have hLR : A9 m + 1 ≤ B9 m := by omega
      rw [v2_row _ _ hLR hL4]
      rw [show A9 m + 1 - 1 = A9 m from by omega]
      have hBge : 2*m-1 ≤ B9 m := by omega
      have hroom : 2*m - 1 + 2^(m-1) ≤ 2^(2*m-1) := by omega
      have hsub : (Finset.Icc 1 (2*m-1)) ⊆ (Finset.Icc 1 (B9 m)) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      have hzero : ∀ j ∈ Finset.Icc 1 (B9 m), j ∉ Finset.Icc 1 (2*m-1) →
          (B9 m / 2^j - A9 m / 2^j) = 0 := by
        intro j hj1 hj2
        simp only [Finset.mem_Icc] at hj1 hj2
        have h2j : 2^(2*m) ≤ 2^j := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega)
        have hAlt : A9 m < 2^(2*m) := by omega
        have hBlt : B9 m < 2^(2*m) := by omega
        have hA0 : A9 m / 2^j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hAlt h2j)
        have hB0 : B9 m / 2^j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hBlt h2j)
        omega
      rw [← Finset.sum_subset hsub hzero]
      rw [sum_Icc_two _ 1 (m-1) (2*m-1) (by omega) (by omega)]
      -- low part
      have hlow : ∑ j ∈ Finset.Icc 1 (m-1), (B9 m / 2^j - A9 m / 2^j) = S9 m := by
        simp only [S9]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have h2jpos : 0 < 2^j := Nat.two_pow_pos _
        have hjp : 2^j * 2^(m-1-j) = 2^(m-1) := by
          rw [← Nat.pow_add, show j + (m-1-j) = m-1 from by omega]
        have eB : B9 m = (2^(m-1-j)*(2^m+1)) * 2^j := by
          rw [hB, hp2m1, ← hjp]; ring
        have eA : A9 m = (2^(m-1-j)*(2^m-1)) * 2^j := by
          rw [hA, hp2m1, ← hjp]
          have hc1 : 2^j * 2^(m-1-j) * 2^m = 2^(m-1-j) * 2^m * 2^j := by ring
          have hc2 : 2^j * 2^(m-1-j) = 2^(m-1-j) * 2^j := by ring
          have hR : 2^(m-1-j) * (2^m - 1) * 2^j = 2^(m-1-j) * 2^m * 2^j - 2^(m-1-j) * 2^j := by
            rw [Nat.mul_sub, Nat.sub_mul, Nat.mul_one]
          have hle : 2^j * 2^(m-1-j) ≤ 2^j * 2^(m-1-j) * 2^m :=
            Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
          omega
        rw [div_of_eq _ _ _ h2jpos eB, div_of_eq _ _ _ h2jpos eA]
        have hpmj : 2^(m-j) = 2^(m-1-j) * 2 := by
          rw [show m - j = Nat.succ (m-1-j) from by omega, Nat.pow_succ', Nat.mul_comm]
        rw [hpmj]
        have g1 : 2^(m-1-j)*(2^m+1) = 2^(m-1-j)*2^m + 2^(m-1-j) := by ring
        have g2 : 2^(m-1-j)*(2^m-1) + 2^(m-1-j) = 2^(m-1-j)*2^m := by
          rw [Nat.mul_sub, Nat.mul_one,
            Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))]
        omega
      rw [hlow]
      -- high part
      have hhigh : ∑ j ∈ Finset.Icc m (2*m-1), (B9 m / 2^j - A9 m / 2^j) = m := by
        have hc : ∑ j ∈ Finset.Icc m (2*m-1), (B9 m / 2^j - A9 m / 2^j)
            = ∑ j ∈ Finset.Icc m (2*m-1), (1:ℕ) := Finset.sum_congr rfl fun j hj => by
          simp only [Finset.mem_Icc] at hj
          have h2jpos : 0 < 2^j := Nat.two_pow_pos _
          have hjp2 : 2^j * 2^(2*m-1-j) = 2^(2*m-1) := by
            rw [← Nat.pow_add, show j + (2*m-1-j) = 2*m-1 from by omega]
          have hp1lt : 2^(m-1) < 2^j := by
            have h1 := Nat.pow_lt_pow_right (by norm_num : (1:ℕ) < 2) (by omega : m-1 < m)
            have h2 := Nat.pow_le_pow_right (by norm_num : (1:ℕ) ≤ 2) (by omega : m ≤ j)
            omega
          have eB : B9 m = 2^(m-1) + 2^(2*m-1-j) * 2^j := by
            rw [hB, ← hjp2]; ring
          have qB : B9 m / 2^j = 2^(2*m-1-j) := by
            rw [eB, Nat.add_mul_div_right _ _ h2jpos, Nat.div_eq_of_lt hp1lt, zero_add]
          have eA : A9 m = 2^j - 2^(m-1) + (2^(2*m-1-j) - 1) * 2^j := by
            have h1 : A9 m + 2^(m-1) = 2^j * 2^(2*m-1-j) := by
              rw [hA, Nat.sub_add_cancel (by omega), hjp2]
            have h2 : (2^(2*m-1-j) - 1) * 2^j = 2^j * 2^(2*m-1-j) - 2^j := by
              rw [Nat.sub_mul, one_mul, Nat.mul_comm (2^(2*m-1-j)) (2^j)]
            have hge : 2^j ≤ 2^j * 2^(2*m-1-j) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
            rw [h2, ← h1]
            omega
          have qA : A9 m / 2^j = 2^(2*m-1-j) - 1 := by
            rw [eA, Nat.add_mul_div_right _ _ h2jpos,
              Nat.div_eq_of_lt (by omega : 2^j - 2^(m-1) < 2^j), zero_add]
          have hqpos : 1 ≤ 2^(2*m-1-j) := Nat.two_pow_pos _
          omega
        rw [hc, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
        omega
      rw [show m - 1 + 1 = m from by omega, hhigh]
    -- v2 of a(2^m+1)
    have hv2 : (OeisA93456.a (2^m + 1)).factorization 2 = S9 m + 1 := by
      rw [hrow2]
      have hL4 : 4 ≤ B9 m + 1 := by omega
      have hLR : B9 m + 1 ≤ C9 m := by omega
      rw [v2_row _ _ hLR hL4]
      rw [show B9 m + 1 - 1 = B9 m from by omega]
      have hCge : 2*m-1 ≤ C9 m := by
        have := Nat.lt_pow_self (by norm_num : (1:ℕ) < 2) (n := 2*m-1)
        omega
      have hsub : (Finset.Icc 1 (2*m-1)) ⊆ (Finset.Icc 1 (C9 m)) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      have hzero : ∀ j ∈ Finset.Icc 1 (C9 m), j ∉ Finset.Icc 1 (2*m-1) →
          (C9 m / 2^j - B9 m / 2^j) = 0 := by
        intro j hj1 hj2
        simp only [Finset.mem_Icc] at hj1 hj2
        have h2j : 2^(2*m) ≤ 2^j := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega)
        have hClt : C9 m < 2^(2*m) := by omega
        have hBlt : B9 m < 2^(2*m) := by omega
        have hC0 : C9 m / 2^j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hClt h2j)
        have hB0 : B9 m / 2^j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hBlt h2j)
        omega
      rw [← Finset.sum_subset hsub hzero]
      rw [sum_Icc_two _ 1 (m-1) (2*m-1) (by omega) (by omega)]
      -- low part
      have hlow : ∑ j ∈ Finset.Icc 1 (m-1), (C9 m / 2^j - B9 m / 2^j) = S9 m := by
        simp only [S9]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have h2jpos : 0 < 2^j := Nat.two_pow_pos _
        have h1lt : 1 < 2^j := Nat.one_lt_two_pow (by omega)
        have hjp : 2^j * 2^(m-1-j) = 2^(m-1) := by
          rw [← Nat.pow_add, show j + (m-1-j) = m-1 from by omega]
        have eB : B9 m = (2^(m-1-j)*(2^m+1)) * 2^j := by
          rw [hB, hp2m1, ← hjp]; ring
        have eC : C9 m = 1 + (2^(m-1-j)*(2^m+3)) * 2^j := by
          rw [hC, hp2m1, ← hjp]; ring
        have qC : C9 m / 2^j = 2^(m-1-j)*(2^m+3) := by
          rw [eC, Nat.add_mul_div_right _ _ h2jpos, Nat.div_eq_of_lt h1lt, zero_add]
        rw [qC, div_of_eq _ _ _ h2jpos eB]
        have hpmj : 2^(m-j) = 2^(m-1-j) * 2 := by
          rw [show m - j = Nat.succ (m-1-j) from by omega, Nat.pow_succ', Nat.mul_comm]
        rw [hpmj]
        have g1 : 2^(m-1-j)*(2^m+3) = 2^(m-1-j)*2^m + 3*2^(m-1-j) := by ring
        have g2 : 2^(m-1-j)*(2^m+1) = 2^(m-1-j)*2^m + 2^(m-1-j) := by ring
        omega
      rw [hlow]
      -- high part
      have hrest : ∑ j ∈ Finset.Icc (m+1) (2*m-1), (C9 m / 2^j - B9 m / 2^j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have h2jpos : 0 < 2^j := Nat.two_pow_pos _
        have hjp2 : 2^j * 2^(2*m-1-j) = 2^(2*m-1) := by
          rw [← Nat.pow_add, show j + (2*m-1-j) = 2*m-1 from by omega]
        have h4 : 2^(m+1) = 4 * 2^(m-1) := by
          rw [show m+1 = Nat.succ m from rfl, Nat.pow_succ']; omega
        have h2 := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega : m+1 ≤ j)
        have h2j4 : 4 * 2^(m-1) ≤ 2^j := by omega
        have eB : B9 m = 2^(m-1) + 2^(2*m-1-j) * 2^j := by
          rw [hB, ← hjp2]; ring
        have qB : B9 m / 2^j = 2^(2*m-1-j) := by
          rw [eB, Nat.add_mul_div_right _ _ h2jpos,
            Nat.div_eq_of_lt (by omega : 2^(m-1) < 2^j), zero_add]
        have eC : C9 m = (3*2^(m-1)+1) + 2^(2*m-1-j) * 2^j := by
          rw [hC, ← hjp2]; ring
        have qC : C9 m / 2^j = 2^(2*m-1-j) := by
          rw [eC, Nat.add_mul_div_right _ _ h2jpos,
            Nat.div_eq_of_lt (by omega : 3*2^(m-1)+1 < 2^j), zero_add]
        omega
      have hhigh : ∑ j ∈ Finset.Icc m (2*m-1), (C9 m / 2^j - B9 m / 2^j) = 1 := by
        rw [sum_Icc_two _ m m (2*m-1) (by omega) (by omega)]
        rw [Finset.Icc_self, Finset.sum_singleton]
        have hpm2 : 2^m * 2^(m-1) = 2^(2*m-1) := by rw [hp2m1]; ring
        have eCm : C9 m = (2^(m-1) + 1) + (2^(m-1) + 1) * 2^m := by
          rw [hC, ← hpm2]
          have h1 : (2^(m-1) + 1) * 2^m = 2^m * 2^(m-1) + 2^m := by ring
          omega
        have h2mpos : 0 < 2^m := Nat.two_pow_pos _
        have qC : C9 m / 2^m = 2^(m-1) + 1 := by
          rw [eCm, Nat.add_mul_div_right _ _ h2mpos,
            Nat.div_eq_of_lt (by omega : 2^(m-1) + 1 < 2^m), zero_add]
        have eBm : B9 m = 2^(m-1) + 2^(m-1) * 2^m := by
          rw [hB, ← hpm2]
          omega
        have qB : B9 m / 2^m = 2^(m-1) := by
          rw [eBm, Nat.add_mul_div_right _ _ h2mpos,
            Nat.div_eq_of_lt (by omega : 2^(m-1) < 2^m), zero_add]
        rw [qC, qB]
        omega
        -- remaining sum over Icc (m+1) (2*m-1)
      rw [show m - 1 + 1 = m from by omega, hhigh]
    -- contradiction
    have hne1 : OeisA93456.a (2^m) ≠ 0 := by rw [hrow1]; exact row_ne _ _
    have hne2 : OeisA93456.a (2^m + 1) ≠ 0 := by rw [hrow2]; exact row_ne _ _
    have hkey : 2^(S9 m + m) ∣ OeisA93456.a (2^m) :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne1).mpr (by rw [hv1])
    have hkey2 : 2^(S9 m + m) ∣ OeisA93456.a (2^m + 1) := Nat.dvd_trans hkey hdvd
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne2).mp hkey2
    rw [hv2] at hle
    omega
  -- infinity
  have hsub : {n : ℕ | ∃ m, 2 ≤ m ∧ n = 2^m + 1} ⊆ {n : ℕ | 1 < n ∧ ¬ (OeisA93456.a (n-1) ∣ OeisA93456.a n)} := by
    rintro n ⟨m, hm, rfl⟩
    exact hfam m hm
  have hf2 : {n : ℕ | ∃ m, 2 ≤ m ∧ n = 2^m + 1}.Finite := hf.subset hsub
  have hinj : Set.InjOn (fun m : ℕ => 2^m + 1) (Set.Ici 2) := by
    intro x hx y hy he
    simp only [Set.mem_Ici] at hx hy
    have he' : 2^x + 1 = 2^y + 1 := he
    have hxy : 2^x = 2^y := by omega
    exact Nat.pow_right_injective (by norm_num) hxy
  have himg : (fun m : ℕ => 2^m + 1) '' (Set.Ici 2) = {n : ℕ | ∃ m, 2 ≤ m ∧ n = 2^m + 1} := by
    ext n
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨m, hm, heq⟩
      exact ⟨m, hm, heq.symm⟩
    · rintro ⟨m, hm, heq⟩
      exact ⟨m, hm, heq.symm⟩
  have hinf := (Set.Ici_infinite (2 : ℕ)).image hinj
  rw [himg] at hinf
  exact absurd hf2 hinf
