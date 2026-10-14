
import FormalConjectures.OEIS.«108306»
set_option maxHeartbeats 2000000

namespace OeisA108306

open Matrix

private lemma D_eq_sum (a b m : ℕ) (hm : 0 < m) :
    invertSeqD a b m = ∑ i ∈ Finset.range m, invertSeqC a b (m - i) * invertSeqD a b i := by
  unfold invertSeqD
  rw [Nat.strongRecOn.eq_def, WellFounded.fix_eq]
  simp only []
  rw [if_neg (Nat.pos_iff_ne_zero.mp hm)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [dif_pos hi]
  rfl

private lemma D_zero (a b : ℕ) : invertSeqD a b 0 = 1 := by
  unfold invertSeqD
  rw [Nat.strongRecOn.eq_def, WellFounded.fix_eq]
  simp only []
  rfl

private lemma D_one (a b : ℕ) : invertSeqD a b 1 = 1 := by
  rw [D_eq_sum a b 1 (by omega)]
  simp [D_zero, invertSeqC]

private lemma Dmaster (a b n : ℕ) :
    invertSeqD a b (n + 2) + b * invertSeqD a b n
      = (b + 1) * invertSeqD a b (n + 1) + a * invertSeqD a b n := by
  have hr2 := D_eq_sum a b (n + 2) (by omega)
  have hr1 := D_eq_sum a b (n + 1) (by omega)
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hr2
  rw [Finset.sum_range_succ] at hr1
  rw [show n + 2 - (n + 1) = 1 from by omega] at hr2
  rw [show n + 2 - n = 2 from by omega] at hr2
  rw [show n + 1 - n = 1 from by omega] at hr1
  have C1 : invertSeqC a b 1 = 1 := rfl
  have C2 : invertSeqC a b 2 = a := by simp [invertSeqC]
  rw [C1, C2] at hr2
  rw [C1] at hr1
  have conv2 : ∑ i ∈ Finset.range n, invertSeqC a b (n + 2 - i) * invertSeqD a b i
      = b * ∑ i ∈ Finset.range n, invertSeqC a b (n + 1 - i) * invertSeqD a b i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hle : i < n := by simpa [Finset.mem_range] using hi
    rw [show n + 2 - i = (n - i) + 2 from by omega]
    rw [show n + 1 - i = (n - 1 - i) + 2 from by omega]
    show a * b ^ (n - i) * invertSeqD a b i
        = b * (a * b ^ (n - 1 - i) * invertSeqD a b i)
    have hpe : n - i = (n - 1 - i) + 1 := by omega
    rw [hpe, Nat.pow_succ]
    ring
  rw [hr2, hr1, conv2]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

private lemma Mchar (a b n : ℕ) :
    genMatrix a b ^ (n + 2) + b • genMatrix a b ^ n
      = (b + 1) • genMatrix a b ^ (n + 1) + a • genMatrix a b ^ n := by
  induction n with
  | zero =>
      have nz0 : (⟨0, by omega⟩ : Fin 2) = 0 := rfl
      have nz1 : (⟨1, by omega⟩ : Fin 2) = 1 := rfl
      have g00 : genMatrix a b 0 0 = 1 := rfl
      have g01 : genMatrix a b 0 1 = a := rfl
      have g10 : genMatrix a b 1 0 = 1 := rfl
      have g11 : genMatrix a b 1 1 = b := rfl
      have i00 : (1 : Matrix (Fin 2) (Fin 2) ℕ) 0 0 = 1 := rfl
      have i01 : (1 : Matrix (Fin 2) (Fin 2) ℕ) 0 1 = 0 := rfl
      have i10 : (1 : Matrix (Fin 2) (Fin 2) ℕ) 1 0 = 0 := rfl
      have i11 : (1 : Matrix (Fin 2) (Fin 2) ℕ) 1 1 = 1 := rfl
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [Nat.zero_add, pow_two, pow_one, pow_zero, nz0, nz1, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
          g00, g01, g10, g11, i00, i01, i10, i11,
          one_mul, mul_one, mul_zero, zero_mul, zero_add, add_zero] <;>
        ring
  | succ k ih =>
      have e1 : genMatrix a b ^ (k + 1 + 2) = genMatrix a b ^ (k + 2) * genMatrix a b :=
        pow_succ _ _
      have e2 : genMatrix a b ^ (k + 1) = genMatrix a b ^ k * genMatrix a b :=
        pow_succ _ _
      have e3 : genMatrix a b ^ (k + 2) = genMatrix a b ^ (k + 1) * genMatrix a b :=
        pow_succ _ _
      rw [e1, e2, ← smul_mul_assoc, ← add_mul, ih, add_mul, smul_mul_assoc,
        smul_mul_assoc, ← e2, ← e3]

private lemma cmaster (a b n : ℕ) :
    (genMatrix a b ^ (n + 2)) 0 0 + b * (genMatrix a b ^ n) 0 0
      = (b + 1) * (genMatrix a b ^ (n + 1)) 0 0 + a * (genMatrix a b ^ n) 0 0 := by
  have h := Mchar a b n
  have e := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℕ => X 0 0) h
  simp only [Matrix.add_apply, Matrix.smul_apply] at e
  exact e

private lemma main (a b n : ℕ) : invertSeqD a b n = (genMatrix a b ^ n) 0 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [D_zero]
  | one => simp [pow_one, D_one, genMatrix]
  | more k ih1 ih2 =>
      have hd := Dmaster a b k
      rw [ih1, ih2] at hd
      have hm := cmaster a b k
      omega

end OeisA108306

open OeisA108306

theorem swarm_proof : type_of% @OeisA108306.conjecture := by
  intro a b n
  exact OeisA108306.main a b n
