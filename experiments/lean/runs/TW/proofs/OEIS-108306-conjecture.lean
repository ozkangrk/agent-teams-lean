
import FormalConjectures.OEIS.«108306»

open OeisA108306 Matrix

namespace SwarmA108306

variable (A B : ℕ)

private def u (n : ℕ) : ℕ := (genMatrix A B ^ n) 0 0
private def v (n : ℕ) : ℕ := (genMatrix A B ^ n) 0 1
private def w (t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), B ^ (t - i) * u A B i

private lemma gM00 : genMatrix A B 0 0 = 1 := rfl
private lemma gM01 : genMatrix A B 0 1 = A := rfl
private lemma gM10 : genMatrix A B 1 0 = 1 := rfl
private lemma gM11 : genMatrix A B 1 1 = B := rfl

private lemma u_zero : u A B 0 = 1 := by unfold u; simp
private lemma v_zero : v A B 0 = 0 := by unfold v; simp

private lemma u_succ (n : ℕ) : u A B (n + 1) = u A B n + v A B n := by
  have hp : genMatrix A B ^ (n + 1) = (genMatrix A B ^ n) * genMatrix A B := pow_succ _ _
  unfold u v
  rw [hp]
  simp [Matrix.mul_apply, Fin.sum_univ_two, gM00, gM10]

private lemma v_succ (n : ℕ) : v A B (n + 1) = A * u A B n + B * v A B n := by
  have hp : genMatrix A B ^ (n + 1) = (genMatrix A B ^ n) * genMatrix A B := pow_succ _ _
  unfold u v
  rw [hp]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, gM00, gM01, gM11]
  ring

private lemma w_succ (t : ℕ) : w A B (t + 1) = u A B (t + 1) + B * w A B t := by
  have key : ∑ x ∈ Finset.range (t + 1), B ^ (t + 1 - x) * u A B x
      = B * ∑ x ∈ Finset.range (t + 1), B ^ (t - x) * u A B x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxb : x < t + 1 := Finset.mem_range.mp hx
    have h1 : t + 1 - x = (t - x) + 1 := by omega
    rw [h1, pow_succ]
    ring
  unfold w
  rw [Finset.sum_range_succ_comm]
  have hz : t + 1 - (t + 1) = 0 := by omega
  rw [hz, pow_zero, one_mul, key]

private lemma hv_w (t : ℕ) : v A B (t + 1) = A * w A B t := by
  induction t with
  | zero =>
      rw [v_succ, u_zero, v_zero, mul_zero, add_zero]
      unfold w
      simp [u_zero]
  | succ t ih =>
      rw [v_succ, ih, w_succ]
      ring

private lemma D_unfold (m : ℕ) : invertSeqD A B m =
    (if m = 0 then 1
     else ∑ i ∈ Finset.range m,
        if h : i < m then invertSeqC A B (m - i) * invertSeqD A B i else 0) := by
  unfold invertSeqD
  change WellFounded.fix Nat.lt_wfRel.wf _ m = _
  rw [WellFounded.fix_eq]
  by_cases hm : m = 0
  · subst hm
    rfl
  · rw [if_neg hm, if_neg hm]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [dif_pos (Finset.mem_range.mp hi)]
    rfl

private lemma C_succ (k : ℕ) : invertSeqC A B (k + 2) = A * B ^ k := rfl

private theorem main_aux : ∀ m, invertSeqD A B m = u A B m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      match m with
      | 0 =>
          rw [D_unfold]
          simp only [if_pos rfl]
          exact u_zero A B
      | 1 =>
          rw [D_unfold]
          simp only [if_neg one_ne_zero]
          have hdite : ∑ i ∈ Finset.range 1,
              (if h : i < 1 then invertSeqC A B (1 - i) * invertSeqD A B i else 0)
              = invertSeqC A B (1 - 0) * invertSeqD A B 0 := by
            simp only [Finset.range_one, Finset.sum_singleton,
              dif_pos (show (0 : ℕ) < 1 by omega)]
          rw [hdite]
          have h1 : invertSeqC A B (1 - 0) = 1 := rfl
          rw [h1, one_mul, ih 0 (by omega)]
          have hu : u A B 1 = u A B 0 + v A B 0 := u_succ A B 0
          rw [hu, u_zero A B, v_zero A B]
      | m' + 2 =>
          rw [D_unfold]
          have hne : m' + 2 ≠ 0 := by omega
          rw [if_neg hne]
          have hdite : ∑ i ∈ Finset.range (m' + 2),
              (if h : i < m' + 2 then invertSeqC A B (m' + 2 - i) * invertSeqD A B i else 0)
              = ∑ i ∈ Finset.range (m' + 2),
                  invertSeqC A B (m' + 2 - i) * invertSeqD A B i :=
            Finset.sum_congr rfl fun i hi => by
              simp only [dif_pos (Finset.mem_range.mp hi)]
          rw [hdite]
          have hsplit : m' + 2 = (m' + 1) + 1 := by omega
          rw [hsplit, Finset.range_add_one, Finset.sum_insert (by simp)]
          have hDm : invertSeqD A B (m' + 1) = u A B (m' + 1) := ih (m' + 1) (by omega)
          rw [hDm]
          have h1 : invertSeqC A B ((m' + 1) + 1 - (m' + 1)) = 1 := by
            have : (m' + 1) + 1 - (m' + 1) = 1 := by omega
            rw [this]
            rfl
          rw [h1, one_mul]
          have hsum : ∑ i ∈ Finset.range (m' + 1),
              invertSeqC A B ((m' + 1) + 1 - i) * invertSeqD A B i = A * w A B m' := by
            rw [show w A B m' = ∑ i ∈ Finset.range (m' + 1), B ^ (m' - i) * u A B i from rfl,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hib : i < m' + 1 := Finset.mem_range.mp hi
            have hsplit2 : (m' + 1) + 1 - i = (m' - i) + 2 := by omega
            rw [hsplit2, C_succ, ih i (by omega)]
            ring
          rw [hsum]
          have hv : v A B (m' + 1) = A * w A B m' := hv_w A B m'
          have hu := u_succ A B (m' + 1)
          omega

end SwarmA108306

theorem swarm_proof (a_val b_val n : ℕ) :
    invertSeqD a_val b_val n = (genMatrix a_val b_val ^ n) 0 0 :=
  SwarmA108306.main_aux a_val b_val n
