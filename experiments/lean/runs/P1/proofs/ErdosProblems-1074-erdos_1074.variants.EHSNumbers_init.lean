import FormalConjectures.ErdosProblems.«1074»

/-! Initial values of the EHS numbers sequence for Erdős problem 1074. -/

open Erdos1074

noncomputable local instance epEHSdec : ∀ m : ℕ, Decidable (m ∈ EHSNumbers) :=
  fun m => Classical.propDecidable (m ∈ EHSNumbers)

theorem ep_ehs8 : 8 ∈ EHSNumbers := by
  show 1 ≤ 8 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 8]) ∧ p ∣ Nat.factorial 8 + 1
  exact ⟨by norm_num, 61, by decide, by decide, by decide⟩

theorem ep_ehs9 : 9 ∈ EHSNumbers := by
  show 1 ≤ 9 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 9]) ∧ p ∣ Nat.factorial 9 + 1
  exact ⟨by norm_num, 71, by decide, by decide, by decide⟩

theorem ep_ehs13 : 13 ∈ EHSNumbers := by
  show 1 ≤ 13 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 13]) ∧ p ∣ Nat.factorial 13 + 1
  exact ⟨by norm_num, 83, by decide, by decide, by decide⟩

theorem ep_ehs14 : 14 ∈ EHSNumbers := by
  show 1 ≤ 14 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 14]) ∧ p ∣ Nat.factorial 14 + 1
  exact ⟨by norm_num, 23, by decide, by decide, by decide⟩

theorem ep_ehs15 : 15 ∈ EHSNumbers := by
  show 1 ≤ 15 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 15]) ∧ p ∣ Nat.factorial 15 + 1
  exact ⟨by norm_num, 59, by decide, by decide, by decide⟩

theorem ep_ehs16 : 16 ∈ EHSNumbers := by
  show 1 ≤ 16 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 16]) ∧ p ∣ Nat.factorial 16 + 1
  exact ⟨by norm_num, 61, by decide, by decide, by decide⟩

theorem ep_ehs17 : 17 ∈ EHSNumbers := by
  show 1 ≤ 17 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 17]) ∧ p ∣ Nat.factorial 17 + 1
  exact ⟨by norm_num, 661, by norm_num, by decide, by decide⟩

theorem ep_notEHS {m : ℕ} {L : List ℕ}
    (hpr : ∀ q ∈ L, q.Prime) (hprod : L.prod = Nat.factorial m + 1)
    (hmod : ∀ q ∈ L, q ≡ 1 [MOD m]) : ¬ m ∈ EHSNumbers := by
  show ¬ (1 ≤ m ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD m]) ∧ p ∣ Nat.factorial m + 1)
  rintro ⟨-, p, hp, hpne, hpdvd⟩
  refine hpne (hmod p (mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hp)
    (fun q hq => Nat.prime_iff.mp (hpr q hq)) ?_))
  rw [hprod]
  exact hpdvd

theorem ep_notEHS0 : ¬ (0 ∈ EHSNumbers) := by
  show ¬ (1 ≤ 0 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 0]) ∧ p ∣ Nat.factorial 0 + 1)
  exact fun h => absurd h.1 (by omega)

theorem ep_notEHS1 : ¬ (1 ∈ EHSNumbers) := by
  show ¬ (1 ≤ 1 ∧ ∃ p, p.Prime ∧ ¬(p ≡ 1 [MOD 1]) ∧ p ∣ Nat.factorial 1 + 1)
  rintro ⟨-, p, hp, hpne, hdvd⟩
  exact hpne (by simp [Nat.ModEq, Nat.mod_one])

theorem ep_notEHS2 : ¬ (2 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [3]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS3 : ¬ (3 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [7]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS4 : ¬ (4 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [5, 5]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS5 : ¬ (5 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [11, 11]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS6 : ¬ (6 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [7, 103]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS7 : ¬ (7 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [71, 71]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    · exact absurd hq (by simp)

theorem ep_notEHS10 : ¬ (10 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [11, 329891]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)

theorem ep_notEHS11 : ¬ (11 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [39916801]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)

theorem ep_notEHS12 : ¬ (12 ∈ EHSNumbers) := by
  refine ep_notEHS (L := [13, 13, 2834329]) ?_ ?_ ?_
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)
  · decide
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · decide
    rcases List.mem_cons.1 hq with rfl | hq
    · norm_num
    · exact absurd hq (by simp)

theorem ep_EHS_iff (m : ℕ) (hm : m ≤ 17) :
    m ∈ EHSNumbers ↔ m ∈ ({8, 9, 13, 14, 15, 16, 17} : Finset ℕ) := by
  interval_cases m
  all_goals first
  | exact iff_of_true ep_ehs8 (by decide)
  | exact iff_of_true ep_ehs9 (by decide)
  | exact iff_of_true ep_ehs13 (by decide)
  | exact iff_of_true ep_ehs14 (by decide)
  | exact iff_of_true ep_ehs15 (by decide)
  | exact iff_of_true ep_ehs16 (by decide)
  | exact iff_of_true ep_ehs17 (by decide)
  | exact iff_of_false ep_notEHS0 (by decide)
  | exact iff_of_false ep_notEHS1 (by decide)
  | exact iff_of_false ep_notEHS2 (by decide)
  | exact iff_of_false ep_notEHS3 (by decide)
  | exact iff_of_false ep_notEHS4 (by decide)
  | exact iff_of_false ep_notEHS5 (by decide)
  | exact iff_of_false ep_notEHS6 (by decide)
  | exact iff_of_false ep_notEHS7 (by decide)
  | exact iff_of_false ep_notEHS10 (by decide)
  | exact iff_of_false ep_notEHS11 (by decide)
  | exact iff_of_false ep_notEHS12 (by decide)

theorem ep_count_EHS (n : ℕ) (hn : n ≤ 18) :
    Nat.count (fun m => m ∈ EHSNumbers) n =
      ((Finset.range n).filter (fun m => m ∈ ({8, 9, 13, 14, 15, 16, 17} : Finset ℕ))).card := by
  rw [Nat.count_eq_card_filter_range (p := fun m => m ∈ EHSNumbers) n]
  show ((Finset.range n).filter (fun m => m ∈ EHSNumbers)).card =
    ((Finset.range n).filter (fun m => m ∈ ({8, 9, 13, 14, 15, 16, 17} : Finset ℕ))).card
  have hf : (Finset.range n).filter (fun m => m ∈ EHSNumbers) =
      (Finset.range n).filter (fun m => m ∈ ({8, 9, 13, 14, 15, 16, 17} : Finset ℕ)) := by
    ext m
    simp only [Finset.mem_filter]
    by_cases hmn : m < n
    · simp only [Finset.mem_range, hmn, true_and]
      exact ep_EHS_iff m (by omega)
    · simp only [Finset.mem_range, hmn, false_and]
  rw [hf]

theorem ep_count_EHS_8 : Nat.count (fun m => m ∈ EHSNumbers) 8 = 0 := by
  rw [ep_count_EHS 8 (by norm_num)]
  decide

theorem ep_count_EHS_9 : Nat.count (fun m => m ∈ EHSNumbers) 9 = 1 := by
  rw [ep_count_EHS 9 (by norm_num)]
  decide

theorem ep_count_EHS_13 : Nat.count (fun m => m ∈ EHSNumbers) 13 = 2 := by
  rw [ep_count_EHS 13 (by norm_num)]
  decide

theorem ep_count_EHS_14 : Nat.count (fun m => m ∈ EHSNumbers) 14 = 3 := by
  rw [ep_count_EHS 14 (by norm_num)]
  decide

theorem ep_count_EHS_15 : Nat.count (fun m => m ∈ EHSNumbers) 15 = 4 := by
  rw [ep_count_EHS 15 (by norm_num)]
  decide

theorem ep_count_EHS_16 : Nat.count (fun m => m ∈ EHSNumbers) 16 = 5 := by
  rw [ep_count_EHS 16 (by norm_num)]
  decide

theorem ep_count_EHS_17 : Nat.count (fun m => m ∈ EHSNumbers) 17 = 6 := by
  rw [ep_count_EHS 17 (by norm_num)]
  decide

theorem ep_nth_EHS_0 : Nat.nth (fun m => m ∈ EHSNumbers) 0 = 8 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs8
  rwa [ep_count_EHS_8] at h

theorem ep_nth_EHS_1 : Nat.nth (fun m => m ∈ EHSNumbers) 1 = 9 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs9
  rwa [ep_count_EHS_9] at h

theorem ep_nth_EHS_2 : Nat.nth (fun m => m ∈ EHSNumbers) 2 = 13 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs13
  rwa [ep_count_EHS_13] at h

theorem ep_nth_EHS_3 : Nat.nth (fun m => m ∈ EHSNumbers) 3 = 14 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs14
  rwa [ep_count_EHS_14] at h

theorem ep_nth_EHS_4 : Nat.nth (fun m => m ∈ EHSNumbers) 4 = 15 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs15
  rwa [ep_count_EHS_15] at h

theorem ep_nth_EHS_5 : Nat.nth (fun m => m ∈ EHSNumbers) 5 = 16 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs16
  rwa [ep_count_EHS_16] at h

theorem ep_nth_EHS_6 : Nat.nth (fun m => m ∈ EHSNumbers) 6 = 17 := by
  have h := Nat.nth_count (p := fun m => m ∈ EHSNumbers) ep_ehs17
  rwa [ep_count_EHS_17] at h

theorem swarm_proof :
    Nat.nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  show Nat.nth (fun m => m ∈ EHSNumbers) '' (Set.Icc 0 6) = ({8, 9, 13, 14, 15, 16, 17} : Set ℕ)
  have hIcc : (Set.Icc 0 6 : Set ℕ) = insert 0 (insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 ∅)))))) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_empty_iff_false, or_false]
    omega
  rw [hIcc]
  simp only [Set.image_insert_eq, Set.image_empty, ep_nth_EHS_0, ep_nth_EHS_1, ep_nth_EHS_2,
    ep_nth_EHS_3, ep_nth_EHS_4, ep_nth_EHS_5, ep_nth_EHS_6]
  ext x
  simp
