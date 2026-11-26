import WildNumber.MatchingKinds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace WildNumber.Reduction

open Finset

private theorem pair_mem {i k : Fin 6} {j : Fin 2} : some (k,j) ∈ pairAt i ↔ k = i := by
  fin_cases j <;> simp [pairAt]

private theorem pair_subset {D : Finset Pos} {i} : pairAt i ⊆ D ↔ kind D i = 2 := by
  by_cases h : some (i,0) ∈ D <;> by_cases h' : some (i,1) ∈ D <;>
    simp [pairAt,kind,h,h',insert_subset_iff]

private theorem count_full (D : Finset Pos) :
    (sixPairs.filter (· ⊆ D)).card = profile D 2 := by
  have inj : Function.Injective pairAt := by
    intro i k eq
    exact pair_mem.mp (eq ▸ (pair_mem (j := 0)).mpr (rfl : i = i))
  rw [sixPairs, filter_image, card_image_of_injective _ inj]
  unfold profile
  exact congrArg card (filter_congr (fun _ _ => pair_subset))

private theorem count_selected (D : Finset Pos) :
    D.card = (∑ i, (kind D i).val) + if none ∈ D then 1 else 0 := by
  let selected (i) := (pairAt i).filter (· ∈ D)
  have hcover : univ.biUnion selected = D.erase none := by
    ext x
    cases x with
    | none => simp [selected, pairAt]
    | some p => rcases p with ⟨k,j⟩; simp [selected,pair_mem]
  have hd : (↑(univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint selected := by
    intro i _ k _ ne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hi hk
    cases x with
    | none => simpa [selected,pairAt] using hi
    | some p =>
      exact ne ((pair_mem.mp (mem_filter.mp hi).1).symm.trans (pair_mem.mp (mem_filter.mp hk).1))
  have he (i) : (selected i).card = (kind D i).val := by
    by_cases h : some (i,0) ∈ D <;> by_cases h' : some (i,1) ∈ D <;>
      simp [selected, pairAt, kind, Finset.filter_insert, Finset.filter_singleton, h, h']
  have hc : (D.erase none).card = ∑ i, (kind D i).val := by
    rw [← hcover, card_biUnion (s := univ) (t := selected) hd]
    simp_rw [he]
  by_cases h : none ∈ D
  · rw [if_pos h, ← hc, card_erase_add_one h]
  · simpa [h] using hc

private theorem counts (D : Finset Pos) :
    profile D 0 + profile D 1 + profile D 2 = 6 ∧
    D.card = profile D 1 + 2 * profile D 2 + if none ∈ D then 1 else 0 := by
  have hs := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin 6)) univ (kind D)
  have ht (i : Fin 6) : (kind D i).val =
      (if kind D i = 1 then 1 else 0) + (if kind D i = 2 then 2 else 0) := by
    generalize kind D i = k
    fin_cases k <;> decide
  constructor
  · simpa [profile, Fin.sum_univ_three, Nat.add_assoc] using hs
  · rw [count_selected]
    simp_rw [ht]
    simp [sum_add_distrib, sum_ite, profile, Nat.mul_comm]

private theorem normal_profile (D : Finset Pos) (hD : D.card = 4)
    (ha : (sixPairs.filter (· ⊆ D)).card ≤ 1) :
    ∃ j, SameProfile (representative j) D := by
  rw [count_full] at ha
  obtain ⟨ht,hs⟩ := counts D
  rw [hD] at hs
  have check : ∀ j : Fin 4, ∀ k : Fin 3, profile (representative j) k =
      (if j = 0 then (if k = 0 then 2 else if k = 1 then 4 else 0)
       else if j = 1 then (if k = 0 then 3 else if k = 1 then 2 else 1)
       else if j = 2 then (if k = 0 then 3 else if k = 1 then 3 else 0)
       else (if k = 0 then 4 else if k = 1 then 1 else 1)) := by decide
  by_cases hm : none ∈ D <;> by_cases hf : profile D 2 = 0
  · refine ⟨2, by simp [representative, hm], ?_⟩
    intro k; fin_cases k <;> simp [check] <;> simp [hm] at hs <;> omega
  · refine ⟨3, by simp [representative, hm], ?_⟩
    intro k; fin_cases k <;> simp [check] <;> simp [hm] at hs <;> omega
  · refine ⟨0, by simp [representative, hm], ?_⟩
    intro k; fin_cases k <;> simp [check] <;> simp [hm] at hs <;> omega
  · refine ⟨1, by simp [representative, hm], ?_⟩
    intro k; fin_cases k <;> simp [check] <;> simp [hm] at hs <;> omega

theorem four_set_profiles :
    ∀ D ∈ (Finset.univ : Finset Pos).powersetCard 4,
      (sixPairs.filter (· ⊆ D)).card ≤ 1 → ∃ j, SameProfile (representative j) D := by
  intro D hD ha
  exact normal_profile D (mem_powersetCard.mp hD).2 ha

end WildNumber.Reduction
