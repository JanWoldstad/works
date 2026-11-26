import WildNumber.Orbit.Data
import WildNumber.FiniteReps

namespace WildNumber.Nine.Orbit

/-- Read the sorted census once per level. Each successful comparison
consumes one level entry and witnesses its membership in the full census. -/
private def scan : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x = y then x < 2^28 && scan xs ys else scan (x :: xs) ys
termination_by structural _ all => all

private theorem scan_sound (xs ys : List Nat) (h : scan xs ys = true) :
    ∀ x ∈ xs, x < 2^28 ∧ x ∈ ys := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp_all [scan]
  | cons y ys ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      by_cases eq : x = y
      · subst y
        simp only [scan, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨h.1, List.mem_cons_self⟩
        · obtain ⟨hlt, hm⟩ := ih _ h.2 z hz
          exact ⟨hlt, List.mem_cons_of_mem _ hm⟩
      · simp only [scan, ite_eq_right eq] at h
        intro z hz
        obtain ⟨hlt, hm⟩ := ih _ h z hz
        exact ⟨hlt, List.mem_cons_of_mem _ hm⟩

private theorem included (xs : Array Nat) (h : scan xs.toList Census.repBatches.flatten = true) :
    ∀ g ∈ xs, g < 2^28 ∧ g ∈ Census.repMasks := by
  intro g hg
  simpa only [Census.repMasks, List.mem_toArray] using
    scan_sound _ _ h g (Array.mem_toList_iff.mpr hg)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem rep_facts (d : Nat) (hd : d ≤ 11) :
    ∀ g ∈ reps d, g < 2^28 ∧ g ∈ Census.repMasks := by
  interval_cases d <;> apply included <;> decide +kernel

end WildNumber.Nine.Orbit
