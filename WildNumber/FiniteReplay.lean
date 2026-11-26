import WildNumber.FiniteModel

/-! A certificate for the vertex-cover search at a fixed link. A split
either retains a triple or omits it. In the latter branch the certificate
can list triples forced by nine-point partitions. A packing leaf lists
disjoint pairs of alternatives, each requiring another selected triple. -/

namespace WildNumber.Nine.Census

abbrev Conflict := ℕ × ℕ × ℕ

/-- Each packing witness stores a 5-bit root edge and two 6-bit triple indices. -/
def unpackConflicts (n code : ℕ) : List Conflict :=
  (List.range n).map fun p =>
    let w := code >>> (17*p)
    (w % 32, (w >>> 5) % 64, (w >>> 11) % 64)

def unpackForced (n code : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun p =>
    let w := code >>> (11*p)
    (w % 32, (w >>> 5) % 64)

def partitionCheck (g k i j : ℕ) : Bool :=
  k < 28 && i < 56 && j < 56 && (edge k ||| triple i ||| triple j) == 255 && !g.testBit k

private theorem partition_sound {g k i j : ℕ} {B : Finset ℕ} (hm : NumericModel g B)
    (h : partitionCheck g k i j = true) : i ∈ B ∨ j ∈ B := by
  simp [partitionCheck, Bool.and_eq_true] at h
  exact hm.cover k i j h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2

theorem degree_mono {g} {B C : Finset ℕ} (h : B ⊆ C) (v : Fin 8) :
    degree g B v ≤ degree g C v :=
  Nat.add_le_add_left (Finset.card_le_card (Finset.filter_subset_filter _ h)) _

private theorem center_mono {g} {B C : Finset ℕ} (h : B ⊆ C) : centerSet g B ⊆ centerSet g C := by
  have hsub : members g B ⊆ members g C :=
    Finset.union_subset_union_right (Finset.image_subset_image h)
  intro x hx
  obtain ⟨_, hh⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
  obtain ⟨t,ht,hx,hy⟩ := hh y hy
  exact ⟨t,hsub ht,hx,hy⟩

def packOK (g : ℕ) : List Conflict → Finset ℕ → Bool
  | [], _ => true
  | (k,i,j)::rest, used => partitionCheck g k i j && decide (i ∉ used) &&
      decide (j ∉ used) && packOK g rest (insert i (insert j used))

private theorem pack_bound {g} {B : Finset ℕ} (hm : NumericModel g B) (w : List Conflict)
    {s used : Finset ℕ} (hB : s ⊆ B) (hused : s ⊆ used) (hw : packOK g w used = true) :
    s.card + w.length ≤ B.card := by
  induction w generalizing s used with
  | nil => simpa using Finset.card_le_card hB
  | cons p w ih =>
    obtain ⟨k,i,j⟩ := p
    simp only [packOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hq, hi⟩, hj⟩, hr⟩ := hw
    have take (z) (hz : z ∈ B) (hz' : z ∉ used) (hij : z = i ∨ z = j) :
        (insert z s).card + w.length ≤ B.card := by
      apply ih (Finset.insert_subset hz hB) _ hr
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases hij with rfl | rfl <;> simp
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hused ha))
    rcases partition_sound hm hq with h | h
    · have hcard := take i h hi (Or.inl rfl)
      rw [Finset.card_insert_of_notMem (fun ha => hi (hused ha))] at hcard
      simp only [List.length_cons]
      omega
    · have hcard := take j h hj (Or.inr rfl)
      rw [Finset.card_insert_of_notMem (fun ha => hj (hused ha))] at hcard
      simp only [List.length_cons]
      omega

inductive Refutation where
  | oversize
  | missing (k i j : ℕ)
  | high (v : Fin 8)
  | low (v : Fin 8)
  | centers
  | full (next : Refutation)
  | pack (w : List Conflict)
  | split (v : ℕ) (forced : List (ℕ × ℕ)) (yes no : Refutation)

def replay (g : ℕ) : Refutation → Finset ℕ → Finset ℕ → Bool
  | .oversize, s, _ => 35 < (bits g).card + s.card
  | .missing k i j, _, a => partitionCheck g k i j && decide (i ∉ a) && decide (j ∉ a)
  | .high v, s, _ => 19 < degree g s v
  | .low v, _, a => degree g a v < (bits g).card
  | .centers, _, a => (centerSet g a).card < 5
  | .full next, s, _ => 35 ≤ (bits g).card + s.card && replay g next s s
  | .pack w, s, _ => 35 < (bits g).card + s.card + w.length && packOK g w s
  | .split v forced yes no, s, a =>
    forced.all (fun (k,j) => partitionCheck g k v j) &&
    replay g yes (insert v s) a &&
    replay g no (s ∪ (forced.map Prod.snd).toFinset) (a.erase v)

theorem replay_sound {g} {B : Finset ℕ} (hm : NumericModel g B) (w : Refutation)
    {s a : Finset ℕ} (hs : s ⊆ B) (ha : B ⊆ a) : replay g w s a = false := by
  apply Bool.eq_false_iff.mpr
  intro hw
  induction w generalizing s a with
  | oversize =>
    simp only [replay, decide_eq_true_eq] at hw
    have := hm.budget
    have := Finset.card_le_card hs
    omega
  | missing k i j =>
    simp only [replay, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases partition_sound hm hw.1.1 with h | h
    · exact hw.1.2 (ha h)
    · exact hw.2 (ha h)
  | high v =>
    simp only [replay, decide_eq_true_eq] at hw
    exact (Nat.not_lt_of_ge ((degree_mono hs v).trans (hm.degree_max v))) hw
  | low v =>
    simp only [replay, decide_eq_true_eq] at hw
    exact (Nat.not_lt_of_ge ((hm.degree_min v).trans (degree_mono ha v))) hw
  | centers =>
    simp only [replay, decide_eq_true_eq] at hw
    exact (Nat.not_lt_of_ge (hm.centers.trans (Finset.card_le_card (center_mono ha)))) hw
  | full next ih =>
    simp only [replay, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hbudget := hm.budget
    have heq : s = B := Finset.eq_of_subset_of_card_le hs (by omega)
    exact ih hs (heq ▸ Finset.Subset.rfl) hw.2
  | pack w =>
    simp only [replay, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hcard := pack_bound hm w hs Finset.Subset.rfl hw.2
    have hbudget := hm.budget
    omega
  | split v forced yes no iy ino =>
    simp only [replay, Bool.and_eq_true, List.all_eq_true] at hw
    by_cases hv : v ∈ B
    · exact iy (Finset.insert_subset hv hs) ha hw.1.2
    · have hh : (forced.map Prod.snd).toFinset ⊆ B := by
        intro j hj
        obtain ⟨⟨k,l⟩,hkl,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
        exact (partition_sound hm (hw.1.1 _ hkl)).resolve_left hv
      apply ino (Finset.union_subset hs hh) (fun i hi => Finset.mem_erase.mpr ⟨?_,ha hi⟩) hw.2
      rintro rfl
      exact hv hi

theorem refute_link {g} (w : Refutation)
    (h : replay g w ∅ (Finset.range 56) = true) (B : Finset ℕ) : ¬ NumericModel g B := by
  intro hm
  have := replay_sound hm w (Finset.empty_subset B) hm.valid
  simp [h] at this

end WildNumber.Nine.Census
