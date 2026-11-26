import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Families of forbidden triples in the nine-point reduction. -/

namespace WildNumber.Nine

abbrev Point := Fin 9
abbrev Family := Finset (Finset Point)

/-- A necessary condition for the link at a center to have a perfect matching. -/
def CoversPairs (B : Family) (x : Point) : Prop :=
  ∀ y, x ≠ y → ∃ t ∈ B, x ∈ t ∧ y ∈ t

def GoodSplit (B : Family) : Prop :=
  ∃ T U V : Finset Point, T.card = 3 ∧ U.card = 3 ∧ V.card = 3 ∧
    T ∪ U ∪ V = Finset.univ ∧ T ∉ B ∧ U ∉ B ∧ V ∉ B

def SevenShape (B : Family) : Prop :=
  ∃ S : Finset Point, S.card = 7 ∧ ∀ t ∈ B, t ⊆ S

def FourShape (B : Family) : Prop :=
  ∃ S E : Finset Point, S.card = 4 ∧ E.card ≤ 3 ∧
    ∀ t ∈ B, t = E ∨ 2 ≤ (t ∩ S).card

private theorem triple_inter_le_one {t S : Finset Point} (ht : t.card = 3)
    {x y : Point} (hxy : x ≠ y) (hx : x ∈ t) (hy : y ∈ t)
    (hxS : x ∉ S) (hyS : y ∉ S) : (t ∩ S).card ≤ 1 := by
  have hdis : Disjoint ({x,y} : Finset Point) (t ∩ S) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxS (Finset.mem_inter.mp hz').2
    · exact hyS (Finset.mem_inter.mp hz').2
  have hsub : ({x,y} : Finset Point) ∪ (t ∩ S) ⊆ t := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> assumption
    · exact (Finset.mem_inter.mp h).1
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_pair hxy, ht] at h
  omega

/-- A family supported on seven vertices has no center covering every pair. -/
theorem not_sevenShape {B : Family} {x : Point} (hx : CoversPairs B x) :
    ¬ SevenShape B := by
  rintro ⟨S, hS, hsub⟩
  have hcover : (Finset.univ : Finset Point) ⊆ insert x S := by
    intro y _
    by_cases h : x = y
    · simp [h]
    · obtain ⟨t, ht, _, hy⟩ := hx y h
      exact Finset.mem_insert_of_mem (hsub t ht hy)
  have hsize := Finset.card_le_card hcover
  have hadd := Finset.card_insert_le x S
  have h9 : (Finset.univ : Finset Point).card = 9 := by decide
  omega

/-- Adding one triple to the four-set obstruction still leaves every vertex
outside the four-set with a missing pair in its link. -/
theorem not_fourShape {B : Family} (ht : ∀ t ∈ B, t.card = 3)
    {C : Finset Point} (hc : 5 ≤ C.card) (hcent : ∀ x ∈ C, CoversPairs B x) :
    ¬ FourShape B := by
  rintro ⟨S,E,hS,hE,hshape⟩
  obtain ⟨x,hx,hxS⟩ : ∃ x ∈ C, x ∉ S := by
    by_contra! h
    have := Finset.card_le_card (show C ⊆ S from h)
    omega
  have hyin : ∀ y, x ≠ y → y ∉ S → y ∈ E := by
    intro y hxy hyS
    obtain ⟨t,htB,hxt,hyt⟩ := hcent x hx y hxy
    rcases hshape t htB with rfl | htwo
    · exact hyt
    · have := triple_inter_le_one (ht t htB) hxy hxt hyt hxS hyS
      omega
  have hcover : (Finset.univ : Finset Point) ⊆ insert x (S ∪ E) := by
    intro y _
    by_cases hxy : x = y
    · simp [hxy]
    · apply Finset.mem_insert_of_mem
      by_cases hyS : y ∈ S
      · exact Finset.mem_union_left _ hyS
      · exact Finset.mem_union_right _ (hyin y hxy hyS)
  have hu := Finset.card_le_card hcover
  have hadd := Finset.card_insert_le x (S ∪ E)
  have hSE := Finset.card_union_le S E
  have h9 : (Finset.univ : Finset Point).card = 9 := by decide
  omega

end WildNumber.Nine
