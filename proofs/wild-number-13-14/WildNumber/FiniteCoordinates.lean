import WildNumber.FiniteModel
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Connecting the census indices to actual triples of nine points. -/
namespace WildNumber.Nine.Census
open Finset

def decode (m : ℕ) : Finset Point := univ.filter fun x => m.testBit x.val
def rootTriple (k : ℕ) := decode (256 + edge k)
def plainTriple (i : ℕ) := decode (triple i)
def rootPair (k : ℕ) : Finset (Fin 8) := univ.filter fun x => (edge k).testBit x.val

@[simp] theorem mem_decode {v : Point} {m : ℕ} : v ∈ decode m ↔ m.testBit v.val := by
  simp [decode]

private theorem root_table : ∀ k : Fin 28,
    (rootTriple k).card = 3 ∧ (8 : Point) ∈ rootTriple k ∧
    ∀ v : Fin 8, (v.castSucc ∈ rootTriple k ↔ (edge k).testBit v.val) := by decide

private theorem plain_table : ∀ i : Fin 56,
    (plainTriple i).card = 3 ∧ (8 : Point) ∉ plainTriple i := by decide

set_option maxRecDepth 10000 in
private theorem root_table_distinct : ((Finset.range 28).image rootTriple).card = 28 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem plain_table_distinct : ((Finset.range 56).image plainTriple).card = 56 := by decide +kernel

theorem coordinates_cover : (univ : Finset Point).powersetCard 3 =
    ((range 28).image rootTriple ∪ (range 56).image plainTriple) := by
  have hr (k : ℕ) (h : k ∈ range 28) := root_table ⟨k,mem_range.mp h⟩
  have hp (k : ℕ) (h : k ∈ range 56) := plain_table ⟨k,mem_range.mp h⟩
  symm
  apply eq_of_subset_of_card_le
  · intro t ht
    rcases mem_union.mp ht with h | h
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      exact mem_powersetCard.mpr ⟨subset_univ _,(hr k hk).1⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact mem_powersetCard.mpr ⟨subset_univ _,(hp i hi).1⟩
  · have dis : Disjoint ((range 28).image rootTriple) ((range 56).image plainTriple) := by
      rw [disjoint_left]
      intro t ht ht'
      obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
      obtain ⟨i,hi,eq⟩ := mem_image.mp ht'
      exact (hp i hi).2 (eq ▸ (hr k hk).2.1)
    rw [card_union_of_disjoint dis, root_table_distinct, plain_table_distinct, card_powersetCard]
    decide

theorem natural_link_index_bound {g k : ℕ} (hg : g < 2^28) (hk : k ∈ bits g) : k < 28 := by
  by_contra! h
  have hb := Nat.testBit_lt_two_pow (lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) h))
  have ht := mem_bits.mp hk
  simp [hb] at ht

private theorem filterCount {α : Type*} [DecidableEq α] {I J : Finset ℕ}
    {f h : ℕ → α} (hi : Set.InjOn f I) (hj : Set.InjOn h J)
    (hd : Disjoint (I.image f) (J.image h)) (P : α → Prop) [DecidablePred P] :
    (((I.image f) ∪ (J.image h)).filter P).card =
      (I.filter fun k => P (f k)).card + (J.filter fun k => P (h k)).card := by
  have hfilter (s : Finset ℕ) (a : ℕ → α) :
      (s.image a).filter P = (s.filter fun k => P (a k)).image a := by
    ext x
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,hx⟩
      exact ⟨i,⟨hi,hx⟩,rfl⟩
    · rintro ⟨i,⟨hi,hx⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,hx⟩
  rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _)),
    hfilter,hfilter, card_image_of_injOn (hi.mono (filter_subset _ _)),
    card_image_of_injOn (hj.mono (filter_subset _ _))]

theorem numeric_of_canonical (F : Family) (typed : ∀ t ∈ F, t.card = 3)
    (size : F.card ≤ 35) (maxdeg : ∀ v, (F.filter (v ∈ ·)).card ≤ 19)
    (minroot : ∀ v, (F.filter ((8 : Point) ∈ ·)).card ≤ (F.filter (v ∈ ·)).card)
    (C : Finset Point) (h5 : 5 ≤ C.card) (hc : ∀ x ∈ C, CoversPairs F x)
    (bad : ¬ GoodSplit F) (g : ℕ) (hg : g < 2^28)
    (root : ∀ k < 28, k ∈ bits g ↔ rootTriple k ∈ F) :
    ∃ B, NumericModel g B ∧ (bits g).card = (F.filter ((8 : Point) ∈ ·)).card := by
  classical
  let A := bits g
  let B := (range 56).filter fun i => plainTriple i ∈ F
  have hA : A ⊆ range 28 := fun _ h => mem_range.mpr (natural_link_index_bound hg h)
  have hB : B ⊆ range 56 := filter_subset _ _
  have ri : Set.InjOn rootTriple A := (injOn_of_card_image_eq (by simpa using root_table_distinct)).mono hA
  have pi : Set.InjOn plainTriple B := (injOn_of_card_image_eq (by simpa using plain_table_distinct)).mono hB
  have r8 (k) (hk : k ∈ A) := (root_table ⟨k,mem_range.mp (hA hk)⟩).2.1
  have p8 (i) (hi : i ∈ B) := (plain_table ⟨i,mem_range.mp (hB hi)⟩).2
  have dis : Disjoint (A.image rootTriple) (B.image plainTriple) := by
    rw [disjoint_left]
    intro t h h'
    obtain ⟨k,hk,rfl⟩ := mem_image.mp h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h'
    exact p8 i hi (eq ▸ r8 k hk)
  have decomp : F = A.image rootTriple ∪ B.image plainTriple := by
    ext t
    constructor
    · intro ht
      have ht' : t ∈ (univ : Finset Point).powersetCard 3 := mem_powersetCard.mpr
        ⟨subset_univ _,typed t ht⟩
      rw [coordinates_cover] at ht'
      rcases mem_union.mp ht' with h|h
      · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
        exact mem_union_left _ (mem_image.mpr ⟨k,(root k (mem_range.mp hk)).mpr ht,rfl⟩)
      · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
        exact mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,ht⟩,rfl⟩)
    · intro ht
      rcases mem_union.mp ht with h|h
      · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
        exact (root k (mem_range.mp (hA hk))).mp hk
      · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
        exact (mem_filter.mp hi).2
  have base (v : Point) := filterCount ri pi dis (fun t => v ∈ t)
  have rootcount : (F.filter ((8 : Point) ∈ ·)).card = A.card := by
    rw [decomp, base, filter_true_of_mem r8, filter_false_of_mem p8]
    simp
  have actualDegree (v : Fin 8) : (F.filter (v.castSucc ∈ ·)).card = degree g B v := by
    rw [decomp, base]
    unfold degree
    congr 1
    · congr 1
      apply filter_congr
      intro k hk
      exact (root_table ⟨k,mem_range.mp (hA hk)⟩).2.2 v
    · congr 1
      apply filter_congr
      intro i _
      exact mem_decode
  refine ⟨B, ⟨hB, ?_, ?_, ?_, ?_, ?_⟩,rootcount.symm⟩
  · rw [decomp,card_union_of_disjoint dis,card_image_of_injOn ri,card_image_of_injOn pi] at size
    exact size
  · intro v
    simpa only [rootcount,actualDegree] using minroot v.castSucc
  · intro v
    rw [← actualDegree]
    exact maxdeg _
  · intro k i j hk hi hj hmask hk0
    by_contra! omitted
    have hnot (i) (hi : i < 56) (h : i ∉ B) : plainTriple i ∉ F := fun hF =>
      h (mem_filter.mpr ⟨mem_range.mpr hi,hF⟩)
    have hsplit : rootTriple k ∪ plainTriple i ∪ plainTriple j = univ := by
      apply eq_univ_of_forall
      intro x
      by_cases hx : x = 8
      · subst x
        exact mem_union_left _ (mem_union_left _ (root_table ⟨k,hk⟩).2.1)
      have hlt : x.val < 8 := by
        have hval : x.val ≠ 8 := fun h => hx (Fin.ext h)
        have := x.isLt
        omega
      let v : Fin 8 := ⟨x.val,hlt⟩
      have eq : v.castSucc = x := rfl
      have h255 : (255 : ℕ).testBit v.val :=
        (by decide : ∀ a : Fin 8, (255 : ℕ).testBit a.val = true) v
      rw [← hmask,Nat.testBit_or,Nat.testBit_or] at h255
      simp only [Bool.or_eq_true] at h255
      rcases h255 with (h|h)|h
      · exact mem_union_left _ (mem_union_left _ (eq ▸ ((root_table ⟨k,hk⟩).2.2 v).mpr h))
      · exact mem_union_left _ (mem_union_right _ (mem_decode.mpr h))
      · exact mem_union_right _ (mem_decode.mpr h)
    apply bad
    refine ⟨_,_,_,(root_table ⟨k,hk⟩).1,(plain_table ⟨i,hi⟩).1,(plain_table ⟨j,hj⟩).1,
      hsplit,?_,hnot i hi omitted.1,hnot j hj omitted.2⟩
    intro hr
    have := mem_bits.mp ((root k hk).mpr hr)
    simp [hk0] at this
  · apply h5.trans (card_le_card ?_)
    intro x hx
    apply mem_filter.mpr
    refine ⟨mem_univ _,fun y hxy => ?_⟩
    obtain ⟨t,ht,hxt,hyt⟩ := hc x hx y hxy
    rw [decomp] at ht
    rcases mem_union.mp ht with h|h
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      exact ⟨_,mem_union_left _ (mem_image_of_mem _ hk),mem_decode.mp hxt,mem_decode.mp hyt⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact ⟨_,mem_union_right _ (mem_image_of_mem _ hi),mem_decode.mp hxt,mem_decode.mp hyt⟩

end WildNumber.Nine.Census
