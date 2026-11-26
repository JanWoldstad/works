import WildNumber.ReductionAssembly

/-! The two abstract nine-point endgames. Each label has a matching of the
prescribed size. No extension of these matchings to thirteen vertices is assumed. -/
namespace WildNumber.Nine
open Finset

structure PartialMatching where
  edges : Finset (Finset Point)
  pair : ∀ e ∈ edges, e.card = 2
  disjoint : (edges : Set (Finset Point)).PairwiseDisjoint id

namespace PartialMatching
def support (M : PartialMatching) : Finset Point := M.edges.biUnion id
def triples (M : PartialMatching) (c : Point) : Family := M.edges.image (insert c)

theorem support_card (M : PartialMatching) : M.support.card = 2 * M.edges.card := by
  rw [support, card_biUnion M.disjoint]
  simp only [id_eq, sum_congr rfl M.pair, sum_const]
  exact Nat.mul_comm _ _

theorem covered {M : PartialMatching} {e : Finset Point} (he : e ∈ M.edges) :
    e ⊆ M.support := fun _ h => mem_biUnion.mpr ⟨e,he,h⟩

theorem triples_size (M : PartialMatching) (c : Point) : (M.triples c).card ≤ M.edges.card :=
  card_image_le

theorem triples_typed {M : PartialMatching} {c : Point} (miss : c ∉ M.support)
    {t : Finset Point} (ht : t ∈ M.triples c) : t.card = 3 := by
  obtain ⟨e,he,rfl⟩ := mem_image.mp ht
  rw [card_insert_of_notMem (fun h => miss (covered he h)),M.pair e he]

theorem triples_degree {M : PartialMatching} {c v : Point} (hne : v ≠ c) :
    ((M.triples c).filter (v ∈ ·)).card ≤ 1 := by
  apply card_le_one_iff.mpr
  intro s t hs ht
  obtain ⟨hs,hvs⟩ := mem_filter.mp hs
  obtain ⟨ht,hvt⟩ := mem_filter.mp ht
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hs
  obtain ⟨b,hb,rfl⟩ := mem_image.mp ht
  congr 1
  by_contra hab
  exact disjoint_left.mp (M.disjoint ha hb hab) ((mem_insert.mp hvs).resolve_left hne)
    ((mem_insert.mp hvt).resolve_left hne)

theorem exists_missed (M : PartialMatching) (h : M.edges.card = 4) : ∃ x, x ∉ M.support := by
  have h1 : M.supportᶜ.card = 1 := by simp [card_compl,M.support_card,h]
  obtain ⟨x,hx⟩ := card_pos.mp (show 0 < M.supportᶜ.card by omega)
  exact ⟨x,mem_compl.mp hx⟩
end PartialMatching

/-- The nine named colors miss their own point. A heavy named color has
three pairs, a light one has two. Of the four other colors, k have four
pairs and the others have three. -/
structure Endgame (k : ℕ) where
  heavy : Finset Point
  heavy_count : heavy.card + k = 6
  special : Finset (Fin 4)
  special_count : special.card = k
  named : Point → PartialMatching
  outside : Fin 4 → PartialMatching
  misses : ∀ c, c ∉ (named c).support
  named_count : ∀ c, (named c).edges.card = if c ∈ heavy then 3 else 2
  outside_count : ∀ c, (outside c).edges.card = if c ∈ special then 4 else 3

namespace Endgame
variable {k : ℕ} (A : Endgame k)

def namedBad (c : Point) : Family :=
  if c ∈ A.heavy then insert (A.named c).supportᶜ ((A.named c).triples c)
  else (A.named c).triples c

noncomputable def specialPoint (c : Fin 4) (h : c ∈ A.special) : Point :=
  ((A.outside c).exists_missed (by simpa [h] using A.outside_count c)).choose

noncomputable def outsideBad (c : Fin 4) : Family :=
  if h : c ∈ A.special then (A.outside c).triples (A.specialPoint c h)
  else {(A.outside c).supportᶜ}

noncomputable def forbidden : Family :=
  (univ.biUnion A.namedBad) ∪ (univ.biUnion A.outsideBad)

private theorem special_missed (c : Fin 4) (h : c ∈ A.special) :
    A.specialPoint c h ∉ (A.outside c).support :=
  ((A.outside c).exists_missed (by simpa [h] using A.outside_count c)).choose_spec

private theorem typed_named (c) {t} (ht : t ∈ A.namedBad c) : t.card = 3 := by
  by_cases h : c ∈ A.heavy
  · rw [namedBad,ite_eq_left h] at ht
    rcases mem_insert.mp ht with rfl | ht
    · simp [card_compl,PartialMatching.support_card,A.named_count,h]
    · exact PartialMatching.triples_typed (A.misses c) ht
  · rw [namedBad,ite_eq_right h] at ht
    exact PartialMatching.triples_typed (A.misses c) ht

private theorem typed_outside (c) {t} (ht : t ∈ A.outsideBad c) : t.card = 3 := by
  by_cases h : c ∈ A.special
  · rw [outsideBad,dite_eq_left h] at ht
    exact PartialMatching.triples_typed (A.special_missed c h) ht
  · rw [outsideBad,dite_eq_right h,mem_singleton] at ht
    subst t
    simp [card_compl,PartialMatching.support_card,A.outside_count,h]

private theorem size_named (c) : (A.namedBad c).card ≤ 2 + (if c ∈ A.heavy then 2 else 0) := by
  have hb := (A.named c).triples_size c
  have hn := A.named_count c
  by_cases h : c ∈ A.heavy
  · have hh := card_insert_le (A.named c).supportᶜ ((A.named c).triples c)
    simp [namedBad,h] at hn ⊢
    omega
  · simpa [namedBad,h,hn] using hb

private theorem size_outside (c) : (A.outsideBad c).card ≤ 1 + (if c ∈ A.special then 3 else 0) := by
  by_cases h : c ∈ A.special
  · simpa [outsideBad,h,A.outside_count] using (A.outside c).triples_size (A.specialPoint c h)
  · simp [outsideBad,h]

private theorem degree_named (c v : Point) :
    ((A.namedBad c).filter (v ∈ ·)).card ≤ 1 + (if c = v then 3 else 0) := by
  by_cases hcv : c = v
  · subst v
    have h1 := card_le_card (filter_subset (c ∈ ·) (A.namedBad c))
    have h2 := A.size_named c
    split at h2 <;> simp only [ite_true,Nat.reduceAdd] <;> omega
  · have hd := PartialMatching.triples_degree (M := A.named c) (Ne.symm hcv)
    simp only [hcv,ite_false, Nat.add_zero]
    by_cases h : c ∈ A.heavy
    · rw [namedBad,ite_eq_left h]
      by_cases hv : v ∈ (A.named c).support
      · simpa [filter_insert, hv] using hd
      · have he : ((A.named c).triples c).filter (v ∈ ·) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨ht,hv'⟩ := mem_filter.mp ht
          obtain ⟨e,he,rfl⟩ := mem_image.mp ht
          exact hv (PartialMatching.covered he ((mem_insert.mp hv').resolve_left (Ne.symm hcv)))
        simp [filter_insert,hv,he]
    · simpa [namedBad,h] using hd

private theorem degree_outside (c : Fin 4) (v : Point) :
    ((A.outsideBad c).filter (v ∈ ·)).card ≤ 1 + (if c ∈ A.special then 3 else 0) :=
  (card_le_card (filter_subset _ _)).trans (A.size_outside c)

private theorem sum_mem {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (w : ℕ) :
    (∑ c : α, if c ∈ S then w else 0) = S.card * w := by
  rw [← sum_filter]; simp

private theorem centers (c : Point) (hc : c ∈ A.heavy) : CoversPairs A.forbidden c := by
  intro y hy
  have ins {t : Finset Point} (ht : t ∈ A.namedBad c) : t ∈ A.forbidden :=
    mem_union_left _ (mem_biUnion.mpr ⟨c,mem_univ _,ht⟩)
  by_cases h : y ∈ (A.named c).support
  · obtain ⟨e,he,hye⟩ := mem_biUnion.mp h
    refine ⟨insert c e,ins ?_,mem_insert_self _ _,mem_insert_of_mem hye⟩
    rw [namedBad,ite_eq_left hc]
    exact mem_insert_of_mem (mem_image_of_mem _ he)
  · refine ⟨_,ins ?_,mem_compl.mpr (A.misses c),mem_compl.mpr h⟩
    simp [namedBad,hc]

/-- Both endgames satisfy the same obstruction theorem. All cardinal and
degree bounds below are derived solely from the individual matchings. -/
theorem goodSplit (nine : Reduction.NinePointClaim) (hk : k ≤ 1) : GoodSplit A.forbidden := by
  classical
  have counts := A.heavy_count
  have special := A.special_count
  refine nine A.forbidden ?_ ?_ ?_ A.heavy (by omega) (A.centers)
  · intro t ht
    rcases mem_union.mp ht with h | h
    · obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
      exact A.typed_named c hc
    · obtain ⟨c,_,hc⟩ := mem_biUnion.mp h
      exact A.typed_outside c hc
  · have named : (univ.biUnion A.namedBad).card ≤ ∑ c : Point,
        (2 + (if c ∈ A.heavy then 2 else 0)) :=
      card_biUnion_le.trans (sum_le_sum fun c _ => A.size_named c)
    have outside : (univ.biUnion A.outsideBad).card ≤ ∑ c : Fin 4,
        (1 + (if c ∈ A.special then 3 else 0)) :=
      card_biUnion_le.trans (sum_le_sum fun c _ => A.size_outside c)
    simp only [sum_add_distrib, sum_mem, sum_const, card_univ, Fintype.card_fin,
      show 9 • (2 : ℕ) = 18 by decide,show 4 • (1 : ℕ) = 4 by decide] at named outside
    have hu := card_union_le (univ.biUnion A.namedBad) (univ.biUnion A.outsideBad)
    unfold forbidden
    omega
  · intro v
    have named : (univ.biUnion fun c => (A.namedBad c).filter (v ∈ ·)).card ≤
        ∑ c : Point, (1 + (if c = v then 3 else 0)) :=
      card_biUnion_le.trans (sum_le_sum fun c _ => A.degree_named c v)
    have outside : (univ.biUnion fun c => (A.outsideBad c).filter (v ∈ ·)).card ≤
        ∑ c : Fin 4, (1 + (if c ∈ A.special then 3 else 0)) :=
      card_biUnion_le.trans (sum_le_sum fun c _ => A.degree_outside c v)
    simp [sum_add_distrib] at named
    simp only [sum_add_distrib,sum_mem,sum_const,card_univ,Fintype.card_fin,
      show 4 • (1 : ℕ) = 4 by decide] at outside
    rw [forbidden,filter_union,filter_biUnion,filter_biUnion]
    apply le_trans (card_union_le _ _)
    omega

end Endgame

theorem A13_zero (nine : Reduction.NinePointClaim) (A : Endgame 0) : GoodSplit A.forbidden :=
  A.goodSplit nine (by decide)

theorem A13_one (nine : Reduction.NinePointClaim) (A : Endgame 1) : GoodSplit A.forbidden :=
  A.goodSplit nine (by decide)

end WildNumber.Nine
