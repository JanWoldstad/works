import WildNumber.Reduction
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Cardinal bounds and center counts after all thirteen color classes are combined. -/

namespace WildNumber.Reduction
open Finset

def used (M : NamedClasses) (D : Finset V) : Finset V :=
  univ.filter fun c => (inside M D c).Nonempty

@[simp] theorem mem_used {M : NamedClasses} {D : Finset V} {c : V} :
    c ∈ used M D ↔ (inside M D c).Nonempty := by simp [used]

theorem used_six (M : NamedClasses) {D : Finset V} (hD : D ∈ eligible M) :
    (used M D).card = 6 := by
  obtain ⟨h4,hr,_⟩ := eligible_properties M hD
  let r (c : V) (e : Edge) := e ∈ M.edges c
  have hcolor (c) (hc : c ∈ used M D) : ((D.powersetCard 2).bipartiteAbove r c).card = 1 := by
    have he : (D.powersetCard 2).bipartiteAbove r c = inside M D c := by
      ext e
      constructor
      · intro h
        obtain ⟨he,her⟩ := (mem_bipartiteAbove r).mp h
        exact mem_filter.mpr ⟨her,(mem_powersetCard.mp he).1⟩
      · intro h
        obtain ⟨he,hs⟩ := mem_filter.mp h
        exact (mem_bipartiteAbove r).mpr ⟨mem_powersetCard.mpr ⟨hs,M.pair c e he⟩,he⟩
    rw [he]
    have hx := hr c
    have hy := card_pos.mpr (mem_used.mp hc)
    omega
  have hedge (e) (he : e ∈ D.powersetCard 2) : ((used M D).bipartiteBelow r e).card = 1 := by
    obtain ⟨c,hc,hu⟩ := M.partition e (mem_powersetCard.mp he).2
    apply card_eq_one_iff_existsUnique.mpr
    refine ⟨c, (mem_bipartiteBelow r).mpr ⟨mem_used.mpr ⟨e,mem_filter.mpr
      ⟨hc,(mem_powersetCard.mp he).1⟩⟩,hc⟩, ?_⟩
    intro b hb
    exact hu b ((mem_bipartiteBelow r).mp hb).2
  have h := card_mul_eq_card_mul r hcolor hedge
  simpa [card_powersetCard,h4,show Nat.choose 4 2 = 6 by decide] using h

theorem used_in_block_le_one (M : NamedClasses) {D : Finset V} (hD : D ∈ eligible M) :
    ((used M D) ∩ D).card ≤ 1 := by
  have hs : used M D ∩ D ⊆ (internalNames M D).image Sigma.fst := by
    intro c hc
    obtain ⟨hused,hcD⟩ := mem_inter.mp hc
    obtain ⟨e,he⟩ := mem_used.mp hused
    obtain ⟨he,hs⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨⟨c,e⟩, mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_univ _,he⟩,
      insert_subset hcD hs⟩,rfl⟩
  exact (card_le_card hs).trans (card_image_le.trans (eligible_properties M hD).2.2)

theorem five_centers (M : NamedClasses) {D : Finset V} (hD : D ∈ eligible M) :
    5 ≤ (used M D \ D).card := by
  have h := card_sdiff_add_card_inter (used M D) D
  have h1 := used_six M hD
  have h2 := used_in_block_le_one M hD
  omega

private theorem sum_of_mem (S : Finset V) (w : ℕ) :
    (∑ c : V, if c ∈ S then w else 0) = S.card * w := by
  rw [← sum_filter]
  simp

/-- Each class contributes at most one, two or four forbidden triples according
to the location of its name and whether it appears inside the four-set. -/
theorem total_bad_le (M : NamedClasses) {D : Finset V} (hD : D ∈ eligible M)
    (f : V → Finset (Finset V))
    (hf : ∀ c, (f c).card ≤ if c ∈ used M D then 4 else if c ∈ D then 1 else 2) :
    (univ.biUnion f).card ≤ 35 := by
  have h4 := (eligible_properties M hD).1
  have h6 := used_six M hD
  have h1 := used_in_block_le_one M hD
  have h9 : Dᶜ.card = 9 := by simp [card_compl, h4]
  have hb (c : V) : (f c).card ≤ 1 + (if c ∈ Dᶜ then 1 else 0) +
      (if c ∈ used M D then 2 else 0) + (if c ∈ used M D ∩ D then 1 else 0) := by
    have hc := hf c
    by_cases h : c ∈ used M D <;> by_cases h' : c ∈ D <;> simp [h,h'] at hc ⊢ <;> omega
  calc
    _ ≤ ∑ c : V, (f c).card := card_biUnion_le
    _ ≤ ∑ c : V, (1 + (if c ∈ Dᶜ then 1 else 0) + (if c ∈ used M D then 2 else 0) +
        (if c ∈ used M D ∩ D then 1 else 0)) := sum_le_sum fun c _ => hb c
    _ ≤ 35 := by
      simp only [sum_add_distrib, sum_of_mem, sum_const, card_univ, Fintype.card_fin,
        show 13 • (1 : ℕ) = 13 by decide, mul_one, h9,h6]
      omega

/-- A point may receive four incidences from its own color and from one
exceptional color, and at most one from every other color. -/
theorem bad_degree_le (M : NamedClasses) {D : Finset V} (hD : D ∈ eligible M)
    (f : V → Finset (Finset V)) (v : V)
    (hf : ∀ c, ((f c).filter (v ∈ ·)).card ≤
      if v = c ∨ c ∈ used M D ∩ D then 4 else 1) :
    ((univ.biUnion f).filter (v ∈ ·)).card ≤ 19 := by
  have hs := used_in_block_le_one M hD
  have hb (c : V) : ((f c).filter (v ∈ ·)).card ≤ 1 +
      (if c ∈ ({v} : Finset V) then 3 else 0) + (if c ∈ used M D ∩ D then 3 else 0) := by
    have hc := hf c
    by_cases h : c = v
    · subst c
      by_cases h' : v ∈ used M D ∩ D <;>
        simp only [mem_singleton, h', true_or, ite_true, ite_false, Nat.reduceAdd] at hc ⊢ <;> omega
    · by_cases h' : c ∈ used M D ∩ D <;>
        simp only [mem_singleton, h, Ne.symm h, h', false_or, ite_true, ite_false,
          Nat.reduceAdd] at hc ⊢ <;> omega
  rw [filter_biUnion]
  calc
    _ ≤ ∑ c : V, ((f c).filter (v ∈ ·)).card := card_biUnion_le
    _ ≤ ∑ c : V, (1 + (if c ∈ ({v} : Finset V) then 3 else 0) +
      (if c ∈ used M D ∩ D then 3 else 0)) := sum_le_sum fun c _ => hb c
    _ ≤ 19 := by
      simp only [sum_add_distrib, sum_of_mem, sum_const, card_univ, Fintype.card_fin,
        show 13 • (1 : ℕ) = 13 by decide, card_singleton, one_mul]
      omega

end WildNumber.Reduction
