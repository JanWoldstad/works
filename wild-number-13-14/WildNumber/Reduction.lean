import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Choose

/-! Choosing the four-vertex block for the nine-vertex reduction. -/

namespace WildNumber.Reduction

open Finset

abbrev V := Fin 13
abbrev Edge := Finset V

/-- The six disjoint edges of each color, indexed by the vertex that color misses. -/
structure NamedClasses where
  edges : V → Finset Edge
  six : ∀ c, (edges c).card = 6
  pair : ∀ c e, e ∈ edges c → e.card = 2
  misses : ∀ c e, e ∈ edges c → c ∉ e
  matching : ∀ c, ∀ e ∈ edges c, ∀ f ∈ edges c, e ≠ f → Disjoint e f
  partition : ∀ e : Edge, e.card = 2 → ∃! c, e ∈ edges c

def fourSets : Finset (Finset V) := univ.powersetCard 4

def inside (M : NamedClasses) (D : Finset V) (c : V) : Finset Edge :=
  (M.edges c).filter (· ⊆ D)

def coloredEdges (M : NamedClasses) : Finset (Σ _ : V, Edge) := univ.sigma M.edges

def internalNames (M : NamedClasses) (D : Finset V) : Finset (Σ _ : V, Edge) :=
  (coloredEdges M).filter fun p => insert p.1 p.2 ⊆ D

def repeated (M : NamedClasses) : Finset (Finset V) :=
  univ.biUnion fun c : V => ((M.edges c).powersetCard 2).image fun es => es.biUnion id

theorem repeated_le (M : NamedClasses) : (repeated M).card ≤ 195 := by
  calc
    _ ≤ ∑ c : V, (((M.edges c).powersetCard 2).image fun es => es.biUnion id).card :=
      card_biUnion_le
    _ ≤ ∑ c : V, ((M.edges c).powersetCard 2).card := by
      gcongr
      exact card_image_le
    _ = 195 := by simp [card_powersetCard, M.six]; decide

theorem no_repeat (M : NamedClasses) {D : Finset V} (hD : D ∈ fourSets)
    (h : D ∉ repeated M) (c : V) : (inside M D c).card ≤ 1 := by
  by_contra! hc
  obtain ⟨e, he, f, hf, hne⟩ := one_lt_card.mp hc
  obtain ⟨hem, hed⟩ := mem_filter.mp he
  obtain ⟨hfm, hfd⟩ := mem_filter.mp hf
  have hunion : e ∪ f = D := by
    apply eq_of_subset_of_card_le (union_subset hed hfd)
    rw [card_union_of_disjoint (M.matching c e hem f hfm hne), M.pair c e hem, M.pair c f hfm,
      (mem_powersetCard.mp hD).2]
  apply h
  apply mem_biUnion.mpr
  refine ⟨c, mem_univ _, mem_image.mpr ⟨{e,f}, ?_, ?_⟩⟩
  · exact mem_powersetCard.mpr ⟨insert_subset hem (singleton_subset_iff.mpr hfm), by simp [hne]⟩
  · simpa using hunion

theorem high_le (M : NamedClasses) :
    (fourSets.filter fun D => 2 ≤ (internalNames M D).card).card ≤ 390 := by
  let bad := fourSets.filter fun D => 2 ≤ (internalNames M D).card
  let r (D : Finset V) (p : Σ _ : V, Edge) := insert p.1 p.2 ⊆ D
  have hlow (D) (hD : D ∈ bad) : 2 ≤ ((coloredEdges M).bipartiteAbove r D).card :=
    (mem_filter.mp hD).2
  have hhigh (p) (hp : p ∈ coloredEdges M) : (bad.bipartiteBelow r p).card ≤ 10 := by
    obtain ⟨_, hpc⟩ := mem_sigma.mp hp
    have h3 : (insert p.1 p.2).card = 3 := by
      rw [card_insert_of_notMem (M.misses p.1 p.2 hpc), M.pair p.1 p.2 hpc]
    calc
      _ ≤ (fourSets.filter (insert p.1 p.2 ⊆ ·)).card := by
        apply card_le_card
        intro D hD
        obtain ⟨hDb, hDr⟩ := (mem_bipartiteBelow _).mp hD
        exact mem_filter.mpr ⟨(mem_filter.mp hDb).1, hDr⟩
      _ = 10 := by
        rw [fourSets, card_filter_powersetCard_subset _ _ _ (subset_univ _) (by omega), h3]
        decide
  have h := card_nsmul_le_card_nsmul r hlow hhigh
  have hc : (coloredEdges M).card = 78 := by simp [coloredEdges, card_sigma, M.six]
  change bad.card * 2 ≤ (coloredEdges M).card * 10 at h
  rw [hc] at h
  change bad.card ≤ 390
  omega

def eligible (M : NamedClasses) : Finset (Finset V) :=
  fourSets \ (repeated M ∪ fourSets.filter fun D => 2 ≤ (internalNames M D).card)

theorem eligible_card (M : NamedClasses) : 130 ≤ (eligible M).card := by
  have ht : fourSets.card = 715 := by simp [fourSets, card_powersetCard]; decide
  have ha := repeated_le M
  have hb := high_le M
  have hu := card_union_le (repeated M) (fourSets.filter fun D => 2 ≤ (internalNames M D).card)
  have hd := card_le_card_sdiff_add_card (s := fourSets)
    (t := repeated M ∪ fourSets.filter fun D => 2 ≤ (internalNames M D).card)
  unfold eligible
  omega

theorem eligible_properties (M : NamedClasses) {D : Finset V} (h : D ∈ eligible M) :
    D.card = 4 ∧ (∀ c, (inside M D c).card ≤ 1) ∧ (internalNames M D).card ≤ 1 := by
  obtain ⟨hD, hbad⟩ := mem_sdiff.mp h
  have hn : D ∉ repeated M := fun he => hbad (mem_union_left _ he)
  refine ⟨(mem_powersetCard.mp hD).2, no_repeat M hD hn, ?_⟩
  by_contra! hhigh
  exact hbad (mem_union_right _ (mem_filter.mpr ⟨hD, hhigh⟩))

section ColorClasses
variable (col : V → V → V) (symm : ∀ x y, col x y = col y x)
  (diag : ∀ x, col x x = x) (inj : ∀ x, Function.Injective (col x))

noncomputable def edgeClass (c : V) : Finset Edge := by
  classical
  exact (univ.powersetCard 2).filter fun e =>
    ∃ a b : V, a ≠ b ∧ e = {a,b} ∧ col a b = c

theorem edgeClass_spec {c : V} {e : Edge} :
    e ∈ edgeClass col c ↔ ∃ a b : V, a ≠ b ∧ e = {a,b} ∧ col a b = c := by
  classical
  constructor
  · intro he
    exact (mem_filter.mp he).2
  · intro h
    obtain ⟨a,b,hab,rfl,habc⟩ := h
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, card_pair hab⟩,
      ⟨a,b,hab,rfl,habc⟩⟩

include symm in
theorem edge_at {c x : V} {e : Edge} (he : e ∈ edgeClass col c) (hx : x ∈ e) :
    ∃ y, x ≠ y ∧ col x y = c ∧ e = {x,y} := by
  obtain ⟨a,b,hab,rfl,hcol⟩ := (edgeClass_spec col).mp he
  rcases mem_insert.mp hx with rfl | hx
  · exact ⟨b,hab,hcol,rfl⟩
  · obtain rfl := eq_of_mem_singleton hx
    exact ⟨a, hab.symm, (symm _ _).trans hcol, pair_comm _ _⟩

include symm diag inj in
theorem class_misses {c : V} {e : Edge} (he : e ∈ edgeClass col c) : c ∉ e := by
  intro hc
  obtain ⟨y,hcy,hy,_⟩ := edge_at col symm he hc
  exact hcy (inj c ((diag c).trans hy.symm))

include symm inj in
theorem edges_eq_at {c x : V} {e f : Edge} (he : e ∈ edgeClass col c) (hx : x ∈ e)
    (hf : f ∈ edgeClass col c) (hx' : x ∈ f) : e = f := by
  obtain ⟨y,_,hy,rfl⟩ := edge_at col symm he hx
  obtain ⟨z,_,hz,rfl⟩ := edge_at col symm hf hx'
  rw [inj x (hy.trans hz.symm)]

include symm diag inj in
theorem class_six (c : V) : (edgeClass col c).card = 6 := by
  classical
  let vert := (univ : Finset V).erase c
  let edges := edgeClass col c
  let r (x : V) (e : Edge) := x ∈ e
  have h1 (x) (hx : x ∈ vert) : (edges.bipartiteAbove r x).card = 1 := by
    have hx' := ne_of_mem_erase hx
    obtain ⟨y,hy⟩ := Finite.surjective_of_injective (inj x) c
    have hxy : x ≠ y := by
      rintro rfl
      exact hx' ((diag x).symm.trans hy)
    have he : ({x,y} : Edge) ∈ edges := (edgeClass_spec col).mpr ⟨x,y,hxy,rfl,hy⟩
    apply card_eq_one_iff_existsUnique.mpr
    refine ⟨{x,y}, (mem_bipartiteAbove r).mpr ⟨he, mem_insert_self _ _⟩, ?_⟩
    intro f hf
    obtain ⟨hf',hxf⟩ := (mem_bipartiteAbove r).mp hf
    exact edges_eq_at col symm inj hf' hxf he (mem_insert_self _ _)
  have h2 (e) (he : e ∈ edges) : (vert.bipartiteBelow r e).card = 2 := by
    have hl : vert.bipartiteBelow r e = e := by
      ext x
      constructor
      · exact fun h => ((mem_bipartiteBelow r).mp h).2
      · intro hx
        exact (mem_bipartiteBelow r).mpr ⟨mem_erase.mpr
          ⟨fun h => class_misses col symm diag inj he (h ▸ hx), mem_univ _⟩, hx⟩
    rw [hl]
    obtain ⟨a,b,hab,rfl,_⟩ := (edgeClass_spec col).mp he
    exact card_pair hab
  have h := card_mul_eq_card_mul r h1 h2
  have hv : vert.card = 12 := by simp [vert, card_erase_of_mem]
  rw [hv] at h
  change edges.card = 6
  omega

noncomputable def namedClasses : NamedClasses where
  edges := edgeClass col
  six := class_six col symm diag inj
  pair c e he := by
    obtain ⟨a,b,hab,rfl,_⟩ := (edgeClass_spec col).mp he
    exact card_pair hab
  misses _ _ := class_misses col symm diag inj
  matching c e he f hf hne := Finset.disjoint_left.mpr fun _ hx hxf =>
    hne (edges_eq_at col symm inj he hx hf hxf)
  partition e he := by
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp he
    refine ⟨col a b, (edgeClass_spec col).mpr ⟨a,b,hab,rfl,rfl⟩, ?_⟩
    intro c hc
    obtain ⟨y,_,hy,hey⟩ := edge_at col symm hc (mem_insert_self _ _)
    have hb : b ∈ ({a,y} : Edge) := hey ▸ (show b ∈ ({a,b} : Edge) by simp)
    obtain rfl : b = y := by simpa [Ne.symm hab] using hb
    exact hy.symm

end ColorClasses

end WildNumber.Reduction
