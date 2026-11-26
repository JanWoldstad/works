import WildNumber.FiniteCoordinates
import WildNumber.Orbit.Data
import Mathlib.Logic.Equiv.Fin.Basic

/-! Choose a point of minimum bad degree and relabel its eight-point link. -/
namespace WildNumber.Nine.Census
open Finset

private structure Counterexample (F : Family) : Prop where
  typed : ∀ t ∈ F, t.card = 3
  size : F.card ≤ 35
  degree : ∀ v, (F.filter (v ∈ ·)).card ≤ 19
  centers : ∃ C : Finset Point, 5 ≤ C.card ∧ ∀ x ∈ C, CoversPairs F x
  bad : ¬ GoodSplit F

private def rename (p : Equiv.Perm Point) (F : Family) : Family :=
  F.map p.finsetCongr.toEmbedding

private theorem mem_rename (p : Equiv.Perm Point) (F : Family) (t) :
    t ∈ rename p F ↔ t.map p.symm.toEmbedding ∈ F :=
  mem_map_equiv

private theorem rename_degree (p : Equiv.Perm Point) (F : Family) (v) :
    ((rename p F).filter (v ∈ ·)).card = (F.filter (p.symm v ∈ ·)).card := by
  rw [rename, filter_map, card_map]
  congr 1
  apply filter_congr
  intro t _
  exact mem_map_equiv

private theorem rename_preserves {F : Family} (H : Counterexample F) (p : Equiv.Perm Point) :
    Counterexample (rename p F) := by
  classical
  refine ⟨?_,by simpa [rename] using H.size, ?_, ?_, ?_⟩
  · intro t ht
    simpa using H.typed _ ((mem_rename p F t).mp ht)
  · intro v
    rw [rename_degree]
    exact H.degree _
  · obtain ⟨C,h5,hc⟩ := H.centers
    refine ⟨C.map p.toEmbedding,by simpa using h5,?_⟩
    intro x hx y hxy
    obtain ⟨t,ht,hx',hy'⟩ := hc (p.symm x) (mem_map_equiv.mp hx) (p.symm y)
      (fun h => hxy (p.symm.injective h))
    exact ⟨t.map p.toEmbedding,mem_map.mpr ⟨t,ht,rfl⟩,mem_map_equiv.mpr hx',mem_map_equiv.mpr hy'⟩
  · rintro ⟨t,u,v,ht,hu,hv,union,gt,gu,gv⟩
    apply H.bad
    refine ⟨t.map p.symm.toEmbedding,u.map p.symm.toEmbedding,v.map p.symm.toEmbedding,
      by simpa using ht,by simpa using hu,by simpa using hv,?_,
      fun h => gt ((mem_rename p F _).mpr h),fun h => gu ((mem_rename p F _).mpr h),
      fun h => gv ((mem_rename p F _).mpr h)⟩
    rw [← map_union,← map_union,union]
    simp

private theorem exists_smallest {F : Family} (H : Counterexample F) :
    ∃ r : Point, (F.filter (r ∈ ·)).card ≤ 11 ∧
      ∀ v, (F.filter (r ∈ ·)).card ≤ (F.filter (v ∈ ·)).card := by
  classical
  obtain ⟨r,_,hr⟩ := exists_min_image (univ : Finset Point)
    (fun v => (F.filter (v ∈ ·)).card) univ_nonempty
  have hmin (v) := hr v (mem_univ _)
  let R (v : Point) (t : Finset Point) := v ∈ t
  have hb (t) (ht : t ∈ F) : (univ.bipartiteBelow R t).card ≤ 3 := by
    simpa [R,bipartiteBelow] using (H.typed t ht).le
  have ha (v) (_ : v ∈ (univ : Finset Point)) :
      (F.filter (r ∈ ·)).card ≤ (F.bipartiteAbove R v).card := hmin v
  have hd := card_mul_le_card_mul R ha hb
  have h9 : (univ : Finset Point).card = 9 := by decide
  rw [h9] at hd
  have hs := H.size
  exact ⟨r,by omega,hmin⟩

private def up : Fin 8 ↪ Point := Fin.castSuccEmb

private def low (t : Finset Point) : Finset (Fin 8) := univ.filter fun i => i.castSucc ∈ t

private theorem low_map (t : Finset Point) : (low t).map up = t.erase 8 := by
  ext x
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := mem_map.mp h
    have ne : up i ≠ 8 := by
      change i.castSucc ≠ Fin.last 8
      exact Fin.castSucc_ne_last _
    exact mem_erase.mpr ⟨ne,(mem_filter.mp hi).2⟩
  · intro h
    obtain ⟨hn,ht⟩ := mem_erase.mp h
    have hlt : x.val < 8 := by
      have hval : x.val ≠ 8 := fun h => hn (Fin.ext h)
      have := x.isLt
      omega
    exact mem_map.mpr ⟨⟨x.val,hlt⟩,mem_filter.mpr ⟨mem_univ _,ht⟩,rfl⟩

private def link (F : Family) : Finset (Finset (Fin 8)) :=
  (F.filter ((8 : Point) ∈ ·)).image low

private theorem link_mem (F : Family) (x y : Fin 8) :
    {x,y} ∈ link F ↔ ({8,x.castSucc,y.castSucc} : Finset Point) ∈ F := by
  constructor
  · intro h
    obtain ⟨t,ht,eq⟩ := mem_image.mp h
    have hmap := congrArg (map up) eq
    rw [low_map] at hmap
    have hfull := insert_erase (mem_filter.mp ht).2
    rw [hmap] at hfull
    have ht' : insert 8 (({x,y} : Finset (Fin 8)).map up) ∈ F := by
      rw [hfull]
      exact (mem_filter.mp ht).1
    simpa [up] using ht'
  · intro h
    refine mem_image.mpr ⟨_,mem_filter.mpr ⟨h,by simp⟩,?_⟩
    apply (map_injective up)
    rw [low_map]
    have hx : (8 : Point) ≠ x.castSucc := (Fin.castSucc_ne_last x).symm
    have hy : (8 : Point) ≠ y.castSucc := (Fin.castSucc_ne_last y).symm
    simp [up,hx,hy]

private def extend (p : Equiv.Perm (Fin 8)) : Equiv.Perm Point :=
  (finSuccEquivLast.trans p.optionCongr).trans finSuccEquivLast.symm

@[simp] private theorem extend_last (p : Equiv.Perm (Fin 8)) : (extend p).symm 8 = 8 := by
  change finSuccEquivLast.symm (Option.map p.symm (finSuccEquivLast (Fin.last 8))) = Fin.last 8
  rw [finSuccEquivLast_last]
  exact finSuccEquivLast_symm_none

@[simp] private theorem extend_cast (p : Equiv.Perm (Fin 8)) (x : Fin 8) :
    (extend p).symm x.castSucc = (p.symm x).castSucc := by
  change finSuccEquivLast.symm (Option.map p.symm (finSuccEquivLast x.castSucc)) = _
  rw [finSuccEquivLast_castSucc]
  exact finSuccEquivLast_symm_some _

private theorem endpoints :
    ∀ k : Fin 28, ∃ x y : Fin 8, x ≠ y ∧ Orbit.pairIndex x y = k.val ∧
      rootTriple k = {8,x.castSucc,y.castSucc} := by decide +kernel

/-- The enumeration of canonical links and a refutation of every numeric
model together imply the abstract nine-point theorem. -/
theorem split_of_orbits
    (canon : ∀ (S : Finset (Finset (Fin 8))), (∀ t ∈ S, t.card = 2) → S.card ≤ 11 →
      ∃ g ∈ Orbit.reps S.card, ∃ p : Equiv.Perm (Fin 8), ∀ x y, x ≠ y →
        ({x,y} ∈ S ↔ g.testBit (Orbit.pairIndex (p x) (p y)) = true))
    (bounded : ∀ d ≤ 11, ∀ g ∈ Orbit.reps d, g < 2 ^ 28)
    (noModel : ∀ d ≤ 11, ∀ g ∈ Orbit.reps d, ∀ B, ¬ NumericModel g B)
    (F : Family) (ht : ∀ t ∈ F, t.card = 3) (hs : F.card ≤ 35)
    (hd : ∀ v, (F.filter (v ∈ ·)).card ≤ 19) (C : Finset Point) (hc : 5 ≤ C.card)
    (centers : ∀ x ∈ C, CoversPairs F x) : GoodSplit F := by
  classical
  by_contra bad
  have H : Counterexample F := ⟨ht,hs,hd,⟨C,hc,centers⟩,bad⟩
  obtain ⟨r,small,hmin⟩ := exists_smallest H
  let s := Equiv.swap r (8 : Point)
  let G := rename s F
  have HG := rename_preserves H s
  have base : (G.filter ((8 : Point) ∈ ·)).card = (F.filter (r ∈ ·)).card := by
    simp [G,rename_degree,s]
  have ls : (link G).card ≤ 11 := (card_image_le.trans (base.le.trans small))
  have lp (t) (h : t ∈ link G) : t.card = 2 := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp h
    obtain ⟨htF,ht8⟩ := mem_filter.mp ht
    rw [← card_map up,low_map,card_erase_of_mem ht8,HG.typed t htF]
  obtain ⟨g,hg,p,hadj⟩ := canon (link G) lp ls
  let K := rename (extend p) G
  have HK := rename_preserves HG (extend p)
  have hr (v) : (K.filter ((8 : Point) ∈ ·)).card ≤ (K.filter (v ∈ ·)).card := by
    change ((rename (extend p) G).filter ((8 : Point) ∈ ·)).card ≤
      ((rename (extend p) G).filter (v ∈ ·)).card
    rw [rename_degree (extend p) G 8,rename_degree (extend p) G v,extend_last,base,
      rename_degree s F]
    exact hmin _
  have hroot (k) (hk : k < 28) : k ∈ bits g ↔ rootTriple k ∈ K := by
    obtain ⟨x,y,hxy,idx,shape⟩ := endpoints ⟨k,hk⟩
    have hh := hadj (p.symm x) (p.symm y) (fun h => hxy (p.symm.injective h))
    rw [p.apply_symm_apply,p.apply_symm_apply,idx] at hh
    change k ∈ bits g ↔ rootTriple k ∈ rename (extend p) G
    rw [mem_bits,← hh,link_mem,mem_rename (extend p) G,shape]
    simp [extend_last,extend_cast]
  obtain ⟨C',h5,hcent⟩ := HK.centers
  obtain ⟨B,model,_⟩ := numeric_of_canonical K HK.typed HK.size HK.degree hr C' h5
    hcent HK.bad g (bounded _ ls _ hg) hroot
  exact noModel _ ls _ hg B model

end WildNumber.Nine.Census
