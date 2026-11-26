import WildNumber.Lift
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace WildNumber

/-- The complete graph admits a proper edge coloring from a palette of size `k`.
Diagonal values are ignored, as in `Coloring`. -/
def PaletteColorable (n k : ℕ) : Prop :=
  ∃ f : Fin n → Fin n → Fin k, (∀ x y, f x y = f y x) ∧
    ∀ x y z, x ≠ y → x ≠ z → f x y = f x z → y = z

theorem palette_thirteen_iff (n : ℕ) : PaletteColorable n 13 ↔ Nonempty (Coloring n) := by
  constructor
  · rintro ⟨f,h,p⟩
    exact ⟨⟨f,h,fun {x y z} => p x y z⟩⟩
  · rintro ⟨C⟩
    exact ⟨C.color,C.symm,fun _ _ _ => C.proper⟩

private def cyclic14 (x y : Fin 14) : Fin 13 :=
  ⟨(if x.val = 13 then 2 * y.val else if y.val = 13 then 2 * x.val else x.val + y.val) % 13,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private def cyclicColoring : Coloring 14 where
  color := cyclic14
  symm := by decide +kernel
  proper := by decide +kernel

private theorem neighbors_le_palette {n k : ℕ} (h : PaletteColorable (n+1) k) : n ≤ k := by
  obtain ⟨f,_,hp⟩ := h
  have hi : Function.Injective (fun i : Fin n => f (Fin.last n) i.castSucc) := by
    intro i j e
    exact Fin.castSucc_injective _ (hp _ _ _ (Fin.castSucc_ne_last i).symm
      (Fin.castSucc_ne_last j).symm e)
  simpa using Fintype.card_le_of_injective _ hi

/-- A 12-coloring would make each color a perfect matching on 13 vertices. -/
private theorem no_twelve : ¬ PaletteColorable 13 12 := by
  classical
  rintro ⟨f,hs,hp⟩
  let G : SimpleGraph (Fin 13) := {
    Adj := fun x y => x ≠ y ∧ f x y = 0
    symm := ⟨fun x y h => ⟨h.1.symm,(hs y x).trans h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have deg (v) : G.degree v = 1 := by
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    have hinj : Function.Injective (fun i : Fin 12 => f v (v.succAbove i)) := by
      intro i j eq
      exact Fin.succAbove_right_injective (hp _ _ _ (v.ne_succAbove _) (v.ne_succAbove _) eq)
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp hinj) 0
    exact ⟨v.succAbove i, ⟨v.ne_succAbove _,hi⟩,
      fun w hw => hp _ _ _ hw.1 (v.ne_succAbove _) (hw.2.trans hi.symm)⟩
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [deg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

theorem minimum_palette_thirteen : IsLeast {k | PaletteColorable 13 k} 13 := by
  refine ⟨(palette_thirteen_iff 13).mpr ⟨cyclicColoring.restrictLast⟩, ?_⟩
  intro k (h : PaletteColorable 13 k)
  have hk : 12 ≤ k := neighbors_le_palette h
  by_contra! hn
  have eq : k = 12 := by omega
  exact no_twelve (eq ▸ h)

theorem minimum_palette_fourteen : IsLeast {k | PaletteColorable 14 k} 13 :=
  ⟨(palette_thirteen_iff 14).mpr ⟨cyclicColoring⟩, fun _ h => neighbors_le_palette h⟩

end WildNumber
