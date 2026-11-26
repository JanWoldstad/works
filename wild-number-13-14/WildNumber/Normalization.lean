import WildNumber.Graph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.EquivFin

namespace WildNumber

/-- The color is absent from all genuine edges at the vertex. -/
def Misses (C : Coloring 13) (v c : Fin 13) : Prop :=
  ∀ w, v ≠ w → C.color v w ≠ c

theorem unique_missing_color (C : Coloring 13) (v : Fin 13) : ∃! c, Misses C v c := by
  classical
  let others := (Finset.univ : Finset (Fin 13)).erase v
  let used := others.image (C.color v)
  have hc : used.card = 12 := by
    have hi : Set.InjOn (C.color v) others := by
      intro x hx y hy hxy
      exact C.proper (Finset.ne_of_mem_erase hx).symm (Finset.ne_of_mem_erase hy).symm hxy
    dsimp [used]
    rw [Finset.card_image_of_injOn hi]
    simp [others, Finset.card_erase_of_mem]
  have h1 : usedᶜ.card = 1 := by simp [Finset.card_compl, hc]
  have hm (c : Fin 13) : c ∈ usedᶜ ↔ Misses C v c := by
    simp [used, others, Misses, eq_comm (a := v)]
  obtain ⟨c, hc', hu⟩ := Finset.card_eq_one_iff_existsUnique.mp h1
  exact ⟨c, (hm c).1 hc', fun d hd => hu d ((hm d).2 hd)⟩

noncomputable def missingColor (C : Coloring 13) (v : Fin 13) : Fin 13 :=
  (unique_missing_color C v).exists.choose

theorem missingColor_spec (C : Coloring 13) (v : Fin 13) : Misses C v (missingColor C v) :=
  (unique_missing_color C v).exists.choose_spec

/-- Each individual color misses a vertex: a perfect matching on 13 points
would have degree sum 13, whereas every graph has even degree sum. -/
theorem exists_missing_vertex (C : Coloring 13) (c : Fin 13) : ∃ v, Misses C v c := by
  classical
  by_contra! hn
  let G := joined C ∅ c
  have hd (v : Fin 13) : G.degree v = 1 := by
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    have h := hn v
    simp only [Misses, not_forall, not_not] at h
    obtain ⟨w, hvw, hw⟩ := h
    refine ⟨w, ⟨hvw, Or.inl hw⟩, ?_⟩
    intro z hz
    change v ≠ z ∧ (C.color v z = c ∨ s(v,z) ∈ (∅ : Finset _)) at hz
    exact C.proper hz.1 hvw ((hz.2.resolve_right (Finset.notMem_empty _)).trans hw.symm)
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  omega

noncomputable def missingEquiv (C : Coloring 13) : Fin 13 ≃ Fin 13 :=
  Equiv.ofBijective (missingColor C) (Finite.surjective_iff_bijective.mp (by
    intro c
    obtain ⟨v, hv⟩ := exists_missing_vertex C c
    exact ⟨v, (unique_missing_color C v).unique (missingColor_spec C v) hv⟩))

/-- Rename the colors by their missed vertices and fill in the diagonal. -/
noncomputable def normalizedColor (C : Coloring 13) (v w : Fin 13) : Fin 13 :=
  if v = w then v else (missingEquiv C).symm (C.color v w)

@[simp] theorem normalizedColor_diag (C : Coloring 13) (v : Fin 13) :
    normalizedColor C v v = v := by simp [normalizedColor]

theorem normalizedColor_symm (C : Coloring 13) (v w : Fin 13) :
    normalizedColor C v w = normalizedColor C w v := by
  by_cases h : v = w
  · subst w; rfl
  · simp [normalizedColor, h, Ne.symm h, C.symm v w]

theorem normalizedColor_injective (C : Coloring 13) (v : Fin 13) :
    Function.Injective (normalizedColor C v) := by
  intro x y h
  have hf (w : Fin 13) (hn : v ≠ w) : normalizedColor C v w ≠ v := by
    intro he
    have hc := congrArg (missingEquiv C) he
    simp [normalizedColor, hn] at hc
    exact missingColor_spec C v w hn hc
  by_cases hx : v = x
  · subst x
    by_contra hy
    exact hf y hy (h.symm.trans (normalizedColor_diag C v))
  by_cases hy : v = y
  · subst y
    exact False.elim (hf x hx (h.trans (normalizedColor_diag C v)))
  apply C.proper hx hy
  apply (missingEquiv C).symm.injective
  simpa [normalizedColor, hx, hy] using h

noncomputable def normalize (C : Coloring 13) : Coloring 13 where
  color := normalizedColor C
  symm := normalizedColor_symm C
  proper := fun {u _ _} _ _ h => normalizedColor_injective C u h

theorem upper_of_normalize {C : Coloring 13} {k : ℕ} (h : Upper (normalize C) k) : Upper C k := by
  obtain ⟨W, hv, hk, hh⟩ := h
  refine ⟨W, hv, hk, fun c => ?_⟩
  have he : joined C W c = joined (normalize C) W ((missingEquiv C).symm c) := by
    ext u v
    by_cases hn : u = v
    · subst v; simp
    · change (_ ∧ (_ ∨ _)) ↔ (_ ∧ (_ ∨ _))
      simp [normalize, normalizedColor, hn]
  rw [he]
  exact hh _

end WildNumber
