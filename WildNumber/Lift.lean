import WildNumber.Graph
import Mathlib.Data.Fin.SuccPred

namespace WildNumber

/-- Delete the last vertex of the complete graph. -/
def Coloring.restrictLast {n : ℕ} (C : Coloring (n+1)) : Coloring n where
  color x y := C.color x.castSucc y.castSucc
  symm x y := C.symm x.castSucc y.castSucc
  proper h₁ h₂ h := Fin.castSucc_injective _ (C.proper
    (fun e => h₁ (Fin.castSucc_injective _ e))
    (fun e => h₂ (Fin.castSucc_injective _ e)) h)

/-- In a minimum coloring of the 14-vertex graph every color occurs at
the deleted vertex. This uses injectivity at that vertex and the fact that
it has exactly 13 neighbors. -/
theorem Coloring.neighbor_last (C : Coloring 14) (c : Fin 13) :
    ∃ x : Fin 13, C.color (Fin.last 13) x.castSucc = c := by
  apply ((Finite.injective_iff_surjective
    (f := fun x : Fin 13 => C.color (Fin.last 13) x.castSucc)).mp ?_) c
  intro x y h
  exact Fin.castSucc_injective _ (C.proper (Fin.castSucc_ne_last x).symm
    (Fin.castSucc_ne_last y).symm h)

/-- Restoring the deleted vertex costs no additional wild edge. -/
theorem upper_restore (C : Coloring 14) (k : ℕ) (h : Upper C.restrictLast k) :
    Upper C k := by
  classical
  obtain ⟨W, valid, bound, connects⟩ := h
  let incl := @Fin.castSucc 13
  let W' := W.image (Sym2.map incl)
  refine ⟨W', ?_, Finset.card_image_le.trans bound, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact fun hd => valid f hf ((Sym2.isDiag_map (Fin.castSucc_injective _)).mp hd)
  intro c
  let embed : (joined C.restrictLast W c) →g (joined C W' c) := {
    toFun := incl
    map_rel' := by
      intro x y h
      obtain ⟨hxy, hc | hw⟩ := h
      · exact ⟨(Fin.castSucc_injective _).ne hxy, Or.inl hc⟩
      · exact ⟨(Fin.castSucc_injective _).ne hxy,
          Or.inr (Finset.mem_image_of_mem (Sym2.map incl) hw)⟩ }
  obtain ⟨t, htc⟩ := C.neighbor_last c
  have allFrom (v : Fin 14) : (joined C W' c).Reachable t.castSucc v := by
    refine Fin.lastCases ?_ (fun x => ?_) v
    · have adj : (joined C W' c).Adj (Fin.last 13) t.castSucc :=
        ⟨(Fin.castSucc_ne_last t).symm, Or.inl htc⟩
      exact adj.reachable.symm
    · exact (connects c t x).map embed
  exact fun x y => (allFrom x).symm.trans (allFrom y)

theorem upper_fourteen_of_thirteen (h : ∀ C : Coloring 13, Upper C 9)
    (C : Coloring 14) : Upper C 9 :=
  upper_restore C 9 (h C.restrictLast)

end WildNumber
