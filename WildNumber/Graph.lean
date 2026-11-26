import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.FinCases

/-! Complete-graph edge colorings and wild edges. The value of a coloring
on the diagonal is immaterial: only pairs of distinct vertices are edges. -/
namespace WildNumber

structure Coloring (n : ℕ) where
  color : Fin n → Fin n → Fin 13
  symm : ∀ u v, color u v = color v u
  proper : ∀ {u v w}, u ≠ v → u ≠ w → color u v = color u w → v = w

def ValidWild {n : ℕ} (W : Finset (Sym2 (Fin n))) : Prop :=
  ∀ e ∈ W, ¬ e.IsDiag

def joined {n : ℕ} (C : Coloring n) (W : Finset (Sym2 (Fin n))) (c : Fin 13) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (C.color u v = c ∨ s(u,v) ∈ W)
  symm := ⟨fun u v h => ⟨Ne.symm h.1, h.2.imp (fun hc => (C.symm v u).trans hc)
    (fun he => (Sym2.eq_swap (a := u) (b := v)) ▸ he)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def Connects {n : ℕ} (C : Coloring n) (W : Finset (Sym2 (Fin n))) : Prop :=
  ∀ c, (joined C W c).Preconnected

def Upper {n : ℕ} (C : Coloring n) (k : ℕ) : Prop :=
  ∃ W, ValidWild W ∧ W.card ≤ k ∧ Connects C W

/-- A crossing of the indicated cut by an edge of color `c`. -/
def Crosses {n : ℕ} (C : Coloring n) (c : Fin 13) (S : Finset (Fin n)) : Prop :=
  ∃ u ∈ S, ∃ v ∉ S, C.color u v = c

end WildNumber
