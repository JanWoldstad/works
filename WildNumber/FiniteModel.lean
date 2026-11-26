import WildNumber.Finite
import Mathlib.Data.Nat.BitIndices

/-! Numeric coordinates for the nine-point obstruction. Point 8 is the
distinguished point. The remaining pairs and triples are in increasing order
of their eight-bit characteristic masks (colexicographic order). -/

namespace WildNumber.Nine.Census

def bits (m : ℕ) : Finset ℕ := m.bitIndices.toFinset

@[simp] theorem mem_bits {i m : ℕ} : i ∈ bits m ↔ m.testBit i := by
  simp [bits]

def edgeMasks : Array ℕ := #[3,5,6,9,10,12,17,18,20,24,33,34,36,40,48,65,66,68,72,80,96,129,130,132,136,144,160,192]

def tripleMasks : Array ℕ := #[7,11,13,14,19,21,22,25,26,28,35,37,38,41,42,44,49,50,52,56,67,69,70,73,74,76,81,82,84,88,97,98,100,104,112,131,133,134,137,138,140,145,146,148,152,161,162,164,168,176,193,194,196,200,208,224]

def edge (k : ℕ) := edgeMasks[k]?.getD 0
def triple (i : ℕ) := tripleMasks[i]?.getD 0

/-- Interpret the link edges and ordinary triples as nine-bit vertex masks. -/
def members (g : ℕ) (B : Finset ℕ) : Finset ℕ :=
  ((bits g).image fun k => 256 + edge k) ∪ B.image triple

def centerSet (g : ℕ) (B : Finset ℕ) : Finset (Fin 9) :=
  Finset.univ.filter fun x => ∀ y : Fin 9, x ≠ y →
    ∃ t ∈ members g B, t.testBit x.val ∧ t.testBit y.val

def degree (g : ℕ) (B : Finset ℕ) (v : Fin 8) : ℕ :=
  ((bits g).filter fun k => (edge k).testBit v.val).card +
  (B.filter fun i => (triple i).testBit v.val).card

/-- The requirements for a counterexample, after moving a vertex of minimum
degree to position 8. B contains precisely the chosen triples avoiding 8. -/
structure NumericModel (g : ℕ) (B : Finset ℕ) : Prop where
  valid : B ⊆ Finset.range 56
  budget : (bits g).card + B.card ≤ 35
  degree_min : ∀ v : Fin 8, (bits g).card ≤ degree g B v
  degree_max : ∀ v : Fin 8, degree g B v ≤ 19
  cover : ∀ k i j : ℕ, k < 28 → i < 56 → j < 56 →
    (edge k ||| triple i ||| triple j) = 255 → g.testBit k = false → i ∈ B ∨ j ∈ B
  centers : 5 ≤ (centerSet g B).card

end WildNumber.Nine.Census
