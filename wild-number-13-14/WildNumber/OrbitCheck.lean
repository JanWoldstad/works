import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Certificates for isomorphisms of eight-vertex link graphs. Every
unlabelled graph can be built by adjoining one missing edge at a time. -/
namespace WildNumber.Nine.Orbit

def pairIndex (a b : Fin 8) : Nat :=
  let hi := max a.val b.val
  min a.val b.val + hi * (hi - 1) / 2

theorem pairIndex_lt : ∀ x y : Fin 8, x ≠ y → pairIndex x y < 28 := by decide +kernel

private theorem index_eq : ∀ a b x y : Fin 8, a ≠ b → x ≠ y →
    (pairIndex a b = pairIndex x y ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x)) := by
  decide +kernel

def vertex (code i : Nat) : Fin 8 := Fin.ofNat 8 (code >>> (3 * i))

private def leftEnd (k : Nat) := vertex 0xd634458d111a21a211040 k
private def rightEnd (k : Nat) := vertex 0xfffffedb6d6db6491b691 k

private theorem endpoints : ∀ x y : Fin 8, x ≠ y →
    let k := pairIndex x y
    (leftEnd k = x ∧ rightEnd k = y) ∨ (leftEnd k = y ∧ rightEnd k = x) := by decide +kernel

theorem pairIndex_comm (x y : Fin 8) : pairIndex x y = pairIndex y x := by
  simp [pairIndex, min_comm, max_comm]

/-- A single certificate consists of a permutation, its inverse, and the
target representative's index. Only the forward/inverse values and adjacency
equalities are used by the soundness proof. -/
def witnessOK (src : Nat) (dst : Array Nat) (w : Nat) : Bool :=
  let f := vertex w
  let inv := vertex (w >>> 24)
  let i := w >>> 48
  let g := dst[i]?.getD 0
  decide (i < dst.size) &&
    (List.range 8).all (fun x => decide ((inv (f x).val).val = x)) &&
    (List.range 28).all (fun k =>
      src.testBit k == g.testBit (pairIndex (f (leftEnd k).val) (f (rightEnd k).val)))

def Isom (g h : Nat) : Prop := ∃ p : Equiv.Perm (Fin 8),
  ∀ x y, x ≠ y → g.testBit (pairIndex x y) = h.testBit (pairIndex (p x) (p y))

theorem witness_sound {src w : Nat} {dst : Array Nat} (h : witnessOK src dst w = true) :
    ∃ g ∈ dst, Isom src g := by
  simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hi, hinv⟩, he⟩ := h
  let f (x : Fin 8) := vertex w x.val
  have inj : Function.Injective f := by
    intro x y hxy
    have hx := hinv x.val x.isLt
    have hy := hinv y.val y.isLt
    exact Fin.ext (hx.symm.trans ((congrArg (fun z : Fin 8 => (vertex (w >>> 24) z.val).val) hxy).trans hy))
  let p := Equiv.ofBijective f inj.bijective_of_finite
  refine ⟨dst[w >>> 48], Array.getElem_mem hi, p, ?_⟩
  intro x y hxy
  have eq := he (pairIndex x y) (pairIndex_lt x y hxy)
  simp only [Array.getElem?_eq_getElem hi, Option.getD_some] at eq
  change _ = (dst[w >>> 48]).testBit (pairIndex (vertex w x.val) (vertex w y.val))
  rcases endpoints x y hxy with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · simpa only [hl,hr] using eq
  · simpa only [hl,hr,pairIndex_comm (vertex w y.val) (vertex w x.val)] using eq

def CoversRows (src dst : Array Nat) (start count : Nat) : Prop :=
  ∀ i, start ≤ i → i < start + count →
    ∀ k : Fin 28, (src[i]?.getD 0).testBit k.val = false →
      ∃ g ∈ dst, Isom (src[i]?.getD 0 ||| 2 ^ k.val) g

def rowsOK (src dst ws : Array Nat) (start count : Nat) : Bool :=
  (List.range count).all fun j =>
    let g := src[start+j]?.getD 0
    let row := ws[j]?.getD 0
    (List.range 28).all fun k =>
      g.testBit k || witnessOK (g ||| 2^k) dst ((row >>> (58*k)) % 2^58)

theorem rows_of_check {src dst : Array Nat} (ws : Array Nat) {start count : Nat}
    (h : rowsOK src dst ws start count = true) : CoversRows src dst start count := by
  simp only [rowsOK, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  intro i ilo ihi k hk
  have hh := h (i-start) (by omega) k.val k.isLt
  rw [show start + (i - start) = i by omega, hk] at hh
  exact witness_sound (hh.resolve_left (by decide))

theorem rows_append {a b : Array Nat} {i m n : Nat} (left : CoversRows a b i m)
    (right : CoversRows a b (i+m) n) : CoversRows a b i (m+n) := by
  intro j hlo hhi
  by_cases h : j < i + m
  · exact left j hlo h
  · exact right j (by omega) (by omega)

/-- If each row has a certificate for inserting each missing edge, the listed
representatives exhaust every family of pairs of the corresponding size. -/
theorem canonicalize_of_rows (reps : Nat → Array Nat) (base : 0 ∈ reps 0)
    (step : ∀ d, d < 11 → CoversRows (reps d) (reps (d+1)) 0 (reps d).size)
    (S : Finset (Finset (Fin 8))) (pairs : ∀ t ∈ S, t.card = 2) (hs : S.card ≤ 11) :
    ∃ g ∈ reps S.card, ∃ p : Equiv.Perm (Fin 8), ∀ x y, x ≠ y →
      ({x,y} ∈ S ↔ g.testBit (pairIndex (p x) (p y)) = true) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨0, base, Equiv.refl _, by simp⟩
  | @insert t S ht ih =>
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (pairs t (Finset.mem_insert_self _ _))
    rw [Finset.card_insert_of_notMem ht] at hs ⊢
    obtain ⟨g,hg,p,hp⟩ := ih (fun u hu => pairs u (Finset.mem_insert_of_mem hu)) (by omega)
    obtain ⟨i,hi,gi⟩ := Array.mem_iff_getElem.mp hg
    let k : Fin 28 := ⟨pairIndex (p a) (p b), pairIndex_lt _ _ (p.injective.ne hab)⟩
    have hk : g.testBit k.val = false := Bool.eq_false_iff.mpr (fun hh => ht ((hp a b hab).mpr hh))
    have hi' : (reps S.card)[i]?.getD 0 = g := by simp [hi,gi]
    obtain ⟨g',hg',q,hq⟩ := step S.card (by omega) i (by omega) (by simpa using hi) k (hi' ▸ hk)
    refine ⟨g',hg',p.trans q,fun x y hxy => ?_⟩
    have eq := hq (p x) (p y) (p.injective.ne hxy)
    rw [hi'] at eq
    change _ ↔ g'.testBit (pairIndex (q (p x)) (q (p y))) = true
    rw [← eq, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      Finset.mem_insert, ← hp x y hxy]
    change ({x,y} = ({a,b} : Finset _) ∨ _) ↔ (_ ∨ pairIndex (p a) (p b) = pairIndex (p x) (p y))
    rw [index_eq _ _ _ _ (p.injective.ne hab) (p.injective.ne hxy)]
    simp only [p.injective.eq_iff]
    have pair_eq : ({x,y} : Finset (Fin 8)) = {a,b} ↔ (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
      constructor
      · intro h
        have hx : x ∈ ({a,b} : Finset _) := h ▸ Finset.mem_insert_self _ _
        have hy : y ∈ ({a,b} : Finset _) := h ▸ (show y ∈ ({x,y} : Finset _) by simp)
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
        grind
      · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
        · rfl
        · exact Finset.pair_comm _ _
    tauto

end WildNumber.Nine.Orbit
