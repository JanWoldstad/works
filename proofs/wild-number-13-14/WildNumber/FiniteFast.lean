import WildNumber.FiniteReplay

/-! Bit-mask implementation of the certificate interpreter. The refinement
theorem below connects its Boolean result to the finite-set proof rules. -/

namespace WildNumber.Nine.Census

theorem checkedCons {α : Type*} {P : α → Prop} {a : α} {xs : List α}
    (ha : P a) (hxs : ∀ x ∈ xs, P x) : ∀ x ∈ a :: xs, P x :=
  fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ ha) (hxs x)

def addBit (m i : ℕ) : ℕ := m ||| 2^i
def removeBit (m i : ℕ) : ℕ := m ^^^ (m &&& 2^i)

@[simp] theorem bits_addBit (m i : ℕ) : bits (addBit m i) = insert i (bits m) := by
  ext j
  simp only [mem_bits, addBit, Nat.testBit_or, Bool.or_eq_true,
    Nat.testBit_two_pow, decide_eq_true_eq, Finset.mem_insert]
  tauto

@[simp] theorem bits_removeBit (m i : ℕ) : bits (removeBit m i) = (bits m).erase i := by
  ext j
  by_cases h : i = j <;> cases hm : m.testBit j <;> simp_all [removeBit] <;> tauto

@[simp] theorem card_bits (m : ℕ) : (bits m).card = m.bitIndices.length :=
  List.toFinset_card_of_nodup Nat.bitIndices_nodup

def addForced : List (ℕ × ℕ) → ℕ → ℕ
  | [], s => s
  | (_,j)::fs, s => addForced fs (addBit s j)

@[simp] theorem bits_addForced (fs : List (ℕ × ℕ)) (s : ℕ) :
    bits (addForced fs s) = bits s ∪ (fs.map Prod.snd).toFinset := by
  induction fs generalizing s with
  | nil => simp [addForced]
  | cons p fs ih =>
    rcases p with ⟨k,j⟩
    ext x
    simp only [addForced, ih, bits_addBit, Finset.mem_union, Finset.mem_insert,
      List.map_cons, List.toFinset_cons]
    tauto

def fastPack (g : ℕ) : List Conflict → ℕ → Bool
  | [], _ => true
  | (k,i,j)::rest, used => partitionCheck g k i j && !used.testBit i &&
      !used.testBit j && fastPack g rest (addBit (addBit used j) i)

theorem fastPack_eq (g m) (w : List Conflict) : fastPack g w m = packOK g w (bits m) := by
  induction w generalizing m with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨k,i,j⟩
    simp [fastPack,packOK,ih]

def fastReplay (g : ℕ) : Refutation → ℕ → ℕ → Bool
  | .oversize, s, _ => 35 < g.bitIndices.length + s.bitIndices.length
  | .missing k i j, _, a => partitionCheck g k i j && !a.testBit i && !a.testBit j
  | .high v, s, _ => 19 < degree g (bits s) v
  | .low v, _, a => degree g (bits a) v < g.bitIndices.length
  | .centers, _, a => (centerSet g (bits a)).card < 5
  | .full next, s, _ => 35 ≤ g.bitIndices.length + s.bitIndices.length && fastReplay g next s s
  | .pack w, s, _ => 35 < g.bitIndices.length + s.bitIndices.length + w.length && fastPack g w s
  | .split v fs yes no, s, a => fs.all (fun (k,j) => partitionCheck g k v j) &&
      fastReplay g yes (addBit s v) a && fastReplay g no (addForced fs s) (removeBit a v)

theorem fastReplay_eq (g) (w : Refutation) (s a) :
    fastReplay g w s a = replay g w (bits s) (bits a) := by
  induction w generalizing s a <;> simp [fastReplay, replay, fastPack_eq, *]

theorem using_hint {g} (w : Refutation)
    (h : fastReplay g w 0 (2^56-1) = true) (B : Finset ℕ) : ¬ NumericModel g B := by
  apply refute_link w _ B
  rw [fastReplay_eq] at h
  have hr : bits (2^56-1) = Finset.range 56 := by
    ext i
    simp only [mem_bits, Nat.testBit_two_pow_sub_one, decide_eq_true_eq, Finset.mem_range]
  have hz : bits 0 = ∅ := by simp [bits]
  rwa [hr, hz] at h

end WildNumber.Nine.Census
