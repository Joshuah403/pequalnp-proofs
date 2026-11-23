import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta368

theorem foldr_bits (n : ℕ) :
    List.foldr (fun (b : Bool) (acc : ℕ) => 2 * acc + (if b = true then 1 else 0)) 0 n.bits = n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [Nat.zero_bits]
  · obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst hm
      have hm0 : m ≠ 0 := by omega
      rw [Nat.bit0_bits m hm0, List.foldr_cons, ih m (by omega)]
      simp
    · subst hm
      rw [Nat.bit1_bits m, List.foldr_cons, ih m (by omega)]
      simp

theorem bits_inj (a b : ℕ) (h : a.bits = b.bits) : a = b := by
  have h2 := congrArg
    (List.foldr (fun (b : Bool) (acc : ℕ) => 2 * acc + (if b = true then 1 else 0)) 0) h
  rwa [foldr_bits, foldr_bits] at h2

theorem pairs_inj : ∀ bs cs : List Bool,
    bs.flatMap (fun d => [true, d]) ++ [false, true] =
      cs.flatMap (fun d => [true, d]) ++ [false, true] → bs = cs := by
  intro bs
  induction bs with
  | nil =>
    intro cs h
    cases cs with
    | nil => rfl
    | cons c cs => simp at h
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil => simp at h
    | cons c cs =>
      have h' : b = c ∧ bs.flatMap (fun d => [true, d]) ++ [false, true] =
          cs.flatMap (fun d => [true, d]) ++ [false, true] := by
        simpa using h
      obtain ⟨rfl, h2⟩ := h'
      rw [ih cs h2]

theorem tail_tail (x : PEqualNP.Search.Literal) :
    (PEqualNP.Search.encodeLiteral x).tail.tail =
      x.1.bits.flatMap (fun d => [true, d]) ++ [false, true] := by
  simp [PEqualNP.Search.encodeLiteral]

end PEqualNP.Outside.Meta368

theorem PEqualNP.Outside.L_meta_368 : ∀ l l' : PEqualNP.Search.Literal, (PEqualNP.Search.encodeLiteral l).tail.tail = (PEqualNP.Search.encodeLiteral l').tail.tail ↔ l.1 = l'.1 := by
  intro l l'
  rw [PEqualNP.Outside.Meta368.tail_tail l, PEqualNP.Outside.Meta368.tail_tail l']
  constructor
  · intro h
    exact PEqualNP.Outside.Meta368.bits_inj _ _ (PEqualNP.Outside.Meta368.pairs_inj _ _ h)
  · intro h
    rw [h]
