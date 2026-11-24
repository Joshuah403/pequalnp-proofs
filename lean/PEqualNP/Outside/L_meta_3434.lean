import Mathlib
import PEqualNP.Defs

-- Renaming the input wires of a circuit.  The map fixes every gate wire and sends an input wire to an
-- input wire or past the last wire; the new input agrees with the old one along the map.  Then every
-- gate has the same value in both circuits: induction on the gate list.

namespace PEqualNP.Outside.L_meta_3434

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ren (s : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map s }

theorem getD_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then v else false := by
  by_cases h : i < w.length
  · rw [if_pos h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    by_cases h2 : i = w.length
    · rw [if_pos h2, h2]
      simp [List.getD_eq_getElem?_getD]
    · rw [if_neg h2]
      exact getD_ge _ _ (by simp; omega)

theorem key (s : ℕ → ℕ) (n S : ℕ) (hfix : ∀ k, n ≤ k → s k = k)
    (hlow : ∀ k, k < n → s k < n ∨ n + S ≤ s k) :
    ∀ (gs : List Gate) (w w' : List Bool), w.length = w'.length → n ≤ w.length →
      w.length + gs.length ≤ n + S → (∀ i, w'.getD (s i) false = w.getD i false) →
      ∀ i, ((gs.map (ren s)).foldl step w').getD (s i) false = (gs.foldl step w).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w w' _ _ _ h i
    exact h i
  | cons g gs ih =>
    intro w w' hlen hn hS h
    have hS' : w.length + (gs.length + 1) ≤ n + S := by simpa using hS
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hv : (ren s g).op.eval ((ren s g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      have hm : (ren s g).inputs.map (fun i => w'.getD i false) =
          g.inputs.map (fun i => w.getD i false) := by
        simp only [ren, List.map_map]
        apply List.map_congr_left
        intro i _
        exact h i
      rw [hm]
      rfl
    apply ih
    · simp [step, hlen]
    · simp [step]
      omega
    · simp [step]
      omega
    · intro i
      show (w' ++ [(ren s g).op.eval ((ren s g).inputs.map fun i => w'.getD i false)]).getD (s i) false =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
      rw [hv, getD_snoc, getD_snoc, ← hlen]
      by_cases hi : i < n
      · rcases hlow i hi with h1 | h1
        · rw [if_pos (by omega : s i < w.length), if_pos (by omega : i < w.length)]
          exact h i
        · rw [if_neg (by omega : ¬ s i < w.length), if_neg (by omega : ¬ s i = w.length),
            if_pos (by omega : i < w.length), ← h i]
          exact (getD_ge w' (s i) (by omega)).symm
      · have hs : s i = i := hfix i (by omega)
        have hi2 := h i
        rw [hs] at hi2
        rw [hs]
        by_cases h1 : i < w.length
        · simp only [if_pos h1]
          exact hi2
        · simp only [if_neg h1]

end PEqualNP.Outside.L_meta_3434

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro s C x y hlen hfix hlow hget
  exact PEqualNP.Outside.L_meta_3434.key s x.length C.size hfix hlow C.gates x y hlen (le_refl _)
    (le_refl _) hget C.output
