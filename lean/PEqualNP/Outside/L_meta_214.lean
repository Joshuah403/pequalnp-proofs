import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta214

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem length_foldl (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, length_step, List.length_cons]
    omega

theorem getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem getD_foldl_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by rw [length_step]; omega), getD_step_lt _ _ _ hi]

theorem any_congr_mem {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | s, m, u :: us => ⟨GateOp.or, [s, u]⟩ :: chain m (m + 1) us

def chainOut : ℕ → ℕ → List ℕ → ℕ
  | s, _, [] => s
  | _, m, _ :: us => chainOut m (m + 1) us

theorem length_chain (us : List ℕ) : ∀ s m : ℕ, (chain s m us).length = us.length := by
  induction us with
  | nil => intro s m; rfl
  | cons u us ih => intro s m; simp [chain, ih]

theorem chain_spec (us : List ℕ) : ∀ (s : ℕ) (w : List Bool), s < w.length →
    (∀ u ∈ us, u < w.length) →
    ((chain s w.length us).foldl step w).getD (chainOut s w.length us) false =
      (w.getD s false || us.any (fun u => w.getD u false)) := by
  induction us with
  | nil => intro s w _ _; simp [chain, chainOut]
  | cons u us ih =>
    intro s w hs hu
    have hlen : (step w ⟨GateOp.or, [s, u]⟩).length = w.length + 1 := length_step _ _
    simp only [chain, chainOut, List.foldl_cons]
    have key := ih w.length (step w ⟨GateOp.or, [s, u]⟩) (by rw [hlen]; omega)
      (fun u' hu' => by rw [hlen]; have := hu u' (by simp [hu']); omega)
    rw [hlen] at key
    rw [key, getD_step_last]
    have hany : us.any (fun u' => (step w ⟨GateOp.or, [s, u]⟩).getD u' false) =
        us.any (fun u' => w.getD u' false) :=
      any_congr_mem us _ _ (fun u' hu' => getD_step_lt _ _ _ (hu u' (by simp [hu'])))
    rw [hany]
    simp [GateOp.eval, Bool.or_assoc]

def blk (a v : ℕ) (Nv : List ℕ) (m : ℕ) : List Gate :=
  ⟨GateOp.or, []⟩ :: (chain m (m + 1) Nv ++
    [⟨GateOp.and, [v, chainOut m (m + 1) Nv]⟩, ⟨GateOp.or, [a, m + 1 + Nv.length]⟩])

theorem length_blk (a v : ℕ) (Nv : List ℕ) (m : ℕ) : (blk a v Nv m).length = Nv.length + 3 := by
  simp [blk, length_chain]

theorem blk_spec (a v : ℕ) (Nv : List ℕ) (w : List Bool) (ha : a < w.length) (hv : v < w.length)
    (hN : ∀ u ∈ Nv, u < w.length) :
    ((blk a v Nv w.length).foldl step w).getD (w.length + Nv.length + 2) false =
      (w.getD a false || (w.getD v false && Nv.any (fun u => w.getD u false))) := by
  have hl1 : (step w ⟨GateOp.or, []⟩).length = w.length + 1 := length_step _ _
  have hl2 : ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩)).length =
      w.length + 1 + Nv.length := by
    rw [length_foldl, length_chain, hl1]
  have hc : ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩)).getD
      (chainOut w.length (w.length + 1) Nv) false = Nv.any (fun u => w.getD u false) := by
    have := chain_spec Nv w.length (step w ⟨GateOp.or, []⟩) (by rw [hl1]; omega)
      (fun u hu => by rw [hl1]; have := hN u hu; omega)
    rw [hl1] at this
    rw [this, getD_step_last]
    simp only [GateOp.eval, List.map_nil, List.any_nil, Bool.false_or]
    exact any_congr_mem Nv _ _ (fun u hu => getD_step_lt _ _ _ (hN u hu))
  have hv2 : ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩)).getD v false =
      w.getD v false := by
    rw [getD_foldl_lt _ _ _ (by rw [hl1]; omega), getD_step_lt _ _ _ hv]
  have ha2 : ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩)).getD a false =
      w.getD a false := by
    rw [getD_foldl_lt _ _ _ (by rw [hl1]; omega), getD_step_lt _ _ _ ha]
  have hfold : (blk a v Nv w.length).foldl step w =
      step (step ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩))
        ⟨GateOp.and, [v, chainOut w.length (w.length + 1) Nv]⟩)
        ⟨GateOp.or, [a, w.length + 1 + Nv.length]⟩ := by
    simp only [blk, List.foldl_cons, List.foldl_append, List.foldl_nil]
  have hl3 : (step ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩))
      ⟨GateOp.and, [v, chainOut w.length (w.length + 1) Nv]⟩).length = w.length + Nv.length + 2 := by
    rw [length_step, hl2]
    omega
  rw [hfold, ← hl3, getD_step_last]
  have hidx : w.length + 1 + Nv.length =
      ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩)).length := hl2.symm
  have hA := getD_step_last ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩))
    ⟨GateOp.and, [v, chainOut w.length (w.length + 1) Nv]⟩
  rw [← hidx] at hA
  have ha3 := getD_step_lt ((chain w.length (w.length + 1) Nv).foldl step (step w ⟨GateOp.or, []⟩))
    ⟨GateOp.and, [v, chainOut w.length (w.length + 1) Nv]⟩ a (by rw [hl2]; omega)
  simp only [List.map_cons, List.map_nil, GateOp.eval]
  rw [hA, ha3, ha2]
  simp only [List.map_cons, List.map_nil, GateOp.eval, hv2, hc]
  simp

def blocks : ℕ → ℕ → List (ℕ × List ℕ) → List Gate
  | _, _, [] => []
  | a, m, p :: rest => blk a p.1 p.2 m ++ blocks (m + p.2.length + 2) (m + p.2.length + 3) rest

def blocksOut : ℕ → ℕ → List (ℕ × List ℕ) → ℕ
  | a, _, [] => a
  | _, m, p :: rest => blocksOut (m + p.2.length + 2) (m + p.2.length + 3) rest

theorem blocks_spec (items : List (ℕ × List ℕ)) : ∀ (a : ℕ) (w : List Bool), a < w.length →
    (∀ p ∈ items, p.1 < w.length ∧ ∀ u ∈ p.2, u < w.length) →
    ((blocks a w.length items).foldl step w).getD (blocksOut a w.length items) false =
      (w.getD a false ||
        items.any (fun p => w.getD p.1 false && p.2.any (fun u => w.getD u false))) := by
  induction items with
  | nil => intro a w _ _; simp [blocks, blocksOut]
  | cons p rest ih =>
    intro a w ha hp
    obtain ⟨hp1, hp2⟩ := hp p (by simp)
    simp only [blocks, blocksOut, List.foldl_append]
    have hl : ((blk a p.1 p.2 w.length).foldl step w).length = w.length + p.2.length + 3 := by
      rw [length_foldl, length_blk]
      omega
    have key := ih (w.length + p.2.length + 2) ((blk a p.1 p.2 w.length).foldl step w) (by omega)
      (fun q hq => by
        have := hp q (by simp [hq])
        exact ⟨by omega, fun u hu => by have := this.2 u hu; omega⟩)
    rw [hl] at key
    rw [key, blk_spec a p.1 p.2 w ha hp1 hp2]
    have hrest : rest.any (fun q => ((blk a p.1 p.2 w.length).foldl step w).getD q.1 false &&
        q.2.any (fun u => ((blk a p.1 p.2 w.length).foldl step w).getD u false)) =
        rest.any (fun q => w.getD q.1 false && q.2.any (fun u => w.getD u false)) := by
      apply any_congr_mem
      intro q hq
      obtain ⟨hq1, hq2⟩ := hp q (by simp [hq])
      rw [getD_foldl_lt _ _ _ hq1,
        any_congr_mem q.2 _ _ (fun u hu => getD_foldl_lt _ _ _ (hq2 u hu))]
    rw [hrest]
    simp [Bool.or_assoc]

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def andIdx : List Gate → Finset ℕ
  | [] => ∅
  | g :: l => (if isAnd g.op = true then {0} else ∅) ∪ (andIdx l).map ⟨Nat.succ, Nat.succ_injective⟩

theorem mem_andIdx (l : List Gate) : ∀ (j : ℕ) (g : Gate), l[j]? = some g →
    g.op = GateOp.and → j ∈ andIdx l := by
  induction l with
  | nil => intro j g h; simp at h
  | cons g0 l ih =>
    intro j g h hop
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [andIdx, isAnd, hop]
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      have hm := ih j g h hop
      simp only [andIdx, Finset.mem_union, Finset.mem_map]
      exact Or.inr ⟨j, hm, rfl⟩

theorem card_andIdx (l : List Gate) : (andIdx l).card ≤ l.countP (fun g => isAnd g.op) := by
  induction l with
  | nil => simp [andIdx]
  | cons g l ih =>
    rw [List.countP_cons]
    cases hg : isAnd g.op
    · have e : andIdx (g :: l) = (andIdx l).map ⟨Nat.succ, Nat.succ_injective⟩ := by
        simp only [andIdx, hg, Bool.false_eq_true, ite_false, Finset.empty_union]
      rw [e, Finset.card_map]
      simpa [hg] using ih
    · have e : (andIdx (g :: l)).card ≤ 1 + (andIdx l).card := by
        simp only [andIdx, hg, ite_true]
        refine le_trans (Finset.card_union_le _ _) ?_
        simp
      simp only [hg, ite_true]
      omega

theorem countP_chain (us : List ℕ) : ∀ s m : ℕ, (chain s m us).countP (fun g => isAnd g.op) = 0 := by
  induction us with
  | nil => intro s m; rfl
  | cons u us ih =>
    intro s m
    simp only [chain, List.countP_cons, ih]
    simp [isAnd]

theorem countP_blocks (items : List (ℕ × List ℕ)) : ∀ a m : ℕ,
    (blocks a m items).countP (fun g => isAnd g.op) = items.length := by
  induction items with
  | nil => intro a m; rfl
  | cons p rest ih =>
    intro a m
    simp only [blocks, blk, List.countP_append, List.countP_cons, List.countP_nil, countP_chain, ih]
    simp [isAnd] <;> omega

def Ok (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem chain_ok (us : List ℕ) : ∀ s m : ℕ, ∀ g ∈ chain s m us, Ok g := by
  induction us with
  | nil => intro s m g hg; simp [chain] at hg
  | cons u us ih =>
    intro s m g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [Ok]
    · exact ih _ _ g hg

theorem blocks_ok (items : List (ℕ × List ℕ)) : ∀ a m : ℕ, ∀ g ∈ blocks a m items, Ok g := by
  induction items with
  | nil => intro a m g hg; simp [blocks] at hg
  | cons p rest ih =>
    intro a m g hg
    simp only [blocks, blk, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with ((rfl | hg | rfl | rfl) | hg)
    · simp [Ok]
    · exact chain_ok _ _ _ g hg
    · simp [Ok]
    · simp [Ok]
    · exact ih _ _ g hg

end PEqualNP.Outside.Meta214

theorem PEqualNP.Outside.L_meta_214 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ T.card ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro n G T hT
  classical
  let items : List (ℕ × List ℕ) := T.toList.map
    (fun v => (v.val, ((Finset.univ.filter (G.Adj v)).toList).map Fin.val))
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: PEqualNP.Outside.Meta214.blocks n (n + 1) items,
      PEqualNP.Outside.Meta214.blocksOut n (n + 1) items⟩
  refine ⟨C, ?_, ⟨PEqualNP.Outside.Meta214.andIdx C.gates, ?_,
    fun j g hj hop => PEqualNP.Outside.Meta214.mem_andIdx _ j g hj hop⟩, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · exact PEqualNP.Outside.Meta214.blocks_ok items n (n + 1) g hg
  · refine le_trans (PEqualNP.Outside.Meta214.card_andIdx _) ?_
    simp only [C]
    rw [List.countP_cons, PEqualNP.Outside.Meta214.countP_blocks]
    simp [PEqualNP.Outside.Meta214.isAnd, items]
  · intro x
    have hw0 : (List.ofFn x).length = n := List.length_ofFn
    have hl1 : (PEqualNP.Outside.Meta214.step (List.ofFn x)
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).length = n + 1 := by
      rw [PEqualNP.Outside.Meta214.length_step, hw0]
    have hval : ∀ i : Fin n, (PEqualNP.Outside.Meta214.step (List.ofFn x)
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).getD i.val false = x i := by
      intro i
      rw [PEqualNP.Outside.Meta214.getD_step_lt _ _ _ (by rw [hw0]; exact i.isLt)]
      simp [List.getD_eq_getElem?_getD]
    have hzero : (PEqualNP.Outside.Meta214.step (List.ofFn x)
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).getD n false = false := by
      have := PEqualNP.Outside.Meta214.getD_step_last (List.ofFn x)
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
      rw [hw0] at this
      rw [this]
      rfl
    have hspec := PEqualNP.Outside.Meta214.blocks_spec items n
      (PEqualNP.Outside.Meta214.step (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)
      (by rw [hl1]; omega)
      (fun p hp => by
        simp only [items, List.mem_map] at hp
        obtain ⟨v, _, rfl⟩ := hp
        refine ⟨by rw [hl1]; have := v.isLt; omega, fun u hu => ?_⟩
        simp only [List.mem_map] at hu
        obtain ⟨u', _, rfl⟩ := hu
        rw [hl1]
        have := u'.isLt
        omega)
    rw [hl1] at hspec
    have heval : C.eval (List.ofFn x) =
        ((PEqualNP.Outside.Meta214.blocks n (n + 1) items).foldl PEqualNP.Outside.Meta214.step
          (PEqualNP.Outside.Meta214.step (List.ofFn x)
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)).getD
          (PEqualNP.Outside.Meta214.blocksOut n (n + 1) items) false := rfl
    rw [heval, hspec, hzero, Bool.false_or]
    simp only [items, List.any_map, List.any_eq_true, Finset.mem_toList, Function.comp_apply,
      Bool.and_eq_true, Finset.mem_filter, Finset.mem_univ, true_and, hval]
    constructor
    · rintro ⟨v, _, hxv, u, hadj, hxu⟩
      exact ⟨v, u, hadj, hxv, hxu⟩
    · rintro ⟨u, v, hadj, hxu, hxv⟩
      rcases hT u v hadj with hu | hv
      · exact ⟨u, hu, hxu, v, hadj, hxv⟩
      · exact ⟨v, hv, hxv, u, hadj.symm, hxu⟩
