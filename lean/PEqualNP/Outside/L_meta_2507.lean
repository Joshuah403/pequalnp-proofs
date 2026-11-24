import Mathlib
import PEqualNP.Defs

-- The gate deletion lemmas at the start follow the checked proof of L-meta-171.

namespace PEqualNP.Outside.L_meta_2507

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem deps_sub (g : Gate) (i : ℕ) (h : i ∈ deps g) : i ∈ g.inputs := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => simp [deps] at h
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton] at h
      simp [h]
  | _ => exact h

-- Gate lists of AND, OR and NOT gates reading at most two wires.
def Fan (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

-- No gate depends on input wire 4 or input wire 9.
def Av (G : List Gate) : Prop := ∀ g ∈ G, 4 ∉ deps g ∧ 9 ∉ deps g

theorem fan_renG (p r : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (renG p r g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (renG p r g).inputs.length ≤ 2 := by
  simpa [renG] using h

theorem fan_map (p r : ℕ) (G : List Gate) (h : Fan G) : Fan (G.map (renG p r)) := by
  intro g hg
  obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
  exact fan_renG p r g1 (h g1 hg1)

theorem fan_del (G : List Gate) (t p r : ℕ) (h : Fan G) : Fan (del G t p r) := by
  intro g hg
  simp only [del, List.mem_append] at hg
  rcases hg with hg | hg
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    exact fan_renG p r g1 (h g1 (List.mem_of_mem_drop hg1))

theorem ren_ne (p r i a : ℕ) (hp : 10 ≤ p) (ha : a < 10) (hr : r ≠ a) (hi : i ≠ a) :
    ren p r i ≠ a := by
  unfold ren
  split_ifs <;> omega

theorem av_renG (p r : ℕ) (g : Gate) (hp : 10 ≤ p) (hr4 : r ≠ 4) (hr9 : r ≠ 9)
    (h : 4 ∉ deps g ∧ 9 ∉ deps g) : 4 ∉ deps (renG p r g) ∧ 9 ∉ deps (renG p r g) := by
  rw [deps_renG]
  constructor
  · intro h4
    obtain ⟨i, hi, hi2⟩ := List.mem_map.1 h4
    exact ren_ne p r i 4 hp (by omega) hr4 (fun e => h.1 (e ▸ hi)) hi2
  · intro h9
    obtain ⟨i, hi, hi2⟩ := List.mem_map.1 h9
    exact ren_ne p r i 9 hp (by omega) hr9 (fun e => h.2 (e ▸ hi)) hi2

theorem av_del (G : List Gate) (t p r : ℕ) (hp : 10 ≤ p) (hr4 : r ≠ 4) (hr9 : r ≠ 9) (h : Av G) :
    Av (del G t p r) := by
  intro g hg
  simp only [del, List.mem_append] at hg
  rcases hg with hg | hg
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    exact av_renG p r g1 hp hr4 hr9 (h g1 (List.mem_of_mem_drop hg1))

-- Deleting gate t and sending its later readers to r, when r carries the same value.
theorem del_ok (G : List Gate) (out n t r : ℕ) (ht : t < G.length) (hfan : Fan G) (hav : Av G)
    (ho4 : out ≠ 4) (ho9 : out ≠ 9) (hn : 10 ≤ n) (hr : r < n + t ∨ n + G.length ≤ r)
    (hr4 : r ≠ 4) (hr9 : r ≠ 9)
    (hv : ∀ x : List Bool, x.length = n →
      (∀ g ∈ G.drop (t + 1), n + t ∈ deps g →
        (G.foldl step x).getD (n + t) false = (G.foldl step x).getD r false) ∧
      (out = n + t → (G.foldl step x).getD (n + t) false = (G.foldl step x).getD r false)) :
    (del G t (n + t) r).length + 1 = G.length ∧ Fan (del G t (n + t) r) ∧
    Av (del G t (n + t) r) ∧ ren (n + t) r out ≠ 4 ∧ ren (n + t) r out ≠ 9 ∧
    ∀ x : List Bool, x.length = n →
      (del G t (n + t) r).foldl step x = (G.foldl step x).eraseIdx (n + t) ∧
      ((del G t (n + t) r).foldl step x).getD (ren (n + t) r out) false =
        (G.foldl step x).getD out false := by
  refine ⟨?_, fan_del G t _ r hfan, av_del G t _ r (by omega) hr4 hr9 hav,
    ren_ne _ r out 4 (by omega) (by omega) hr4 ho4,
    ren_ne _ r out 9 (by omega) (by omega) hr9 ho9, ?_⟩
  · rw [del_length G t _ r ht]; omega
  · intro x hx
    subst hx
    exact ⟨del_foldl G x t r ht hr (hv x rfl).1,
      del_eval G out x t r ht hr (hv x rfl).1 (hv x rfl).2⟩

-- How a gate that reads a wire of known value c behaves.
theorem hcase (g : Gate) (p : ℕ) (c : Bool)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hl : g.inputs.length ≤ 2)
    (hp : p ∈ deps g) :
    (∀ f : ℕ → Bool, f p = c → g.op.eval (g.inputs.map f) = false) ∨
    (∃ o ∈ deps g, ∀ f : ℕ → Bool, f p = c → g.op.eval (g.inputs.map f) = f o) ∨
    (c = false ∧ ∀ f : ℕ → Bool, f p = c → g.op.eval (g.inputs.map f) = true) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [deps] at hp ⊢
    match l, hl, hp with
    | [], _, hp => simp at hp
    | [a], _, hp =>
      simp only [List.mem_singleton] at hp
      subst hp
      exact Or.inr (Or.inl ⟨p, by simp, fun f _ => by simp [GateOp.eval]⟩)
    | [a, b], _, hp =>
      cases c with
      | false =>
        left
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> simp [GateOp.eval, hf]
      | true =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inr (Or.inl ⟨b, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
        · exact Or.inr (Or.inl ⟨a, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  · simp only [deps] at hp ⊢
    match l, hl, hp with
    | [], _, hp => simp at hp
    | [a], _, hp =>
      simp only [List.mem_singleton] at hp
      subst hp
      exact Or.inr (Or.inl ⟨p, by simp, fun f _ => by simp [GateOp.eval]⟩)
    | [a, b], _, hp =>
      cases c with
      | true =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inr (Or.inl ⟨p, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
        · exact Or.inr (Or.inl ⟨p, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
      | false =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact Or.inr (Or.inl ⟨b, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
        · exact Or.inr (Or.inl ⟨a, by simp, fun f hf => by simp [GateOp.eval, hf]⟩)
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  · cases l with
    | nil => simp [deps] at hp
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton] at hp
      subst hp
      cases c with
      | true => exact Or.inl (fun f hf => by simp [GateOp.eval, hf])
      | false => exact Or.inr (Or.inr ⟨rfl, fun f hf => by simp [GateOp.eval, hf]⟩)

-- A gate whose value is the same constant on every input: two gates can be saved, or the
-- circuit is constant, or the gate is never read.
theorem K : ∀ (m : ℕ) (G : List Gate) (out n j : ℕ) (c : Bool), G.length = m → Fan G → Av G →
    out ≠ 4 → out ≠ 9 → 10 ≤ n → j < G.length →
    (∀ x : List Bool, x.length = n → (G.foldl step x).getD (n + j) false = c) →
    ((∃ (G2 : List Gate) (out2 : ℕ), G2.length + 2 ≤ G.length ∧ Fan G2 ∧ Av G2 ∧ out2 ≠ 4 ∧
        out2 ≠ 9 ∧ ∀ x : List Bool, x.length = n →
          (G2.foldl step x).getD out2 false = (G.foldl step x).getD out false) ∨
      (∃ d : Bool, ∀ x : List Bool, x.length = n → (G.foldl step x).getD out false = d) ∨
      (out ≠ n + j ∧ ∀ g ∈ G.drop (j + 1), n + j ∉ deps g)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G out n j c hm hfan hav ho4 ho9 hn hj hc
  have finish : ∀ (G1 : List Gate) (out1 j1 : ℕ) (c1 : Bool), G1.length + 1 = G.length → Fan G1 →
      Av G1 → out1 ≠ 4 → out1 ≠ 9 → j1 < G1.length →
      (∀ x : List Bool, x.length = n → (G1.foldl step x).getD (n + j1) false = c1) →
      (∀ x : List Bool, x.length = n →
        (G1.foldl step x).getD out1 false = (G.foldl step x).getD out false) →
      ((∃ (G2 : List Gate) (out2 : ℕ), G2.length + 2 ≤ G.length ∧ Fan G2 ∧ Av G2 ∧ out2 ≠ 4 ∧
          out2 ≠ 9 ∧ ∀ x : List Bool, x.length = n →
            (G2.foldl step x).getD out2 false = (G.foldl step x).getD out false) ∨
        (∃ d : Bool, ∀ x : List Bool, x.length = n → (G.foldl step x).getD out false = d) ∨
        (out ≠ n + j ∧ ∀ g ∈ G.drop (j + 1), n + j ∉ deps g)) := by
    intro G1 out1 j1 c1 hlen hf1 ha1 h41 h91 hj1 hc1 heq
    rcases ih G1.length (by omega) G1 out1 n j1 c1 rfl hf1 ha1 h41 h91 hn hj1 hc1 with
      ⟨G2, out2, hl2, hf2, ha2, h42, h92, he2⟩ | ⟨d, hd⟩ | ⟨hne, hnr⟩
    · exact Or.inl ⟨G2, out2, by omega, hf2, ha2, h42, h92,
        fun x hx => (he2 x hx).trans (heq x hx)⟩
    · exact Or.inr (Or.inl ⟨d, fun x hx => (heq x hx).symm.trans (hd x hx)⟩)
    · obtain ⟨hlen3, hf3, ha3, h43, h93, hx3⟩ :=
        del_ok G1 out1 n j1 (n + G1.length) hj1 hf1 ha1 h41 h91 hn (Or.inr le_rfl) (by omega)
          (by omega) (fun x hx => ⟨fun g hg hd => absurd hd (hnr g hg), fun e => absurd e hne⟩)
      exact Or.inl ⟨_, _, by omega, hf3, ha3, h43, h93,
        fun x hx => ((hx3 x hx).2).trans (heq x hx)⟩
  by_cases hdead : out ≠ n + j ∧ ∀ g ∈ G.drop (j + 1), n + j ∉ deps g
  · exact Or.inr (Or.inr hdead)
  by_cases hout : out = n + j
  · exact Or.inr (Or.inl ⟨c, fun x hx => by rw [hout]; exact hc x hx⟩)
  have hex : ∃ g ∈ G.drop (j + 1), n + j ∈ deps g := by
    by_contra hne
    exact hdead ⟨hout, fun g hg hd => hne ⟨g, hg, hd⟩⟩
  obtain ⟨h, hh, hp⟩ := hex
  obtain ⟨s, hs, hsh⟩ := List.getElem_of_mem hh
  have hs2 : j + 1 + s < G.length := by
    rw [List.length_drop] at hs
    omega
  have hgt : G[j + 1 + s] = h := by
    rw [← hsh, List.getElem_drop]
  have hmem : G[j + 1 + s] ∈ G := List.getElem_mem hs2
  have hval : ∀ x : List Bool, x.length = n → (G.foldl step x).getD (n + (j + 1 + s)) false =
      h.op.eval (h.inputs.map fun i =>
        if i < n + (j + 1 + s) then (G.foldl step x).getD i false else false) := by
    intro x hx
    subst hx
    rw [gate_value G x (j + 1 + s) hs2, hgt]
  have hfp : ∀ x : List Bool, x.length = n →
      (fun i => if i < n + (j + 1 + s) then (G.foldl step x).getD i false else false) (n + j)
        = c := by
    intro x hx
    simp only
    rw [if_pos (by omega)]
    exact hc x hx
  have hM : ∀ x : List Bool, x.length = n →
      (G.foldl step x).getD (n + G.length) false = false := by
    intro x hx
    exact getD_of_length_le _ _ (by rw [foldl_step_length]; omega)
  have simple : ∀ r : ℕ, (r < n + (j + 1 + s) ∨ n + G.length ≤ r) → r ≠ 4 → r ≠ 9 →
      (∀ x : List Bool, x.length = n →
        (G.foldl step x).getD (n + (j + 1 + s)) false = (G.foldl step x).getD r false) →
      ((∃ (G2 : List Gate) (out2 : ℕ), G2.length + 2 ≤ G.length ∧ Fan G2 ∧ Av G2 ∧ out2 ≠ 4 ∧
          out2 ≠ 9 ∧ ∀ x : List Bool, x.length = n →
            (G2.foldl step x).getD out2 false = (G.foldl step x).getD out false) ∨
        (∃ d : Bool, ∀ x : List Bool, x.length = n → (G.foldl step x).getD out false = d) ∨
        (out ≠ n + j ∧ ∀ g ∈ G.drop (j + 1), n + j ∉ deps g)) := by
    intro r hr hr4 hr9 hrv
    obtain ⟨hlen, hf1, ha1, h41, h91, hx1⟩ :=
      del_ok G out n (j + 1 + s) r hs2 hfan hav ho4 ho9 hn hr hr4 hr9
        (fun x hx => ⟨fun _ _ _ => hrv x hx, fun _ => hrv x hx⟩)
    refine finish _ _ j c hlen hf1 ha1 h41 h91 (by omega) (fun x hx => ?_)
      (fun x hx => (hx1 x hx).2)
    rw [(hx1 x hx).1, getD_eraseIdx_lt _ _ _ (by omega)]
    exact hc x hx
  have hfanh := hfan _ hmem
  have havh := hav _ hmem
  rw [hgt] at hfanh havh
  rcases hcase h (n + j) c hfanh.1 hfanh.2 hp with hfalse | ⟨o, ho, hov⟩ | ⟨hcf, htrue⟩
  · exact simple (n + G.length) (Or.inr le_rfl) (by omega) (by omega)
      (fun x hx => by rw [hval x hx, hfalse _ (hfp x hx), hM x hx])
  · by_cases hlt : o < n + (j + 1 + s)
    · exact simple o (Or.inl hlt) (fun e => havh.1 (e ▸ ho)) (fun e => havh.2 (e ▸ ho))
        (fun x hx => by rw [hval x hx, hov _ (hfp x hx)]; show (if o < n + (j + 1 + s) then _ else _) = _; rw [if_pos hlt])
    · exact simple (n + G.length) (Or.inr le_rfl) (by omega) (by omega)
        (fun x hx => by
          rw [hval x hx, hov _ (hfp x hx)]; show (if o < n + (j + 1 + s) then _ else _) = _; rw [if_neg hlt, hM x hx])
  · subst hcf
    obtain ⟨hlen, hf1, ha1, h41, h91, hx1⟩ :=
      del_ok G out n j (n + G.length) hj hfan hav ho4 ho9 hn (Or.inr le_rfl) (by omega)
        (by omega)
        (fun x hx => ⟨fun _ _ _ => by rw [hc x hx, hM x hx], fun e => absurd e hout⟩)
    refine finish _ _ (j + s) true hlen hf1 ha1 h41 h91 (by omega) (fun x hx => ?_)
      (fun x hx => (hx1 x hx).2)
    rw [(hx1 x hx).1, getD_eraseIdx_ge _ _ _ (by omega)]
    have e : n + (j + s) + 1 = n + (j + 1 + s) := by omega
    rw [e, hval x hx]
    exact htrue _ (hfp x hx)

-- Removing the two input wires 9 and 4 from a gate list that does not depend on them.
def r8 (L : List Gate) : List Gate := (L.map (renG 9 0)).map (renG 4 0)

def sg (o : ℕ) : ℕ := ren 4 0 (ren 9 0 o)

theorem fan_r8 (L : List Gate) (h : Fan L) : Fan (r8 L) := fan_map 4 0 _ (fan_map 9 0 _ h)

theorem r8_length (L : List Gate) : (r8 L).length = L.length := by simp [r8]

theorem r8_foldl (L : List Gate) (v : List Bool) (hv : 10 ≤ v.length) (hav : Av L) :
    (r8 L).foldl step ((v.eraseIdx 9).eraseIdx 4) = ((L.foldl step v).eraseIdx 9).eraseIdx 4 := by
  have h1 : (L.map (renG 9 0)).foldl step (v.eraseIdx 9) = (L.foldl step v).eraseIdx 9 :=
    del_foldl_aux (L.foldl step v) 9 0 (Or.inl (by omega)) L v rfl (by omega)
      (fun g hg hd => absurd hd (hav g hg).2)
  exact del_foldl_aux ((L.foldl step v).eraseIdx 9) 4 0 (Or.inl (by omega)) (L.map (renG 9 0))
    (v.eraseIdx 9) h1 (by rw [List.length_eraseIdx_of_lt (by omega)]; omega)
    (fun g hg hd => by
      obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
      rw [deps_renG] at hd
      obtain ⟨i, hi, hi2⟩ := List.mem_map.1 hd
      have h4 : i = 4 := by
        unfold ren at hi2
        split_ifs at hi2 <;> omega
      exact absurd (h4 ▸ hi) (hav g1 hg1).1)

theorem sg_lt (o : ℕ) (h : o < 4) : sg o = o := by
  unfold sg ren
  split_ifs <;> omega

theorem sg_mid (o : ℕ) (h1 : 4 < o) (h2 : o < 9) : sg o = o - 1 := by
  unfold sg ren
  split_ifs <;> omega

theorem sg_big (o : ℕ) (h : 9 < o) : sg o = o - 2 := by
  unfold sg ren
  split_ifs <;> omega

theorem sg_getD (W : List Bool) (o : ℕ) (h4 : o ≠ 4) (h9 : o ≠ 9) :
    ((W.eraseIdx 9).eraseIdx 4).getD (sg o) false = W.getD o false := by
  by_cases h1 : o < 4
  · rw [sg_lt o h1, getD_eraseIdx_lt _ _ _ h1, getD_eraseIdx_lt _ _ _ (by omega)]
  by_cases h2 : o < 9
  · rw [sg_mid o (by omega) h2, getD_eraseIdx_ge _ _ _ (by omega),
      Nat.sub_add_cancel (by omega), getD_eraseIdx_lt _ _ _ h2]
  · rw [sg_big o (by omega), getD_eraseIdx_ge _ _ _ (by omega),
      getD_eraseIdx_ge _ _ _ (by omega)]
    congr 1
    omega

-- The ten inputs: eight free bits, the bit b at position 4 and its negation at position 9.
def inp (b : Bool) (y : Fin 8 → Bool) : List Bool :=
  [y 0, y 1, y 2, y 3, b, y 4, y 5, y 6, y 7, !b]

theorem inp_erase (b : Bool) (y : Fin 8 → Bool) :
    ((inp b y).eraseIdx 9).eraseIdx 4 = List.ofFn y := by
  simp [inp, List.ofFn_succ]

theorem r8_eval (L : List Gate) (o : ℕ) (hav : Av L) (h4 : o ≠ 4) (h9 : o ≠ 9) (b : Bool)
    (y : Fin 8 → Bool) :
    ((r8 L).foldl step (List.ofFn y)).getD (sg o) false =
      (L.foldl step (inp b y)).getD o false := by
  rw [← inp_erase b y, r8_foldl L (inp b y) (by simp [inp]) hav, sg_getD _ _ h4 h9]

theorem indep (L : List Gate) (o : ℕ) (hav : Av L) (h4 : o ≠ 4) (h9 : o ≠ 9)
    (y : Fin 8 → Bool) :
    (L.foldl step (inp false y)).getD o false = (L.foldl step (inp true y)).getD o false := by
  rw [← r8_eval L o hav h4 h9 false y, r8_eval L o hav h4 h9 true y]

theorem pre_facts (A : List Gate) (b : Bool) (y : Fin 8 → Bool) :
    (A.foldl step (inp b y)).getD 4 false = b ∧ (A.foldl step (inp b y)).getD 9 false = (!b) ∧
    ∀ i, 10 + A.length ≤ i → (A.foldl step (inp b y)).getD i false = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [foldl_step_getD _ _ _ (by simp [inp])]
    rfl
  · rw [foldl_step_getD _ _ _ (by simp [inp])]
    rfl
  · intro i hi
    exact getD_of_length_le _ _ (by rw [foldl_step_length]; simpa [inp] using hi)

theorem any_iff (l : List ℕ) :
    (l.any fun i => i == 4 || i == 9) = true ↔ (4 ∈ l ∨ 9 ∈ l) := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (h | h)
    · exact ⟨4, h, by simp⟩
    · exact ⟨9, h, by simp⟩

theorem reads_iff (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ((if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
      fun i => i == 4 || i == 9) = true ↔ (4 ∈ deps g ∨ 9 ∈ deps g) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rw [if_neg (by simp [GateOp.eval])]
    exact any_iff l
  · rw [if_neg (by simp [GateOp.eval])]
    exact any_iff l
  · rw [if_pos (by simp [GateOp.eval])]
    cases l with
    | nil => exact any_iff []
    | cons a l => exact any_iff [a]

-- The constant gates.
def kap : Bool → Gate
  | true => ⟨GateOp.and, []⟩
  | false => ⟨GateOp.or, []⟩

theorem kap_inputs (c : Bool) : (kap c).inputs = [] := by cases c <;> rfl

theorem kap_eval (c : Bool) : (kap c).op.eval [] = c := by cases c <;> rfl

theorem kap_fan (c : Bool) :
    (kap c).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (kap c).inputs.length ≤ 2 := by
  cases c <;> simp [kap]

theorem kap_deps (c : Bool) : deps (kap c) = [] := by cases c <;> rfl

theorem replace_foldl (G : List Gate) (j : ℕ) (hj : j < G.length) (k : Gate) (x : List Bool)
    (h : k.op.eval (k.inputs.map fun i => ((G.take j).foldl step x).getD i false) =
      (G[j]).op.eval ((G[j]).inputs.map fun i => ((G.take j).foldl step x).getD i false)) :
    (G.take j ++ k :: G.drop (j + 1)).foldl step x = G.foldl step x := by
  have hsplit : G = G.take j ++ G[j] :: G.drop (j + 1) := by simp
  conv_rhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  congr 1
  simp only [step]
  rw [h]

theorem const_foldl (A B : List Gate) (k : Gate) (c0 : Bool) (hk : k.inputs = [])
    (hc : k.op.eval [] = c0) (x : List Bool) :
    ((A ++ k :: B).foldl step x).getD (x.length + A.length) false = c0 := by
  rw [List.foldl_append, List.foldl_cons,
    foldl_step_getD _ _ _ (by simp [step, foldl_step_length])]
  simp only [step, hk, List.map_nil, hc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [foldl_step_length])]
  simp [foldl_step_length]

theorem drop_mid (A B : List Gate) (k : Gate) : (A ++ k :: B).drop (A.length + 1) = B := by
  rw [show A ++ k :: B = (A ++ [k]) ++ B by simp]
  exact List.drop_left' (by simp)

-- The one gate that reads wire 4 or wire 9: at b = false it is constant, or it copies another
-- wire and is constant at b = true.
theorem cls (g : Gate) (J : ℕ)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hl : g.inputs.length ≤ 2)
    (hr : 4 ∈ deps g ∨ 9 ∈ deps g) :
    (∃ c0 : Bool, ∀ f : ℕ → Bool, f 4 = false → f 9 = true → (∀ i, J ≤ i → f i = false) →
        g.op.eval (g.inputs.map f) = c0) ∨
    (∃ (u : ℕ) (cc : Bool), u ≠ 4 ∧ u ≠ 9 ∧ u < J ∧ ∀ (f : ℕ → Bool) (b : Bool), f 4 = b →
        f 9 = (!b) → g.op.eval (g.inputs.map f) = if b = true then cc else f u) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [deps] at hr
    match l, hl, hr with
    | [], _, hr => simp at hr
    | [a], _, hr =>
      simp only [List.mem_singleton] at hr
      rcases hr with h | h
      · subst h
        exact Or.inl ⟨false, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
      · subst h
        exact Or.inl ⟨true, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩
    | [a, b], _, hr =>
      by_cases ha4 : a = 4
      · subst ha4
        exact Or.inl ⟨false, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
      by_cases hb4 : b = 4
      · subst hb4
        exact Or.inl ⟨false, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
      have h9 : a = 9 ∨ b = 9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (h | h) | (h | h)
        · exact absurd h.symm ha4
        · exact absurd h.symm hb4
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      by_cases ha9 : a = 9
      · subst ha9
        by_cases hb9 : b = 9
        · subst hb9
          exact Or.inl ⟨true, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩
        by_cases hbJ : b < J
        · exact Or.inr ⟨b, false, hb4, hb9, hbJ, fun f bb h4 h9 => by
            cases bb <;> simp_all [GateOp.eval]⟩
        · exact Or.inl ⟨false, fun f _ h9 hm => by simp [GateOp.eval, h9, hm b (by omega)]⟩
      · have hb9 : b = 9 := by tauto
        subst hb9
        by_cases haJ : a < J
        · exact Or.inr ⟨a, false, ha4, ha9, haJ, fun f bb h4 h9 => by
            cases bb <;> simp_all [GateOp.eval]⟩
        · exact Or.inl ⟨false, fun f _ h9 hm => by simp [GateOp.eval, h9, hm a (by omega)]⟩
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  · simp only [deps] at hr
    match l, hl, hr with
    | [], _, hr => simp at hr
    | [a], _, hr =>
      simp only [List.mem_singleton] at hr
      rcases hr with h | h
      · subst h
        exact Or.inl ⟨false, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
      · subst h
        exact Or.inl ⟨true, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩
    | [a, b], _, hr =>
      by_cases ha9 : a = 9
      · subst ha9
        exact Or.inl ⟨true, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩
      by_cases hb9 : b = 9
      · subst hb9
        exact Or.inl ⟨true, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩
      have h4 : a = 4 ∨ b = 4 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (h | h) | (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
        · exact absurd h.symm ha9
        · exact absurd h.symm hb9
      by_cases ha4 : a = 4
      · subst ha4
        by_cases hb4 : b = 4
        · subst hb4
          exact Or.inl ⟨false, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
        by_cases hbJ : b < J
        · exact Or.inr ⟨b, true, hb4, hb9, hbJ, fun f bb h4 h9 => by
            cases bb <;> simp_all [GateOp.eval]⟩
        · exact Or.inl ⟨false, fun f h4 _ hm => by simp [GateOp.eval, h4, hm b (by omega)]⟩
      · have hb4 : b = 4 := by tauto
        subst hb4
        by_cases haJ : a < J
        · exact Or.inr ⟨a, true, ha4, ha9, haJ, fun f bb h4 h9 => by
            cases bb <;> simp_all [GateOp.eval]⟩
        · exact Or.inl ⟨false, fun f h4 _ hm => by simp [GateOp.eval, h4, hm a (by omega)]⟩
    | _ :: _ :: _ :: _, hl, _ => simp at hl
  · cases l with
    | nil => simp [deps] at hr
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton] at hr
      rcases hr with h | h
      · subst h
        exact Or.inl ⟨true, fun f h4 _ _ => by simp [GateOp.eval, h4]⟩
      · subst h
        exact Or.inl ⟨false, fun f _ h9 _ => by simp [GateOp.eval, h9]⟩

theorem main : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     List.countP x1 x3.gates ≤ (1 : ℕ) →       x3.eval (x2 Bool.false fun (x6 : Fin (8 : ℕ)) => Bool.false) = Bool.false →         x3.eval (x2 Bool.false fun (x7 : Fin (8 : ℕ)) => Bool.true) = Bool.true →           (∃ (x8 : Fin (8 : ℕ) → Bool), x3.eval (x2 Bool.false x8) ≠ x3.eval (x2 Bool.true x8)) →             (∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (8 : ℕ) → Bool), x9.eval (List.ofFn x10) = x3.eval (x2 Bool.false x10)) ∨               ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) (x12 : Bool),                 PEqualNP.MetaComplexity.FanInTwo x9 ∧                   PEqualNP.MetaComplexity.FanInTwo x10 ∧                     x9.size + x10.size + (1 : ℕ) ≤ x3.size ∧                       x11 < (8 : ℕ) + x9.size ∧                         ∀ (x13 : Fin (8 : ℕ) → Bool) (x14 : Bool),                           have x15 : List Bool := x9.wires (List.ofFn x13);                           x10.eval (x15 ++ [if x14 = Bool.true then x12 else x15.getD x11 Bool.false]) = x3.eval (x2 x14 x13) := by
  intro rd ip C hfan hcnt h0 h1 hdep
  have hrd : ∀ g : Gate, rd g = ((if g.op.eval [false, false] = true then List.take 1 g.inputs
      else g.inputs).any fun i => i == 4 || i == 9) := fun g => rfl
  have hip : ∀ (b : Bool) (y : Fin 8 → Bool), ip b y = inp b y := fun b y => rfl
  obtain ⟨G, out⟩ := C
  have hF : Fan G := hfan
  have hrds : ∀ g ∈ G, (rd g = true ↔ (4 ∈ deps g ∨ 9 ∈ deps g)) := fun g hg => by
    rw [hrd]
    exact reads_iff g (hF g hg).1
  have a0 : (G.foldl step (inp false fun _ => false)).getD out false = false := h0
  have a1 : (G.foldl step (inp false fun _ => true)).getD out false = true := h1
  have adep : ∃ y : Fin 8 → Bool,
      (G.foldl step (inp false y)).getD out false ≠ (G.foldl step (inp true y)).getD out false :=
    hdep
  have ho4 : out ≠ 4 := by
    rintro rfl
    rw [foldl_step_getD _ _ _ (by simp [inp])] at a1
    simp [inp] at a1
  have ho9 : out ≠ 9 := by
    rintro rfl
    rw [foldl_step_getD _ _ _ (by simp [inp])] at a0
    simp [inp] at a0
  by_cases hnone : ∀ g ∈ G, rd g = false
  · exfalso
    have hav : Av G := fun g hg => by
      have hn := (hrds g hg).not.1 (by rw [hnone g hg]; simp)
      exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
    obtain ⟨y, hy⟩ := adep
    exact hy (indep G out hav ho4 ho9 y)
  have hsome : ∃ g ∈ G, rd g = true := by
    by_contra hne
    exact hnone (fun g hg => by
      cases hr : rd g with
      | false => rfl
      | true => exact absurd ⟨g, hg, hr⟩ hne)
  obtain ⟨g, hg, hgr⟩ := hsome
  obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hg
  have hsplit : G = G.take j ++ G[j] :: G.drop (j + 1) := by simp
  have htl : (G.take j).length = j := by rw [List.length_take, Nat.min_eq_left hj.le]
  have hc : List.countP rd (G.take j) + (List.countP rd (G.drop (j + 1)) + 1) ≤ 1 := by
    have h : List.countP rd G ≤ 1 := hcnt
    rw [hsplit, List.countP_append, List.countP_cons_of_pos (by rw [hgj]; exact hgr)] at h
    exact h
  have hA : Av (G.take j) := fun g1 hg1 => by
    have hz : List.countP rd (G.take j) = 0 := by omega
    have hn := (hrds g1 (List.mem_of_mem_take hg1)).not.1 (List.countP_eq_zero.1 hz g1 hg1)
    exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
  have hB : Av (G.drop (j + 1)) := fun g1 hg1 => by
    have hz : List.countP rd (G.drop (j + 1)) = 0 := by omega
    have hn := (hrds g1 (List.mem_of_mem_drop hg1)).not.1 (List.countP_eq_zero.1 hz g1 hg1)
    exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
  by_cases hdead : out ≠ 10 + j ∧ ∀ g1 ∈ G.drop (j + 1), 10 + j ∉ deps g1
  · exfalso
    have hav : Av (del G j (10 + j) (10 + G.length)) := by
      intro g1 hg1
      simp only [del, List.mem_append] at hg1
      rcases hg1 with hg1 | hg1
      · exact hA g1 hg1
      · obtain ⟨g2, hg2, rfl⟩ := List.mem_map.1 hg1
        exact av_renG _ _ g2 (by omega) (by omega) (by omega) (hB g2 hg2)
    have he : ∀ (b : Bool) (y : Fin 8 → Bool),
        ((del G j (10 + j) (10 + G.length)).foldl step (inp b y)).getD
          (ren (10 + j) (10 + G.length) out) false = (G.foldl step (inp b y)).getD out false := by
      intro b y
      exact del_eval G out (inp b y) j (10 + G.length) hj (Or.inr (by simp [inp]))
        (fun g1 hg1 hd => absurd hd (hdead.2 g1 hg1)) (fun e => absurd e hdead.1)
    obtain ⟨y, hy⟩ := adep
    apply hy
    rw [← he false y, ← he true y]
    exact indep _ _ hav (ren_ne _ _ out 4 (by omega) (by omega) (by omega) ho4)
      (ren_ne _ _ out 9 (by omega) (by omega) (by omega) ho9) y
  have hgate := hF _ (List.getElem_mem hj)
  have hread : 4 ∈ deps G[j] ∨ 9 ∈ deps G[j] :=
    (hrds _ (List.getElem_mem hj)).1 (by rw [hgj]; exact hgr)
  rcases cls G[j] (10 + j) hgate.1 hgate.2 hread with ⟨c0, hc0⟩ | ⟨u, cc, hu4, hu9, huJ, hucc⟩
  · -- the reader is constant when b is false
    have hlen0 : (G.take j ++ kap c0 :: G.drop (j + 1)).length = G.length := by
      simp only [List.length_append, List.length_cons, List.length_drop, htl]
      omega
    have hF0 : Fan (G.take j ++ kap c0 :: G.drop (j + 1)) := by
      intro g1 hg1
      simp only [List.mem_append, List.mem_cons] at hg1
      rcases hg1 with hg1 | rfl | hg1
      · exact hF g1 (List.mem_of_mem_take hg1)
      · exact kap_fan c0
      · exact hF g1 (List.mem_of_mem_drop hg1)
    have hA0 : Av (G.take j ++ kap c0 :: G.drop (j + 1)) := by
      intro g1 hg1
      simp only [List.mem_append, List.mem_cons] at hg1
      rcases hg1 with hg1 | rfl | hg1
      · exact hA g1 hg1
      · rw [kap_deps]
        simp
      · exact hB g1 hg1
    have hsame : ∀ y : Fin 8 → Bool,
        (G.take j ++ kap c0 :: G.drop (j + 1)).foldl step (inp false y) =
          G.foldl step (inp false y) := by
      intro y
      apply replace_foldl G j hj (kap c0) (inp false y)
      obtain ⟨p4, p9, pm⟩ := pre_facts (G.take j) false y
      rw [kap_inputs, List.map_nil, kap_eval]
      exact (hc0 _ p4 p9 (fun i hi => pm i (by rw [htl]; exact hi))).symm
    have hconst : ∀ x : List Bool, x.length = 10 →
        ((G.take j ++ kap c0 :: G.drop (j + 1)).foldl step x).getD (10 + j) false = c0 := by
      intro x hx
      have h := const_foldl (G.take j) (G.drop (j + 1)) (kap c0) c0 (kap_inputs c0) (kap_eval c0) x
      rw [hx, htl] at h
      exact h
    rcases K _ (G.take j ++ kap c0 :: G.drop (j + 1)) out 10 j c0 rfl hF0 hA0 ho4 ho9 le_rfl
        (by omega) hconst with ⟨G2, out2, hl2, hf2, ha2, h42, h92, he2⟩ | ⟨d, hd⟩ | ⟨hne, hnr⟩
    · left
      refine ⟨⟨r8 G2, sg out2⟩, fan_r8 G2 hf2, ?_, ?_⟩
      · show (r8 G2).length + 2 ≤ G.length
        rw [r8_length]
        omega
      · intro y
        show ((r8 G2).foldl step (List.ofFn y)).getD (sg out2) false =
          (G.foldl step (inp false y)).getD out false
        rw [r8_eval G2 out2 ha2 h42 h92 false y, he2 _ (by simp [inp]), hsame y]
    · exfalso
      have e0 := hd (inp false fun _ => false) (by simp [inp])
      have e1 := hd (inp false fun _ => true) (by simp [inp])
      rw [hsame, a0] at e0
      rw [hsame, a1] at e1
      rw [← e0] at e1
      exact Bool.noConfusion e1
    · exfalso
      apply hdead
      refine ⟨hne, fun g1 hg1 => hnr g1 ?_⟩
      have hd := drop_mid (G.take j) (G.drop (j + 1)) (kap c0)
      rw [htl] at hd
      rw [hd]
      exact hg1
  · -- the reader copies the wire u when b is false and is constant when b is true
    right
    refine ⟨⟨r8 (G.take j), 0⟩, ⟨r8 (G.drop (j + 1)), sg out⟩, sg u, cc,
      fan_r8 _ (fun g1 hg1 => hF g1 (List.mem_of_mem_take hg1)),
      fan_r8 _ (fun g1 hg1 => hF g1 (List.mem_of_mem_drop hg1)), ?_, ?_, ?_⟩
    · show (r8 (G.take j)).length + (r8 (G.drop (j + 1))).length + 1 ≤ G.length
      rw [r8_length, r8_length, htl, List.length_drop]
      omega
    · show sg u < 8 + (r8 (G.take j)).length
      rw [r8_length, htl]
      rcases Nat.lt_or_ge u 4 with h | h
      · rw [sg_lt u h]
        omega
      · rcases Nat.lt_or_ge u 9 with h2 | h2
        · rw [sg_mid u (by omega) h2]
          omega
        · rw [sg_big u (by omega)]
          omega
    · intro y b
      show ((r8 (G.drop (j + 1))).foldl step
          ((r8 (G.take j)).foldl step (List.ofFn y) ++
            [if b = true then cc
              else ((r8 (G.take j)).foldl step (List.ofFn y)).getD (sg u) false])).getD
          (sg out) false = (G.foldl step (inp b y)).getD out false
      have hPlen : ((G.take j).foldl step (inp b y)).length = 10 + j := by
        rw [foldl_step_length, htl]
        simp [inp]
      have hw : (r8 (G.take j)).foldl step (List.ofFn y) =
          (((G.take j).foldl step (inp b y)).eraseIdx 9).eraseIdx 4 := by
        rw [← inp_erase b y]
        exact r8_foldl _ _ (by simp [inp]) hA
      obtain ⟨p4, p9, _⟩ := pre_facts (G.take j) b y
      have hgv : G[j].op.eval (G[j].inputs.map fun i =>
          ((G.take j).foldl step (inp b y)).getD i false) =
          if b = true then cc else ((G.take j).foldl step (inp b y)).getD u false :=
        hucc (fun i => ((G.take j).foldl step (inp b y)).getD i false) b p4 p9
      have hW : G.foldl step (inp b y) = (G.drop (j + 1)).foldl step
          ((G.take j).foldl step (inp b y) ++ [G[j].op.eval (G[j].inputs.map fun i =>
            ((G.take j).foldl step (inp b y)).getD i false)]) := by
        conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
        rfl
      rw [hw, sg_getD _ u hu4 hu9, ← hgv, hW]
      have hv2 : ∀ gv : Bool, ((((G.take j).foldl step (inp b y) ++ [gv]).eraseIdx 9).eraseIdx 4) =
          (((G.take j).foldl step (inp b y)).eraseIdx 9).eraseIdx 4 ++ [gv] := by
        intro gv
        rw [List.eraseIdx_append_of_lt_length (by omega),
          List.eraseIdx_append_of_lt_length (by
            rw [List.length_eraseIdx_of_lt (by omega)]
            omega)]
      rw [← hv2, r8_foldl _ _ (by rw [List.length_append, hPlen]; omega) hB,
        sg_getD _ _ ho4 ho9]

end PEqualNP.Outside.L_meta_2507

theorem PEqualNP.Outside.L_meta_2507 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     List.countP x1 x3.gates ≤ (1 : ℕ) →       x3.eval (x2 Bool.false fun (x6 : Fin (8 : ℕ)) => Bool.false) = Bool.false →         x3.eval (x2 Bool.false fun (x7 : Fin (8 : ℕ)) => Bool.true) = Bool.true →           (∃ (x8 : Fin (8 : ℕ) → Bool), x3.eval (x2 Bool.false x8) ≠ x3.eval (x2 Bool.true x8)) →             (∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size + (2 : ℕ) ≤ x3.size ∧ ∀ (x10 : Fin (8 : ℕ) → Bool), x9.eval (List.ofFn x10) = x3.eval (x2 Bool.false x10)) ∨               ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ) (x12 : Bool),                 PEqualNP.MetaComplexity.FanInTwo x9 ∧                   PEqualNP.MetaComplexity.FanInTwo x10 ∧                     x9.size + x10.size + (1 : ℕ) ≤ x3.size ∧                       x11 < (8 : ℕ) + x9.size ∧                         ∀ (x13 : Fin (8 : ℕ) → Bool) (x14 : Bool),                           have x15 : List Bool := x9.wires (List.ofFn x13);                           x10.eval (x15 ++ [if x14 = Bool.true then x12 else x15.getD x11 Bool.false]) = x3.eval (x2 x14 x13) :=
  PEqualNP.Outside.L_meta_2507.main
