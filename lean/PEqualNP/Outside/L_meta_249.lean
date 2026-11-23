import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_249 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧ ∀ v a b c : Fin N, E v a → E v b → E v c → a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  rintro N k E pos hk ⟨hsym, hedge, hthr⟩
  have h3' : ∀ v : Fin N, ∃ a b : Fin N, pos v ≠ 0 →
      (pos v ≤ 2 * k ∧ (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧
        pos b = (pos v + 1) % (2 * k + 1)) := by
    intro v
    by_cases hv : pos v = 0
    · exact ⟨v, v, fun h => absurd hv h⟩
    · obtain ⟨h1, a, b, h⟩ := hthr v hv
      exact ⟨a, b, fun _ => ⟨h1, h⟩⟩
  choose A B hAB using h3'
  have hnb : ∀ x u : Fin N, pos x ≠ 0 → E x u → u = A x ∨ u = B x :=
    fun x u hx he => ((hAB x hx).2.1 u).1 he
  have hApos : ∀ x : Fin N, pos x ≠ 0 → pos (A x) + 1 = pos x := fun x hx => (hAB x hx).2.2.1
  have hBpos : ∀ x : Fin N, pos x ≠ 0 → pos (B x) = (pos x + 1) % (2 * k + 1) :=
    fun x hx => (hAB x hx).2.2.2
  have hle : ∀ x : Fin N, pos x ≠ 0 → pos x ≤ 2 * k := fun x hx => (hAB x hx).1
  have hmc : ∀ q : ℕ, q ≤ 2 * k + 1 →
      (q < 2 * k + 1 ∧ q % (2 * k + 1) = q) ∨ (q = 2 * k + 1 ∧ q % (2 * k + 1) = 0) := by
    intro q hq
    rcases Nat.lt_or_ge q (2 * k + 1) with h | h
    · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
    · have hq' : q = 2 * k + 1 := by omega
      exact Or.inr ⟨hq', by rw [hq']; exact Nat.mod_self _⟩
  refine ⟨?_, ?_⟩
  · intro L w h0 hL hne hw
    by_contra hlt0
    have hlt : L < 2 * k + 1 := by omega
    have key : ∀ i : ℕ, i ≤ L → (w i = w 0 ∨
        (∃ d : ℕ, 1 ≤ d ∧ d ≤ i ∧ pos (w i) = d ∧ A^[d] (w i) = w 0) ∨
        (∃ m : ℕ, 1 ≤ m ∧ m ≤ i ∧ pos (w i) = 2 * k + 1 - m ∧ B^[m] (w i) = w 0)) := by
      intro i
      induction i with
      | zero => intro _; exact Or.inl rfl
      | succ i ih =>
        intro hi
        have hiL : i < L := by omega
        have hE := hw i hiL
        have hi2 : i + 1 < 2 * k + 1 := by omega
        rcases ih (by omega) with h | ⟨d, hd1, hdi, hpd, hAd⟩ | ⟨m, hm1, hmi, hpm, hBm⟩
        · have hp0 : pos (w i) = 0 := by rw [h]; exact h0
          have hu : pos (w (i + 1)) ≠ 0 := by
            rcases hedge _ _ hE with h' | h'
            · exact absurd hp0 h'
            · exact h'
          rcases hnb _ _ hu (hsym _ _ hE) with h' | h'
          · refine Or.inr (Or.inl ⟨1, le_refl _, by omega, ?_, ?_⟩)
            · have h1 := hApos _ hu
              rw [← h'] at h1
              omega
            · rw [Function.iterate_one, ← h', h]
          · refine Or.inr (Or.inr ⟨1, le_refl _, by omega, ?_, ?_⟩)
            · have h1 := hBpos _ hu
              have h2 := hle _ hu
              rw [← h'] at h1
              rcases hmc (pos (w (i + 1)) + 1) (by omega) with ⟨_, hm⟩ | ⟨hq, _⟩
              · omega
              · omega
            · rw [Function.iterate_one, ← h', h]
        · have hx : pos (w i) ≠ 0 := by omega
          rcases hnb _ _ hx hE with hu | hu
          · have h1 := hApos _ hx
            rw [← hu] at h1
            rcases Nat.lt_or_ge d 2 with hd | hd
            · obtain rfl : d = 1 := by omega
              refine Or.inl ?_
              rw [Function.iterate_one] at hAd
              rw [hu]
              exact hAd
            · obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 2 := ⟨d - 2, by omega⟩
              refine Or.inr (Or.inl ⟨e + 1, by omega, by omega, by omega, ?_⟩)
              rw [Function.iterate_succ_apply] at hAd
              rw [hu]
              exact hAd
          · have h1 := hBpos _ hx
            rw [← hu] at h1
            have hpu : pos (w (i + 1)) = d + 1 := by
              rcases hmc (pos (w i) + 1) (by omega) with ⟨_, hm⟩ | ⟨hq, _⟩
              · omega
              · omega
            have hu0 : pos (w (i + 1)) ≠ 0 := by omega
            rcases hnb _ _ hu0 (hsym _ _ hE) with hx' | hx'
            · refine Or.inr (Or.inl ⟨d + 1, by omega, by omega, hpu, ?_⟩)
              rw [Function.iterate_succ_apply, ← hx']
              exact hAd
            · exfalso
              have h2 := hBpos _ hu0
              rw [← hx'] at h2
              rcases hmc (pos (w (i + 1)) + 1) (by omega) with ⟨_, hm⟩ | ⟨hq, _⟩
              · omega
              · omega
        · have hx : pos (w i) ≠ 0 := by omega
          rcases hnb _ _ hx hE with hu | hu
          · have h1 := hApos _ hx
            rw [← hu] at h1
            have hu0 : pos (w (i + 1)) ≠ 0 := by omega
            rcases hnb _ _ hu0 (hsym _ _ hE) with hx' | hx'
            · exfalso
              have h2 := hApos _ hu0
              rw [← hx'] at h2
              omega
            · refine Or.inr (Or.inr ⟨m + 1, by omega, by omega, by omega, ?_⟩)
              rw [Function.iterate_succ_apply, ← hx']
              exact hBm
          · have h1 := hBpos _ hx
            rw [← hu] at h1
            rcases Nat.lt_or_ge m 2 with hm2 | hm2
            · obtain rfl : m = 1 := by omega
              refine Or.inl ?_
              rw [Function.iterate_one] at hBm
              rw [hu]
              exact hBm
            · obtain ⟨e, rfl⟩ : ∃ e : ℕ, m = e + 2 := ⟨m - 2, by omega⟩
              refine Or.inr (Or.inr ⟨e + 1, by omega, by omega, ?_, ?_⟩)
              · rcases hmc (pos (w i) + 1) (by omega) with ⟨_, hm⟩ | ⟨hq, _⟩
                · omega
                · omega
              · rw [Function.iterate_succ_apply] at hBm
                rw [hu]
                exact hBm
    rcases key L le_rfl with h | ⟨d, hd1, _, hpd, _⟩ | ⟨m, hm1, hmL, hpm, _⟩
    · exact hne h.symm
    · omega
    · omega
  · intro v a b c ha hb hc hab hac hbc
    by_contra hv
    rcases hnb v a hv ha with h1 | h1 <;> rcases hnb v b hv hb with h2 | h2 <;>
      rcases hnb v c hv hc with h3 | h3 <;>
      first
        | exact hab (h1.trans h2.symm)
        | exact hac (h1.trans h3.symm)
        | exact hbc (h2.trans h3.symm)
