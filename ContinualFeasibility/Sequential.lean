import ContinualFeasibility.Farkas

/-!
# Sequential class-incremental formulation (Theorems B, C, F, joint E)

Times `0..T` (`Fin (T+1)`); time 0 is the given initial classifier `W0`; times `1..T`
are the experiences. Variables are the FULL arrays `W t k j` (`(T+1)·K·p` of them);
entries of columns not yet introduced are constrained to 0 by explicit (Z) rows, so
"unseen classes are inactive" is a constraint, not a convention.

* `ct k`  : time at which class `k` is introduced; `A_t = {k | ct k ≤ t}`, `N_t = {k | ct k = t}`.
* `et e`  : time at which example `e` is introduced; `et e = 0` means initial reference data.
* `isRef e` : `e` is a designated reference example (reference ⊆ training is the data's
  responsibility: a reference example is introduced with its task).

Constraints (all linear in `W`):
* (Z) inactive columns are 0;  (I) time-0 active columns equal `W0`.
* (P) for `t ≥ 1`, reference `e` with `et e < t`, class `k` with `ct k < t`:
      `logit_t(e,k) = logit_{t-1}(e,k)`            (exact preservation `R ΔW_old = 0`).
* (N) for `e` with `et e ≥ 1`, `k ≠ y e`, `ct k ≤ et e`:
      `logit(e,y e) - logit(e,k) ≥ γ` at time `et e`.
* (O) for `t ≥ 1`, reference `e` with `et e < t`, new class `k` (`ct k = t`):
      `logit_t(e,y e) - logit_t(e,k) ≥ γ`.

Everything is stated in `ℕ`-valued (`Fin.val`) comparisons to keep `omega` usable.
-/

namespace ContinualFeasibility

open Matrix

structure Spec (p K T N : ℕ) where
  ct : Fin K → Fin (T + 1)
  W0 : Fin K → Fin p → ℚ
  x : Fin N → Fin p → ℚ
  y : Fin N → Fin K
  et : Fin N → Fin (T + 1)
  isRef : Fin N → Bool
  γ : ℚ
  hγ : 0 < γ
  hy : ∀ e, (ct (y e)).val = (et e).val

variable {p K T N : ℕ}

def t0 {T : ℕ} : Fin (T + 1) := ⟨0, Nat.succ_pos T⟩

def pv {T : ℕ} (t : Fin (T + 1)) : Fin (T + 1) := ⟨t.val - 1, by have := t.isLt; omega⟩

def logit (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ)
    (t : Fin (T + 1)) (e : Fin N) (k : Fin K) : ℚ := S.x e ⬝ᵥ W t k

/-- Reference examples born at time 0 must already have margin `γ` under `W0` (hypothesis H₀). -/
abbrev InitOK (S : Spec p K T N) : Prop :=
  ∀ e, S.isRef e = true → (S.et e).val = 0 → ∀ k, k ≠ S.y e → (S.ct k).val = 0 →
    S.γ ≤ S.x e ⬝ᵥ S.W0 (S.y e) - S.x e ⬝ᵥ S.W0 k

/-- The joint feasibility problem over all `W_0..W_T`. -/
structure Feasible (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ) : Prop where
  zero : ∀ t k j, t.val < (S.ct k).val → W t k j = 0
  init : ∀ k j, (S.ct k).val = 0 → W t0 k j = S.W0 k j
  pres : ∀ t e k, S.isRef e = true → (S.et e).val < t.val → (S.ct k).val < t.val →
    logit S W t e k = logit S W (pv t) e k
  new : ∀ e k, 0 < (S.et e).val → k ≠ S.y e → (S.ct k).val ≤ (S.et e).val →
    S.γ ≤ logit S W (S.et e) e (S.y e) - logit S W (S.et e) e k
  old : ∀ t e k, S.isRef e = true → (S.et e).val < t.val → (S.ct k).val = t.val →
    S.γ ≤ logit S W t e (S.y e) - logit S W t e k

/-! ### The linear system `C b ≥ d` -/

abbrev Var (p K T : ℕ) := Fin (T + 1) × Fin K × Fin p

/-- Row index: Z, I, P (each with a sign for the two inequalities of an equality), N, O. -/
abbrev RowIx (p K T N : ℕ) :=
  (Fin (T + 1) × Fin K × Fin p × Bool) ⊕ (Fin K × Fin p × Bool) ⊕
  (Fin (T + 1) × Fin N × Fin K × Bool) ⊕ (Fin N × Fin K) ⊕ (Fin (T + 1) × Fin N × Fin K)

def sg : Bool → ℚ
  | true => 1
  | false => -1

def lin (t : Fin (T + 1)) (k : Fin K) (v : Fin p → ℚ) : Var p K T → ℚ :=
  fun u => if u.1 = t ∧ u.2.1 = k then v u.2.2 else 0

def flat (W : Fin (T + 1) → Fin K → Fin p → ℚ) : Var p K T → ℚ := fun u => W u.1 u.2.1 u.2.2
def unflat (b : Var p K T → ℚ) : Fin (T + 1) → Fin K → Fin p → ℚ := fun t k j => b (t, k, j)

/-- Rows whose side condition fails are the vacuous row `0 ≥ 0`. -/
def coef (S : Spec p K T N) : RowIx p K T N → (Var p K T → ℚ)
  | .inl (t, k, j, s) =>
      if t.val < (S.ct k).val then sg s • lin t k (Pi.single j 1) else 0
  | .inr (.inl (k, j, s)) =>
      if (S.ct k).val = 0 then sg s • lin t0 k (Pi.single j 1) else 0
  | .inr (.inr (.inl (t, e, k, s))) =>
      if S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val < t.val
      then sg s • (lin t k (S.x e) - lin (pv t) k (S.x e)) else 0
  | .inr (.inr (.inr (.inl (e, k)))) =>
      if 0 < (S.et e).val ∧ k ≠ S.y e ∧ (S.ct k).val ≤ (S.et e).val
      then lin (S.et e) (S.y e) (S.x e) - lin (S.et e) k (S.x e) else 0
  | .inr (.inr (.inr (.inr (t, e, k)))) =>
      if S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val = t.val
      then lin t (S.y e) (S.x e) - lin t k (S.x e) else 0

def rhs (S : Spec p K T N) : RowIx p K T N → ℚ
  | .inl _ => 0
  | .inr (.inl (k, j, s)) => if (S.ct k).val = 0 then sg s * S.W0 k j else 0
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr (.inl (e, k)))) =>
      if 0 < (S.et e).val ∧ k ≠ S.y e ∧ (S.ct k).val ≤ (S.et e).val then S.γ else 0
  | .inr (.inr (.inr (.inr (t, e, k)))) =>
      if S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val = t.val then S.γ else 0

/-- Semantic value of a row at `W`. -/
def val (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ) : RowIx p K T N → ℚ
  | .inl (t, k, j, s) => if t.val < (S.ct k).val then sg s * W t k j else 0
  | .inr (.inl (k, j, s)) => if (S.ct k).val = 0 then sg s * W t0 k j else 0
  | .inr (.inr (.inl (t, e, k, s))) =>
      if S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val < t.val
      then sg s * (logit S W t e k - logit S W (pv t) e k) else 0
  | .inr (.inr (.inr (.inl (e, k)))) =>
      if 0 < (S.et e).val ∧ k ≠ S.y e ∧ (S.ct k).val ≤ (S.et e).val
      then logit S W (S.et e) e (S.y e) - logit S W (S.et e) e k else 0
  | .inr (.inr (.inr (.inr (t, e, k)))) =>
      if S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val = t.val
      then logit S W t e (S.y e) - logit S W t e k else 0

def Cmat (S : Spec p K T N) : Matrix (RowIx p K T N) (Var p K T) ℚ := Matrix.of (coef S)
def dvec (S : Spec p K T N) : RowIx p K T N → ℚ := rhs S

theorem lin_dot (t : Fin (T + 1)) (k : Fin K) (v : Fin p → ℚ)
    (W : Fin (T + 1) → Fin K → Fin p → ℚ) :
    lin t k v ⬝ᵥ flat W = v ⬝ᵥ W t k := by
  simp only [dotProduct, lin, flat, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single t]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem coef_dot (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ) (r : RowIx p K T N) :
    coef S r ⬝ᵥ flat W = val S W r := by
  rcases r with ⟨t, k, j, s⟩ | ⟨k, j, s⟩ | ⟨t, e, k, s⟩ | ⟨e, k⟩ | ⟨t, e, k⟩
  · simp only [coef, val]
    split_ifs <;> simp [lin_dot, smul_dotProduct]
  · simp only [coef, val]
    split_ifs <;> simp [lin_dot, smul_dotProduct]
  · simp only [coef, val]
    split_ifs <;> simp [lin_dot, smul_dotProduct, sub_dotProduct, logit]
  · simp only [coef, val]
    split_ifs <;> simp [lin_dot, sub_dotProduct, logit]
  · simp only [coef, val]
    split_ifs <;> simp [lin_dot, sub_dotProduct, logit]

/-- Row-wise reformulation of `Feasible`. -/
theorem feasible_iff (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ) :
    Feasible S W ↔ ∀ r, rhs S r ≤ val S W r := by
  constructor
  · intro hW r
    rcases r with ⟨t, k, j, s⟩ | ⟨k, j, s⟩ | ⟨t, e, k, s⟩ | ⟨e, k⟩ | ⟨t, e, k⟩
    · simp only [rhs, val]
      split_ifs with h
      · rw [hW.zero t k j h]; simp
      · exact le_refl _
    · simp only [rhs, val]
      split_ifs with h
      · exact le_of_eq (by rw [hW.init k j h])
      · exact le_refl _
    · simp only [rhs, val]
      split_ifs with h
      · rw [hW.pres t e k h.1 h.2.1 h.2.2]; simp
      · exact le_refl _
    · simp only [rhs, val]
      split_ifs with h
      · exact hW.new e k h.1 h.2.1 h.2.2
      · exact le_refl _
    · simp only [rhs, val]
      split_ifs with h
      · exact hW.old t e k h.1 h.2.1 h.2.2
      · exact le_refl _
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t k j hlt
      have h1 := h (Sum.inl (t, k, j, true))
      have h2 := h (Sum.inl (t, k, j, false))
      simp only [rhs, val, if_pos hlt, sg] at h1 h2
      linarith
    · intro k j hk
      have h1 := h (Sum.inr (Sum.inl (k, j, true)))
      have h2 := h (Sum.inr (Sum.inl (k, j, false)))
      simp only [rhs, val, if_pos hk, sg] at h1 h2
      linarith
    · intro t e k h1 h2 h3
      have hc : S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val < t.val := ⟨h1, h2, h3⟩
      have hA := h (Sum.inr (Sum.inr (Sum.inl (t, e, k, true))))
      have hB := h (Sum.inr (Sum.inr (Sum.inl (t, e, k, false))))
      simp only [rhs, val, if_pos hc, sg] at hA hB
      linarith
    · intro e k h1 h2 h3
      have hc : 0 < (S.et e).val ∧ k ≠ S.y e ∧ (S.ct k).val ≤ (S.et e).val := ⟨h1, h2, h3⟩
      have := h (Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, k)))))
      simp only [rhs, val, if_pos hc] at this
      exact this
    · intro t e k h1 h2 h3
      have hc : S.isRef e = true ∧ (S.et e).val < t.val ∧ (S.ct k).val = t.val := ⟨h1, h2, h3⟩
      have := h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, e, k)))))
      simp only [rhs, val, if_pos hc] at this
      exact this

/-- Theorem B: joint feasibility ⇔ the finite linear system `C b ≥ d` has a solution. -/
theorem theoremB (S : Spec p K T N) :
    (∃ W, Feasible S W) ↔ ∃ b, YesCert (Cmat S) (dvec S) b := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨flat W, fun r => ?_⟩
    show rhs S r ≤ coef S r ⬝ᵥ flat W
    rw [coef_dot]
    exact (feasible_iff S W).1 hW r
  · rintro ⟨b, hb⟩
    refine ⟨unflat b, (feasible_iff S _).2 fun r => ?_⟩
    have hflat : flat (unflat b) = b := by funext u; rfl
    have := hb r
    show rhs S r ≤ _
    rw [← coef_dot, hflat]
    exact this

/-- Theorem C: a YES certificate yields a full classifier sequence satisfying (Z)(I)(P)(N)(O). -/
theorem theoremC (S : Spec p K T N) (b : Var p K T → ℚ) (h : YesCert (Cmat S) (dvec S) b) :
    Feasible S (unflat b) := by
  have hflat : flat (unflat b) = b := by funext u; rfl
  refine (feasible_iff S _).2 fun r => ?_
  have := h r
  show rhs S r ≤ _
  rw [← coef_dot, hflat]
  exact this

/-- Theorem D for the sequential system: a NO certificate refutes every classifier sequence. -/
theorem theoremD (S : Spec p K T N) (l : RowIx p K T N → ℚ) (h : NoCert (Cmat S) (dvec S) l) :
    ¬ ∃ W, Feasible S W := fun hW =>
  farkas_forward _ _ l h ((theoremB S).1 hW)

/-- Theorem E for the sequential system: exactly one of a feasible sequence / a NO certificate. -/
theorem theoremE (S : Spec p K T N) :
    ((∃ W, Feasible S W) ∨ (∃ l, NoCert (Cmat S) (dvec S) l)) ∧
    ¬ ((∃ W, Feasible S W) ∧ (∃ l, NoCert (Cmat S) (dvec S) l)) := by
  refine ⟨?_, ?_⟩
  · rcases decision (Cmat S) (dvec S) with h | h
    · exact Or.inl ((theoremB S).2 h)
    · exact Or.inr h
  · rintro ⟨hW, l, hl⟩
    exact theoremD S l hl hW

/-! ### Theorem F: preservation of classification behavior -/

theorem behavior_aux (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ)
    (hW : Feasible S W) (H0 : InitOK S) (e : Fin N) (he : S.isRef e = true) :
    ∀ n : ℕ, ∀ t : Fin (T + 1), t.val = (S.et e).val + n →
      (∀ k, (S.ct k).val ≤ (S.et e).val → logit S W t e k = logit S W (S.et e) e k) ∧
      (∀ k, k ≠ S.y e → (S.ct k).val ≤ t.val →
        S.γ ≤ logit S W t e (S.y e) - logit S W t e k) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have htt : t = S.et e := Fin.ext (by omega)
    subst htt
    refine ⟨fun k _ => rfl, fun k hky hkt => ?_⟩
    by_cases h0 : 0 < (S.et e).val
    · exact hW.new e k h0 hky hkt
    · have hz : (S.et e).val = 0 := by omega
      have hz' : S.et e = t0 := Fin.ext (by show (S.et e).val = 0; exact hz)
      have hk0 : (S.ct k).val = 0 := by omega
      have hy0 : (S.ct (S.y e)).val = 0 := by rw [S.hy]; exact hz
      have hk : W t0 k = S.W0 k := funext fun j => hW.init k j hk0
      have hyk : W t0 (S.y e) = S.W0 (S.y e) := funext fun j => hW.init _ j hy0
      have := H0 e he hz k hky hk0
      simp only [logit]
      rw [hz', hk, hyk]
      exact this
  | succ n ih =>
    intro t ht
    have hlt : (S.et e).val < t.val := by omega
    have hpv : (pv t).val = (S.et e).val + n := by simp only [pv]; omega
    obtain ⟨ha, hb⟩ := ih (pv t) hpv
    constructor
    · intro k hk
      have hk' : (S.ct k).val < t.val := by omega
      rw [hW.pres t e k he hlt hk']
      exact ha k hk
    · intro k hky hkt
      by_cases hnew : (S.ct k).val = t.val
      · exact hW.old t e k he hlt hnew
      · have hk' : (S.ct k).val < t.val := by omega
        have hy' : (S.ct (S.y e)).val < t.val := by rw [S.hy]; exact hlt
        rw [hW.pres t e (S.y e) he hlt hy', hW.pres t e k he hlt hk']
        exact hb k hky (by simp only [pv]; omega)

/-- **Theorem F.** Under H₀ (`InitOK`), any feasible sequence keeps, for every reference example
`e` and every later time `t`: its old logits unchanged, margin `γ` against every active
competitor, hence `y e` is the strict argmax over the active classes. -/
theorem theoremF (S : Spec p K T N) (W : Fin (T + 1) → Fin K → Fin p → ℚ)
    (hW : Feasible S W) (H0 : InitOK S) (e : Fin N) (he : S.isRef e = true)
    (t : Fin (T + 1)) (hge : (S.et e).val ≤ t.val) :
    (∀ k, (S.ct k).val ≤ (S.et e).val → logit S W t e k = logit S W (S.et e) e k) ∧
    (∀ k, k ≠ S.y e → (S.ct k).val ≤ t.val →
      S.γ ≤ logit S W t e (S.y e) - logit S W t e k) ∧
    (∀ k, k ≠ S.y e → (S.ct k).val ≤ t.val → logit S W t e k < logit S W t e (S.y e)) := by
  obtain ⟨h1, h2⟩ := behavior_aux S W hW H0 e he (t.val - (S.et e).val) t (by omega)
  refine ⟨h1, h2, fun k hk hkt => ?_⟩
  have := h2 k hk hkt
  have hγ := S.hγ
  linarith

/-- Combined statement: a verified YES certificate gives preservation + margins (Theorem F). -/
theorem yes_behavior (S : Spec p K T N) (b : Var p K T → ℚ) (h : YesCert (Cmat S) (dvec S) b)
    (H0 : InitOK S) (e : Fin N) (he : S.isRef e = true) (t : Fin (T + 1))
    (hge : (S.et e).val ≤ t.val) :
    (∀ k, k ≠ S.y e → (S.ct k).val ≤ t.val →
      S.γ ≤ logit S (unflat b) t e (S.y e) - logit S (unflat b) t e k) :=
  (theoremF S _ (theoremC S b h) H0 e he t hge).2.1

def nrow (e : Fin N) (k : Fin K) : RowIx p K T N := Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, k))))
def orow (t : Fin (T + 1)) (e : Fin N) (k : Fin K) : RowIx p K T N :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, e, k))))
def prow (t : Fin (T + 1)) (e : Fin N) (k : Fin K) (s : Bool) : RowIx p K T N :=
  Sum.inr (Sum.inr (Sum.inl (t, e, k, s)))
def irow (k : Fin K) (j : Fin p) (s : Bool) : RowIx p K T N := Sum.inr (Sum.inl (k, j, s))

end ContinualFeasibility
