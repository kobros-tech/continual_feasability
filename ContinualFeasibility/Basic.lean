import Mathlib

/-!
# Theorem A — preservation characterization

Dimensions: `R : Matrix (Fin m) (Fin p) ℚ`, `Q : Matrix (Fin p) (Fin r) ℚ`,
`P : Matrix (Fin r) (Fin p) ℚ`, `S : Matrix (Fin p) (Fin m) ℚ`.

Spanning certificate (`NullCert`):  `R Q = 0`,  `Q P + S R = I_p`,  `P Q = I_r`.

Conclusions: `im Q = ker R`, `nullity R = r`, `rank R = p - r`.

Soundness (`R (Q B) = 0`) needs only `R Q = 0`; *completeness* (every `ΔW` with
`R ΔW = 0` is `Q B`) needs the certificate, i.e. the explicit assumption that `Q`
spans the whole null space. The decision LP does not use `Q` (decision D2).
-/

namespace ContinualFeasibility

open Matrix

section TheoremA

variable {m p r : ℕ}

/-- Exactly checkable certificate that the columns of `Q` form a basis of `ker R`. -/
structure NullCert (R : Matrix (Fin m) (Fin p) ℚ) (Q : Matrix (Fin p) (Fin r) ℚ)
    (P : Matrix (Fin r) (Fin p) ℚ) (S : Matrix (Fin p) (Fin m) ℚ) : Prop where
  rq : R * Q = 0
  qp : Q * P + S * R = 1
  pq : P * Q = 1

/-- Soundness: every `Q B` preserves the reference logits. Needs only `R Q = 0`. -/
theorem preserves_of_rep {K : ℕ} (R : Matrix (Fin m) (Fin p) ℚ) (Q : Matrix (Fin p) (Fin r) ℚ)
    (hRQ : R * Q = 0) (B : Matrix (Fin r) (Fin K) ℚ) : R * (Q * B) = 0 := by
  rw [← Matrix.mul_assoc, hRQ, Matrix.zero_mul]

variable {R : Matrix (Fin m) (Fin p) ℚ} {Q : Matrix (Fin p) (Fin r) ℚ}
  {P : Matrix (Fin r) (Fin p) ℚ} {S : Matrix (Fin p) (Fin m) ℚ}

/-- Vector form: `R v = 0 ↔ v ∈ im Q`. -/
theorem mulVec_zero_iff (h : NullCert R Q P S) (v : Fin p → ℚ) :
    R *ᵥ v = 0 ↔ ∃ c, Q *ᵥ c = v := by
  constructor
  · intro hv
    refine ⟨P *ᵥ v, ?_⟩
    calc Q *ᵥ (P *ᵥ v)
        = Q *ᵥ (P *ᵥ v) + S *ᵥ (R *ᵥ v) := by rw [hv, Matrix.mulVec_zero, add_zero]
      _ = (Q * P + S * R) *ᵥ v := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = v := by rw [h.qp, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_mulVec, h.rq, Matrix.zero_mulVec]

/-- Matrix form (Theorem A): `R ΔW = 0 ↔ ΔW = Q B` for some `B`. -/
theorem mul_zero_iff (h : NullCert R Q P S) {K : ℕ} (Δ : Matrix (Fin p) (Fin K) ℚ) :
    R * Δ = 0 ↔ ∃ B : Matrix (Fin r) (Fin K) ℚ, Δ = Q * B := by
  constructor
  · intro hΔ
    refine ⟨P * Δ, ?_⟩
    calc Δ = (1 : Matrix (Fin p) (Fin p) ℚ) * Δ := (Matrix.one_mul Δ).symm
      _ = (Q * P + S * R) * Δ := by rw [h.qp]
      _ = Q * (P * Δ) + S * (R * Δ) := by rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q * (P * Δ) := by rw [hΔ, Matrix.mul_zero, add_zero]
  · rintro ⟨B, rfl⟩
    exact preserves_of_rep R Q h.rq B

/-- `Q` is injective (needed for the exact nullity). -/
theorem Q_injective (h : NullCert R Q P S) : Function.Injective Q.mulVecLin := by
  intro c c' hcc
  have key : ∀ c : Fin r → ℚ, P *ᵥ (Q *ᵥ c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, h.pq, Matrix.one_mulVec]
  have h1 : Q *ᵥ c = Q *ᵥ c' := hcc
  calc c = P *ᵥ (Q *ᵥ c) := (key c).symm
    _ = P *ᵥ (Q *ᵥ c') := by rw [h1]
    _ = c' := key c'

theorem ker_eq_range (h : NullCert R Q P S) :
    LinearMap.ker R.mulVecLin = LinearMap.range Q.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply]
  exact mulVec_zero_iff h v

/-- `nullity(R) = r`. -/
theorem nullity_eq (h : NullCert R Q P S) :
    Module.finrank ℚ (LinearMap.ker R.mulVecLin) = r := by
  rw [ker_eq_range h, LinearMap.finrank_range_of_inj (Q_injective h)]
  simp

/-- `rank(R) = p - r` (rank–nullity). -/
theorem rank_eq (h : NullCert R Q P S) : R.rank = p - r := by
  have h1 := LinearMap.finrank_range_add_finrank_ker R.mulVecLin
  rw [nullity_eq h] at h1
  have h2 : Module.finrank ℚ (Fin p → ℚ) = p := by simp
  rw [h2] at h1
  unfold Matrix.rank
  omega

/-- If the null space is trivial (`r = 0`), preservation forces the update to be zero. -/
theorem forced_zero (h : NullCert R Q P S) (hr : r = 0) (v : Fin p → ℚ) (hv : R *ᵥ v = 0) :
    v = 0 := by
  obtain ⟨c, rfl⟩ := (mulVec_zero_iff h v).1 hv
  subst hr
  funext i
  simp [Matrix.mulVec, dotProduct]

end TheoremA

end ContinualFeasibility
