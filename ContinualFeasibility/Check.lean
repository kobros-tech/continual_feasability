import ContinualFeasibility.Farkas

/-!
# Stage 3a — executable certificate checker and its bridge to the Matrix specification

The solver (Stage 3b) is *untrusted*: it only proposes arrays. Acceptance is decided here.

* `ArrSys`          : a dense exact-rational system `C b ≥ d` as `Array`s plus declared shape `(m, n)`.
* `ArrSys.Wf`       : shape validation (row count, `d` length, every row length). Never truncates.
* `checkYes S b`    : `Wf ∧ b.size = n ∧ ∀ i, d i ≤ (row i)·b`.
* `checkNo S l`     : `Wf ∧ l.size = m ∧ l ≥ 0 ∧ Cᵀ l = 0 ∧ dᵀ l > 0`.
* `checkYes_iff`, `checkNo_iff` : each checker is *equivalent* to the Matrix-level `YesCert` /
  `NoCert` of `toMat S`, `toD S` (plus shape conditions). So malformed input is rejected and a
  `true` answer is exactly the mathematical statement; nothing about a solver is assumed.
* `yes_transfer`, `no_transfer` : if the arrays encode a Matrix problem `(C, d)` under index
  bijections, an accepted array certificate yields a `YesCert` / `NoCert` for `(C, d)`.
  (Instantiating this for the sequential `Spec` is the next step.)
* Vacuous rows: `vacuous_row_sat` (a row `0 ≥ 0` is always satisfied) and
  `zero_row_infeasible` (a row `0 ≥ c` with `c > 0` is NOT vacuous: it refutes the system).
-/

namespace ContinualFeasibility

open Matrix

structure ArrSys where
  m : ℕ
  n : ℕ
  C : Array (Array ℚ)
  d : Array ℚ

namespace ArrSys

/-- Shape validation. -/
abbrev Wf (S : ArrSys) : Prop :=
  S.C.size = S.m ∧ S.d.size = S.m ∧ ∀ i : Fin S.m, (S.C.getD i.val #[]).size = S.n

/-- Dot product of the first `n` entries (entries are required to exist by `Wf`/size checks). -/
def dotA (n : ℕ) (a b : Array ℚ) : ℚ := ∑ j : Fin n, a.getD j.val 0 * b.getD j.val 0

def checkYes (S : ArrSys) (b : Array ℚ) : Bool :=
  decide (S.Wf ∧ b.size = S.n ∧
    ∀ i : Fin S.m, S.d.getD i.val 0 ≤ dotA S.n (S.C.getD i.val #[]) b)

def checkNo (S : ArrSys) (l : Array ℚ) : Bool :=
  decide (S.Wf ∧ l.size = S.m ∧ (∀ i : Fin S.m, 0 ≤ l.getD i.val 0) ∧
    (∀ j : Fin S.n, ∑ i : Fin S.m, l.getD i.val 0 * (S.C.getD i.val #[]).getD j.val 0 = 0) ∧
    0 < ∑ i : Fin S.m, S.d.getD i.val 0 * l.getD i.val 0)

/-- Matrix view of a (well-formed) array system. -/
def toMat (S : ArrSys) : Matrix (Fin S.m) (Fin S.n) ℚ :=
  fun i j => (S.C.getD i.val #[]).getD j.val 0

def toD (S : ArrSys) : Fin S.m → ℚ := fun i => S.d.getD i.val 0

def vecOf (n : ℕ) (a : Array ℚ) : Fin n → ℚ := fun j => a.getD j.val 0

/-- The YES checker is exactly shape validity plus the Matrix-level YES certificate. -/
theorem checkYes_iff (S : ArrSys) (b : Array ℚ) :
    checkYes S b = true ↔
      S.Wf ∧ b.size = S.n ∧ YesCert (toMat S) (toD S) (vecOf S.n b) := by
  unfold checkYes
  rw [decide_eq_true_iff]
  exact Iff.rfl

/-- The NO checker is exactly shape validity plus the Matrix-level Farkas certificate. -/
theorem checkNo_iff (S : ArrSys) (l : Array ℚ) :
    checkNo S l = true ↔
      S.Wf ∧ l.size = S.m ∧ NoCert (toMat S) (toD S) (vecOf S.m l) := by
  unfold checkNo
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hw, hs, hnn, hz, hp⟩
    exact ⟨hw, hs, fun i => hnn i, funext fun j => hz j, hp⟩
  · rintro ⟨hw, hs, hnn, hz, hp⟩
    exact ⟨hw, hs, fun i => hnn i, fun j => congrFun hz j, hp⟩

/-- Soundness against the mathematical statement: acceptance refutes/solves the Matrix system. -/
theorem checkYes_sound (S : ArrSys) (b : Array ℚ) (h : checkYes S b = true) :
    ∃ b', YesCert (toMat S) (toD S) b' :=
  ⟨vecOf S.n b, ((checkYes_iff S b).1 h).2.2⟩

theorem checkNo_sound (S : ArrSys) (l : Array ℚ) (h : checkNo S l = true) :
    ¬ ∃ b, YesCert (toMat S) (toD S) b :=
  farkas_forward _ _ (vecOf S.m l) ((checkNo_iff S l).1 h).2.2

/-- Accepted YES and accepted NO certificates for the same system are contradictory. -/
theorem check_exclusive (S : ArrSys) (b l : Array ℚ)
    (hy : checkYes S b = true) (hn : checkNo S l = true) : False :=
  checkNo_sound S l hn ⟨vecOf S.n b, ((checkYes_iff S b).1 hy).2.2⟩

/-! ### Relating an array system to an original Matrix problem -/

/-- `S` encodes `(C, d)` under row/column bijections `e`, `f`. -/
structure Encodes (S : ArrSys) {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (C : Matrix ρ ι ℚ) (d : ρ → ℚ) (e : Fin S.m ≃ ρ) (f : Fin S.n ≃ ι) : Prop where
  C_eq : ∀ i j, toMat S i j = C (e i) (f j)
  d_eq : ∀ i, toD S i = d (e i)

theorem yes_transfer {S : ArrSys} {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C : Matrix ρ ι ℚ} {d : ρ → ℚ} {e : Fin S.m ≃ ρ} {f : Fin S.n ≃ ι}
    (hE : Encodes S C d e f) (b : Array ℚ) (h : checkYes S b = true) :
    ∃ b', YesCert C d b' := by
  have hY := ((checkYes_iff S b).1 h).2.2
  refine ⟨fun u => vecOf S.n b (f.symm u), fun r => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective r
  have h2 : (C *ᵥ fun u => vecOf S.n b (f.symm u)) (e i) = (toMat S *ᵥ vecOf S.n b) i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp f]
    simp [hE.C_eq]
  rw [h2, ← hE.d_eq]
  exact hY i

theorem no_transfer {S : ArrSys} {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C : Matrix ρ ι ℚ} {d : ρ → ℚ} {e : Fin S.m ≃ ρ} {f : Fin S.n ≃ ι}
    (hE : Encodes S C d e f) (l : Array ℚ) (h : checkNo S l = true) :
    ∃ l', NoCert C d l' := by
  obtain ⟨_, _, hnn, hz, hp⟩ := (checkNo_iff S l).1 h
  refine ⟨fun r => vecOf S.m l (e.symm r), fun r => hnn (e.symm r), ?_, ?_⟩
  · funext u
    obtain ⟨j, rfl⟩ := f.surjective u
    have hj := congrFun hz j
    simp only [Matrix.vecMul, dotProduct]
    rw [← Equiv.sum_comp e]
    simp only [← hE.C_eq, Equiv.symm_apply_apply]
    exact hj
  · show 0 < ∑ r, d r * vecOf S.m l (e.symm r)
    rw [← Equiv.sum_comp e]
    simp only [← hE.d_eq, Equiv.symm_apply_apply]
    exact hp

end ArrSys

/-! ### Vacuous rows (needed before any sparse / row-skipping checker) -/

/-- A row `0 ≥ 0` is satisfied by every `b`; only such rows may be skipped. -/
theorem vacuous_row_sat {ρ ι : Type*} [Fintype ρ] [Fintype ι] (C : Matrix ρ ι ℚ) (d : ρ → ℚ)
    (r : ρ) (hC : C r = 0) (hd : d r = 0) (b : ι → ℚ) : d r ≤ (C *ᵥ b) r := by
  have : (C *ᵥ b) r = C r ⬝ᵥ b := rfl
  rw [this, hC, zero_dotProduct, hd]

/-- A row `0 ≥ c` with `c > 0` is NOT vacuous: it makes the system infeasible. -/
theorem zero_row_infeasible {ρ ι : Type*} [Fintype ρ] [Fintype ι] (C : Matrix ρ ι ℚ)
    (d : ρ → ℚ) (r : ρ) (hC : C r = 0) (hd : 0 < d r) : ¬ ∃ b, YesCert C d b := by
  rintro ⟨b, hb⟩
  have h1 := hb r
  have : (C *ᵥ b) r = C r ⬝ᵥ b := rfl
  rw [this, hC, zero_dotProduct] at h1
  linarith

end ContinualFeasibility
