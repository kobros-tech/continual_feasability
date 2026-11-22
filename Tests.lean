import ContinualFeasibility

/-!
Kernel-checked synthetic tests (`decide +kernel`: kernel evaluation, no `native_decide`,
no `ofReduceBool`). Every test checks an actual certificate, not a label.
Conventions: `Spec p K T N`; times `0..T`; `ct`/`et` give class/example introduction time.
-/

open ContinualFeasibility Matrix

/-- Componentwise Boolean equality of row indices (avoids a `DecidableEq (RowIx ..)` instance). -/
def rowEq {p K T N : ℕ} : RowIx p K T N → RowIx p K T N → Bool
  | .inl a, .inl b => decide (a = b)
  | .inr (.inl a), .inr (.inl b) => decide (a = b)
  | .inr (.inr (.inl a)), .inr (.inr (.inl b)) => decide (a = b)
  | .inr (.inr (.inr (.inl a))), .inr (.inr (.inr (.inl b))) => decide (a = b)
  | .inr (.inr (.inr (.inr a))), .inr (.inr (.inr (.inr b))) => decide (a = b)
  | _, _ => false

/-- Indicator (multiplier 1) of a listed set of rows; all other multipliers are 0. -/
def supp {p K T N : ℕ} (L : List (RowIx p K T N)) : RowIx p K T N → ℚ :=
  fun r => if L.any (rowEq r) = true then 1 else 0

/-! ## Test 1: simple YES with known rational witness -/
def s1 : Spec 1 2 1 2 where
  ct := ![1, 1]
  W0 := fun _ _ => 0
  x := ![![1], ![-1]]
  y := ![0, 1]
  et := ![1, 1]
  isRef := fun _ => false
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def b1 : Var 1 2 1 → ℚ := fun u => if u.1 = 1 then (if u.2.1 = 0 then 1 else -1) else 0

theorem test1 : YesCert (Cmat s1) (dvec s1) b1 := by decide +kernel
theorem test1_feasible : Feasible s1 (unflat b1) := theoremC s1 b1 test1

/-! ## Test 2: simple NO with a known Farkas certificate (same feature, two labels) -/
def s2 : Spec 1 2 1 2 where
  ct := ![1, 1]
  W0 := fun _ _ => 0
  x := ![![1], ![1]]
  y := ![0, 1]
  et := ![1, 1]
  isRef := fun _ => false
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def l2 : RowIx 1 2 1 2 → ℚ := supp [nrow 0 1, nrow 1 0]

theorem test2 : NoCert (Cmat s2) (dvec s2) l2 := by decide +kernel
theorem test2_infeasible : ¬ ∃ W, Feasible s2 W := theoremD s2 l2 test2

/-! ## Test 3: nonzero null space, infeasible classification
Reference `x=(1,0)` has `R = [1 0]` with nullity 1; the new example `x=(1,0)` of the new class
contradicts the reference's margin against that class. -/
def s3 : Spec 2 3 2 3 where
  ct := ![1, 1, 2]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![0, 1], ![1, 0]]
  y := ![0, 1, 2]
  et := ![1, 1, 2]
  isRef := ![true, false, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def l3 : RowIx 2 3 2 3 → ℚ := supp [orow 2 0 2, nrow 2 0]

theorem test3 : NoCert (Cmat s3) (dvec s3) l3 := by decide +kernel
theorem test3_infeasible : ¬ ∃ W, Feasible s3 W := theoremD s3 l3 test3

def R3 : Matrix (Fin 1) (Fin 2) ℚ := !![1, 0]
def Q3 : Matrix (Fin 2) (Fin 1) ℚ := !![0; 1]
def P3 : Matrix (Fin 1) (Fin 2) ℚ := !![0, 1]
def S3 : Matrix (Fin 2) (Fin 1) ℚ := !![1; 0]
theorem cert3 : NullCert R3 Q3 P3 S3 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem test3_rank : R3.rank = 1 := (rank_eq cert3).trans (by norm_num)
theorem test3_nullity : Module.finrank ℚ (LinearMap.ker R3.mulVecLin) = 1 := nullity_eq cert3

/-! ## Test 4: preservation forces the update to zero -/
def R4 : Matrix (Fin 1) (Fin 1) ℚ := !![1]
def Q4 : Matrix (Fin 1) (Fin 0) ℚ := 0
def P4 : Matrix (Fin 0) (Fin 1) ℚ := 0
def S4 : Matrix (Fin 1) (Fin 1) ℚ := !![1]
theorem cert4 : NullCert R4 Q4 P4 S4 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem test4_forced : ∀ v, R4 *ᵥ v = 0 → v = 0 := fun v hv => forced_zero cert4 rfl v hv
theorem test4_rank : R4.rank = 1 := (rank_eq cert4).trans (by norm_num)

/-- Sequential YES where the old column is frozen (`W₂[0] = W₁[0]`). -/
def s4 : Spec 1 2 2 2 where
  ct := ![1, 2]
  W0 := fun _ _ => 0
  x := ![![1], ![-1]]
  y := ![0, 1]
  et := ![1, 2]
  isRef := ![true, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def b4 : Var 1 2 2 → ℚ := fun u => if u.2.1 = 0 then (if u.1 = 0 then 0 else 1) else 0
theorem test4_yes : YesCert (Cmat s4) (dvec s4) b4 := by decide +kernel

/-! ## Test 5: multiclass (3 classes, 2 competitors per example) -/
def s5 : Spec 2 3 1 3 where
  ct := ![1, 1, 1]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![0, 1], ![-1, -1]]
  y := ![0, 1, 2]
  et := ![1, 1, 1]
  isRef := fun _ => false
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def b5 : Var 2 3 1 → ℚ := fun u =>
  if u.1 = 0 then 0 else (![![2, 0], ![0, 2], ![-1, -1]] : Fin 3 → Fin 2 → ℚ) u.2.1 u.2.2
theorem test5 : YesCert (Cmat s5) (dvec s5) b5 := by decide +kernel

/-! ## Test 6: G₁ feasible, G₂ infeasible (prefix-joint results) -/
def s6g1 : Spec 2 2 1 2 where
  ct := ![1, 1]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![0, 1]]
  y := ![0, 1]
  et := ![1, 1]
  isRef := ![true, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def b6 : Var 2 2 1 → ℚ := fun u =>
  if u.1 = 0 then 0 else if u.2.1 = 0 then (if u.2.2 = 0 then 2 else 0)
  else (if u.2.2 = 0 then 0 else 2)
theorem test6_g1 : YesCert (Cmat s6g1) (dvec s6g1) b6 := by decide +kernel
-- G₂ is `s3` with `test3`.
theorem test6_g2 : ¬ ∃ W, Feasible s3 W := test3_infeasible

/-! ## Test 7: three experiences, all feasible; Theorem F applied to the witness -/
def s7 : Spec 2 4 3 4 where
  ct := ![1, 1, 2, 3]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![0, 1], ![-1, -1], ![1, 1]]
  y := ![0, 1, 2, 3]
  et := ![1, 1, 2, 3]
  isRef := ![true, true, true, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def b7 : Var 2 4 3 → ℚ := fun u =>
  if u.1 = 0 then 0
  else if u.2.1 = 0 then (if u.2.2 = 0 then 4 else 0)
  else if u.2.1 = 1 then (if u.2.2 = 1 then 4 else 0)
  else if u.2.1 = 3 then (if u.1 = 3 then 3 else 0)
  else 0

theorem test7 : YesCert (Cmat s7) (dvec s7) b7 := by decide +kernel
theorem test7_H0 : InitOK s7 := by decide +kernel
/-- Reference margins persist at the last experience (instance of Theorem F). -/
theorem test7_F (e : Fin 4) (he : s7.isRef e = true) (t : Fin 4) (hge : (s7.et e).val ≤ t.val) :
    ∀ k, k ≠ s7.y e → (s7.ct k).val ≤ t.val →
      s7.γ ≤ logit s7 (unflat b7) t e (s7.y e) - logit s7 (unflat b7) t e k :=
  yes_behavior s7 b7 test7 test7_H0 e he t hge

/-! ## Test 8: greedy trap
Joint problem is YES; one valid first-experience classifier (margin exactly γ) makes the
*conditional* second step infeasible. -/
def sJ : Spec 2 3 2 3 where
  ct := ![1, 1, 2]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![-1, 0], ![0, 1]]
  y := ![0, 1, 2]
  et := ![1, 1, 2]
  isRef := ![true, true, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def bJ : Var 2 3 2 → ℚ := fun u =>
  if u.1 = 0 then 0
  else if u.2.1 = 0 then (if u.2.2 = 0 then 2 else 0)
  else if u.2.1 = 1 then 0
  else (if u.1 = 2 then 1 else 0)
theorem test8_joint_yes : YesCert (Cmat sJ) (dvec sJ) bJ := by decide +kernel

/-- First experience alone, with the "bad" witness `w₀=(1,0), w₁=(0,0)` (margin exactly γ). -/
def sG1 : Spec 2 2 1 2 where
  ct := ![1, 1]
  W0 := fun _ _ => 0
  x := ![![1, 0], ![-1, 0]]
  y := ![0, 1]
  et := ![1, 1]
  isRef := ![true, true]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel
def bBad : Var 2 2 1 → ℚ := fun u => if u.1 = 0 then 0 else if u.2.1 = 0 ∧ u.2.2 = 0 then 1 else 0
theorem test8_bad_first_step_valid : YesCert (Cmat sG1) (dvec sG1) bBad := by decide +kernel

/-- Conditional second step from that fixed predecessor (`W0 = bad W₁`, old refs at time 0). -/
def sCond : Spec 2 3 1 3 where
  ct := ![0, 0, 1]
  W0 := ![![1, 0], ![0, 0], ![0, 0]]
  x := ![![1, 0], ![-1, 0], ![0, 1]]
  y := ![0, 1, 2]
  et := ![0, 0, 1]
  isRef := ![true, true, false]
  γ := 1
  hγ := by norm_num
  hy := by decide +kernel

def lCond : RowIx 2 3 1 3 → ℚ :=
  supp [orow 1 0 2, orow 1 1 2, prow 1 0 0 false, irow 0 0 false, prow 1 1 1 false, irow 1 0 true]

theorem test8_cond_no : NoCert (Cmat sCond) (dvec sCond) lCond := by decide +kernel
theorem test8_cond_infeasible : ¬ ∃ W, Feasible sCond W := theoremD sCond lCond test8_cond_no

/-! ## Stage 3a: array checker — valid AND deliberately invalid certificates
Systems are `C b ≥ d`. `sysY`: `x ≥ 1, -x ≥ -3`.  `sysN`: `x ≥ 1, -x ≥ 0` (infeasible). -/
open ContinualFeasibility.ArrSys

def sysY : ArrSys := { m := 2, n := 1, C := #[#[1], #[-1]], d := #[1, -3] }
def sysN : ArrSys := { m := 2, n := 1, C := #[#[1], #[-1]], d := #[1, 0] }

-- YES: valid witness accepted; violating, wrong-length and empty vectors rejected (no truncation)
theorem chk_yes_ok : checkYes sysY #[2] = true := by decide +kernel
theorem chk_yes_boundary : checkYes sysY #[1] = true := by decide +kernel
theorem chk_yes_violates : checkYes sysY #[5] = false := by decide +kernel
theorem chk_yes_toolong : checkYes sysY #[2, 2] = false := by decide +kernel
theorem chk_yes_empty : checkYes sysY #[] = false := by decide +kernel
-- infeasible system: no witness is accepted
theorem chk_yes_on_infeasible : checkYes sysN #[1] = false := by decide +kernel

-- NO: valid Farkas certificate accepted (also scaled); every defect rejected
theorem chk_no_ok : checkNo sysN #[1, 1] = true := by decide +kernel
theorem chk_no_scaled : checkNo sysN #[2, 2] = true := by decide +kernel
theorem chk_no_not_cancelling : checkNo sysN #[1, 0] = false := by decide +kernel   -- Cᵀλ ≠ 0
theorem chk_no_negative : checkNo sysN #[-1, -1] = false := by decide +kernel      -- λ ≱ 0
theorem chk_no_zero_obj : checkNo sysN #[0, 0] = false := by decide +kernel         -- dᵀλ = 0
theorem chk_no_toolong : checkNo sysN #[1, 1, 1] = false := by decide +kernel
theorem chk_no_tooshort : checkNo sysN #[1] = false := by decide +kernel
-- a feasible system admits no NO certificate in these attempts
theorem chk_no_on_feasible : checkNo sysY #[1, 1] = false := by decide +kernel

-- malformed systems are rejected by BOTH checkers (never silently truncated/padded)
def sysRagged : ArrSys := { m := 2, n := 1, C := #[#[1], #[-1, 0]], d := #[1, 0] }
def sysShortD : ArrSys := { m := 2, n := 1, C := #[#[1], #[-1]], d := #[1] }
def sysFewRows : ArrSys := { m := 3, n := 1, C := #[#[1], #[-1]], d := #[1, 0, 0] }
theorem chk_ragged_yes : checkYes sysRagged #[2] = false := by decide +kernel
theorem chk_ragged_no : checkNo sysRagged #[1, 1] = false := by decide +kernel
theorem chk_shortd_yes : checkYes sysShortD #[2] = false := by decide +kernel
theorem chk_shortd_no : checkNo sysShortD #[1, 1] = false := by decide +kernel
theorem chk_fewrows_no : checkNo sysFewRows #[1, 1, 0] = false := by decide +kernel

-- vacuous vs non-vacuous zero rows
def sysVac : ArrSys := { m := 2, n := 1, C := #[#[0], #[1]], d := #[0, 1] }   -- row 0: 0 ≥ 0
def sysZero : ArrSys := { m := 1, n := 1, C := #[#[0]], d := #[1] }           -- row 0: 0 ≥ 1
theorem chk_vacuous_ok : checkYes sysVac #[1] = true := by decide +kernel
theorem chk_zero_row_no : checkNo sysZero #[1] = true := by decide +kernel
theorem chk_zero_row_yes : checkYes sysZero #[0] = false := by decide +kernel

-- the accepted NO certificate really refutes the Matrix system (bridge theorem in use)
theorem chk_no_refutes : ¬ ∃ b, YesCert (toMat sysN) (toD sysN) b :=
  checkNo_sound sysN #[1, 1] chk_no_ok
theorem chk_yes_solves : ∃ b, YesCert (toMat sysY) (toD sysY) b :=
  checkYes_sound sysY #[2] chk_yes_ok

#print axioms theoremB
#print axioms theoremC
#print axioms theoremD
#print axioms theoremE
#print axioms theoremF
#print axioms yes_behavior
#print axioms ContinualFeasibility.preserves_of_rep
#print axioms ContinualFeasibility.mul_zero_iff
#print axioms ContinualFeasibility.forced_zero
#print axioms ContinualFeasibility.nullity_eq
#print axioms ContinualFeasibility.rank_eq
#print axioms ContinualFeasibility.farkas_forward
#print axioms ContinualFeasibility.farkas
#print axioms ContinualFeasibility.decision
#print axioms ContinualFeasibility.decision_exclusive
#print axioms ContinualFeasibility.vacuous_row_sat
#print axioms ContinualFeasibility.zero_row_infeasible
#print axioms ContinualFeasibility.ArrSys.checkYes_iff
#print axioms ContinualFeasibility.ArrSys.checkNo_iff
#print axioms ContinualFeasibility.ArrSys.checkYes_sound
#print axioms ContinualFeasibility.ArrSys.checkNo_sound
#print axioms ContinualFeasibility.ArrSys.check_exclusive
#print axioms ContinualFeasibility.ArrSys.yes_transfer
#print axioms ContinualFeasibility.ArrSys.no_transfer
#print axioms test1
#print axioms test2
#print axioms test3
#print axioms test3_rank
#print axioms test4_forced
#print axioms test4_yes
#print axioms test5
#print axioms test6_g1
#print axioms test6_g2
#print axioms test7_F
#print axioms test8_joint_yes
#print axioms test8_bad_first_step_valid
#print axioms test8_cond_infeasible
#print axioms chk_no_refutes
#print axioms chk_yes_solves
