import ContinualFeasibility

/-!
Kernel-checked synthetic tests (`decide +kernel`: kernel evaluation, no `native_decide`,
no `ofReduceBool`). Every test checks an actual certificate, not a label.
Conventions: `Spec p K T N`; times `0..T`; `ct`/`et` give class/example introduction time.
-/

open ContinualFeasibility Matrix

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

def l2 : RowIx 1 2 1 2 → ℚ := fun r => if r = nrow 0 1 ∨ r = nrow 1 0 then 1 else 0

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

def l3 : RowIx 2 3 2 3 → ℚ := fun r => if r = orow 2 0 2 ∨ r = nrow 2 0 then 1 else 0

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

def lCond : RowIx 2 3 1 3 → ℚ := fun r =>
  if r = orow 1 0 2 ∨ r = orow 1 1 2 ∨ r = prow 1 0 0 false ∨ r = irow 0 0 false
     ∨ r = prow 1 1 1 false ∨ r = irow 1 0 true then 1 else 0

theorem test8_cond_no : NoCert (Cmat sCond) (dvec sCond) lCond := by decide +kernel
theorem test8_cond_infeasible : ¬ ∃ W, Feasible sCond W := theoremD sCond lCond test8_cond_no

#print axioms theoremB
#print axioms theoremC
#print axioms theoremD
#print axioms theoremE
#print axioms theoremF
#print axioms ContinualFeasibility.rank_eq
#print axioms test7_F
#print axioms test8_cond_infeasible
