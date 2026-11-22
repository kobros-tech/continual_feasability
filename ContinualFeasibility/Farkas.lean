import Mathlib

/-!
# Theorem D / E (core): Farkas' lemma over ℚ

Mathlib (tag v4.36.0) has no ordered-field Farkas / Motzkin transposition theorem
(checked by file listing; `Mathlib/Geometry/Convex/Cone/DualFinite` has `DualFG`
duality but not this statement). We therefore prove the needed form directly by
Fourier–Motzkin elimination, which also produces the multiplier `l`.

Final statements, for `C : Matrix ρ ι ℚ`, `d : ρ → ℚ`, `ρ ι` finite:

* `farkas_forward` : `l ≥ 0 ∧ l ᵥ* C = 0 ∧ 0 < d ⬝ᵥ l → ¬ ∃ b, d ≤ C *ᵥ b`
* `farkas`         : `¬ ∃ b, d ≤ C *ᵥ b → ∃ l, l ≥ 0 ∧ l ᵥ* C = 0 ∧ 0 < d ⬝ᵥ l`

Note `l ᵥ* C = 0` is the statement `Cᵀ l = 0`.
-/

namespace ContinualFeasibility

open Matrix

/-- Feasibility `∃ b, d ≤ C b` as the certificate predicate for YES. -/
abbrev YesCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (C : Matrix ρ ι ℚ) (d : ρ → ℚ) (b : ι → ℚ) : Prop :=
  ∀ r, d r ≤ (C *ᵥ b) r

/-- Farkas certificate for NO: `l ≥ 0`, `Cᵀ l = 0`, `dᵀ l > 0`. -/
abbrev NoCert {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (C : Matrix ρ ι ℚ) (d : ρ → ℚ) (l : ρ → ℚ) : Prop :=
  (∀ r, 0 ≤ l r) ∧ l ᵥ* C = 0 ∧ 0 < d ⬝ᵥ l

/-- Theorem D (forward): a NO certificate refutes every candidate YES vector. -/
theorem farkas_forward {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (C : Matrix ρ ι ℚ) (d l : ρ → ℚ) (h : NoCert C d l) :
    ¬ ∃ b, YesCert C d b := by
  rintro ⟨b, hb⟩
  obtain ⟨hl, hC, hd⟩ := h
  have h1 : d ⬝ᵥ l ≤ (C *ᵥ b) ⬝ᵥ l := by
    unfold dotProduct
    exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hb r) (hl r)
  have h2 : (C *ᵥ b) ⬝ᵥ l = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, hC]
    simp
  linarith

/-- Theorem E (exclusivity half): YES and NO certificates cannot coexist. -/
theorem not_both {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (C : Matrix ρ ι ℚ) (d : ρ → ℚ) (b : ι → ℚ) (l : ρ → ℚ)
    (hy : YesCert C d b) (hn : NoCert C d l) : False :=
  farkas_forward C d l hn ⟨b, hy⟩

/-! ### Fourier–Motzkin core -/

/-- A row `(a, c)` represents the constraint `c ≤ a ⬝ᵥ b`. -/
abbrev LRow (n : ℕ) := (Fin n → ℚ) × ℚ

/-- Satisfaction of a row. -/
def LRow.Sat {n : ℕ} (b : Fin n → ℚ) (r : LRow n) : Prop := r.2 ≤ r.1 ⬝ᵥ b

/-- Nonnegative-combination closure of a set of rows. -/
inductive Cone {n : ℕ} (S : Set (LRow n)) : LRow n → Prop
  | base {r : LRow n} : r ∈ S → Cone S r
  | zero : Cone S 0
  | add {r s : LRow n} : Cone S r → Cone S s → Cone S (r + s)
  | smul {t : ℚ} {r : LRow n} : 0 ≤ t → Cone S r → Cone S (t • r)

/-- Extend a vector by a last coordinate. -/
def ext {n : ℕ} (b : Fin n → ℚ) (x : ℚ) : Fin (n + 1) → ℚ :=
  Fin.snoc (α := fun _ => ℚ) b x

/-- Tail of a row (drop the last variable). -/
def tail {n : ℕ} (a : Fin (n + 1) → ℚ) : Fin n → ℚ := fun i => a i.castSucc

theorem dot_ext {n : ℕ} (a : Fin (n + 1) → ℚ) (b : Fin n → ℚ) (x : ℚ) :
    a ⬝ᵥ ext b x = tail a ⬝ᵥ b + a (Fin.last n) * x := by
  simp [dotProduct, ext, tail, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Projection of a row with zero last coefficient. -/
def proj {n : ℕ} (r : LRow (n + 1)) : LRow n := (tail r.1, r.2)

/-- Elimination combination of a positive and a negative row. -/
def comb {n : ℕ} (r s : LRow (n + 1)) : LRow n :=
  ((fun i => (-s.1 (Fin.last n)) * r.1 i.castSucc + r.1 (Fin.last n) * s.1 i.castSucc),
   (-s.1 (Fin.last n)) * r.2 + r.1 (Fin.last n) * s.2)

def posS {n : ℕ} (S : Set (LRow (n + 1))) : Set (LRow (n + 1)) :=
  {r | r ∈ S ∧ 0 < r.1 (Fin.last n)}
def negS {n : ℕ} (S : Set (LRow (n + 1))) : Set (LRow (n + 1)) :=
  {r | r ∈ S ∧ r.1 (Fin.last n) < 0}
def zerS {n : ℕ} (S : Set (LRow (n + 1))) : Set (LRow (n + 1)) :=
  {r | r ∈ S ∧ r.1 (Fin.last n) = 0}

/-- The system with the last variable eliminated. -/
def elim {n : ℕ} (S : Set (LRow (n + 1))) : Set (LRow n) :=
  proj '' zerS S ∪ Set.image2 comb (posS S) (negS S)

theorem posS_sub {n : ℕ} (S : Set (LRow (n + 1))) : posS S ⊆ S := fun _ hr => hr.1
theorem negS_sub {n : ℕ} (S : Set (LRow (n + 1))) : negS S ⊆ S := fun _ hr => hr.1
theorem zerS_sub {n : ℕ} (S : Set (LRow (n + 1))) : zerS S ⊆ S := fun _ hr => hr.1

theorem elim_finite {n : ℕ} {S : Set (LRow (n + 1))} (hS : S.Finite) : (elim S).Finite :=
  ((hS.subset (zerS_sub S)).image proj).union
    (Set.Finite.image2 comb (hS.subset (posS_sub S)) (hS.subset (negS_sub S)))

theorem exists_between (L U : Set ℚ) (hL : L.Finite) (hU : U.Finite)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ x, (∀ l ∈ L, l ≤ x) ∧ ∀ u ∈ U, x ≤ u := by
  by_cases hLn : L.Nonempty
  · obtain ⟨m, hm, hmax⟩ := Set.exists_max_image L id hL hLn
    exact ⟨m, fun l hl => hmax l hl, fun u hu => h m hm u hu⟩
  · have hL0 : L = ∅ := Set.not_nonempty_iff_eq_empty.mp hLn
    by_cases hUn : U.Nonempty
    · obtain ⟨m, hm, hmin⟩ := Set.exists_min_image U id hU hUn
      exact ⟨m, fun l hl => by simp [hL0] at hl, fun u hu => hmin u hu⟩
    · have hU0 : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUn
      exact ⟨0, fun l hl => by simp [hL0] at hl, fun u hu => by simp [hU0] at hu⟩

/-- If `b'` satisfies the eliminated system, it extends to the original one. -/
theorem extend {n : ℕ} (S : Set (LRow (n + 1))) (hS : S.Finite) (b' : Fin n → ℚ)
    (h : ∀ r ∈ elim S, r.Sat b') : ∃ x, ∀ r ∈ S, r.Sat (ext b' x) := by
  classical
  let A : LRow (n + 1) → ℚ := fun r => tail r.1 ⬝ᵥ b'
  let lo : LRow (n + 1) → ℚ := fun r => (r.2 - A r) / r.1 (Fin.last n)
  have hpos : (posS S).Finite := hS.subset (posS_sub S)
  have hneg : (negS S).Finite := hS.subset (negS_sub S)
  obtain ⟨x, hxL, hxU⟩ := exists_between (lo '' posS S) (lo '' negS S)
    (hpos.image lo) (hneg.image lo) (by
      rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
      have hc : (comb r s).Sat b' := h _ (Or.inr (Set.mem_image2_of_mem hr hs))
      have hcd : (comb r s).1 ⬝ᵥ b' = (-s.1 (Fin.last n)) * A r + r.1 (Fin.last n) * A s := by
        simp only [comb, dotProduct, A, tail]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hc' : (comb r s).2 ≤ (comb r s).1 ⬝ᵥ b' := hc
      rw [hcd] at hc'
      have ha := hr.2
      have hb := hs.2
      simp only [comb] at hc'
      have ha0 : r.1 (Fin.last n) ≠ 0 := ha.ne'
      have hb0 : s.1 (Fin.last n) ≠ 0 := hb.ne
      have hmr : r.1 (Fin.last n) * lo r = r.2 - A r := by
        simp only [lo]; field_simp
      have hms : s.1 (Fin.last n) * lo s = s.2 - A s := by
        simp only [lo]; field_simp
      by_contra hlt
      push_neg at hlt
      have hpos' : 0 < r.1 (Fin.last n) * (-s.1 (Fin.last n)) * (lo r - lo s) :=
        mul_pos (mul_pos ha (neg_pos.2 hb)) (sub_pos.2 hlt)
      have e1 : (-s.1 (Fin.last n)) * (r.1 (Fin.last n) * lo r)
          = (-s.1 (Fin.last n)) * (r.2 - A r) := by rw [hmr]
      have e2 : r.1 (Fin.last n) * (s.1 (Fin.last n) * lo s)
          = r.1 (Fin.last n) * (s.2 - A s) := by rw [hms]
      nlinarith [hpos', e1, e2, hc'])
  refine ⟨x, fun r hr => ?_⟩
  show r.2 ≤ r.1 ⬝ᵥ ext b' x
  rw [dot_ext]
  rcases lt_trichotomy (r.1 (Fin.last n)) 0 with ha | ha | ha
  · have ha0 : r.1 (Fin.last n) ≠ 0 := ha.ne
    have hx : x ≤ lo r := hxU _ ⟨r, ⟨hr, ha⟩, rfl⟩
    have hm : r.1 (Fin.last n) * lo r = r.2 - A r := by
      simp only [lo]; field_simp
    nlinarith [mul_nonneg (neg_nonneg.2 ha.le) (sub_nonneg.2 hx)]
  · have hz : proj r ∈ elim S := Or.inl ⟨r, ⟨hr, ha⟩, rfl⟩
    have := h _ hz
    simp only [LRow.Sat, proj] at this
    rw [ha]
    simpa [A] using this
  · have ha0 : r.1 (Fin.last n) ≠ 0 := ha.ne'
    have hx : lo r ≤ x := hxL _ ⟨r, ⟨hr, ha⟩, rfl⟩
    have hm : r.1 (Fin.last n) * lo r = r.2 - A r := by
      simp only [lo]; field_simp
    nlinarith [mul_nonneg ha.le (sub_nonneg.2 hx)]

/-- Cone elements of the eliminated system lift to cone elements of the original. -/
theorem lift {n : ℕ} (S : Set (LRow (n + 1))) :
    ∀ t', Cone (elim S) t' → ∃ t, Cone S t ∧ t.1 (Fin.last n) = 0 ∧ tail t.1 = t'.1 ∧ t.2 = t'.2 := by
  intro t' ht'
  induction ht' with
  | @base r0 hmem =>
    rcases hmem with ⟨z, hz, rfl⟩ | ⟨r, hr, s, hs, rfl⟩
    · exact ⟨z, Cone.base hz.1, hz.2, rfl, rfl⟩
    · refine ⟨(-s.1 (Fin.last n)) • r + (r.1 (Fin.last n)) • s,
        Cone.add (Cone.smul (neg_nonneg.2 hs.2.le) (Cone.base hr.1))
          (Cone.smul hr.2.le (Cone.base hs.1)), ?_, ?_, ?_⟩
      · simp <;> ring
      · funext i; simp [tail, comb]
      · simp [comb]
  | zero => exact ⟨0, Cone.zero, by simp, by funext i; simp [tail], by simp⟩
  | @add r0 s0 _ _ ih1 ih2 =>
    obtain ⟨t1, c1, l1, a1, b1⟩ := ih1
    obtain ⟨t2, c2, l2, a2, b2⟩ := ih2
    refine ⟨t1 + t2, Cone.add c1 c2, by simp [l1, l2], ?_, by simp [b1, b2]⟩
    funext i
    have e1 := congrFun a1 i
    have e2 := congrFun a2 i
    simp only [tail] at e1 e2 ⊢
    simp [e1, e2]
  | @smul c0 r0 hc _ ih =>
    obtain ⟨t1, c1, l1, a1, b1⟩ := ih
    refine ⟨c0 • t1, Cone.smul hc c1, by simp [l1], ?_, by simp [b1]⟩
    funext i
    have e1 := congrFun a1 i
    simp only [tail] at e1 ⊢
    simp [e1]

/-- Fourier–Motzkin: an infeasible finite system derives `0 ≥ c > 0`. -/
theorem fm : ∀ (n : ℕ) (S : Set (LRow n)), S.Finite →
    (∀ b : Fin n → ℚ, ∃ r ∈ S, ¬ r.Sat b) → ∃ c : ℚ, 0 < c ∧ Cone S ((0 : Fin n → ℚ), c) := by
  intro n
  induction n with
  | zero =>
    intro S _ hinf
    obtain ⟨r, hr, hnot⟩ := hinf (fun i => i.elim0)
    have hc : 0 < r.2 := by
      simp [LRow.Sat, dotProduct] at hnot
      exact hnot
    refine ⟨r.2, hc, ?_⟩
    have h2 : ((0 : Fin 0 → ℚ), r.2) = r := Prod.ext (Subsingleton.elim _ _) rfl
    rw [h2]
    exact Cone.base hr
  | succ n ih =>
    intro S hS hinf
    have hinf' : ∀ b' : Fin n → ℚ, ∃ r ∈ elim S, ¬ r.Sat b' := by
      intro b'
      by_contra hcon
      push_neg at hcon
      obtain ⟨x, hx⟩ := extend S hS b' hcon
      obtain ⟨r, hr, hnot⟩ := hinf (ext b' x)
      exact hnot (hx r hr)
    obtain ⟨c, hc, hcone⟩ := ih (elim S) (elim_finite hS) hinf'
    obtain ⟨t, ht, hl, htl, htc⟩ := lift S _ hcone
    refine ⟨c, hc, ?_⟩
    have h2 : t = ((0 : Fin (n + 1) → ℚ), c) := by
      refine Prod.ext ?_ htc
      funext i
      induction i using Fin.lastCases with
      | last => simpa using hl
      | cast j =>
        have := congrFun htl j
        simpa [tail] using this
    rw [← h2]
    exact ht

/-- Multipliers extracted from a cone derivation over the rows of `(C, d)`. -/
theorem cone_mult_fin {ρ : Type*} [Fintype ρ] {n : ℕ} (C : Matrix ρ (Fin n) ℚ) (d : ρ → ℚ) :
    ∀ r : LRow n, Cone (Set.range fun i => ((C i : Fin n → ℚ), d i)) r →
      ∃ l : ρ → ℚ, (∀ i, 0 ≤ l i) ∧ r.1 = l ᵥ* C ∧ r.2 = d ⬝ᵥ l := by
  classical
  intro r hr
  induction hr with
  | @base r0 hmem =>
    obtain ⟨i, rfl⟩ := hmem
    refine ⟨Pi.single i 1, fun j => ?_, ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · funext j
      simp [Matrix.vecMul, dotProduct, Pi.single_apply]
    · simp [dotProduct, Pi.single_apply]
  | zero => exact ⟨0, fun _ => le_refl _, by simp, by simp⟩
  | @add r0 s0 _ _ ih1 ih2 =>
    obtain ⟨l1, p1, e1, f1⟩ := ih1
    obtain ⟨l2, p2, e2, f2⟩ := ih2
    refine ⟨l1 + l2, fun i => add_nonneg (p1 i) (p2 i), ?_, ?_⟩
    · simp [e1, e2, Matrix.add_vecMul]
    · simp [f1, f2, dotProduct_add]
  | @smul c0 r0 hc _ ih =>
    obtain ⟨l1, p1, e1, f1⟩ := ih
    refine ⟨c0 • l1, fun i => mul_nonneg hc (p1 i), ?_, ?_⟩
    · simp [e1, Matrix.smul_vecMul]
    · simp [f1, dotProduct_smul]

/-- Farkas over `Fin n` variables. -/
theorem farkas_fin {ρ : Type*} [Fintype ρ] {n : ℕ} (C : Matrix ρ (Fin n) ℚ) (d : ρ → ℚ)
    (h : ¬ ∃ b, YesCert C d b) : ∃ l, NoCert C d l := by
  classical
  have hfin : (Set.range fun i => ((C i : Fin n → ℚ), d i)).Finite := Set.finite_range _
  have hinf : ∀ b : Fin n → ℚ, ∃ r ∈ Set.range (fun i => ((C i : Fin n → ℚ), d i)),
      ¬ LRow.Sat b r := by
    intro b
    by_contra hcon
    push_neg at hcon
    exact h ⟨b, fun i => hcon _ ⟨i, rfl⟩⟩
  obtain ⟨c, hc, hcone⟩ := fm n _ hfin hinf
  obtain ⟨l, hl, e1, e2⟩ := cone_mult_fin C d _ hcone
  exact ⟨l, hl, e1.symm, lt_of_lt_of_eq hc e2⟩

/-- Theorem D (converse) over arbitrary finite index types. -/
theorem farkas {ρ ι : Type*} [Fintype ρ] [Fintype ι] (C : Matrix ρ ι ℚ) (d : ρ → ℚ)
    (h : ¬ ∃ b, YesCert C d b) : ∃ l, NoCert C d l := by
  classical
  let e := Fintype.equivFin ι
  let C' : Matrix ρ (Fin (Fintype.card ι)) ℚ := fun r k => C r (e.symm k)
  have key : ∀ (b' : Fin (Fintype.card ι) → ℚ) r,
      (C' *ᵥ b') r = (C *ᵥ (fun i => b' (e i))) r := by
    intro b' r
    simp only [Matrix.mulVec, dotProduct, C']
    rw [← Equiv.sum_comp e.symm (fun i => C r i * b' (e i))]
    simp
  have h' : ¬ ∃ b', YesCert C' d b' := by
    rintro ⟨b', hb'⟩
    exact h ⟨fun i => b' (e i), fun r => by rw [← key]; exact hb' r⟩
  obtain ⟨l, hl, hC, hd⟩ := farkas_fin C' d h'
  refine ⟨l, hl, ?_, hd⟩
  funext i
  have := congrFun hC (e i)
  simpa [Matrix.vecMul, dotProduct, C'] using this

/-- Theorem E (finite rational system): exactly one of YES / NO certificate exists. -/
theorem decision {ρ ι : Type*} [Fintype ρ] [Fintype ι] (C : Matrix ρ ι ℚ) (d : ρ → ℚ) :
    (∃ b, YesCert C d b) ∨ (∃ l, NoCert C d l) := by
  by_cases h : ∃ b, YesCert C d b
  · exact Or.inl h
  · exact Or.inr (farkas C d h)

theorem decision_exclusive {ρ ι : Type*} [Fintype ρ] [Fintype ι] (C : Matrix ρ ι ℚ) (d : ρ → ℚ) :
    ¬ ((∃ b, YesCert C d b) ∧ (∃ l, NoCert C d l)) := by
  rintro ⟨⟨b, hb⟩, ⟨l, hl⟩⟩
  exact not_both C d b l hb hl

end ContinualFeasibility
