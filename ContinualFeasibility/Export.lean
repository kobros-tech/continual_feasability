import ContinualFeasibility.Sequential
import ContinualFeasibility.Check

/-!
# Stage 3c — exporting the sequential `Spec` to an array system, with its correctness proof

`exportSys S : ArrSys` is the executable dense system `C b ≥ d` of the sequential `Spec S`
(rows (Z), (I), (P), (N), (O); variables `W t k j`). It is defined *computably* from `coef`/`rhs`
of `Sequential.lean` through explicit index bijections

* `varEquiv p K T : Var p K T ≃ Fin ((T+1)·(K·p))`  (index `(t·K + k)·p + j`),
* `rowEquiv p K T N : RowIx p K T N ≃ Fin (exportM p K T N)`  (blocks Z, I, P, N, O in this order;
  inside a block the components are lexicographic, `Bool` as `false ↦ 0`, `true ↦ 1`).

Main results (no solver is trusted anywhere):

* `exportSys_wf`           : the array system is well formed.
* `exportSys_encodes`      : `exportSys S` encodes `(Cmat S, dvec S)` under these bijections.
* `export_yes`             : an accepted YES array ⇒ a classifier sequence satisfying (Z)(I)(P)(N)(O).
* `export_no`              : an accepted NO array ⇒ no such sequence exists.
* `export_feasible_iff`    : `(∃ W, Feasible S W) ↔ ` the array system has a YES vector.
* `export_infeasible_iff`  : `(¬ ∃ W, Feasible S W) ↔ ` the array system has a Farkas certificate.

`ArrSys.beq` is a computable equality test used only to compare the exporter against an
independently produced array system on concrete instances (`SpecCerts.lean`).
-/

namespace ContinualFeasibility

open Matrix

/-! ### Arrays from functions, with the lookup lemma -/

def arrOfFn {α : Type*} (n : ℕ) (f : Fin n → α) : Array α := (List.ofFn f).toArray

theorem arrOfFn_size {α : Type*} (n : ℕ) (f : Fin n → α) : (arrOfFn n f).size = n := by
  first
  | (simp [arrOfFn]; done)
  | (unfold arrOfFn; rw [List.size_toArray, List.length_ofFn])

theorem arrOfFn_getD {α : Type*} (n : ℕ) (f : Fin n → α) (i : ℕ) (hi : i < n) (v : α) :
    (arrOfFn n f).getD i v = f ⟨i, hi⟩ := by
  have hs : i < (arrOfFn n f).size := by rw [arrOfFn_size]; exact hi
  first
  | (simp [arrOfFn, Array.getD, hi]; done)
  | (unfold Array.getD; rw [dif_pos hs]; simp [arrOfFn]; done)
  | (rw [Array.getD_eq_getD_getElem?]; simp [arrOfFn, hi]; done)

/-! ### Computable index bijections -/

def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
  invFun i := decide (i.val = 1)
  left_inv b := by cases b <;> first | rfl | decide | simp
  right_inv i := by
    rcases i with ⟨v, hv⟩
    have h : v = 0 ∨ v = 1 := by omega
    rcases h with rfl | rfl <;> first | rfl | decide | simp

def eProd3 (a b c : ℕ) : Fin a × Fin b × Fin c ≃ Fin (a * (b * c)) :=
  (Equiv.prodCongr (Equiv.refl (Fin a)) (finProdFinEquiv : Fin b × Fin c ≃ Fin (b * c))).trans
    (finProdFinEquiv : Fin a × Fin (b * c) ≃ Fin (a * (b * c)))

def eProd4 (a b c d : ℕ) : Fin a × Fin b × Fin c × Fin d ≃ Fin (a * (b * (c * d))) :=
  (Equiv.prodCongr (Equiv.refl (Fin a)) (eProd3 b c d)).trans
    (finProdFinEquiv : Fin a × Fin (b * (c * d)) ≃ Fin (a * (b * (c * d))))

abbrev nZ (p K T : ℕ) : ℕ := (T + 1) * (K * (p * 2))
abbrev nI (p K : ℕ) : ℕ := K * (p * 2)
abbrev nP (K T N : ℕ) : ℕ := (T + 1) * (N * (K * 2))
abbrev nN (K N : ℕ) : ℕ := N * K
abbrev nO (K T N : ℕ) : ℕ := (T + 1) * (N * K)
abbrev exportM (p K T N : ℕ) : ℕ := nZ p K T + (nI p K + (nP K T N + (nN K N + nO K T N)))
abbrev exportN (p K T : ℕ) : ℕ := (T + 1) * (K * p)

def eZ (p K T : ℕ) : Fin (T + 1) × Fin K × Fin p × Bool ≃ Fin (nZ p K T) :=
  (Equiv.prodCongr (Equiv.refl (Fin (T + 1)))
    (Equiv.prodCongr (Equiv.refl (Fin K)) (Equiv.prodCongr (Equiv.refl (Fin p)) boolFin))).trans
    (eProd4 (T + 1) K p 2)

def eI (p K : ℕ) : Fin K × Fin p × Bool ≃ Fin (nI p K) :=
  (Equiv.prodCongr (Equiv.refl (Fin K))
    (Equiv.prodCongr (Equiv.refl (Fin p)) boolFin)).trans (eProd3 K p 2)

def eP (K T N : ℕ) : Fin (T + 1) × Fin N × Fin K × Bool ≃ Fin (nP K T N) :=
  (Equiv.prodCongr (Equiv.refl (Fin (T + 1)))
    (Equiv.prodCongr (Equiv.refl (Fin N)) (Equiv.prodCongr (Equiv.refl (Fin K)) boolFin))).trans
    (eProd4 (T + 1) N K 2)

def eN (K N : ℕ) : Fin N × Fin K ≃ Fin (nN K N) :=
  (finProdFinEquiv : Fin N × Fin K ≃ Fin (N * K))

def eO (K T N : ℕ) : Fin (T + 1) × Fin N × Fin K ≃ Fin (nO K T N) := eProd3 (T + 1) N K

/-- Nested sum of five `Fin`s, laid out block after block. -/
def sum5 (a b c d e : ℕ) :
    Fin a ⊕ Fin b ⊕ Fin c ⊕ Fin d ⊕ Fin e ≃ Fin (a + (b + (c + (d + e)))) :=
  let q4 : Fin d ⊕ Fin e ≃ Fin (d + e) := finSumFinEquiv
  let q3 : Fin c ⊕ Fin d ⊕ Fin e ≃ Fin (c + (d + e)) :=
    (Equiv.sumCongr (Equiv.refl (Fin c)) q4).trans finSumFinEquiv
  let q2 : Fin b ⊕ Fin c ⊕ Fin d ⊕ Fin e ≃ Fin (b + (c + (d + e))) :=
    (Equiv.sumCongr (Equiv.refl (Fin b)) q3).trans finSumFinEquiv
  (Equiv.sumCongr (Equiv.refl (Fin a)) q2).trans finSumFinEquiv

def varEquiv (p K T : ℕ) : Var p K T ≃ Fin (exportN p K T) := eProd3 (T + 1) K p

def rowEquiv (p K T N : ℕ) : RowIx p K T N ≃ Fin (exportM p K T N) :=
  (Equiv.sumCongr (eZ p K T)
    (Equiv.sumCongr (eI p K)
      (Equiv.sumCongr (eP K T N) (Equiv.sumCongr (eN K N) (eO K T N))))).trans
    (sum5 (nZ p K T) (nI p K) (nP K T N) (nN K N) (nO K T N))

/-! ### The exporter -/

variable {p K T N : ℕ}

/-- The dense array system of a sequential specification. -/
def exportSys (S : Spec p K T N) : ArrSys where
  m := exportM p K T N
  n := exportN p K T
  C := arrOfFn (exportM p K T N) fun i =>
        arrOfFn (exportN p K T) fun j =>
          coef S ((rowEquiv p K T N).symm i) ((varEquiv p K T).symm j)
  d := arrOfFn (exportM p K T N) fun i => rhs S ((rowEquiv p K T N).symm i)

theorem exportSys_C_row (S : Spec p K T N) (i : Fin (exportM p K T N)) :
    (exportSys S).C.getD i.val #[] =
      arrOfFn (exportN p K T) fun j =>
        coef S ((rowEquiv p K T N).symm i) ((varEquiv p K T).symm j) :=
  arrOfFn_getD (exportM p K T N) _ i.val i.isLt #[]

theorem toMat_exportSys (S : Spec p K T N) (i : Fin (exportM p K T N))
    (j : Fin (exportN p K T)) :
    ArrSys.toMat (exportSys S) i j =
      coef S ((rowEquiv p K T N).symm i) ((varEquiv p K T).symm j) := by
  show ((exportSys S).C.getD i.val #[]).getD j.val 0 = _
  rw [exportSys_C_row S i]
  exact arrOfFn_getD _ _ _ j.isLt _

theorem toD_exportSys (S : Spec p K T N) (i : Fin (exportM p K T N)) :
    ArrSys.toD (exportSys S) i = rhs S ((rowEquiv p K T N).symm i) := by
  show (exportSys S).d.getD i.val 0 = _
  exact arrOfFn_getD _ _ _ i.isLt _

/-- The exported array system is well formed (no ragged rows, no short `d`). -/
theorem exportSys_wf (S : Spec p K T N) : (exportSys S).Wf := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · exact arrOfFn_size _ _
  · exact arrOfFn_size _ _
  · exact (congrArg Array.size (exportSys_C_row S i)).trans (arrOfFn_size _ _)

/-- **Stage 3c core.** The exported arrays encode exactly `(Cmat S, dvec S)`. -/
theorem exportSys_encodes (S : Spec p K T N) :
    ArrSys.Encodes (exportSys S) (Cmat S) (dvec S)
      (rowEquiv p K T N).symm (varEquiv p K T).symm :=
  ⟨fun i j => toMat_exportSys S i j, fun i => toD_exportSys S i⟩

/-! ### Consequences: accepted array certificates decide the sequential problem -/

theorem export_yes (S : Spec p K T N) (b : Array ℚ)
    (h : ArrSys.checkYes (exportSys S) b = true) : ∃ W, Feasible S W := by
  obtain ⟨b', hb'⟩ := ArrSys.yes_transfer (exportSys_encodes S) b h
  exact ⟨unflat b', theoremC S b' hb'⟩

theorem export_no (S : Spec p K T N) (l : Array ℚ)
    (h : ArrSys.checkNo (exportSys S) l = true) : ¬ ∃ W, Feasible S W := by
  obtain ⟨l', hl'⟩ := ArrSys.no_transfer (exportSys_encodes S) l h
  exact theoremD S l' hl'

/-- Reindexing a YES vector along an encoding, in both directions. -/
theorem encodes_yes_iff {S : ArrSys} {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    {C : Matrix ρ ι ℚ} {d : ρ → ℚ} {e : Fin S.m ≃ ρ} {f : Fin S.n ≃ ι}
    (hE : ArrSys.Encodes S C d e f) :
    (∃ b, YesCert (ArrSys.toMat S) (ArrSys.toD S) b) ↔ ∃ b, YesCert C d b := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun u => b (f.symm u), fun r => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective r
    have h2 : (C *ᵥ fun u => b (f.symm u)) (e i) = (ArrSys.toMat S *ᵥ b) i := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Equiv.sum_comp f]
      simp [hE.C_eq]
    rw [h2, ← hE.d_eq]
    exact hb i
  · rintro ⟨b, hb⟩
    refine ⟨fun j => b (f j), fun i => ?_⟩
    have h2 : (ArrSys.toMat S *ᵥ fun j => b (f j)) i = (C *ᵥ b) (e i) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Equiv.sum_comp f]
      simp [hE.C_eq]
    rw [h2, hE.d_eq]
    exact hb (e i)

/-- Joint feasibility of the sequential problem ⇔ the exported array system has a YES vector. -/
theorem export_feasible_iff (S : Spec p K T N) :
    (∃ W, Feasible S W) ↔
      ∃ b', YesCert (ArrSys.toMat (exportSys S)) (ArrSys.toD (exportSys S)) b' :=
  (theoremB S).trans (encodes_yes_iff (exportSys_encodes S)).symm

/-- Infeasibility of the sequential problem ⇔ the exported array system has a Farkas certificate. -/
theorem export_infeasible_iff (S : Spec p K T N) :
    (¬ ∃ W, Feasible S W) ↔
      ∃ l, NoCert (ArrSys.toMat (exportSys S)) (ArrSys.toD (exportSys S)) l := by
  constructor
  · intro h
    have h' : ¬ ∃ b', YesCert (ArrSys.toMat (exportSys S)) (ArrSys.toD (exportSys S)) b' :=
      fun hy => h ((export_feasible_iff S).2 hy)
    exact farkas _ _ h'
  · rintro ⟨l, hl⟩ hW
    exact farkas_forward _ _ l hl ((export_feasible_iff S).1 hW)

/-! ### A computable equality test (used only to compare against an independent exporter) -/

def ArrSys.beq (a b : ArrSys) : Bool :=
  (a.m == b.m) && (a.n == b.n) &&
    (a.C.toList.map Array.toList == b.C.toList.map Array.toList) &&
    (a.d.toList == b.d.toList)

end ContinualFeasibility
