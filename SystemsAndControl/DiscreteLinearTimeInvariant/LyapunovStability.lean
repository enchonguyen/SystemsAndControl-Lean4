import SystemsAndControl.DiscreteLinearTimeInvariant.AsymptoticStability
import SystemsAndControl.Machinery.TelescopingSum
import SystemsAndControl.Machinery.Tsum_MulConst
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Lyapunov Stability Theory for Discrete-Time Systems

Given a square complex matrix $A$, we prove that the equivalent statements
(1) the autonomous system $x(t + 1) = A x(t)$ is asymptotically stable, i.e.
  $\lim_{t \to \infty} x(t) = 0$;
(2) $\lim_{k \to \infty} A^k = 0$;
(3) $|z| < 1$, where $z$ is an eigenvalue of $A$
are also equivalent to
(4) there exists a positive definite matrix $P \succ 0$ such that $P - A^T P A \succ 0$.

## Main results

- `DLTI.isAsymptoticallyStable_iff_exists_lyapunov_ineq_solution`: (1) ↔ (4)
- `DLTI.matrix_pow_tendsto_zero_iff_exists_lyapunov_ineq_solution`: (2) ↔ (4)
- `DLTI.eigenvalue_norm_lt_one_iff_exists_lyapunov_ineq_solution`: (3) ↔ (4)
-/

open DLTI ENNReal Filter Matrix
open scoped Matrix.Norms.Operator ComplexOrder -- $l_\infty$-induced matrix norm; Partial order on ℂ

variable {n : Type*} [Fintype n] [DecidableEq n] -- number of states

-- Existence of a nonnegative constant $r$, less than 1, such that $\|(A^H)^k A^k\| \leq r^k$ for a
-- sufficiently large $k$ if the spectral radius of $A$ is less than 1
lemma exists_nonneg_const_lt_one_gramian_pow_norm_eventually_le_const_pow_if_spectralRadius_lt_one
    {A : Matrix n n ℂ}
    (hA1 : spectralRadius ℂ A < 1) :
    ∃ r : ℝ, r ≥ 0 ∧ r < 1 ∧ ∀ᶠ k : ℕ in atTop, ‖(Aᴴ) ^ k * A ^ k‖ ≤ r ^ k := by
  obtain ⟨r, hr0, hr_fin, hAr, hr1⟩ := exists_finite_nonneg_const_gt_spectralRadius_lt_finite_bound
    (lt_top_iff_ne_top.mp one_lt_top) hA1
  -- r : ℝ≥0∞
  -- hr0 : r ≥ 0
  -- hr_fin : r ≠ ∞
  -- hAr : spectralRadius ℂ A < r
  -- hr1 : r < 1
  use ENNReal.toReal r ^ 2
  -- ⊢ r.toReal ^ 2 ≥ 0 ∧ r.toReal ^ 2 < 1 ∧
  --     ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ (r.toReal ^ 2) ^ k
  have hAr_pow_ev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ ENNReal.toReal r ^ k :=
    matrix_pow_norm_eventually_le_spectralRadius_bound_pow hr_fin hAr
  -- hAr_pow_ev : ∀ᶠ (k : ℕ) in atTop, ‖A ^ k‖ ≤ r.toReal ^ k
  rw [spectralRadius_eq_conjTranspose] at hAr
  -- hAr : spectralRadius ℂ Aᴴ < r
  have hA'r_pow_ev : ∀ᶠ k : ℕ in atTop, ‖(Aᴴ) ^ k‖ ≤ ENNReal.toReal r ^ k :=
    matrix_pow_norm_eventually_le_spectralRadius_bound_pow hr_fin hAr
  -- hA'r_pow_ev : ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k‖ ≤ r.toReal ^ k
  refine ⟨?_, ?_, ?_⟩
  · -- ⊢ r.toReal ^ 2 ≥ 0
    simp
  · -- ⊢ r.toReal ^ 2 < 1
    simpa using ((toReal_lt_toReal hr_fin (lt_top_iff_ne_top.mp one_lt_top)).mpr hr1)
  · -- ⊢ ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ (r.toReal ^ 2) ^ k
    filter_upwards [hAr_pow_ev, hA'r_pow_ev]
    -- ⊢ ∀ (k : ℕ), ‖A ^ k‖ ≤ r.toReal ^ k → ‖Aᴴ ^ k‖ ≤ r.toReal ^ k →
    --                 ‖Aᴴ ^ k * A ^ k‖ ≤ (r.toReal ^ 2) ^ k
    intro k hk hk'
    -- k : ℕ
    -- hk : ‖A ^ k‖ ≤ r.toReal ^ k
    -- hk' : ‖Aᴴ ^ k‖ ≤ r.toReal ^ k
    -- ⊢ ‖Aᴴ ^ k * A ^ k‖ ≤ (r.toReal ^ 2) ^ k
    calc
        ‖(Aᴴ) ^ k * A ^ k‖
      ≤ ‖(Aᴴ) ^ k‖ * ‖A ^ k‖ :=
          norm_mul_le ((Aᴴ) ^ k) (A ^ k)
    _ ≤ (ENNReal.toReal r ^ k) * (ENNReal.toReal r ^ k) :=
          mul_le_mul hk' hk (norm_nonneg (A ^ k)) (by simp)
    _ = (r.toReal ^ 2) ^ k := by
          ring_nf

-- $(A^H)^k A^k$ is summable if the spectral radius of $A$ is less than 1.
lemma gramian_pow_summable_if_spectralRadius_lt_one
    {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) :
    Summable (fun k => (Aᴴ) ^ k * A ^ k) := by
  obtain ⟨r, hr0, hr1, hAr_pow_ev⟩ :=
    exists_nonneg_const_lt_one_gramian_pow_norm_eventually_le_const_pow_if_spectralRadius_lt_one hA
  -- r : ℝ
  -- hr0 : r ≥ 0
  -- hr1 : r < 1
  -- hAr_pow_ev : ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ r ^ k
  apply Summable.of_norm_bounded_eventually_nat
  -- (hg : Summable g) (h : ∀ᶠ (i : ℕ) in atTop, ‖f i‖ ≤ g i) : Summable f
  · -- ⊢ Summable ?g
    exact summable_geometric_of_lt_one hr0 hr1
  · -- ⊢ ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ r ^ k
    exact hAr_pow_ev

-- $(A^H)^k A^k$ is goes to 0 if the spectral radius of $A$ is less than 1.
lemma gramian_pow_tendsto_zero_if_spectralRadius_lt_one
    {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) :
    Tendsto (fun k => (Aᴴ) ^ k * A ^ k) atTop (nhds 0) := by
  obtain ⟨r, hr0, hr1, hAr_pow_ev⟩ :=
    exists_nonneg_const_lt_one_gramian_pow_norm_eventually_le_const_pow_if_spectralRadius_lt_one hA
  -- r : ℝ
  -- hr0 : r ≥ 0
  -- hr1 : r < 1
  -- hAr_pow_ev : ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ r ^ k
  apply squeeze_zero_norm'
  -- (h : ∀ᶠ (n : α) in t₀, ‖f n‖ ≤ a n) (h' : Tendsto a t₀ (nhds 0)) : Tendsto f t₀ (nhds 0)
  · -- ⊢ ∀ᶠ (k : ℕ) in atTop, ‖Aᴴ ^ k * A ^ k‖ ≤ ?a k
    exact hAr_pow_ev
  · -- ⊢ Tendsto (fun k => r ^ k) atTop (nhds 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

-- Positive semidefiniteness of $(A^H)^k A^k$
lemma gramian_pow_isPosSemidef
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    (A : Matrix n n R) :
    ∀ k : ℕ, PosSemidef ((Aᴴ) ^ k * A ^ k) := by
  intro k
  -- k : ℕ
  -- ⊢ (Aᴴ ^ k * A ^ k).PosSemidef
  rw [posSemidef_iff_dotProduct_mulVec]
  -- ⊢ (Aᴴ ^ k * A ^ k).IsHermitian ∧ ∀ (x : n → R), 0 ≤ star x ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ x
  constructor
  · -- ⊢ (Aᴴ ^ k * A ^ k).IsHermitian
    simpa using isHermitian_conjTranspose_mul_self (A ^ k)
  · -- ⊢ ∀ (x : n → R), 0 ≤ star x ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ x
    intro v
    -- v : n → R
    -- ⊢ 0 ≤ star v ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ v
    calc
        star v ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ v
      = star v ⬝ᵥ (Aᴴ ^ k *ᵥ A ^ k *ᵥ v) := by
          rw [← mulVec_mulVec]
    _ = (star v ᵥ* Aᴴ ^ k) ⬝ᵥ (A ^ k *ᵥ v) := by
          rw [dotProduct_mulVec]
    _ = star ((Aᴴ ^ k)ᴴ *ᵥ v) ⬝ᵥ (A ^ k *ᵥ v) := by
          rw [star_mulVec, conjTranspose_conjTranspose]
          -- ⊢ ... = (star v ᵥ* (Aᴴ ^ k)ᴴᴴ) ⬝ᵥ (A ^ k *ᵥ v)
          -- ⊢ ... = (star v ᵥ* Aᴴ ^ k) ⬝ᵥ (A ^ k *ᵥ v)
    _ = star (A ^ k *ᵥ v) ⬝ᵥ (A ^ k *ᵥ v) := by
          rw [conjTranspose_pow, conjTranspose_conjTranspose]
          -- ⊢ star (Aᴴᴴ ^ k *ᵥ v) ⬝ᵥ (A ^ k *ᵥ v) = ...
          -- ⊢ star (A ^ k *ᵥ v) ⬝ᵥ (A ^ k *ᵥ v) = ...
    _ ≥ 0 :=
          dotProduct_star_self_nonneg (A ^ k *ᵥ v)

-- The infinite sum of $(A^H)^k A^k$ is Hermitian.
lemma gramian_pow_tsum_isHermitian
    {R : Type*} [Semiring R] [StarRing R] [TopologicalSpace R] [ContinuousStar R] [T2Space R]
    (A : Matrix n n R) :
    IsHermitian (∑' k : ℕ, (Aᴴ) ^ k * A ^ k) := by
  unfold IsHermitian
  -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k)ᴴ = ∑' (k : ℕ), Aᴴ ^ k * A ^ k
  rw [conjTranspose_tsum]
  -- ⊢ ∑' (k : ℕ), (Aᴴ ^ k * A ^ k)ᴴ = ∑' (k : ℕ), Aᴴ ^ k * A ^ k
  apply tsum_congr
  -- ⊢ ∀ (k : ℕ), (Aᴴ ^ k * A ^ k)ᴴ = Aᴴ ^ k * A ^ k
  intro k
  -- k : ℕ
  -- ⊢ (Aᴴ ^ k * A ^ k)ᴴ = Aᴴ ^ k * A ^ k
  rw [conjTranspose_mul]
  -- ⊢ (A ^ k)ᴴ * (Aᴴ ^ k)ᴴ = Aᴴ ^ k * A ^ k
  simp only [conjTranspose_pow, conjTranspose_conjTranspose]

-- Positive definiteness of the infinite sum of $(A^H)^k A^k$ if the spectral radius of $A$ is less
-- than 1
lemma gramian_pow_tsum_PosDef_if_spectralRadius_lt_one
    {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) :
    PosDef (∑' k : ℕ, (Aᴴ) ^ k * A ^ k) := by
  rw [posDef_iff_dotProduct_mulVec]
  -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k).IsHermitian ∧
  --      ∀ (x : n → ℂ), x ≠ 0 → 0 < star x ⬝ᵥ (∑' (k : ℕ), Aᴴ ^ k * A ^ k) *ᵥ x
  constructor
  · -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k).IsHermitian
    exact gramian_pow_tsum_isHermitian A
  · -- ⊢ ∀ (x : n → ℂ), x ≠ 0 → 0 < star x ⬝ᵥ (∑' (k : ℕ), Aᴴ ^ k * A ^ k) *ᵥ x
    intro v hv
    -- v : n → ℂ
    -- hv : v ≠ 0
    -- ⊢ 0 < star v ⬝ᵥ (∑' (k : ℕ), Aᴴ ^ k * A ^ k) *ᵥ v
    have : Summable (fun k => (Aᴴ) ^ k * A ^ k) := gramian_pow_summable_if_spectralRadius_lt_one hA
    -- this : Summable fun k ↦ Aᴴ ^ k * A ^ k
    rw [tsum_mulVec v this]
    -- ⊢ 0 < star v ⬝ᵥ ∑' (k : ℕ), (Aᴴ ^ k * A ^ k) *ᵥ v
    rw [dotProduct_tsum (star v) (summable_mulVec_right v this)]
    -- ⊢ 0 < ∑' (i : ℕ), star v ⬝ᵥ (Aᴴ ^ i * A ^ i) *ᵥ v
    apply Summable.tsum_pos (i := 0)
    -- (hsum : Summable g) (hg : ∀ (i : ι), 0 ≤ g i) (i : ι) (hi : 0 < g i) : 0 < ∑' (i : ι), g i
    · -- ⊢ 0 < star v ⬝ᵥ (Aᴴ ^ 0 * A ^ 0) *ᵥ v
      simpa
    · -- ⊢ Summable fun k ↦ star v ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ v
      exact summable_dotProduct_left (star v) (summable_mulVec_right v this)
    · -- ⊢ ∀ (k : ℕ), 0 ≤ star v ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ v
      intro k
      -- k : ℕ
      -- ⊢ 0 ≤ star v ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ v
      obtain ⟨_, hA_psd⟩ := posSemidef_iff_dotProduct_mulVec.mp (gramian_pow_isPosSemidef A k)
      -- hA_psd : ∀ (x : n → ℂ), 0 ≤ star x ⬝ᵥ (Aᴴ ^ k * A ^ k) *ᵥ x
      exact hA_psd v

-- Left- and right-distributivity with $A^H$ and $A$, respectively, of the infinite sum of
-- $(A^H)^k A^k$
lemma gramian_pow_tsum_mul_if_summable
    {R : Type*} [Semiring R] [Star R] [TopologicalSpace R] [IsTopologicalSemiring R] [T2Space R]
    {A : Matrix n n R}
    (hA : Summable (fun k => (Aᴴ) ^ k * A ^ k)) :
    Aᴴ * (∑' k : ℕ, (Aᴴ) ^ k * A ^ k) * A = ∑' k : ℕ, (Aᴴ) ^ (k + 1) * A ^ (k + 1) := by
  calc
      Aᴴ * (∑' k : ℕ, (Aᴴ) ^ k * A ^ k) * A
    = (∑' k : ℕ, Aᴴ * (Aᴴ) ^ k * A ^ k) * A := by
        simp only [Summable.tsum_mul_left Aᴴ hA, mul_assoc]
  _ = ∑' k : ℕ, Aᴴ * (Aᴴ) ^ k * A ^ k * A := by
        simp only [← Summable.tsum_mul_right A (Summable.mul_left Aᴴ hA), mul_assoc]
  _ = ∑' k : ℕ, (Aᴴ) ^ (k + 1) * A ^ (k + 1) := by
        simp only [pow_succ' (Aᴴ), pow_succ A, mul_assoc]

namespace DLTI

-- The infinite sum of $(A^H)^k A^k$ is a solution to the Lyapunov inequality if $(A^H)^k A^k$ is
-- summable and goes to 0.
lemma lyapunov_ineq_isPosDef_if_sol_summable_tendsto_zero
    {R : Type*} [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] [NoZeroDivisors R]
      [TopologicalSpace R] [IsTopologicalAddGroup R] [IsTopologicalSemiring R] [T2Space R]
    {A : Matrix n n R}
    (hA_summ : Summable (fun k => (Aᴴ) ^ k * A ^ k))
    (hA_tends : Tendsto (fun k => (Aᴴ) ^ k * A ^ k) atTop (nhds 0)) :
    PosDef (∑' k : ℕ, (Aᴴ) ^ k * A ^ k - Aᴴ * (∑' k : ℕ, (Aᴴ) ^ k * A ^ k) * A) := by
  rw [gramian_pow_tsum_mul_if_summable hA_summ]
  -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k - ∑' (k : ℕ), Aᴴ ^ (k + 1) * A ^ (k + 1)).PosDef
  rw [← Summable.tsum_sub]
  -- (hf : Summable f) (hg : Summable g) :
  --   ∑' (b : β), (f b - g b) = ∑' (b : β), f b - ∑' (b : β), g b
  · -- ⊢ (∑' (k : ℕ), (Aᴴ ^ k * A ^ k - Aᴴ ^ (k + 1) * A ^ (k + 1))).PosDef
    rw [tsum_telescope_if_summable' hA_summ hA_tends]
    simpa using PosDef.one
  · -- ⊢ Summable fun k ↦ Aᴴ ^ k * A ^ k
    exact hA_summ
  · -- ⊢ Summable fun k ↦ Aᴴ ^ (k + 1) * A ^ (k + 1)
    exact (summable_nat_add_iff (f := (fun k => (Aᴴ) ^ k * A ^ k)) 1).mpr hA_summ

-- Existence of a positive definite solution to the Lyapunov inequality, assuming that the spectral
-- radius of $A$ is less than 1
lemma exists_lyapunov_ineq_solution_if_spectralRadius_lt_one
    {A : Matrix n n ℂ}
    (hA : spectralRadius ℂ A < 1) :
    ∃ P : Matrix n n ℂ, PosDef P ∧ PosDef (P - Aᴴ * P * A) := by
  use ∑' k : ℕ, (Aᴴ) ^ k * A ^ k
  -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k).PosDef ∧
  --     (∑' (k : ℕ), Aᴴ ^ k * A ^ k - (Aᴴ * ∑' (k : ℕ), Aᴴ ^ k * A ^ k) * A).PosDef
  constructor
  · -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k).PosDef
    exact gramian_pow_tsum_PosDef_if_spectralRadius_lt_one hA
  · -- ⊢ (∑' (k : ℕ), Aᴴ ^ k * A ^ k - (Aᴴ * ∑' (k : ℕ), Aᴴ ^ k * A ^ k) * A).PosDef
    apply lyapunov_ineq_isPosDef_if_sol_summable_tendsto_zero
    -- (hA_summ : Summable fun k ↦ Aᴴ ^ k * A ^ k)
    --   (hA_tends : Tendsto (fun k ↦ Aᴴ ^ k * A ^ k) atTop (nhds 0)) :
    --     (∑' (k : ℕ), Aᴴ ^ k * A ^ k - (Aᴴ * ∑' (k : ℕ), Aᴴ ^ k * A ^ k) * A).PosDef
    · -- ⊢ Summable fun k ↦ Aᴴ ^ k * A ^ k
      exact gramian_pow_summable_if_spectralRadius_lt_one hA
    · -- ⊢ Tendsto (fun k ↦ Aᴴ ^ k * A ^ k) atTop (nhds 0)
      exact gramian_pow_tendsto_zero_if_spectralRadius_lt_one hA

-- For square matrices $A$ and $P$, as well as an eigenpair $(z, v)$ of $A$, we have
-- $v^* (P - A^H PA)v = (1 - |z|) (v^* Pv)$
lemma lyapunov_ineq_dotProduct_mulVec_eigenvector
    {n : Type*} [Fintype n] -- [DecidableEq n] is not necessary
    {z : ℂ}
    {v : n → ℂ}
    {A P : Matrix n n ℂ}
    (he : A *ᵥ v = z • v) :
    star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v = (1 - ‖z‖ ^ 2) * (star v ⬝ᵥ P *ᵥ v) := by
  calc
      star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v
    = star v ⬝ᵥ P *ᵥ v - star v ⬝ᵥ (Aᴴ *ᵥ P *ᵥ A *ᵥ v) := by
          simp_rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec]
  _ = star v ⬝ᵥ P *ᵥ v - star (A *ᵥ v) ⬝ᵥ P *ᵥ (A *ᵥ v) := by
        rw [dotProduct_mulVec (A := Aᴴ), ← star_mulVec]
        -- ⊢ ... - (star v ᵥ* Aᴴ) ⬝ᵥ P *ᵥ (A *ᵥ v) = ...
        -- ⊢ ... - star (A *ᵥ v) ⬝ᵥ P *ᵥ (A *ᵥ v) = ...
  _ = star v ⬝ᵥ P *ᵥ v - star (z • v) ⬝ᵥ P *ᵥ (z • v) := by
        rw [he]
  _ = star v ⬝ᵥ P *ᵥ v - ((star z) * z) * (star v ⬝ᵥ P *ᵥ v) := by
        rw [star_smul]
        -- ⊢ star v ⬝ᵥ P *ᵥ v - (star z • star v) ⬝ᵥ P *ᵥ (z • v) = ...
        simp_rw [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul, mul_assoc]
  _ = star v ⬝ᵥ P *ᵥ v - (‖z‖ ^ 2) * (star v ⬝ᵥ P *ᵥ v) := by
        rw [← starRingEnd_apply z, RCLike.conj_mul]
        -- ⊢ star v ⬝ᵥ P *ᵥ v - ((starRingEnd ℂ) z * z) * (star v ⬝ᵥ P *ᵥ v) = ...
        -- ⊢ star v ⬝ᵥ P *ᵥ v - ↑‖z‖ ^ 2 * star v ⬝ᵥ P *ᵥ v = ...
        rfl
  _ = (1 - ‖z‖ ^ 2) * (star v ⬝ᵥ P *ᵥ v) := by
          simp [sub_mul]

-- The eigenvalues of $A$ have modulus less than 1 if there exists a positive definite solution to
-- the Lyapunov inequality.
lemma eigenvalue_norm_lt_one_if_exists_lyapunov_ineq_solution
    {A : Matrix n n ℂ}
    (h : ∃ P : Matrix n n ℂ, PosDef P ∧ PosDef (P - Aᴴ * P * A)) :
    ∀ z ∈ spectrum ℂ A, ‖z‖ < 1 := by
  obtain ⟨P, hP, h_lyap⟩ := h
  -- P : Matrix n n ℂ
  -- hP : P.PosDef
  -- h_lyap : (P - Aᴴ * P * A).PosDef
  -- ⊢ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
  rw [posDef_iff_dotProduct_mulVec] at h_lyap
  -- h_lyap : (P - Aᴴ * P * A).IsHermitian ∧ ∀
  --            (x : n → ℂ), x ≠ 0 → 0 < star x ⬝ᵥ (P - Aᴴ * P * A) *ᵥ x
  by_contra ch
  -- ch : ¬∀ z ∈ spectrum ℂ A, ‖z‖ < 1
  -- ⊢ False
  push Not at ch
  -- ch : ∃ z ∈ spectrum ℂ A, 1 ≤ ‖z‖
  obtain ⟨z, hz, hz1⟩ := ch
  -- z : ℂ
  -- hz : z ∈ spectrum ℂ A
  -- hz1 : 1 ≤ ‖z‖
  obtain ⟨v, hv0, he⟩ := exists_eigenvector hz
  -- v : n → ℂ
  -- hv0 : v ≠ 0
  -- hve : A *ᵥ v = z • v
  apply absurd
  -- (h₁ : a) (h₂ : ¬a) : b
  · -- ⊢ ?a
    exact h_lyap.2 hv0
  · -- ⊢ ¬0 < star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v
    rw [Complex.not_lt_iff]
    -- ⊢ (star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v).re ≤ Complex.re 0 ∨
    --     Complex.im 0 ≠ (star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v).im
    left
    -- ⊢ (star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v).re ≤ Complex.re 0
    apply (Complex.le_def.mp _).1
    -- z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im
    -- ⊢ star v ⬝ᵥ (P - Aᴴ * P * A) *ᵥ v ≤ 0
    rw [lyapunov_ineq_dotProduct_mulVec_eigenvector he]
    -- ⊢ (1 - ↑‖z‖ ^ 2) * star v ⬝ᵥ P *ᵥ v ≤ 0
    apply mul_nonpos_of_nonpos_of_nonneg
    -- (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0
    · -- ⊢ 1 - ↑‖z‖ ^ 2 ≤ 0
      norm_cast
      -- ⊢ 1 - ‖z‖ ^ 2 ≤ 0
      simpa using hz1
    · -- ⊢ 0 ≤ star v ⬝ᵥ P *ᵥ v
      apply PosDef.posSemidef at hP
      -- hP : P.PosSemidef
      rw [posSemidef_iff_dotProduct_mulVec] at hP
      -- hP : P.IsHermitian ∧ ∀ (x : n → ℂ), 0 ≤ star x ⬝ᵥ P *ᵥ x
      exact hP.2 v

-- The eigenvalues of $A$ have modulus less than 1 if and only there exists a positive definite
-- solution to the Lyapunov inequality.
theorem eigenvalue_norm_lt_one_iff_exists_lyapunov_ineq_solution
    (A : Matrix n n ℂ) :
    (∀ z ∈ spectrum ℂ A, ‖z‖ < 1) ↔ ∃ P : Matrix n n ℂ, PosDef P ∧ PosDef (P - Aᴴ * P * A) := by
  constructor
  · -- ⊢ (∀ z ∈ spectrum ℂ A, ‖z‖ < 1) → ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef
    intro h_onlyif
    -- h_onlyif : ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
    -- ⊢ ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef
    by_cases h : Nontrivial (Matrix n n ℂ)
    · -- h : Nontrivial (Matrix n n ℂ)
      apply exists_lyapunov_ineq_solution_if_spectralRadius_lt_one
      -- ⊢ spectralRadius ℂ A < 1
      exact spectrum.spectralRadius_lt_of_forall_lt A h_onlyif
    · -- h : ¬Nontrivial (Matrix n n ℂ)
      have : Subsingleton (Matrix n n ℂ) := not_nontrivial_iff_subsingleton.mp h
      -- this : Subsingleton (Matrix n n ℂ)
      apply exists_lyapunov_ineq_solution_if_spectralRadius_lt_one
      -- ⊢ spectralRadius ℂ A < 1
      rw [spectrum.SpectralRadius.of_subsingleton A]
      -- ⊢ 0 < 1
      simp
  · -- ⊢ (∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef) → ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
    exact eigenvalue_norm_lt_one_if_exists_lyapunov_ineq_solution

-- $x(t)$ goes to 0 if and only if there exists a positive definite solution to the Lyapunov
-- inequality.
set_option linter.unusedDecidableInType false in
-- [DecidableEq n] is not necessary for the statement to make sense, but is required for its proof.
theorem isAsymptoticallyStable_iff_exists_lyapunov_ineq_solution
    (A : Matrix n n ℂ) :
    IsAsymptoticallyStable A ↔ ∃ P : Matrix n n ℂ, PosDef P ∧ PosDef (P - Aᴴ * P * A) := by
  rw [isAsymptoticallyStable_iff_eigenvalue_norm_lt_one,
    eigenvalue_norm_lt_one_iff_exists_lyapunov_ineq_solution]
  -- ⊢ (∀ z ∈ spectrum ℂ A, ‖z‖ < 1) ↔ ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef
  -- ⊢ (∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef) ↔ ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef

-- $A^k$ goes to 0 if and only if there exists a positive definite solution to the Lyapunov
-- inequality.
theorem matrix_pow_tendsto_zero_iff_exists_lyapunov_ineq_solution
    (A : Matrix n n ℂ) :
    Tendsto (fun k => A ^ k) atTop (nhds 0) ↔
      ∃ P : Matrix n n ℂ, PosDef P ∧ PosDef (P - Aᴴ * P * A) := by
  rw [← isAsymptoticallyStable_iff_matrix_pow_tendsto_zero,
    isAsymptoticallyStable_iff_exists_lyapunov_ineq_solution]
  -- ⊢ IsAsymptoticallyStable A ↔ ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef
  -- ⊢ (∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef) ↔ ∃ P, P.PosDef ∧ (P - Aᴴ * P * A).PosDef

end DLTI
