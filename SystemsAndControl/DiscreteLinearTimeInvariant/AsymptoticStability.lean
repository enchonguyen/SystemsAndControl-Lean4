import SystemsAndControl.DiscreteLinearTimeInvariant.Solution
import SystemsAndControl.Machinery.MatrixPowGelfand
import SystemsAndControl.Machinery.MatrixSpectralTheory

/-!
# Asymptotic Stability of Discrete-Time Linear Time-Invariant Systems

Given a square complex matrix $A$, we show that the following are equivalent:
(1) the autonomous system $x(t + 1) = A x(t)$ is asymptotically stable, i.e.
  $\lim_{t \to \infty} x(t) = 0$;
(2) $\lim_{k \to \infty} A^k = 0$;
(3) $|z| < 1$, where $z$ is an eigenvalue of $A$.

## Main results

- `DLTI.isAsymptoticallyStable_iff_matrix_pow_tendsto_zero`: (1) ↔ (2)
- `DLTI.isAsymptoticallyStable_iff_eigenvalue_norm_lt_one`: (1) ↔ (3)
- `matrix_pow_tendsto_zero_iff_eigenvalue_norm_lt_one`: (2) ↔ (3)
-/

open DLTI Filter Matrix
open scoped Matrix.Norms.Operator -- $l_\infty$-induced matrix norm

variable {n : Type*} [Fintype n] [DecidableEq n] -- number of states

namespace DLTI

-- The system $x(t + 1) = A x(t)$ is asymptotically stable if $x(t)$ goes to 0 for all initial
-- conditions $x(0) = x_0$.
def IsAsymptoticallyStable
    (A : Matrix n n ℂ) : Prop :=
  ∀ x₀ : n → ℂ, Tendsto (State A (0 : Matrix n n ℂ) x₀ (fun _ => 0)) atTop (nhds 0)

-- State solution of $x(t + 1) = A x(t)$
lemma state_solution_autonomous
    {R : Type*} [Semiring R]
    (A : Matrix n n R)
    (x₀ : n → R) :
    State A (0 : Matrix n n R) x₀ (fun _ => 0) = (fun t => A ^ t *ᵥ x₀) := by
  funext t
  -- t : ℕ
  -- ⊢ State A 0 x₀ (fun x ↦ 0) t = A ^ t *ᵥ x₀
  rw [state_solution]
  -- ⊢ A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ 0 *ᵥ 0 = A ^ t *ᵥ x₀
  simp

-- The eigenvalues of $A$ have modulus less than 1 if $x(t)$ goes to 0.
lemma eigenvalue_norm_lt_one_if_isAsymptoticallyStable
    {A : Matrix n n ℂ}
    (hA : IsAsymptoticallyStable A) :
    ∀ z ∈ spectrum ℂ A, ‖z‖ < 1 := by
  unfold IsAsymptoticallyStable at hA
  -- hA : ∀ (x₀ : n → ℂ), Tendsto (State A 0 x₀ fun x ↦ 0) atTop (nhds 0)
  intro z hz
  -- z : ℂ
  -- hz : z ∈ spectrum ℂ A
  -- ⊢ ‖z‖ < 1
  obtain ⟨v, hv, he⟩ := exists_eigenvector hz
  -- v : n → ℂ
  -- hv : v ≠ 0
  -- he : A *ᵥ v = z • v
  specialize hA v
  -- hA : Tendsto (State A 0 v fun x ↦ 0) atTop (nhds 0)
  rw [state_solution_autonomous] at hA
  -- hA : Tendsto (fun t ↦ A ^ t *ᵥ v) atTop (nhds 0)
  apply eigenpower at he
  -- he : ∀ (k : ℕ), A ^ k *ᵥ v = z ^ k • v
  apply funext_iff.mpr at he
  -- he : (fun x ↦ A ^ x *ᵥ v) = (fun x ↦ z ^ x • v)
  rw [he] at hA
  -- hA : Tendsto (fun x ↦ z ^ x • v) atTop (nhds 0)
  apply tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp
  -- ⊢ Tendsto (fun n ↦ z ^ n) atTop (nhds 0)
  exact scalar_pow_tendsto_zero_if_scalar_pow_smul_nonzero_vector_tendsto_zero hv hA

-- $A^k$ goes to 0 if its eigenvalues have modulus less than 1.
lemma _root_.matrix_pow_tendsto_zero_if_eigenvalue_norm_lt_one
    {A : Matrix n n ℂ}
    (hz : ∀ z ∈ spectrum ℂ A, ‖z‖ < 1) :
    Tendsto (fun k => A ^ k) atTop (nhds 0) := by
  apply matrix_pow_tendsto_zero_if_spectralRadius_lt_one
  -- ⊢ spectralRadius ℂ A < 1
  by_cases h : Nontrivial (Matrix n n ℂ)
  · -- h : Nontrivial (Matrix n n ℂ)
    exact spectrum.spectralRadius_lt_of_forall_lt A hz
  · -- h : ¬Nontrivial (Matrix n n ℂ)
    have : Subsingleton (Matrix n n ℂ) := not_nontrivial_iff_subsingleton.mp h
    -- this : Subsingleton (Matrix n n ℂ)
    rw [spectrum.SpectralRadius.of_subsingleton A]
    -- ⊢ 0 < 1
    simp

-- $x(t)$ goes to 0 if $A^k$ goes to 0.
lemma isAsymptoticallyStable_if_matrix_pow_tendsto_zero
    {A : Matrix n n ℂ}
    (hA : Tendsto (fun k => A ^ k) atTop (nhds 0)) :
    IsAsymptoticallyStable A := by
  unfold IsAsymptoticallyStable
  -- ⊢ ∀ (x₀ : n → ℂ), Tendsto (State A 0 x₀ fun x ↦ 0) atTop (nhds 0)
  intro x₀
  -- x₀ : n → ℂ
  -- ⊢ Tendsto (State A 0 x₀ fun x ↦ 0) atTop (nhds 0)
  rw [state_solution_autonomous, tendsto_zero_iff_norm_tendsto_zero]
  -- ⊢ Tendsto (fun t ↦ A ^ t *ᵥ x₀) atTop (nhds 0)
  -- ⊢ Tendsto (fun x ↦ ‖A ^ x *ᵥ x₀‖) atTop (nhds 0)
  apply squeeze_zero
  -- (hf : ∀ (t : α), 0 ≤ f t) (hft : ∀ (t : α), f t ≤ g t) (g0 : Tendsto g t₀ (nhds 0)) :
  --   Tendsto f t₀ (nhds 0)
  · -- ⊢ ∀ (t : ℕ), 0 ≤ ‖A ^ t *ᵥ x₀‖
    exact fun k => norm_nonneg (A ^ k *ᵥ x₀)
  · -- ⊢ ∀ (t : ℕ), ‖A ^ t *ᵥ x₀‖ ≤ ?g t
    exact fun k => linfty_opNorm_mulVec (A ^ k) x₀
  · -- ⊢ Tendsto (fun k ↦ ‖A ^ k‖ * ‖x₀‖) atTop (nhds 0)
    simpa using Tendsto.mul_const ‖x₀‖ (tendsto_zero_iff_norm_tendsto_zero.mp hA)

-- $x(t)$ goes to 0 if and only if $A^k$ goes to 0.
theorem isAsymptoticallyStable_iff_matrix_pow_tendsto_zero
    (A : Matrix n n ℂ) :
    IsAsymptoticallyStable A ↔ Tendsto (fun k => A ^ k) atTop (nhds 0) := by
  constructor
  · -- ⊢ IsAsymptoticallyStable A → Tendsto (fun k ↦ A ^ k) atTop (nhds 0)
    intro h_onlyif
    -- h_onlyif : IsAsymptoticallyStable A
    -- ⊢ Tendsto (fun k ↦ A ^ k) atTop (nhds 0)
    apply matrix_pow_tendsto_zero_if_eigenvalue_norm_lt_one
    -- ⊢ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
    exact eigenvalue_norm_lt_one_if_isAsymptoticallyStable h_onlyif
  · -- ⊢ Tendsto (fun k ↦ A ^ k) atTop (nhds 0) → IsAsymptoticallyStable A
    exact isAsymptoticallyStable_if_matrix_pow_tendsto_zero

-- $x(t)$ goes to 0 if and only if the eigenvalues of $A$ have modulus less than 1.
theorem isAsymptoticallyStable_iff_eigenvalue_norm_lt_one
    (A : Matrix n n ℂ) :
    IsAsymptoticallyStable A ↔ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1 := by
  constructor
  · -- ⊢ IsAsymptoticallyStable A → ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
    exact eigenvalue_norm_lt_one_if_isAsymptoticallyStable
  · -- ⊢ (∀ z ∈ spectrum ℂ A, ‖z‖ < 1) → IsAsymptoticallyStable A
    intro h_if
    -- h_if : ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
    -- ⊢ IsAsymptoticallyStable A
    apply matrix_pow_tendsto_zero_if_eigenvalue_norm_lt_one at h_if
    -- h_if : Tendsto (fun k ↦ A ^ k) atTop (nhds 0)
    exact (isAsymptoticallyStable_iff_matrix_pow_tendsto_zero A).mpr h_if

-- $A^k$ goes to 0 if and only if its eigenvalues have modulus less than 1.
theorem _root_.matrix_pow_tendsto_zero_iff_eigenvalue_norm_lt_one
    (A : Matrix n n ℂ) :
    Tendsto (fun k => A ^ k) atTop (nhds 0) ↔ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1 := by
  rw [← isAsymptoticallyStable_iff_matrix_pow_tendsto_zero,
    isAsymptoticallyStable_iff_eigenvalue_norm_lt_one]
  -- ⊢ IsAsymptoticallyStable A ↔ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1
  -- ⊢ (∀ z ∈ spectrum ℂ A, ‖z‖ < 1) ↔ ∀ z ∈ spectrum ℂ A, ‖z‖ < 1

end DLTI
