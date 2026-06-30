import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Spectral Theory for Matrices

For a (complex) matrix, we derive various results, related to its eigenpair: exponentiation,
asymptotics and conjugate transposes.

## Main results

- `Matrix.exists_eigenvector`: Extract an eigenvector from a matrix, given an eigenvalue
- `Matrix.exists_eigenpair`: Extract an eigenpair from a nonvoid complex matrix
- `Matrix.eigenpower`: Given an eigenpair $(z, v)$ of $A$, $A v = z v$ implies $A^k v = z^k v$ for
  all natural numbers k.
- `Matrix.eigenvalue_norm_lt_one_if_matrix_pow_tendsto_zero`: For an eigenvalue $z$ of a complex
  matrix $A$, if $A^k$ goes to 0, then $|z| < 1$.
- `Matrix.spectralRadius_eq_conjTranspose`: The spectral radius of a complex matrix is equal to the
  one of its conjugate transpose.
-/

open ENNReal Filter Matrix Module.End spectrum
open scoped Matrix.Norms.Operator -- $l_\infty$-induced matrix norm

namespace Matrix

-- Eigenvalues and eigenvectors

-- Finding an eigenvector corresponding to a given eigenvalue
theorem exists_eigenvector
    {F : Type*} [Field F]
    {n : Type*} [Fintype n] [DecidableEq n]
    {z : F}
    {A : Matrix n n F}
    (hz : z ∈ spectrum F A) :
    ∃ v : n → F, v ≠ 0 ∧ A *ᵥ v = z • v := by
  rw [← spectrum_toLin' A, ← hasEigenvalue_iff_mem_spectrum] at hz
  -- hz : z ∈ spectrum F (toLin' A)
  -- hz : HasEigenvalue (toLin' A) z
  obtain ⟨v, hv⟩ := HasEigenvalue.exists_hasEigenvector hz
  -- v : n → F
  -- hv : HasEigenvector (toLin' A) z v
  use v
  -- ⊢ v ≠ 0 ∧ A *ᵥ v = z • v
  constructor
  · -- ⊢ v ≠ 0
    exact (hasEigenvector_iff.mp hv).2
  · -- ⊢ A *ᵥ v = z • v
    rw [← toLin'_apply]
    -- ⊢ (toLin' A) v = z • v
    exact HasEigenvector.apply_eq_smul hv

-- Extracting an eigenpair from a nonvoid complex matrix
theorem exists_eigenpair
    {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]
    (A : Matrix n n ℂ) :
    ∃ z ∈ spectrum ℂ A, ∃ v : n → ℂ, v ≠ 0 ∧ A *ᵥ v = z • v := by
  obtain ⟨z, hz⟩ := spectrum.nonempty A
  -- z : ℂ
  -- hz : z ∈ spectrum ℂ A
  obtain ⟨v, hv, he⟩ := exists_eigenvector hz
  -- v : n → ℂ
  -- hv : v ≠ 0
  -- he : A *ᵥ v = z • v
  exact ⟨z, hz, v, hv, he⟩

-- An eigenpair $(z, v)$ of $A$ satisfies $A^k v = z^k v$ for all natural numbers k.
theorem eigenpower
    {F : Type*} [Field F]
    {n : Type*} [Fintype n] [DecidableEq n]
    {z : F}
    {v : n → F}
    {A : Matrix n n F}
    (he : A *ᵥ v = z • v) :
    ∀ k : ℕ, (A ^ k) *ᵥ v = z ^ k • v := by
  intro k
  -- k : ℕ
  -- ⊢ A ^ k *ᵥ v = z ^ k • v
  induction k with
  | zero =>
    -- ⊢ A ^ 0 *ᵥ v = z ^ 0 • v
    simp
  | succ k ih =>
    -- k : ℕ
    -- ih : A ^ k *ᵥ v = z ^ k • v
    -- ⊢ A ^ (k + 1) *ᵥ v = z ^ (k + 1) • v
    rw [pow_succ, ← mulVec_mulVec, he, mulVec_smul, ih, smul_smul, ← pow_succ']
    -- ⊢ (A ^ k * A) *ᵥ v = ...
    -- ⊢ A ^ k *ᵥ A *ᵥ v = ...
    -- ⊢ A ^ k *ᵥ z • v = ...
    -- ⊢ z • A ^ k *ᵥ v = ...
    -- ⊢ z • z ^ k • v = ...
    -- ⊢ (z * z ^ k) • v = ...
    -- ⊢ z ^ (k + 1) • v = ...

-- Asymptotics of eigenpairs

-- If $z^k * v$ goes to 0 for a scalar $z$ and a nonzero vector $v$, then $z^k$ goes to 0.
lemma _root_.scalar_pow_tendsto_zero_if_scalar_pow_smul_nonzero_vector_tendsto_zero
    {F : Type*} [Field F] [TopologicalSpace F] [SeparatelyContinuousMul F]
    {n : Type*}
    {z : F}
    {v : n → F}
    (hv : v ≠ 0)
    (hz : Tendsto (fun k => z ^ k • v) atTop (nhds 0)) :
    Tendsto (fun k => z ^ k) atTop (nhds 0) := by
  have ⟨i, hv_i⟩ : ∃ i : n, v i ≠ 0 := by
    by_contra ch
    -- ch : ¬∃ i, v i ≠ 0
    -- ⊢ False
    push Not at ch
    -- ch : ∀ (i : n), v i = 0
    have hv0 : v = 0 := funext ch
    -- hv0 : v = 0
    exact hv hv0
  -- i : n
  -- hv_i : v i ≠ 0
  rw [tendsto_pi_nhds] at hz
  -- hz : ∀ (x : n), Tendsto (fun i ↦ (z ^ i • v) x) atTop (nhds (0 x))
  specialize hz i
  -- hz : Tendsto (fun a ↦ (z ^ a • v) i) atTop (nhds (0 i))
  apply Tendsto.div_const (y := v i) at hz
  -- hz : Tendsto (fun a ↦ (z ^ a • v) i / v i) atTop (nhds (0 i / v i))
  simp at hz
  -- hz : Tendsto (fun a ↦ z ^ a * v i / v i) atTop (nhds 0)
  field_simp at hz
  -- hz : Tendsto (fun a ↦ z ^ a) atTop (nhds 0)
  exact hz

-- If $A^k$ goes to 0, then so does $z^k$, where $z$ is an eigenvalue of a complex matrix $A$.
theorem eigenvalue_norm_lt_one_if_matrix_pow_tendsto_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    {z : ℂ}
    {v : n → ℂ}
    {A : Matrix n n ℂ}
    (hv : v ≠ 0)
    (he : A *ᵥ v = z • v)
    (hA : Tendsto (fun k => A ^ k) atTop (nhds 0)) :
    ‖z‖ < 1 := by
  apply eigenpower at he
  -- he : ∀ (k : ℕ), A ^ k *ᵥ v = z ^ k • v
  have he_fun : (fun k => A ^ k *ᵥ v) = (fun k => z ^ k • v) := funext he
  -- he_fun : (fun k ↦ A ^ k *ᵥ v) = fun k ↦ z ^ k • v
  apply tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp
  -- ⊢ Tendsto (fun k ↦ z ^ k) atTop (nhds 0)
  apply scalar_pow_tendsto_zero_if_scalar_pow_smul_nonzero_vector_tendsto_zero
  -- (hv : v ≠ 0) (hz : Tendsto (fun k ↦ z ^ k • v) atTop (nhds 0)) :
  --   Tendsto (fun k ↦ z ^ k) atTop (nhds 0)
  · -- ⊢ ?v ≠ 0
    exact hv
  · -- ⊢ Tendsto (fun k ↦ z ^ k • v) atTop (nhds 0)
    rw [← he_fun, tendsto_zero_iff_norm_tendsto_zero]
    -- ⊢ Tendsto (fun k ↦ A ^ k *ᵥ v) atTop (nhds 0)
    -- ⊢ Tendsto (fun k ↦ ‖A ^ k *ᵥ v‖) atTop (nhds 0)
    apply squeeze_zero
    -- (hf : ∀ (t : α), 0 ≤ f t) (hft : ∀ (t : α), f t ≤ g t) (g0 : Tendsto g t₀ (nhds 0)) :
    --   Tendsto f t₀ (nhds 0)
    · -- ⊢ ∀ (t : ℕ), 0 ≤ ‖A ^ t *ᵥ v‖
      exact fun k => norm_nonneg ((A ^ k) *ᵥ v)
    · -- ⊢ ∀ (t : ℕ), ‖A ^ t *ᵥ v‖ ≤ ?hz.g t
      exact fun k => linfty_opNorm_mulVec (A ^ k) v
    · -- ⊢ Tendsto (fun k ↦ ‖A ^ k‖ * ‖v‖) atTop (nhds 0)
      rw [tendsto_zero_iff_norm_tendsto_zero] at hA
      -- hA : Tendsto (fun k ↦ ‖A ^ k‖) atTop (nhds 0)
      apply Tendsto.mul_const ‖v‖ at hA
      -- hA : Tendsto (fun k ↦ ‖A ^ k‖ * ‖v‖) atTop (nhds (0 * ‖v‖))
      simpa using hA

-- Conjugate transposed complex matrices

-- If $z$ is an eigenvalue of a complex matrix $A$, then the conjugate of $z$ is an
-- eigenvalue of the conjugate transpose of $A$.
lemma star_eigenvalue_in_spectrum_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    {z : ℂ}
    {A : Matrix n n ℂ}
    (hz : z ∈ spectrum ℂ A) :
    star z ∈ spectrum ℂ Aᴴ := by
  have : Aᴴ = star A := by rfl
  -- this : Aᴴ = star A
  rw [this, spectrum.map_star]
  -- ⊢ star z ∈ spectrum ℂ (star A)
  -- ⊢ star z ∈ star (spectrum ℂ A)
  exact Set.star_mem_star.mpr hz

-- The spectral radius of a complex matrix is at most the one of its conjugate transpose.
lemma spectralRadius_lt_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    spectralRadius ℂ A ≤ spectralRadius ℂ Aᴴ := by
  by_cases h : Nontrivial (Matrix n n ℂ)
  · -- h : Nontrivial (Matrix n n ℂ)
    obtain ⟨z, hz, hz_sr⟩ := exists_nnnorm_eq_spectralRadius A
    -- z : ℂ
    -- hz : z ∈ spectrum ℂ A
    -- hz_sr : ↑‖z‖₊ = spectralRadius ℂ A
    rw [← hz_sr]
    -- ⊢ ↑‖z‖₊ ≤ spectralRadius ℂ Aᴴ
    unfold spectralRadius
    -- ⊢ ↑‖z‖₊ ≤ ⨆ k ∈ spectrum ℂ Aᴴ, ↑‖k‖₊
    have : ‖z‖₊ = ‖star z‖₊ := by simp
    -- this : ‖z‖₊ = ‖star z‖₊
    rw [this]
    -- ⊢ ↑‖star z‖₊ ≤ ⨆ k ∈ spectrum ℂ Aᴴ, ↑‖k‖₊
    apply star_eigenvalue_in_spectrum_conjTranspose at hz
    -- hz : star z ∈ spectrum ℂ Aᴴ
    exact le_biSup (fun k => (‖k‖₊ : ℝ≥0∞)) hz
  · -- h : ¬Nontrivial (Matrix n n ℂ)
    have : Subsingleton (Matrix n n ℂ) := not_nontrivial_iff_subsingleton.mp h
    -- this : Subsingleton (Matrix n n ℂ)
    rw [SpectralRadius.of_subsingleton A, SpectralRadius.of_subsingleton Aᴴ]
    -- ⊢ 0 ≤ spectralRadius ℂ Aᴴ
    -- ⊢ 0 ≤ 0

-- The spectral radius of a complex matrix is equal to the one of its conjugate transpose.
theorem spectralRadius_eq_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    spectralRadius ℂ A = spectralRadius ℂ Aᴴ := by
  apply le_antisymm
  -- a ≤ b → b ≤ a → a = b
  · -- ⊢ spectralRadius ℂ A ≤ spectralRadius ℂ Aᴴ
    exact spectralRadius_lt_conjTranspose A
  · -- ⊢ spectralRadius ℂ Aᴴ ≤ spectralRadius ℂ A
    have := spectralRadius_lt_conjTranspose Aᴴ
    -- this : spectralRadius ℂ Aᴴ ≤ spectralRadius ℂ Aᴴᴴ
    rwa [conjTranspose_conjTranspose] at this
    -- this : spectralRadius ℂ Aᴴ ≤ spectralRadius ℂ A

end Matrix
