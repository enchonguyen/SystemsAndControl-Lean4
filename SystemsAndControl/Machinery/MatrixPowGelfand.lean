import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Matrix Exponentiation Corollaries of Gelfand's Formula

We provide results regarding (the norm of) exponentiated complex matrices under the assumption that
the spectral radius is bounded. They are consequences of Gelfand's formula.

## Main results

- `matrix_pow_enorm_eventually_le_spectralRadius_bound_pow`: If the spectral radius of a complex
  matrix $A$ is less than $r$, then $||A ^ k||_e \leq r ^ k$ for a sufficiently large $k$.
- `matrix_pow_nnnorm_eventually_le_spectralRadius_bound_pow`: If the spectral radius of a complex
  matrix $A$ is less than $r$, then $||A ^ k||_+ \leq r ^ k$ for a sufficiently large $k$.
- `matrix_pow_norm_eventually_le_spectralRadius_bound_pow` : If the spectral radius of a complex
  matrix $A$ is less than $r$, then $||A ^ k|| \leq r ^ k$ for a sufficiently large $k$.
- `matrix_pow_enorm_tendsto_zero_if_spectralRadius_lt_one`: If the spectral radius of a complex
  matrix $A$ is less than 1, then $||A ^ k||_e$ goes to 0.
- `matrix_pow_nnnorm_tendsto_zero_if_spectralRadius_lt_one`: If the spectral radius of a complex
  matrix $A$ is less than 1, then $||A ^ k||_+$ goes to 0.
- `matrix_pow_norm_tendsto_zero_if_spectralRadius_lt_one`: If the spectral radius of a complex
  matrix $A$ is less than 1, then $||A ^ k||$ goes to 0.
- `matrix_pow_tendsto_zero_if_spectralRadius_lt_one`: If the spectral radius of a complex matrix $A$
  is less than 1, then $A ^ k$ goes to 0.
-/

open ENNReal Filter spectrum
open scoped Matrix.Norms.Operator -- $l_\infty$-induced matrix norm
-- open scoped Matrix.Norms.Frobenius -- Frobenius norm; also works

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}
variable {r : ℝ≥0∞} -- strict upper bound on the spectral radius of $A$

-- The (e)norm of a complex exponentiated matrix is bounded by the exponentiated bound
-- of its spectral radius.
theorem matrix_pow_enorm_eventually_le_spectralRadius_bound_pow
    (hA : spectralRadius ℂ A < r) :
    ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ₑ ≤ r ^ k := by
  have h_gf := Tendsto.eventually_le_const hA (gelfand_formula A)
  -- h_gf : ∀ᶠ (b : ℕ) in atTop, ↑‖A ^ b‖₊ ^ (1 / ↑b) ≤ r
  rw [eventually_atTop] at h_gf
  -- h_gf : ∃ a, ∀ b ≥ a, ↑‖A ^ b‖₊ ^ (1 / ↑b) ≤ r
  obtain ⟨N, hN⟩ := h_gf
  -- N : ℕ
  -- hN : ∀ b ≥ N, ↑‖A ^ b‖₊ ^ (1 / ↑b) ≤ r
  rw [eventually_atTop]
  -- ⊢ ∃ a, ∀ b ≥ a, ‖A ^ b‖ₑ ≤ r ^ b
  use max 1 N
  -- ⊢ ∀ b ≥ max 1 N, ‖A ^ b‖ₑ ≤ r ^ b
  intro k hk
  -- k : ℕ
  -- hk : k ≥ max 1 N
  -- ⊢ ‖A ^ k‖ₑ ≤ r ^ k
  have hk0_nat: (k : ℕ) > 0 := by omega
  -- hk0_nat : k > 0
  have hk0_real : (k : ℝ) > 0 := Nat.cast_pos.mpr hk0_nat
  -- hk0_real : ↑k > 0
  have hkN : k ≥ N := le_of_max_le_right hk
  -- hkN : k ≥ N
  specialize hN k hkN
  -- hN : ↑‖A ^ k‖₊ ^ (1 / ↑k) ≤ r
  rwa [← rpow_natCast r k, ← rpow_inv_le_iff hk0_real, ← one_div]
  -- ⊢ ‖A ^ k‖ₑ ≤ r ^ ↑k
  -- ⊢ ‖A ^ k‖ₑ ^ (↑k)⁻¹ ≤ r
  -- ⊢ ‖A ^ k‖ₑ ^ (1 / ↑k) ≤ r

-- The (nn)norm of a complex exponentiated matrix is bounded by the exponentiated bound
-- of its spectral radius.
theorem matrix_pow_nnnorm_eventually_le_spectralRadius_bound_pow
    (hA : spectralRadius ℂ A < r) :
    ∀ᶠ k : ℕ in atTop, ‖A ^ k‖₊ ≤ r ^ k :=
  matrix_pow_enorm_eventually_le_spectralRadius_bound_pow hA

-- The norm of a complex exponentiated matrix is bounded by the exponentiated bound
-- of its spectral radius.
theorem matrix_pow_norm_eventually_le_spectralRadius_bound_pow
    (hr : r ≠ ∞)
    (hA : spectralRadius ℂ A < r) :
    ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ ENNReal.toReal r ^ k := by
  filter_upwards [matrix_pow_nnnorm_eventually_le_spectralRadius_bound_pow hA]
  -- ⊢ ∀ (b : ℕ), ↑‖A ^ b‖₊ ≤ r ^ b → ‖A ^ b‖ ≤ r.toReal ^ b
  intro k hk
  -- k : ℕ
  -- hk : ↑‖A ^ k‖₊ ≤ r ^ k
  -- ⊢ ‖A ^ k‖ ≤ r.toReal ^ k
  rwa [← toReal_le_toReal (coe_ne_top) (pow_ne_top hr), toReal_pow] at hk
  -- hk : (↑‖A ^ k‖₊).toReal ≤ (r ^ k).toReal
  -- hk : (↑‖A ^ k‖₊).toReal ≤ r.toReal ^ k

-- Existence of a finite nonnegative constant between the spectral radius and its finite bound
lemma exists_finite_nonneg_const_gt_spectralRadius_lt_finite_bound
    (hr : r ≠ ∞)
    (hAr : spectralRadius ℂ A < r) :
    ∃ r' : ℝ≥0∞, r' ≥ 0 ∧ r' ≠ ∞ ∧ spectralRadius ℂ A < r' ∧ r' < r := by
  obtain ⟨r', hAr', hr'r⟩ : ∃ r' : ℝ≥0∞, spectralRadius ℂ A < r' ∧ r' < r := exists_between hAr
  -- r' : ℝ≥0∞
  -- hAr' : spectralRadius ℂ A < r'
  -- hr'r : r' < r
  have hr'0 : r' ≥ 0 := zero_le r'
  -- hr'0 : r' ≥ 0
  have hr'_fin : r' ≠ ∞ := ne_of_lt (lt_trans hr'r (Ne.lt_top hr))
  -- hr'_fin : r' ≠ ∞
  exact ⟨r', hr'0, hr'_fin, hAr', hr'r⟩

-- The (e)norm of an exponentiated complex matrix goes to 0 if its spectral radius is less than 1.
theorem matrix_pow_enorm_tendsto_zero_if_spectralRadius_lt_one
    (hA1 : spectralRadius ℂ A < 1) :
    Tendsto (fun k => ‖A ^ k‖ₑ) atTop (nhds 0) := by
  obtain ⟨r, _, _, hAr, hr⟩ := exists_finite_nonneg_const_gt_spectralRadius_lt_finite_bound
    (lt_top_iff_ne_top.mp one_lt_top) hA1
  -- r : ℝ≥0∞
  -- hAr : spectralRadius ℂ A < r
  -- hr : r < 1
  apply Tendsto.squeeze'
  -- (hg : Tendsto g b (nhds a)) (hh : Tendsto h b (nhds a)) (hgf : ∀ᶠ (b : β) in b, g b ≤ f b)
  --   (hfh : ∀ᶠ (b : β) in b, f b ≤ h b) : Tendsto f b (nhds a)
  · -- ⊢ Tendsto ?g atTop (nhds 0)
    exact tendsto_const_nhds
  · -- ⊢ Tendsto ?h atTop (nhds 0)
    exact ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr hr
  · -- ⊢ ∀ᶠ (b : ℕ) in atTop, 0 ≤ ‖A ^ b‖ₑ
    exact Eventually.of_forall (fun k => zero_le ‖A ^ k‖ₑ)
  · -- ⊢ ∀ᶠ (b : ℕ) in atTop, ‖A ^ b‖ₑ ≤ r ^ b
    exact matrix_pow_enorm_eventually_le_spectralRadius_bound_pow hAr

-- The (nn)norm of an exponentiated complex matrix goes to 0 if its spectral radius is less than 1.
theorem matrix_pow_nnnorm_tendsto_zero_if_spectralRadius_lt_one
    (hA : spectralRadius ℂ A < 1) :
    Tendsto (fun k => ‖A ^ k‖₊) atTop (nhds 0) :=
  ENNReal.tendsto_coe.mp (matrix_pow_enorm_tendsto_zero_if_spectralRadius_lt_one hA)

-- The norm of an exponentiated complex matrix goes to 0 if its spectral radius is less than 1.
theorem matrix_pow_norm_tendsto_zero_if_spectralRadius_lt_one
    (hA : spectralRadius ℂ A < 1) :
    Tendsto (fun k => ‖A ^ k‖) atTop (nhds 0) :=
  NNReal.tendsto_coe.mpr (matrix_pow_nnnorm_tendsto_zero_if_spectralRadius_lt_one hA)

-- An exponentiated complex matrix goes to 0 if its spectral radius is less than 1.
theorem matrix_pow_tendsto_zero_if_spectralRadius_lt_one
    (hA : spectralRadius ℂ A < 1) :
    Tendsto (fun k => A ^ k) atTop (nhds 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (matrix_pow_norm_tendsto_zero_if_spectralRadius_lt_one hA)
