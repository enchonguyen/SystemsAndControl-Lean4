import Mathlib.Data.Finset.Range
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# State and Output Solutions of Discrete-Time Linear Time-Invariant Systems

Given matrices $A$, $B$, $C$ and $D$, we show the solutions of the state and output equations
$x(t + 1) = A x(t) + B u(t)$ and $y(t) = C x(t) + D u(t)$, respectively:
$x(t; x_0, u) = A^t x_0 + \sum_{i = 0}^{t - 1} A^{t - i - 1} B u(i)$ and
$y(t; x_0, u) = C A^t x_0 + \sum_{i = 0}^{t - 1} C A^{t - i - 1} B u(i) + D u(t)$.
There are $n$ states, $m$ inputs and $p$ outputs. The initial condition $x(0)$ is denoted by x₀.

## Main results

- `DLTI.state_solution`: The solution of the state equation
- `DLTI.output_solution`: The solution of the output equation
-/

open Finset Matrix

variable {R : Type*} [Semiring R] -- elements of matrices and vectors
variable {n : Type*} [Fintype n] [DecidableEq n] -- number of states
variable {m : Type*} [Fintype m] -- number of inputs
variable {p : Type*} -- number of outputs

namespace DLTI

-- State equation: $x(t + 1) = A x(t) + B u(t)$ with $x(0) = x_0$
def State
    (A : Matrix n n R)
    (B : Matrix n m R)
    (x₀ : n → R)
    (u : ℕ → m → R) :
    ℕ → n → R
  | 0 => x₀
  | t + 1 => A *ᵥ State A B x₀ u t + B *ᵥ u t

-- Output equation: $y(t) = C x(t) + D u(t)$ with $x(0) = x_0$
def Output
    (A : Matrix n n R)
    (B : Matrix n m R)
    (C : Matrix p n R)
    (D : Matrix p m R)
    (x₀ : n → R)
    (u : ℕ → m → R) :
    ℕ → p → R :=
  fun t => C *ᵥ State A B x₀ u t + D *ᵥ u t

-- By induction, we prove that
-- $x(t; x_0, u) = A^t x_0 + \sum_{i = 0}^{t - 1} A^{t - i - 1} B u(i)$.
theorem state_solution
    (A : Matrix n n R)
    (B : Matrix n m R)
    (x₀ : n → R)
    (u : ℕ → m → R) :
    State A B x₀ u = (fun t => A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i) := by
  funext t
  -- t : ℕ
  -- ⊢ State A B x₀ u t = A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i
  induction t with
  | zero =>
    -- ⊢ State A B x₀ u 0 = A ^ 0 *ᵥ x₀ + ∑ i ∈ range 0, A ^ (0 - i - 1) *ᵥ B *ᵥ u i
    simp
    -- ⊢ State A B x₀ u 0 = x₀
    rfl
  | succ t ih =>
    -- t : ℕ
    -- ih : State A B x₀ u t = A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i
    -- ⊢ State A B x₀ u (t + 1) =
    --     A ^ (t + 1) *ᵥ x₀ + ∑ i ∈ range (t + 1), A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i
    have hA : ∑ i ∈ range t, A ^ (t - i - 1 + 1) *ᵥ B *ᵥ u i =
                ∑ i ∈ range t, A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i := by
    -- i < t is not directly implied from i ∈ range t
      apply sum_congr
      -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
      · -- ⊢ range t = range t
        rfl
      · -- ⊢ ∀ x ∈ range t, A ^ (t - x - 1 + 1) *ᵥ B *ᵥ u x = A ^ (t + 1 - x - 1) *ᵥ B *ᵥ u x
        intro i hi
        -- i : ℕ
        -- hi : i ∈ range t
        -- ⊢ A ^ (t - i - 1 + 1) *ᵥ B *ᵥ u i = A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i
        congr 2
        -- ⊢ t - i - 1 + 1 = t + 1 - i - 1
        have : i < t := mem_range.mp hi
        -- this : i < t
        omega
    -- hA : ∑ i ∈ range t, A ^ (t - i - 1 + 1) *ᵥ B *ᵥ u i =
    --        ∑ i ∈ range t, A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i
    calc
        State A B x₀ u (t + 1)
      = A *ᵥ State A B x₀ u t + B *ᵥ u t := by
          rfl
    _ = A *ᵥ (A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i) + B *ᵥ u t := by
          rw [ih]
    _ = A ^ (t + 1) *ᵥ x₀ + A *ᵥ ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i + B *ᵥ u t := by
          rw [mulVec_add, mulVec_mulVec, ← pow_succ'];
          -- ⊢ A *ᵥ A ^ t *ᵥ x₀ + ... = ...
          -- ⊢ (A * A ^ t) *ᵥ x₀ + ... = ...
          -- ⊢ A ^ (t + 1) *ᵥ x₀ + ... = ...
    _ = A ^ (t + 1) *ᵥ x₀ + ∑ i ∈ range t, A *ᵥ A ^ (t - i - 1) *ᵥ B *ᵥ u i + B *ᵥ u t := by
          rw [mulVec_sum]
    _ = A ^ (t + 1) *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1 + 1) *ᵥ B *ᵥ u i + B *ᵥ u t := by
          simp only [pow_succ', ← mulVec_mulVec]
    _ = A ^ (t + 1) *ᵥ x₀ + ∑ i ∈ range t, A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i + B *ᵥ u t := by
          rw [hA]
    _ = A ^ (t + 1) *ᵥ x₀ + ∑ i ∈ range (t + 1), A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i := by
          rw [sum_range_succ]
          -- ⊢ ... = ... + (∑ i ∈ range t, A ^ (t + 1 - i - 1) *ᵥ B *ᵥ u i +
          --                  A ^ (t + 1 - t - 1) *ᵥ B *ᵥ u t)
          simp only [mulVec_mulVec, add_tsub_cancel_left, tsub_self, pow_zero, Matrix.one_mul,
            add_assoc]

-- Substituting the state solution in the output equation results in
-- $y(t; x_0, u) = C A^t x_0 + \sum_{i = 0}^{t - 1} C A^{t - i - 1} B u(i) + D u(t)$.
theorem output_solution
    (A : Matrix n n R)
    (B : Matrix n m R)
    (C : Matrix p n R)
    (D : Matrix p m R)
    (x₀ : n → R)
    (u : ℕ → m → R) :
    Output A B C D x₀ u =
      fun t => C *ᵥ A ^ t *ᵥ x₀ + ∑ i ∈ range t, C *ᵥ A ^ (t - i - 1) *ᵥ B *ᵥ u i + D *ᵥ u t := by
  funext t
  -- ⊢ Output A B C D x₀ u t =
  --     C *ᵥ A ^ t *ᵥ x₀ + ∑ i ∈ range t, C *ᵥ A ^ (t - i - 1) *ᵥ B *ᵥ u i + D *ᵥ u t
  calc
      Output A B C D x₀ u t
    = C *ᵥ State A B x₀ u t +  D *ᵥ u t := by
        rfl
  _ = C *ᵥ (A ^ t *ᵥ x₀ + ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i) + D *ᵥ u t := by
        rw [state_solution]
  _ = C *ᵥ A ^ t *ᵥ x₀ + C *ᵥ ∑ i ∈ range t, A ^ (t - i - 1) *ᵥ B *ᵥ u i + D *ᵥ u t := by
        rw [mulVec_add]
  _ = C *ᵥ A ^ t *ᵥ x₀ + ∑ i ∈ range t, C *ᵥ A ^ (t - i - 1) *ᵥ B *ᵥ u i + D *ᵥ u t := by
        rw [mulVec_sum]

end DLTI
