import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Multiplication of Infinite Sums by a Constant Vector or Matrix

We show that summability and distributivity is preserved when multiplying infinite sums (if they
exist) by constant vectors and matrices. This includes the dot product as well as matrix-vector and
vector-matrix multiplication.

The results for "hMul" are "Summable.mul_left", "Summable.mul_right", "Summable.tsum_mul_left" and
"Summable.tsum_mul_right":
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Ring.html#Summable.mul_left
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Ring.html#Summable.mul_right
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Ring.html#Summable.tsum_mul_left
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/Ring.html#Summable.tsum_mul_right

The versions of the distributivity results for finite sums are "dotProduct_sum",
"sum_dotProduct", "Matrix.sum_mulVec", "Matrix.mulVec_sum", "Matrix.sum_vecMul" and
"Matrix.vecMul_sum":
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html#dotProduct_sum
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html#sum_dotProduct
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.sum_mulVec
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.mulVec_sum
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.sum_vecMul
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Basic.html#Matrix.vecMul_sum

## Main results

- `summable_dotProduct_left`: Left dot products preserve summability.
- `summable_dotProduct_right`: Right dot products preserve summability.
- `summable_vecMul_left`: Left multiplication by a vector preserves summability.
- `summable_mulVec_right`: Right multiplication by a vector preserves summability.
- `summable_mulVec_left`: Left multiplication by a matrix preserves summability.
- `summable_vecMul_right`: Right multiplication by a matrix preserves summability.
- `dotProduct_tsum`: Left dot products are distributive.
- `tsum_dotProduct`: Right dot products are distributive.
- `vecMul_tsum`: Left multiplication by a vector is distributive.
- `tsum_mulVec`: Right multiplication by a vector is distributive.
- `mulVec_tsum`: Left multiplication by a matrix is distributive.
- `tsum_vecMul`: Right multiplication by a matrix is distributive.
-/

open Finset Matrix

-- Elements of matrices and vectors
variable {R : Type*} [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
variable {R' : Type*} [NonUnitalNonAssocSemiring R'] [TopologicalSpace R']
  [IsTopologicalSemiring R'] [T2Space R']
-- Dimensions of matrices and vectors; Summation index
variable {n : Type*} [Fintype n]
variable {ι m : Type*}

-- By definition, Matrix m n R = (m → n → R).
instance
    {m n R : Type*} [TopologicalSpace R] :
    TopologicalSpace (Matrix m n R) := inferInstanceAs (TopologicalSpace (m → n → R))

-- Summability

-- Summability is preserved when taking dot products from the left.
theorem summable_dotProduct_left
    {f : ι → n → R}
    (a : n → R)
    (hf : Summable f) :
    Summable (fun (i : ι) => a ⬝ᵥ f i) := by
  unfold dotProduct
  -- ⊢ Summable fun b ↦ ∑ i, a i * f b i
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a i * f b i
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ a n' * f b n'
  apply Summable.mul_left
  -- ⊢ Summable fun b ↦ f b n'
  apply Pi.summable.mp hf

-- Summability is preserved when taking dot products from the right.
theorem summable_dotProduct_right
    {f : ι → n → R}
    (a : n → R)
    (hf : Summable f) :
    Summable (fun (i : ι) => f i ⬝ᵥ a) := by
  unfold dotProduct
  -- ⊢ Summable fun b ↦ ∑ i, f b i * a i
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b i * a i
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ f b n' * a n'
  apply Summable.mul_right
  -- ⊢ Summable fun b ↦ f b n'
  apply Pi.summable.mp hf

-- Summability is preserved when left-multiplying by a vector.
theorem summable_vecMul_left
    {f : ι → Matrix n m R}
    (a : n → R)
    (hf : Summable f) :
    Summable (fun (i : ι) => a ᵥ* f i) := by
  unfold vecMul
  -- ⊢ Summable fun b x ↦ a ⬝ᵥ (fun i ↦ f b i x)
  unfold dotProduct
  -- ⊢ Summable fun b x ↦ ∑ i, a i * f b i x
  rw [Pi.summable]
  -- ⊢ ∀ (x : m), Summable fun b ↦ ∑ i, a i * f b i x
  intro m'
  -- m' : m
  -- ⊢ Summable fun b ↦ ∑ i, a i * f b i m'
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a i * f b i m'
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ a n' * f b n' m'
  apply Summable.mul_left
  -- ⊢ Summable fun b ↦ f b n' m'
  apply Pi.summable.mp
  -- ⊢ Summable fun b ↦ f b n'
  apply Pi.summable.mp hf

-- Summability is preserved when right-multiplying by a vector.
theorem summable_mulVec_right
    {f : ι → Matrix m n R}
    (a : n → R)
    (hf : Summable f) :
    Summable (fun (i : ι) => f i *ᵥ a) := by
  unfold mulVec
  -- ⊢ Summable fun b x ↦ (fun i ↦ f b x i) ⬝ᵥ a
  unfold dotProduct
  -- ⊢ Summable fun b x ↦ ∑ i, f b x i * a i
  rw [Pi.summable]
  -- ⊢ ∀ (x : m), Summable fun b ↦ ∑ i, f b x i * a i
  intro m'
  -- m' : m
  -- ⊢ Summable fun b ↦ ∑ i, f b m' i * a i
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b m' i * a i
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ f b m' n' * a n'
  apply Summable.mul_right
  -- ⊢ Summable fun b ↦ f b m' n'
  apply Pi.summable.mp
  -- ⊢ Summable fun b ↦ f b m'
  apply Pi.summable.mp hf

-- Summability is preserved when left-multiplying by a matrix.
theorem summable_mulVec_left
    {f : ι → n → R}
    (a : Matrix m n R)
    (hf : Summable f) :
    Summable (fun (i : ι) => a *ᵥ f i) := by
  unfold mulVec
  -- ⊢ Summable fun b x ↦ (fun i ↦ a x i) ⬝ᵥ f b
  unfold dotProduct
  -- ⊢ Summable fun b x ↦ ∑ i, a x i * f b i
  rw [Pi.summable]
  -- ⊢ ∀ (x : m), Summable fun b ↦ ∑ i, a x i * f b i
  intro m'
  -- m' : m
  -- ⊢ Summable fun b ↦ ∑ i, a m' i * f b i
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a m' i * f b i
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ a m' n' * f b n'
  apply Summable.mul_left
  -- ⊢ Summable fun b ↦ f b n'
  apply Pi.summable.mp hf

-- Summability is preserved when right-multiplying by a matrix.
theorem summable_vecMul_right
    {f : ι → n → R}
    (a : Matrix n m R)
    (hf : Summable f) :
    Summable (fun (i : ι) => f i ᵥ* a) := by
  unfold vecMul
  -- ⊢ Summable fun b x ↦ f b ⬝ᵥ (fun i ↦ a i x)
  unfold dotProduct
  -- ⊢ Summable fun b x ↦ ∑ i, f b i * a i x
  rw [Pi.summable]
  -- ⊢ ∀ (x : m), Summable fun b ↦ ∑ i, f b i * a i x
  intro m'
  -- m' : m
  -- ⊢ Summable fun b ↦ ∑ i, f b i * a i m'
  apply summable_sum
  -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b i * a i m'
  intro n' _
  -- n' : n
  -- ⊢ Summable fun b ↦ f b n' * a n' m'
  apply Summable.mul_right
  -- ⊢ Summable fun b ↦ f b n'
  apply Pi.summable.mp hf

-- Distributivity

-- Distributivity is preserved when taking dot products from the left.
theorem dotProduct_tsum
    {f : ι → n → R'}
    (a : n → R')
    (hf : Summable f) :
    a ⬝ᵥ ∑' i : ι, f i = ∑' i : ι, a ⬝ᵥ f i := by
  unfold dotProduct
  -- ⊢ ∑ i, a i * (∑' (b : ι), f b) i = ∑' (b : ι), ∑ i, a i * f b i
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ⊢ ∑ i, a i * (∑' (b : ι), f b) i = ∑ i, ∑' (b : ι), a i * f b i
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, a i * (∑' (b : ι), f b) i = ∑' (b : ι), a i * f b i
      intro n' _
      -- n' : n
      -- ⊢ a n' * (∑' (b : ι), f b) n' = ∑' (b : ι), a n' * f b n'
      rw [Summable.tsum_mul_left]
      -- (hf : Summable f) : ∑' (i : ι), a * f i = a * ∑' (i : ι), f i
      · -- ⊢ a n' * (∑' (b : ι), f b) n' = a n' * ∑' (b : ι), f b n'
        rw [tsum_apply hf]
      · -- ⊢ Summable fun b ↦ f b n'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a i * f b i
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ a n' * f b n'
    apply Summable.mul_left
    -- ⊢ Summable fun b ↦ f b n'
    apply Pi.summable.mp hf

-- Distributivity is preserved when taking dot products from the right.
theorem tsum_dotProduct
    {f : ι → n → R'}
    (a : n → R')
    (hf : Summable f) :
    (∑' i : ι, f i) ⬝ᵥ a = ∑' i : ι, f i ⬝ᵥ a := by
  unfold dotProduct
  -- ⊢ ∑ i, (∑' (b : ι), f b) i * a i = ∑' (b : ι), ∑ i, f b i * a i
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ⊢ ∑ i, (∑' (b : ι), f b) i * a i = ∑ i, ∑' (b : ι), f b i * a i
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, (∑' (b : ι), f b) i * a i = ∑' (b : ι), f b i * a i
      intro n' _
      -- n' : n
      -- ⊢ (∑' (b : ι), f b) n' * a n' = ∑' (b : ι), f b n' * a n'
      rw [Summable.tsum_mul_right]
      -- (hf : Summable f) : ∑' (i : ι), f i * a = (∑' (i : ι), f i) * a
      · -- ⊢ (∑' (b : ι), f b) n' * a n' = (∑' (b : ι), f b n') * a n'
        rw [tsum_apply hf]
      · -- ⊢ Summable fun b ↦ f b n'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b i * a i
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ f b n' * a n'
    apply Summable.mul_right
    -- ⊢ Summable fun b ↦ f b n'
    apply Pi.summable.mp hf

-- Distributivity is preserved when left-multiplying by a vector.
theorem vecMul_tsum
    {f : ι → Matrix n m R'}
    (a : n → R')
    (hf : Summable f) :
    a ᵥ* ∑' i : ι, f i = ∑' i : ι, a ᵥ* f i := by
  funext m'
  -- m' : m
  -- ⊢ (a ᵥ* ∑' (b : ι), f b) m' = (∑' (b : ι), a ᵥ* f b) m'
  rw [tsum_apply (summable_vecMul_left a hf)]
  -- ⊢ (a ᵥ* ∑' (b : ι), f b) m' = ∑' (b : ι), (a ᵥ* f b) m'
  unfold vecMul
  -- ⊢ a ⬝ᵥ (fun i ↦ (∑' (b : ι), f b) i m') = ∑' (b : ι), a ⬝ᵥ (fun i ↦ f b i m')
  unfold dotProduct
  -- ⊢ ∑ i, a i * (∑' (b : ι), f b) i m' = ∑' (b : ι), ∑ i, a i * f b i m'
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ∑ i, a i * (∑' (b : ι), f b) i m' = ∑ i, ∑' (b : ι), a i * f b i m'
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, a i * (∑' (b : ι), f b) i m' = ∑' (b : ι), a i * f b i m'
      intro n' _
      -- n' : n
      -- ⊢ a n' * (∑' (b : ι), f b) n' m' = ∑' (b : ι), a n' * f b n' m'
      rw [Summable.tsum_mul_left]
      -- (hf : Summable f) : ∑' (i : ι), a * f i = a * ∑' (i : ι), f i
      · -- ⊢ a n' * (∑' (b : ι), f b) n' m' = a n' * ∑' (b : ι), f b n' m'
        congr 1
        -- ⊢ (∑' (b : ι), f b) n' m' = ∑' (b : ι), f b n' m'
        rw [← tsum_apply]
        -- (hf : Summable f) : (∑' (i : ι), f i) x = ∑' (i : ι), f i x
        · -- ⊢ (∑' (b : ι), f b) n' m' = (∑' (b : ι), f b n') m'
          apply congrFun
          -- ⊢ (∑' (b : ι), f b) n' = ∑' (b : ι), f b n'
          apply tsum_apply hf
        · -- ⊢ Summable fun b ↦ f b n'
          apply Pi.summable.mp hf
      · -- ⊢ Summable fun b ↦ f b n' m'
        apply Pi.summable.mp
        -- ⊢ Summable fun b ↦ f b n'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a i * f b i m'
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ a n' * f b n' m'
    apply Summable.mul_left
    -- ⊢ Summable fun b ↦ f b n' m'
    apply Pi.summable.mp
    -- ⊢ Summable fun b ↦ f b n'
    apply Pi.summable.mp hf

-- Distributivity is preserved when right-multiplying by a vector.
theorem tsum_mulVec
    {f : ι → Matrix m n R'}
    (a : n → R')
    (hf : Summable f) :
    (∑' i : ι, f i) *ᵥ a = ∑' i : ι, f i *ᵥ a := by
  funext m'
  -- m' : m
  -- ⊢ ((∑' (b : ι), f b) *ᵥ a) m' = (∑' (b : ι), f b *ᵥ a) m'
  rw [tsum_apply (summable_mulVec_right a hf)]
  -- ⊢ ((∑' (b : ι), f b) *ᵥ a) m' = ∑' (b : ι), (f b *ᵥ a) m'
  unfold mulVec
  -- ⊢ (fun i ↦ (∑' (b : ι), f b) m' i) ⬝ᵥ a = ∑' (b : ι), (fun i ↦ f b m' i) ⬝ᵥ a
  unfold dotProduct
  -- ⊢ ∑ i, (∑' (b : ι), f b) m' i * a i = ∑' (b : ι), ∑ i, f b m' i * a i
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ⊢ ∑ i, (∑' (b : ι), f b) m' i * a i = ∑ i, ∑' (b : ι), f b m' i * a i
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, (∑' (b : ι), f b) m' i * a i = ∑' (b : ι), f b m' i * a i
      intro n' _
      -- n' : n
      -- ⊢ (∑' (b : ι), f b) m' n' * a n' = ∑' (b : ι), f b m' n' * a n'
      rw [Summable.tsum_mul_right]
      -- (hf : Summable f) : ∑' (i : ι), f i * a = (∑' (i : ι), f i) * a
      · -- ⊢ (∑' (b : ι), f b) m' n' * a n' = (∑' (b : ι), f b m' n') * a n'
        congr 1
        -- ⊢ (∑' (b : ι), f b) m' n' = ∑' (b : ι), f b m' n'
        rw [← tsum_apply]
        -- (hf : Summable f) : (∑' (i : ι), f i) x = ∑' (i : ι), f i x
        · -- ⊢ (∑' (b : ι), f b) m' n' = (∑' (b : ι), f b m') n'
          apply congrFun
          -- ⊢ (∑' (b : ι), f b) m' = ∑' (b : ι), f b m'
          apply tsum_apply hf
        · -- ⊢ Summable fun b ↦ f b m'
          apply Pi.summable.mp hf
      · -- ⊢ Summable fun b ↦ f b m' n'
        apply Pi.summable.mp
        -- ⊢ Summable fun b ↦ f b m'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b m' i * a i
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ f b m' n' * a n'
    apply Summable.mul_right
    -- ⊢ Summable fun b ↦ f b m' n'
    apply Pi.summable.mp
    -- ⊢ Summable fun b ↦ f b m'
    apply Pi.summable.mp hf

-- Distributivity is preserved when left-multiplying by a matrix.
theorem mulVec_tsum
    {f : ι → n → R'}
    (a : Matrix m n R')
    (hf : Summable f) :
    a *ᵥ ∑' i : ι, f i = ∑' i : ι, a *ᵥ f i := by
  funext m'
  -- m' : m
  -- ⊢ (a *ᵥ ∑' (b : ι), f b) m' = (∑' (b : ι), a *ᵥ f b) m'
  rw [tsum_apply (summable_mulVec_left a hf)]
  -- ⊢ (a *ᵥ ∑' (b : ι), f b) m' = ∑' (b : ι), (a *ᵥ f b) m'
  unfold mulVec
  -- ⊢ (fun i ↦ a m' i) ⬝ᵥ ∑' (b : ι), f b = ∑' (b : ι), (fun i ↦ a m' i) ⬝ᵥ f b
  unfold dotProduct
  -- ⊢ ∑ i, a m' i * (∑' (b : ι), f b) i = ∑' (b : ι), ∑ i, a m' i * f b i
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ⊢ ∑ i, a m' i * (∑' (b : ι), f b) i = ∑ i, ∑' (b : ι), a m' i * f b i
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, a m' i * (∑' (b : ι), f b) i = ∑' (b : ι), a m' i * f b i
      intro n' _
      -- n' : n
      -- ⊢ a m' n' * (∑' (b : ι), f b) n' = ∑' (b : ι), a m' n' * f b n'
      rw [Summable.tsum_mul_left]
      -- (hf : Summable f) : ∑' (i : ι), a * f i = a * ∑' (i : ι), f i
      · -- ⊢ a m' n' * (∑' (b : ι), f b) n' = a m' n' * ∑' (b : ι), f b n'
        rw [tsum_apply hf]
      · -- ⊢ Summable fun b ↦ f b n'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ a m' i * f b i
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ a m' n' * f b n'
    apply Summable.mul_left
    -- ⊢ Summable fun b ↦ f b n'
    apply Pi.summable.mp hf

-- Distributivity is preserved when right-multiplying by a matrix.
theorem tsum_vecMul
    {f : ι → n → R'}
    (a : Matrix n m R')
    (hf : Summable f) :
    (∑' i : ι, f i) ᵥ* a = ∑' i : ι, f i ᵥ* a := by
  funext m'
  -- m' : m
  -- ⊢ ((∑' (b : ι), f b) ᵥ* a) m' = (∑' (b : ι), f b ᵥ* a) m'
  rw [tsum_apply (summable_vecMul_right a hf)]
  -- ⊢ ((∑' (b : ι), f b) ᵥ* a) m' = ∑' (b : ι), (f b ᵥ* a) m'
  unfold vecMul
  -- ⊢ ∑' (b : ι), f b) ⬝ᵥ (fun i ↦ a i m') = ∑' (b : ι), f b ⬝ᵥ (fun i ↦ a i m')
  unfold dotProduct
  -- ⊢ ∑ i, (∑' (b : ι), f b) i * a i m' = ∑' (b : ι), ∑ i, f b i * a i m'
  rw [Summable.tsum_finsetSum]
  -- (hf : ∀ i ∈ s, Summable (f i)) : ∑' (b : β), ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' (b : β), f i b
  · -- ⊢ ∑ i, (∑' (b : ι), f b) i * a i m' = ∑ i, ∑' (b : ι), f b i * a i m'
    apply sum_congr
    -- (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
    · -- ⊢ univ = univ
      rfl
    · -- ⊢ ∀ i ∈ univ, (∑' (b : ι), f b) i * a i m' = ∑' (b : ι), f b i * a i m'
      intro n' _
      -- n' : n
      -- ⊢ (∑' (b : ι), f b) n' * a n' m' = ∑' (b : ι), f b n' * a n' m'
      rw [Summable.tsum_mul_right]
      -- (hf : Summable f) : ∑' (i : ι), f i * a = (∑' (i : ι), f i) * a
      · -- ⊢ (∑' (b : ι), f b) n' * a n' m' = (∑' (b : ι), f b n') * a n' m'
        rw [tsum_apply hf]
      · -- ⊢ Summable fun b ↦ f b n'
        apply Pi.summable.mp hf
  · -- ⊢ ∀ i ∈ univ, Summable fun b ↦ f b i * a i m'
    intro n' _
    -- n' : n
    -- ⊢ Summable fun b ↦ f b n' * a n' m'
    apply Summable.mul_right
    -- ⊢ Summable fun b ↦ f b n'
    apply Pi.summable.mp hf
