import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Telescoping Sums

We provide results about partial and infinite telescoping sums. For infinite sums, we assume that
the sequence $(f_k)$ converges to $L$ and that either $f_k$ or the difference $f_{k + 1} - f_k$ is
summable (though, the former implies the latter). Each statement comes with its "dual", where we add
a minus sign to both sides.

## Main results

- `Finset.sum_telescope`: Partial telescoping sum for $f_{k + 1} - f_k$
- `Finset.sum_telescope'`: Partial telescoping sum for $f_k - f_{k + 1}$
- `tsum_telescope_if_sub_summable`: Infinite telescoping sum for $f_{k + 1} - f_k$, assuming
  $f_{k + 1} - f_k$ is summable
- `tsum_telescope_if_sub_summable'`: Infinite telescoping sum for $f_k - f_{k + 1}$, assuming
  $f_k - f_{k + 1}$ is summable
- `tsum_telescope_if_summable`: Infinite telescoping sum for $f_{k + 1} - f_k$, assuming $f_k$ is
  summable
- `tsum_telescope_if_summable'`: Infinite telescoping sum for $f_k - f_{k + 1}$, assuming $f_k$ is
  summable
-/

open Filter Finset

namespace Finset

-- Partial telescoping sums

-- Partial telescoping sum: $f_{k + 1} - f_k$
theorem sum_telescope
    {G : Type*} [AddCommGroup G]
    (f : ℕ → G) :
    ∀ k : ℕ, ∑ i ∈ range k, (f (i + 1) - f i) = f k - f 0 := by
  intro k
  -- k : ℕ
  -- ⊢ ∑ i ∈ range k, (f (i + 1) - f i) = f k - f 0
  induction k with
  | zero =>
    -- ⊢ ∑ i ∈ range 0, (f (i + 1) - f i) = f 0 - f 0
    simp
  | succ k ih =>
    -- k : ℕ
    -- ih : ∑ i ∈ range k, (f (i + 1) - f i) = f k - f 0
    -- ⊢ ∑ i ∈ range (k + 1), (f (i + 1) - f i) = f (k + 1) - f 0
    rw [sum_range_succ, ih]
    -- ⊢ ∑ x ∈ range k, (f (x + 1) - f x) + (f (k + 1) - f k) = f (k + 1) - f 0
    -- ⊢ f k - f 0 + (f (k + 1) - f k) = f (k + 1) - f 0
    simp

-- Partial telescoping sum: $f_k - f_{k + 1}$
theorem sum_telescope'
    {G : Type*} [AddCommGroup G]
    (f : ℕ → G) :
    ∀ k : ℕ, ∑ i ∈ range k, (f i - f (i + 1)) = f 0 - f k := by
  intro k
  -- k : ℕ
  -- ⊢ ∑ i ∈ range k, (f i - f (i + 1)) = f 0 - f k
  induction k with
  | zero =>
    -- ⊢ ∑ i ∈ range 0, (f i - f (i + 1)) = f 0 - f 0
    simp
  | succ k ih =>
    -- k : ℕ
    -- ih : ∑ i ∈ range k, (f i - f (i + 1)) = f 0 - f k
    -- ⊢ ∑ i ∈ range (k + 1), (f i - f (i + 1)) = f 0 - f (k + 1)
    rw [sum_range_succ, ih]
    -- ⊢ ∑ x ∈ range k, (f x - f (x + 1)) + (f k - f (k + 1)) = f 0 - f (k + 1)
    -- ⊢ f 0 - f k + (f k - f (k + 1)) = f 0 - f (k + 1)
    simp

  -- ALTERNATIVE PROOF:
  -- intro k
  -- -- k : ℕ
  -- -- ⊢ ∑ i ∈ range k, (f i - f (i + 1)) = f 0 - f k
  -- rw [← neg_inj, ← sum_neg_distrib]
  -- -- ⊢ -∑ i ∈ range k, (f i - f (i + 1)) = -(f 0 - f k)
  -- -- ⊢ ∑ i ∈ range k, -(f i - f (i + 1)) = -(f 0 - f k)
  -- simp [← sum_telescope]

end Finset

-- Infinite telescoping sums

-- Infinite telescoping sum if $f_{k + 1} - f_k$ is summable
theorem tsum_telescope_if_sub_summable
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    {L : G}
    {f : ℕ → G}
    (hf : Summable (fun k => f (k + 1) - f k))
    (hfL : Tendsto f atTop (nhds L)) :
    ∑' k : ℕ, (f (k + 1) - f k) = L - f 0 := by
  have hf_lim : Tendsto (fun k => ∑ i ∈ range k, (f (i + 1) - f i)) atTop (nhds (L - f 0)) := by
    simp_rw [sum_telescope]
    -- ⊢ Tendsto (fun k ↦ f k - f 0) atTop (nhds (L - f 0))
    exact Tendsto.sub_const hfL (f 0)
  -- hf_lim : Tendsto (fun k ↦ ∑ i ∈ range k, (f (i + 1) - f i)) atTop (nhds (L - f 0))
  exact tendsto_nhds_unique (HasSum.tendsto_sum_nat (Summable.hasSum hf)) hf_lim

-- Infinite telescoping sum if $f_k - f_{k + 1}$ is summable
theorem tsum_telescope_if_sub_summable'
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    {L : G}
    {f : ℕ → G}
    (hf : Summable (fun k => f k - f (k + 1)))
    (hfL : Tendsto f atTop (nhds L)) :
    ∑' k : ℕ, (f k - f (k + 1)) = f 0 - L := by
  have hf_lim : Tendsto (fun k => ∑ i ∈ range k, (f i - f (i + 1))) atTop (nhds (f 0 - L)) := by
    simp_rw [sum_telescope']
    -- ⊢ Tendsto (fun k ↦ f 0 - f k) atTop (nhds (f 0 - L))
    exact Tendsto.const_sub (f 0) hfL
  -- hf_lim : Tendsto (fun k ↦ ∑ i ∈ range k, (f i - f (i + 1))) atTop (nhds (f 0 - L))
  exact tendsto_nhds_unique (HasSum.tendsto_sum_nat (Summable.hasSum hf)) hf_lim

  -- -- ALTERNATIVE PROOF:
  -- have hf' : Summable (fun k => f (k + 1) - f k) := by
  --   apply Summable.of_neg
  --   -- ⊢ Summable fun k ↦ -(f (k + 1) - f k)
  --   simp [hf]
  -- -- hf' : Summable fun k ↦ f (k + 1) - f k
  -- rw [← neg_inj, ← tsum_neg]
  -- -- ⊢ -∑' (k : ℕ), (f k - f (k + 1)) = -(f 0 - L)
  -- -- ⊢ ∑' (k : ℕ), -(f k - f (k + 1)) = -(f 0 - L)
  -- simp [tsum_telescope_if_sub_summable hf' hfL]

-- If $f_k$ is summable, then so is $f_{k + 1} - f_k$.
lemma summable_sub_if_summable
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {f : ℕ → G}
    (hf : Summable f) :
    Summable (fun k => f (k + 1) - f k) := by
  apply Summable.sub
  -- (hf : Summable f) (hg : Summable g) : Summable (fun b ↦ f b - g b)
  · -- ⊢ Summable fun k ↦ f (k + 1)
    exact (summable_nat_add_iff 1).mpr hf
  · -- ⊢ Summable f
    exact hf

-- If $f_k$ is summable, then so is $f_k - f_{k + 1}$.
lemma summable_sub_if_summable'
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {f : ℕ → G}
    (hf : Summable f) :
    Summable (fun k => f k - f (k + 1)) := by
  apply Summable.sub
  -- (hf : Summable f) (hg : Summable g) : Summable (fun b ↦ f b - g b)
  · -- ⊢ Summable f
    exact hf
  · -- ⊢ Summable fun k ↦ f (k + 1)
    exact (summable_nat_add_iff 1).mpr hf

  -- -- ALTERNATIVE PROOF:
  -- apply Summable.of_neg
  -- -- ⊢ Summable fun k ↦ -(f k - f (k + 1))
  -- simp [summable_sub_if_summable hf]

-- Infinite telescoping sum for $f_{k + 1} - f_k$ if $f_k$ is summable
theorem tsum_telescope_if_summable
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    {L : G}
    {f : ℕ → G}
    (hf : Summable f)
    (hfL : Tendsto f atTop (nhds L)) :
    ∑' k : ℕ, (f (k + 1) - f k) = L - f 0 := by
  apply tsum_telescope_if_sub_summable
  -- (hf : Summable fun k ↦ f (k + 1) - f k) (hfL : Tendsto f atTop (nhds L)) :
  --   ∑' (k : ℕ), (f (k + 1) - f k) = L - f 0
  · -- ⊢ Summable fun k ↦ f (k + 1) - f k
    exact summable_sub_if_summable hf
  · -- ⊢ Tendsto f atTop (nhds L)
    exact hfL

-- Infinite telescoping sum for $f_k - f_{k + 1}$ if $f_k$ is summable
theorem tsum_telescope_if_summable'
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    {L : G}
    {f : ℕ → G}
    (hf : Summable f)
    (hfL : Tendsto f atTop (nhds L)) :
    ∑' k : ℕ, (f k - f (k + 1)) = f 0 - L := by
  apply tsum_telescope_if_sub_summable'
  -- (hf : Summable fun k ↦ f k - f (k + 1)) (hfL : Tendsto f atTop (nhds L)) :
  --   ∑' (k : ℕ), (f k - f (k + 1)) = f 0 - L
  · -- ⊢ Summable fun k ↦ f k - f (k + 1)
    exact summable_sub_if_summable' hf
  · -- ⊢ Tendsto f atTop (nhds L)
    exact hfL

  -- -- ALTERNATIVE PROOF:
  -- rw [← neg_inj, ← tsum_neg]
  -- -- ⊢ -∑' (k : ℕ), (f k - f (k + 1)) = -(f 0 - L)
  -- -- ⊢ ∑' (k : ℕ), -(f k - f (k + 1)) = -(f 0 - L)
  -- simp [tsum_telescope_if_summable hf hfL]
