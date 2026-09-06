/-
Copyright (c) 2026 Allen Goodman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Goodman
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Convergence of nested intervals

Let `f` be monotone, `g` antitone, and `f ≤ g`. The lower endpoints `f` and upper endpoints `g`
are bounded by each other, so they converge to their supremum and infimum, respectively.
The intersection of their closed intervals is the interval between these two limits.

If the distance between the endpoints tends to zero, both limits agree, the intersection is a
singleton, and every sequence lying between the endpoints converges to this common limit.
These results apply to both `ℝ` and `ℝ≥0`, in particular to bisection and the arithmetic–geometric
mean. They do not require an algebraic structure or a particular rule for choosing the endpoints.
-/

public section

open Filter Set Topology

variable {ι α : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

section Preorder

variable [Preorder α] {f g : ι → α}

/-- A monotone lower sequence is bounded above by any term of an antitone upper sequence. -/
theorem Monotone.bddAbove_range_of_antitone (hf : Monotone f) (hg : Antitone g) (hfg : f ≤ g) :
    BddAbove (range f) :=
  ⟨g (Classical.arbitrary ι), forall_mem_range.mpr fun i ↦
    hf.forall_le_of_antitone hg hfg i _⟩

/-- An antitone upper sequence is bounded below by any term of a monotone lower sequence. -/
theorem Antitone.bddBelow_range_of_monotone (hg : Antitone g) (hf : Monotone f) (hfg : f ≤ g) :
    BddBelow (range g) :=
  ⟨f (Classical.arbitrary ι), forall_mem_range.mpr fun i ↦
    hf.forall_le_of_antitone hg hfg _ i⟩

end Preorder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f g : ι → α}

/-- The supremum of the lower endpoints is at most the infimum of the upper endpoints. -/
theorem Monotone.ciSup_le_ciInf_of_antitone (hf : Monotone f) (hg : Antitone g) (hfg : f ≤ g) :
    (⨆ i, f i) ≤ ⨅ i, g i :=
  ciSup_le fun i ↦ le_ciInf fun j ↦ hf.forall_le_of_antitone hg hfg i j

/-- The intersection of nested closed intervals is the interval from the supremum of their
lower endpoints to the infimum of their upper endpoints. -/
theorem Monotone.iInter_Icc_eq_Icc_ciSup_ciInf (hf : Monotone f) (hg : Antitone g) (hfg : f ≤ g) :
    (⋂ i, Icc (f i) (g i)) = Icc (⨆ i, f i) (⨅ i, g i) := by
  ext x
  simp only [mem_iInter, mem_Icc, ciSup_le_iff (hf.bddAbove_range_of_antitone hg hfg),
    le_ciInf_iff (hg.bddBelow_range_of_monotone hf hfg), forall_and]

section OrderTopology

variable [TopologicalSpace α] [OrderTopology α]

/-- The lower endpoints converge to their supremum. -/
theorem Monotone.tendsto_atTop_ciSup_of_antitone (hf : Monotone f) (hg : Antitone g)
    (hfg : f ≤ g) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup hf (hf.bddAbove_range_of_antitone hg hfg)

/-- The upper endpoints converge to their infimum. -/
theorem Antitone.tendsto_atTop_ciInf_of_monotone (hg : Antitone g) (hf : Monotone f)
    (hfg : f ≤ g) : Tendsto g atTop (𝓝 (⨅ i, g i)) :=
  tendsto_atTop_ciInf hg (hg.bddBelow_range_of_monotone hf hfg)

end OrderTopology

section PseudoMetricSpace

variable [PseudoMetricSpace α] [OrderTopology α]

/-- Nested endpoints whose distance tends to zero have the same supremum and infimum. -/
theorem Monotone.ciSup_eq_ciInf_of_tendsto_dist (hf : Monotone f) (hg : Antitone g)
    (hfg : f ≤ g) (hd : Tendsto (fun i ↦ dist (f i) (g i)) atTop (𝓝 0)) :
    (⨆ i, f i) = ⨅ i, g i :=
  tendsto_nhds_unique ((hf.tendsto_atTop_ciSup_of_antitone hg hfg).congr_dist hd)
    (hg.tendsto_atTop_ciInf_of_monotone hf hfg)

/-- The lower endpoints converge to the infimum of the upper endpoints when their distance
tends to zero. -/
theorem Monotone.tendsto_atTop_ciInf_of_tendsto_dist (hf : Monotone f) (hg : Antitone g)
    (hfg : f ≤ g) (hd : Tendsto (fun i ↦ dist (f i) (g i)) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 (⨅ i, g i)) := by
  rw [← hf.ciSup_eq_ciInf_of_tendsto_dist hg hfg hd]
  exact hf.tendsto_atTop_ciSup_of_antitone hg hfg

/-- The upper endpoints converge to the supremum of the lower endpoints when their distance
tends to zero. -/
theorem Antitone.tendsto_atTop_ciSup_of_tendsto_dist (hg : Antitone g) (hf : Monotone f)
    (hfg : f ≤ g) (hd : Tendsto (fun i ↦ dist (f i) (g i)) atTop (𝓝 0)) :
    Tendsto g atTop (𝓝 (⨆ i, f i)) :=
  (hf.tendsto_atTop_ciSup_of_antitone hg hfg).congr_dist hd

/-- Any sequence between nested endpoints converges to their common limit if the distance
between the endpoints tends to zero. -/
theorem Monotone.tendsto_of_mem_Icc_of_tendsto_dist (hf : Monotone f) (hg : Antitone g)
    (hfg : f ≤ g) (hd : Tendsto (fun i ↦ dist (f i) (g i)) atTop (𝓝 0))
    {u : ι → α} (hu : ∀ i, u i ∈ Icc (f i) (g i)) :
    Tendsto u atTop (𝓝 (⨆ i, f i)) :=
  (hf.tendsto_atTop_ciSup_of_antitone hg hfg).squeeze
    (hg.tendsto_atTop_ciSup_of_tendsto_dist hf hfg hd) (fun i ↦ (hu i).1) (fun i ↦ (hu i).2)

/-- Nested closed intervals whose endpoint distance tends to zero have a unique common point. -/
theorem Monotone.iInter_Icc_eq_singleton_of_tendsto_dist (hf : Monotone f) (hg : Antitone g)
    (hfg : f ≤ g) (hd : Tendsto (fun i ↦ dist (f i) (g i)) atTop (𝓝 0)) :
    (⋂ i, Icc (f i) (g i)) = {⨆ i, f i} := by
  rw [hf.iInter_Icc_eq_Icc_ciSup_ciInf hg hfg,
    ← hf.ciSup_eq_ciInf_of_tendsto_dist hg hfg hd, Icc_self]

end PseudoMetricSpace

end ConditionallyCompleteLinearOrder
