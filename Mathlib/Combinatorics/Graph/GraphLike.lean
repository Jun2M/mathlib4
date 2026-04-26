/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
In this file we make `Graph` an instance of `GraphLike`.
-/

public section

variable {V E D : Type*} {G : Graph V E}

namespace Graph

/-- `HasDart` is a typeclass for graphs with a dart structure. -/
class HasDart (G : Graph V E) (D : outParam Type*) [DartLike V D] where
  /-- The set of darts of a graph. -/
  dartSet : Set D
  /-- The opposite dart, provided by fixed-point-free involution. -/
  symm : D → D
  symm_invol : ∀ ⦃d⦄, symm (symm d) = d
  symm_ne : ∀ ⦃d⦄, symm d ≠ d
  symm_fst : ∀ ⦃d⦄, DartLike.fst (symm d) = (DartLike.snd d : V)
  symm_mem : ∀ ⦃d⦄, d ∈ dartSet → symm d ∈ dartSet
  /-- The edge of a dart. -/
  edge : D → E
  edge_eq_edge_iff : ∀ ⦃d₁ d₂⦄, edge d₁ = edge d₂ ↔ d₁ = d₂ ∨ d₁ = symm d₂
  edge_surj : ∀ ⦃e⦄, e ∈ G.edgeSet → ∃ d ∈ dartSet, e = edge d
  isLink : ∀ ⦃d⦄, d ∈ dartSet → G.IsLink (edge d) (DartLike.fst d) (DartLike.snd d)

open HasDart

instance [DartLike V D] [HasDart G D] : GraphLike V D {H : Graph V E // H ≤ G} where
  verts H := V(H.val)
  darts H := (HasDart.edge G) ⁻¹' E(H.val)
  fst_mem_of_darts H d hd := by
    simp only [Set.mem_preimage] at hd
    obtain ⟨d', hd', heq⟩ := edge_surj (H.prop.edgeSet_mono hd)
    obtain rfl | rfl := edge_eq_edge_iff.mp heq
    · exact isLink hd' |>.of_compatible (H.prop.compatible') hd |>.left_mem
    rw [symm_fst]
    exact heq ▸ isLink hd' |>.of_compatible (H.prop.compatible') hd |>.right_mem
  snd_mem_of_darts H d hd := by
    simp only [Set.mem_preimage] at hd
    obtain ⟨d', hd', heq⟩ := edge_surj (H.prop.edgeSet_mono hd)
    obtain rfl | rfl := edge_eq_edge_iff.mp heq
    · exact isLink hd' |>.of_compatible (H.prop.compatible') hd |>.right_mem
    rw [← symm_fst (G := G), symm_invol]
    exact heq ▸ isLink hd' |>.of_compatible (H.prop.compatible') hd |>.left_mem
  Adj H u v := H.val.Adj u v
  exists_darts_iff_adj H u v := by
    refine ⟨?_, fun ⟨e, he⟩ => ?_⟩
    · rintro ⟨d, hd, rfl, rfl⟩
      rw [Set.mem_preimage] at hd
      obtain ⟨d', hd', heq⟩ := edge_surj (H.prop.edgeSet_mono hd)
      obtain rfl | rfl := edge_eq_edge_iff.mp heq
      · exact isLink hd' |>.of_compatible (H.prop.compatible') hd |>.adj
      rw [← symm_fst (G := G), symm_invol, symm_fst]
      exact heq ▸ (heq ▸ isLink hd' |>.of_compatible (H.prop.compatible') hd) |>.adj.symm
    obtain ⟨d, hd, rfl, rfl⟩ := edge_surj (he.mono H.prop).edge_mem
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (he.mono H.prop).eq_and_eq_or_eq_and_eq <| isLink hd
    · use d, by simp [he.edge_mem]
    refine ⟨symm G d, ?_, ?_⟩
    · have := edge_eq_edge_iff.mpr (show symm G d = d ∨ symm G d = symm G d from by tauto)
      simp [this, he.edge_mem]
    simp only [symm_fst, true_and]
    rw [← symm_fst (G := G), symm_invol]

end Graph
