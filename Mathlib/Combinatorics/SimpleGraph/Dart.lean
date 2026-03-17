/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.HasDart.Basic
public import Mathlib.Combinatorics.SimpleGraph.HasDart

/-!
# Darts in simple graphs

This files gives simple-graph-specific properties of darts.
-/

@[expose] public section

namespace HasDart

variable {V : Type*} {G : SimpleGraph V}

/-- The edge associated to the dart. -/
def prodDart.edge (d : prodDart G) : Sym2 V := s(d.fst, d.snd)

@[simp]
theorem prodDart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (prodDart.mk p h).edge = s(p.1, p.2) :=
  rfl

@[simp]
theorem prodDart.edge_mem (d : prodDart G) : d.edge ∈ G.edgeSet :=
  d.dart'

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def prodDart.symm (d : prodDart G) : prodDart G :=
  ⟨d.toProd.swap, G.symm d.dart'⟩

@[simp]
theorem prodDart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) :
    (prodDart.mk p h).symm = prodDart.mk p.swap h.symm :=
  rfl

@[simp]
theorem prodDart.edge_symm (d : prodDart G) : d.symm.edge = d.edge :=
  Sym2.eq_swap

@[simp]
theorem prodDart.edge_comp_symm :
    prodDart.edge ∘ prodDart.symm = (prodDart.edge : prodDart G → Sym2 V) :=
  funext prodDart.edge_symm

@[simp]
theorem prodDart.symm_symm (d : prodDart G) : d.symm.symm = d :=
  prodDart.ext' _ _ <| Prod.swap_swap _

@[simp]
theorem prodDart.symm_involutive : Function.Involutive (prodDart.symm : prodDart G → prodDart G) :=
  prodDart.symm_symm

theorem prodDart.symm_ne (d : prodDart G) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ prodDart.toProd) d.dart'.ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : prodDart G, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp only [prodDart.edge_mk, Sym2.eq, Prod.mk.eta, Sym2.rel_iff', prodDart.mk.injEq,
    prodDart.symm_mk, Prod.fst_swap, Prod.snd_swap]
  grind

theorem dart_edge_eq_mk'_iff :
    ∀ {d : prodDart G} {u v : V}, d.edge = s(u, v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u) := by
  rintro ⟨p, h⟩ _ _
  simp

theorem dart_edge_eq_mk'_iff' :
    ∀ {d : prodDart G} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : prodDart G :=
  ⟨(v, w), w.property⟩

theorem dartOfNeighborSet_injective (v : V) : Function.Injective (dartOfNeighborSet G v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

instance nonempty_dart_top [Nontrivial V] : Nonempty (prodDart (⊤ : SimpleGraph V)) := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end HasDart
