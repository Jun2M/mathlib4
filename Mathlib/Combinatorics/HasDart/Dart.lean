/-
Copyright (c) 2026 Iván Renison, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Kyle Miller
-/
module

public import Mathlib.Combinatorics.HasDart.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

@[expose] public section

universe u' u''

namespace HasDart

variable {α : Type*} {Gr : Type*}

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
structure prodDart [HasDart α Gr] (G : Gr) : Type (max u'' u_1) extends α × α where
  adj : (dart G fst snd : Sort u'')

initialize_simps_projections prodDart (+toProd, -fst, -snd)

attribute [simp] prodDart.adj

variable {G : Gr} [HasDart.{0} α Gr]

theorem prodDart.ext_iff (d₁ d₂ : prodDart G) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp +contextual

@[ext]
theorem prodDart.ext (d₁ d₂ : prodDart G) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (prodDart.ext_iff d₁ d₂).mpr h

theorem prodDart.toProd_injective : Function.Injective (prodDart.toProd : prodDart G → α × α) :=
  prodDart.ext

instance [DecidableEq α] (G : Gr) : DecidableEq (prodDart G) :=
  prodDart.toProd_injective.decidableEq

instance prodDart.fintype [Fintype α] [DecidableRel (dart G)] : Fintype (prodDart G) :=
  Fintype.ofEquiv (Σ v, { w | dart G v w })
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def prodDartAdj (d d' : prodDart G) : Prop :=
  d.snd = d'.fst

end HasDart
