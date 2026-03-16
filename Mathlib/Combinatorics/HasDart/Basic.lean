/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Data.Rel

/-!
# Typeclass for different kinds of (simple) graphs

This module defines the typeclass `HasDart` for capturing the common structure of different kinds of
(simple) graphs.

## Main definitions

* `HasDart`: is the main typeclass in question. The field `verts` gives the set of vertices of a
  graph, and the field `Adj` gives the adjacency relation between vertices.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.

-/

@[expose] public section

universe u'

class HasDart (α : outParam Type*) (Gr : Type*) where
  verts (G : Gr) : Set α
  adj (G : Gr) : α → α → Prop
  dart : Gr → α → α → Sort u'
  adj_iff_dart_like {G : Gr} {u v : α} : adj G u v ↔ Nonempty (dart G u v)
  left_mem_verts_of_adj {G : Gr} {u v : α} (h : adj G u v) : u ∈ verts G
  right_mem_verts_of_adj {G : Gr} {u v : α} (h : adj G u v) : v ∈ verts G

namespace HasDart

variable {Gr : Type*} {α : Type*} [HasDart α Gr]

/-- Dot notation for `left_mem_verts_of_adj`. -/
lemma adj.left_mem_verts {G : Gr} {v w : α} (h : adj G v w) : v ∈ verts G :=
  left_mem_verts_of_adj h

/-- Dot notation for `right_mem_verts_of_adj`. -/
lemma adj.right_mem_verts {G : Gr} {v w : α} (h : adj G v w) : w ∈ verts G :=
  right_mem_verts_of_adj h

end HasDart
