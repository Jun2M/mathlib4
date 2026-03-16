/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.HasDart.Walks.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
In this file we make `SimpleGraph` an instance of `HasDart`.
-/

@[expose] public section

variable {α : Type*}

variable {Gr : Type*} [HasDart α Gr] {G : Gr} {u v : α}

instance : HasDart α (SimpleGraph α) where
  verts _ := Set.univ
  adj G := G.Adj
  left_mem_verts_of_adj _ {u _ : α} _ := Set.mem_univ u
  right_mem_verts_of_adj _ {_ v : α} _ := Set.mem_univ v
  dart G u v := G.Adj u v
  adj_iff_dart_like := nonempty_prop.symm
