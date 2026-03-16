/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.HasDart.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
In this file we make `Digraph` an instance of `HasDart`.
-/

@[expose] public section

variable {α : Type*}

instance : HasDart α (Digraph α) where
  verts _ := Set.univ
  adj G := G.Adj
  dart G u v := G.Adj u v
  adj_iff_dart_like := nonempty_prop.symm
  left_mem_verts_of_adj _ := Set.mem_univ _
  right_mem_verts_of_adj _ := Set.mem_univ _
