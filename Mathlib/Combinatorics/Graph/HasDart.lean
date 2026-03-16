import Mathlib.Combinatorics.HasDart.Basic
import Mathlib.Combinatorics.Graph.Basic


@[expose] public section

namespace Graph

instance {α β : Type*} : HasDart α (Graph α β) where
  verts G := V(G)
  adj G := G.Adj
  left_mem_verts_of_adj {G : Graph α β} {u v : α} (h : G.Adj u v) := h.left_mem
  right_mem_verts_of_adj {G : Graph α β} {u v : α} (h : G.Adj u v) := h.right_mem
  dart G u v := {e : β | G.IsLink e u v}
  adj_iff_dart_like := nonempty_subtype.symm
