/-
Copyright (c) 2026 Kyle Miller, Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson, Iván Renison
-/
module

public import Mathlib.Combinatorics.HasDart.Dart
public import Mathlib.Data.Multiset.Basic

/-!
# Walks

In a (simple) graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `HasDart.Walk` (with accompanying pattern definitions
  `HasDart.Walk.nil'` and `HasDart.Walk.cons'`)
* `HasDart.Walk.Nil`: A predicate for the empty walk
* `HasDart.Walk.length`: The length of a walk
* `HasDart.Walk.support`: The list of vertices a walk visits in order
* `HasDart.Walk.darts`: The list of darts a walk visits in order
* `HasDart.Walk.edges`: The list of edges a walk visits in order
* `HasDart.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

@[expose] public section

namespace HasDart

universe u'' u'
variable {V : Type*} {Gr : Type*} [HasDart V Gr] (G : Gr) {u v w : V}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `Walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `HasDart.Walk.support`.

See `HasDart.Walk.nil'` and `HasDart.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk {α : Type u'} {Gr : Type*} [HasDart.{u''} α Gr] (G : Gr) :
    α → α → Type (max u' u'')
  | nil {u : α} : Walk G u u
  | cons {u v w : α} (d : dart G u v) (p : Walk G v w) : Walk G u w

/- Manual instances for `DecidableEq` because deriving gives an instance that requires
  `DecidableEq Gr` -/
@[reducible]
instance Walk.instDecidable [DecidableEq V] [∀ u v, DecidableEq (dart G u v)] {u v : V}
    (p q : Walk G u v) : Decidable (p = q) := by
  rcases p with (nil | @⟨u, v₁, w, h₁, p₁⟩)
  <;> rcases q with (nil | @⟨u, v₂, w, h₂, p₂⟩)
  · exact isTrue rfl
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · by_cases hv : v₁ = v₂
    · subst hv
      simp only [cons.injEq, heq_eq_eq, true_and]
      haveI := Walk.instDecidable p₁ p₂
      infer_instance
    · apply isFalse (by simp [hv])

instance Walk.instDecidableEq [DecidableEq V] [∀ u v, DecidableEq (dart G u v)] {u v : V} :
    DecidableEq (Walk G u v) :=
  Walk.instDecidable G

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (v : V) : Inhabited (Walk G v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def dart.toWalk {G : Gr} {u v : V} (h : dart G u v) : Walk G u v :=
  Walk.cons h Walk.nil

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : Walk G u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : dart G u v) (p : Walk G v w) : Walk G u w := Walk.cons h p

theorem exists_eq_cons_of_ne {u v : V} (hne : u ≠ v) :
    ∀ (p : Walk G u v), ∃ (w : V) (h : dart G u w) (p' : Walk G w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : Walk G u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
theorem length_nil {u : V} : (nil : Walk G u u).length = 0 := rfl

@[simp]
theorem length_cons {u v w : V} (h : dart G u v) (p : Walk G v w) :
    (cons h p).length = p.length + 1 := rfl

theorem eq_of_length_eq_zero {u v : V} : ∀ {p : Walk G u v}, p.length = 0 → u = v
  | nil, _ => rfl

def adj_of_length_eq_one {u v : V} : ∀ {p : Walk G u v}, p.length = 1 → dart G u v
  | cons h nil, _ => h

@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : Walk G u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
lemma exists_length_eq_one_iff {u v : V} :
    (∃ (p : Walk G u v), p.length = 1) ↔ Nonempty (dart G u v) := by
  refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun ⟨d⟩ ↦ ⟨d.toWalk, by simp⟩⟩
  induction p with
  | nil => simp at hp
  | cons d p' =>
    simp only [length_cons, Nat.add_eq_right] at hp
    exact ⟨(p'.eq_of_length_eq_zero hp) ▸ d⟩

@[simp]
theorem length_eq_zero_iff {u : V} {p : Walk G u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : Walk G u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : Walk G u v → List (prodDart G)
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

@[simp]
theorem support_nil {u : V} : (nil : Walk G u u).support = [u] := rfl

@[simp, grind =]
theorem support_cons {u v w : V} (h : dart G u v) (p : Walk G v w) :
    (cons h p).support = u :: p.support := rfl

@[simp]
theorem support_ne_nil {u v : V} (p : Walk G u v) : p.support ≠ [] := by cases p <;> simp

@[simp]
theorem head_support {G : Gr} {a b : V} (p : Walk G a b) :
    p.support.head (by simp) = a := by cases p <;> simp

@[simp]
theorem getLast_support {G : Gr} {a b : V} (p : Walk G a b) :
    p.support.getLast (by simp) = b := by
  induction p <;> simp [*]

theorem support_eq_cons {u v : V} (p : Walk G u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : Walk G u v) : u ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : Walk G u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {u v : V} (p : Walk G u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩

theorem mem_support_iff {u v w : V} (p : Walk G u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : Walk G v v).support ↔ u = v := by simp

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : Walk G u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

theorem support_subset_support_cons {u v w : V} (p : Walk G v w) (hadj : dart G u v) :
    p.support ⊆ (p.cons hadj).support := by
  simp

theorem coe_support {u v : V} (p : Walk G u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl

theorem isChain_adj_cons_support {u v w : V} (h : dart G u v) :
    ∀ (p : Walk G v w), List.IsChain (dart G) (u :: p.support)
  | nil => .cons_cons h (.singleton v)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)

theorem isChain_adj_support {u v : V} :
    ∀ (p : Walk G u v), List.IsChain (dart G) p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

theorem isChain_dartAdj_cons_darts {d : prodDart G} {v w : V} (h : d.snd = v) (p : Walk G v w) :
    List.IsChain (prodDartAdj G) (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

theorem isChain_dartAdj_darts {u v : V} : ∀ (p : Walk G u v), List.IsChain (prodDartAdj G) p.darts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_darts (by rfl) p

@[simp]
theorem darts_nil {u : V} : (nil : Walk G u u).darts = [] := rfl

@[simp]
theorem darts_cons {u v w : V} (h : dart G u v) (p : Walk G v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

theorem cons_map_snd_darts {u v : V} (p : Walk G u v) :
    (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp [*]

theorem map_snd_darts {u v : V} (p : Walk G u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

theorem map_fst_darts_append {u v : V} (p : Walk G u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp [*]

theorem map_fst_darts {u v : V} (p : Walk G u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)

@[simp, grind =]
theorem length_support {u v : V} (p : Walk G u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
theorem length_darts {u v : V} (p : Walk G u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem fst_darts_getElem {p : Walk G u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].fst = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_darts]

@[simp]
theorem snd_darts_getElem {p : Walk G u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].snd = p.support.tail[i]'(by grind) := by
  grind [map_snd_darts]

@[simp]
lemma support_getElem_zero (p : Walk G u v) : p.support[0] = u := by cases p <;> simp

@[simp]
lemma support_getElem_length (p : Walk G u v) : p.support[p.length] = v := by
  induction p <;> simp_all

theorem mem_darts_iff_infix_support {u' v'} {p : Walk G u v} (h : (dart G u' v' : Prop)) :
    ⟨(u', v'), h⟩ ∈ p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert p.darts.getElem_mem (n := i) (by grind)
      <;> grind [fst_darts_getElem, snd_darts_getElem]

theorem mem_darts_iff_fst_snd_infix_support {p : Walk.{0} G u v} {d : prodDart G} :
    d ∈ p.darts ↔ [d.fst, d.snd] <:+: p.support :=
  mem_darts_iff_infix_support ..

theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    ∀ (p : Walk G u v) {d : prodDart G}, d ∈ p.darts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl rfl
    · exact .inr (dart_fst_mem_support_of_mem_darts _ hd)

theorem darts_nodup_of_support_nodup {u v : V} {p : Walk G u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩

theorem darts_injective {u v : V} : Function.Injective (Walk.darts : Walk G u v → List (prodDart G))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    simp only [darts_cons, List.cons.injEq, prodDart.mk.injEq, Prod.mk.injEq, true_and] at h
    obtain ⟨⟨rfl, hh⟩, h⟩ := h
    congr
    · simpa using hh
    · exact darts_injective h

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = Walk G.nil` typechecks
only if `p` has defeq endpoints. -/
inductive Nil : {v w : V} → Walk G v w → Prop
  | nil {u : V} : Nil (nil : Walk G u u)

@[simp, grind .] lemma nil_nil : (nil : Walk G u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : dart G u v} {p : Walk G v w} : ¬ (cons h p).Nil := nofun

instance (p : Walk G v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq {p : Walk G v w} : p.Nil → v = w | .nil => rfl

lemma not_nil_of_ne {p : Walk G v w} : v ≠ w → ¬ p.Nil := mt Nil.eq

lemma nil_iff_support_eq {p : Walk G v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp]
lemma darts_eq_nil {p : Walk G v w} : p.darts = [] ↔ p.Nil := by
  cases p <;> simp

lemma nil_iff_length_eq {p : Walk G v w} : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff_lt_length {p : Walk G v w} : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

lemma not_nil_iff {p : Walk G v w} :
    ¬ p.Nil ↔ ∃ (u : V) (h : dart G v u) (q : Walk G u w), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : Walk G v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : Walk G u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : dart G u v) → (q : Walk G v w) → motive (cons h q) not_nil_cons)
    (p : Walk G u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : Walk G u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (h : dart G u v) → (q : Walk G v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : dart G u v) (q' : Walk G v w) :
    @notNilRec _ _ _ _ _ _ _ cons _ _ = cons h' q' := by rfl

theorem end_mem_tail_support {u v : V} {p : Walk G u v} (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart {u v : V} (p : Walk G u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : (prodDart G), d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x y z
    by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨(x, y), a⟩, List.Mem.head _, uS, h⟩

end Walk

end HasDart
