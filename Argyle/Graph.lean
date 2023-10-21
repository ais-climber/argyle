import Argyle.Helpers
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rel
open Classical

-------------------------------------------------
-- Weighted Directed Graphs
-- 
-- Since graphs are internally represented by lists,
-- we can just do induction on this inner list.
-- 
-- It's common for graph theory proofs to go by
-- induction on the graph:  "Suppose P holds for the
-- subgraph, and now add a new node."  In this case
-- what you probably want is to do induction on
-- *Graph.vertices.reverse*, so that each new node
-- can only "see" those nodes that come *before* it.
-- 
-- NOTE: For hygiene, we expect that the vertices
-- are natural numbers given in order, i.e. 0, 1, 2, ...
-- In principle, you can pick any other labels for your 
-- vertices, but I will be relying on the fact that they come
-- in this order.  My apologies.
-- 
-- WARNING: We will also assume that graphs are acyclic.
-- But NOTHING in this file directly enforces that.
-- Whenever I construct a new graph, I will check that
-- it preserves acyclic-ness.  But when making a graph
-- from scratch, kindly refrain from creating cycles.
-------------------------------------------------

structure testGraph (α : Type) (β : Type) where
  vertices : Finset α
  edges : Rel α α
  weights : Rel (α × α) β

/-
-- OLD; refactoring now!
structure Graph (α : Type) (β : Type) where
  vertices : List α
  edges : List (α × α)
  weights : List ((α × α) × β)

  -- Constraints to make sure everything is hygenic.
  edges_from_vertices_left : ∀ {x y : α}, ⟨x, y⟩ ∈ edges → x ∈ vertices
  edges_from_vertices_right : ∀ {x y : α}, ⟨x, y⟩ ∈ edges → y ∈ vertices
  -- weights_from_edges : ∀ {x y : α} {w : β}, 
  --   ⟨⟨x, y⟩, w⟩ ∈ weights → ⟨x, y⟩ ∈ edges
deriving Repr
-/

-- Finite graphs
-- k is the size of the graph;
-- nodes are Fin n, weights are rationals ℚ
-- We assume that the data is hygenic
structure Graph (k : ℕ) where
  vertices : Finset (Fin k)
  Edge : Rel (Fin k) (Fin k)
  Weight : Rel ((Fin k) × (Fin k)) ℚ

  -- Constraints to make sure everything is hygenic.
  edges_from_vertices_left : ∀ {x y}, Edge x y → x ∈ vertices
  edges_from_vertices_right : ∀ {x y}, Edge x y → y ∈ vertices
-- deriving Repr

/-
h₇: ∀ (b : ℚ), ¬((m, n), b) ∈ net.graph.weights
⊢ ¬(m, n) ∈ net.graph.edges
-/

-------------------------------------------------
-- Graph functions
-------------------------------------------------

-- TODO: for convenience, define 'map', 'foldl', 'filter',
-- 'find?', 'zip', 'some', 'any', and 'all' over graph vertices.

-- TODO: Make graph functions computable! (this shouldn't be
-- hard -- right now it just depends on 'Prop')
namespace Graph

-- Function that gets the vertices as a *finite set*
def get_vertices (g : Graph k) : Finset ℕ := g.vertices.toFinset


def hasEdge (g : Graph k) (m n : ℕ) : Bool :=
  match List.lookup m g.edges with
  | some v => if v = n then true else false
  | none => false

-- Function that gets the edges as a *relation*
def hasEdge_Rel (g : Graph ℕ ℚ) : ℕ → ℕ → Prop :=
  fun m n => ⟨m, n⟩ ∈ g.edges

def predecessors (g : Graph ℕ ℚ) (n : ℕ) : List ℕ :=
  List.filter (fun m => g.hasEdge m n) g.vertices

def successors (g : Graph ℕ ℚ) (n : ℕ) : List ℕ :=
  List.filter (fun m => g.hasEdge n m) g.vertices

-- Returns the weight of the edge m ⟶ n, if it exists.
-- Otherwise we return None.
def getEdgeWeight (g : Graph ℕ ℚ) (m n : ℕ) : ℚ :=
  match List.lookup ⟨m, n⟩ g.weights with
  | some weight => weight
  | none => 0

--------------------------------------------------------------------
theorem edge_of_hasEdge (g : Graph ℕ ℚ) (m n : ℕ) :
  g.hasEdge m n → ⟨m, n⟩ ∈ g.edges := by
--------------------------------------------------------------------
  simp only [Graph.hasEdge]
  
  -- Split up the match
  split 
  case _ v h₁ => 
    intro h₂
    have h₃ : v = n := by
      apply byContradiction
      intro hcontr
      rw [if_neg hcontr] at h₂
      exact absurd (symm h₂) (Bool.of_decide_false rfl)

    rw [← h₃]
    exact lookup_mem _ _ _ h₁
    
  case _ _ => 
    intro h₂
    simp at h₂

--------------------------------------------------------------------
theorem hasEdge_iff_edge (g : Graph ℕ ℚ) (m n : ℕ) :
  g.hasEdge m n ↔ ⟨m, n⟩ ∈ g.edges  := by
--------------------------------------------------------------------
  sorry



--------------------------------------------------------------------
theorem hasEdgeRel_of_hasEdge (g : Graph ℕ ℚ) (m n : ℕ) :
  g.hasEdge m n → g.hasEdge_Rel m n := by
--------------------------------------------------------------------
  simp only [hasEdge_Rel]
  exact edge_of_hasEdge g m n

inductive Path (g : Graph ℕ ℚ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      Path g u u
  | from_path {u v w : ℕ} : 
      Path g u v → g.hasEdge v w → Path g u w

--------------------------------------------------------------------
theorem Path_trans {u v w : ℕ} (g : Graph ℕ ℚ) :
  Path g u v → Path g v w → Path g u w := by
--------------------------------------------------------------------
  intro (h₁ : Path g u v)
  intro (h₂ : Path g v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y _ edge_xy path_ux => 
    exact Path.from_path path_ux edge_xy


def is_refl (g : Graph ℕ ℚ) : Prop := ∀ (u : ℕ), 
  u ∈ g.get_vertices → g.hasEdge u u

def is_symm (g : Graph ℕ ℚ) : Prop := ∀ (u v : ℕ), 
  g.hasEdge u v → g.hasEdge v u

def is_trans (g : Graph ℕ ℚ) : Prop := ∀ (u v w : ℕ),
  g.hasEdge u v → g.hasEdge v w → g.hasEdge u w

-- Note that we don't allow reflexive edges at all.
def is_acyclic (g : Graph ℕ ℚ) : Prop := ∀ (u v : ℕ),
  g.Path u v → ¬ g.Path v u

-- Fully connected:
-- Either u ⟶ v, v ⟶ u, or u and v have the same
-- predecessors and successors.
def is_connected (g : Graph ℕ ℚ) : Prop := ∀ (u v : ℕ),
  (g.hasEdge u v) ∨ (g.hasEdge v u) 
  ∨ (g.successors u = g.successors v
      ∧ g.predecessors u = g.predecessors v)

end Graph

/-
TODO for later:  Make 'Path' computable so that we can execute
this code:
> #eval Path graphA 1 3

Some old code when I was trying to do this:

instance decPath : Decidable (Path g u v) :=
  sorry -- this should implement BFS!!!
  -- if h : u = v then
  --   isTrue (Eq.subst h Path.trivial)
  -- else if h : hasEdge g u v then
  --   isTrue (Path.from_path (Path.trivial) h)
  -- else
  --   sorry

instance decLte : Decidable (my_lte m n) :=
  if h : m = n then
    .isTrue (h ▸ .trivial)
  else
    match n with
    | x + 1 =>
      have := @decLte m x
      decidable_of_iff (my_lte m x) ⟨(.from_path · rfl), fun h => by
        cases h with
        | trivial => cases h rfl
        | from_path h e => exact Nat.succ.inj e ▸ h⟩
    | 0 => .isFalse fun h => by
      cases h with
      | trivial => exact h rfl
      | from_path h e => cases e
-/

/-
TODO:  Define 'acyclic' as:  Recursively on graph.vertices,
every vertex can only "see" the vertices ahead of it.

TODO: We want to be able to check if a graph is acyclic by
just "computing" it -- i.e. we call Topological Sort on the
graph, and if successful we know it is acyclic.

So here is some old code I was using to try to do topological
sort.  I'll need to come back to this when I want to make
everything in this library computable.
namespace TopologicalSort

-- @[simp]
-- def topol_sort (g : Graph ℕ ℚ) :=
--   (topSortUnsafe g).toList.reverse

-- holds iff u precedes v in array
-- note that we assume lst elements are all distinct
def list_precedes (lst : List ℕ) (u v : ℕ) : Bool :=
  match lst with
    | List.nil => false
    | List.cons x xs =>
      -- If we find 'u' first, and v is in the rest, true
      if x = u ∧ v ∈ xs then 
        true
      else 
        list_precedes xs u v

def listA : List ℕ :=
  [2, 4, 9, 8, 5]

-- a couple of unit tests for good measure
#eval list_precedes listA 4 8 -- true
#eval list_precedes listA 2 8 -- true
#eval list_precedes listA 2 4 -- true
#eval list_precedes listA 2 9 -- true
#eval list_precedes listA 9 5 -- true

#eval list_precedes listA 8 2 -- should be false, is true
#eval list_precedes listA 5 9 -- should be false, is true

#eval list_precedes listA 1 7 -- undefined (false)
#eval list_precedes listA 9 9 -- false, makes sure an element
                              -- does not precede itself.

-- The ordering induced by Topological Sort
-- TODO: Rewrite as an inductive data type!
/-
def topOrder (g : Graph ℕ β) (u v : ℕ) : Prop :=
  match (topSort g) with
    | some sorted => list_precedes sorted.toList u v
    | none => sorry
-/

-- inductive TopologicalOrdering (g : Graph ℕ β) (u : ℕ) where
--   | constr1 : TopologicalOrdering g u
--   | constr2 (x : ℕ) : TopologicalOrdering g u

-- inductive graph_≺ (g : Graph ℕ β) (u v : ℕ) where
--   | constr1 : sorry
--   | constr2 : sorry

-- Says that Topological Sort is actually correct, i.e.
-- if there is an edge from x to y, then x ≺ y in the ordering.
-- theorem topSort_is_ordered (g : Graph ℕ β) (u v : ℕ) :
--   g.hasEdge u v → topOrder g u v := by

--   intro (h₁ : hasEdge g u v)
--   rw [topOrder]
--   sorry

end TopologicalSort
-/