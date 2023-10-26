import Argyle.Helpers
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Logic.Embedding.Basic
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

-- TODO: Make a computable/evaluatable interface.
--     But this isn't important right now!
-- deriving Repr

structure Graph (Node : Type) where
  Edge : Rel Node Node
  Weight : Node → Node → ℚ

  -- Whatever our nodes are, we need them to be provably
  -- finite and inhabited (nonempty)
  nodes : Fintype Node
  instance node_inhabited : Inhabited Node := sorry


instance edge_is_decidable₁ {g : Graph Node} {n : Node} :
  DecidablePred (g.Edge n) := sorry

instance edge_is_decidable₂ {g : Graph Node} {n : Node} :
  DecidablePred (fun m => g.Edge m n) := sorry

-- axiom edge_is_decidable {Node : Type} {g : Graph Node} {n : Node} :
--   DecidablePred fun m => g.Edge m n

-------------------------------------------------
-- Graph functions
-------------------------------------------------

-- TODO: Make graph functions computable!
namespace Graph

noncomputable
def predecessors (g : Graph Node) (n : Node) : Finset Node :=
  Finset.filter (fun m => g.Edge m n) g.nodes.elems

noncomputable
def successors (g : Graph Node) (n : Node) : Finset Node :=
  Finset.filter (fun m => g.Edge m n) g.nodes.elems

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
-- def topol_sort (g : Graph k) :=
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
