import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NthRewrite
import Mathlib.Mathport.Syntax
import Std.Tactic.ShowTerm
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Tactic.Basic
import Mathlib.Data.List.Sigma

import Lean.Parser.Tactic
-- import Graph.Graph
-- import Graph.TopologicalSort
import Mathlib.Init.Set
import Mathlib.Data.List.Defs
import Mathlib.Init.Propext
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

-- open Graph
open Set
open Tactic
open Classical

-- Doesn't detect inefficient code!
set_option maxHeartbeats 0

-------------------------------------------------
-- Goofing about with inductive types
-------------------------------------------------

inductive my_lte : ℕ → ℕ → Prop where
  | reflexive : my_lte n n
  | from_succ : my_lte m x → (n = x + 1) → my_lte m n

-- #eval my_lte 1 3





-------------------------------------------------
-- List comprehensions,
-- courtesy of lovettchris
-- See: 
--   https://github.com/leanprover/lean4-samples/blob/main/ListComprehension/ListComprehension.lean
-------------------------------------------------

declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause

syntax "[" term " | " compClause,* "]" : term

def List.map' (xs : List α) (f : α → β) : List β := List.map f xs

macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map' $xs  (λ $x => $t))
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c])

def prod_comprehens (xs : List α) (ys : List β) : List (α × β) := 
  [(x, y) | for x in xs, for y in ys]

#eval [(x, y) | for x in [1, 2], for y in [3, 4]]


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
-- These graphs are based on Peter Kementzey's 
-- implementation, but modified slightly.
-------------------------------------------------

-- α is the type of the nodes
-- β is the type of the weights
structure Vertex (α β : Type) where
  label : α 
  successors : List (ℕ × β)
deriving Repr

instance [Inhabited α] : Inhabited (Vertex α β) := 
  ⟨ { label := default, successors := default } ⟩

structure Graph (α : Type) (β : Type) where
  vertices : List (Vertex α β) := []
deriving Repr

-- Notice that this graph is acyclic, since each predecessor
-- list only refers to nodes above the current node.  This
-- is foreshadowing.
def graphA : Graph ℕ Float :=
  ⟨[⟨0, [⟨1, 0.5⟩, ⟨2, 0.6⟩, ⟨3, 0.7⟩]⟩, 
    ⟨1, [⟨2, 0.8⟩, ⟨3, 0.9⟩]⟩, 
    ⟨2, [⟨3, 1.0⟩, ⟨3, 3.0⟩]⟩, 
    ⟨3, []⟩]⟩

#check graphA
#eval graphA

-------------------------------------------------
-- Graph functions
-------------------------------------------------

-- TODO: for convenience, define 'map', 'foldl', 'filter',
-- 'find?', 'zip', 'some', 'any', and 'all' over graph vertices.

-- TODO: Make graph functions computable! (this shouldn't be
-- hard -- right now it just depends on 'Prop')
namespace Graph

def get_vertices (g : Graph ℕ Float) : List ℕ :=
  g.vertices.map (fun ⟨label, _⟩ => label)

def successors (g : Graph ℕ Float) (n : ℕ) : List ℕ :=
  g.vertices[n]!.successors.unzip.1

def predecessors (g : Graph ℕ Float) (n : ℕ) : List ℕ :=
  List.filter (fun v => n ∈ (g.successors v)) g.get_vertices

-- Using 'predecessors' is slower than 'successors',
-- but we will tend to look backwards from a node rather
-- than forwards.
def hasEdge (g : Graph ℕ Float) (m n : ℕ) : Bool :=
  m ∈ (g.predecessors n)

-- Returns the weight of the edge m ⟶ n, if it exists.
-- If it does not exist, we say the weight is 0.0
-- TODO: In the future, it's better to use Option here
-- and return none if none!!!
def getEdgeWeight (g : Graph ℕ Float) (m n : ℕ) : Float :=
  match g.vertices[m]!.successors.find? (fun ⟨label, _⟩ => label = n) with
  | some ⟨_, weight⟩ => weight
  | none => 0.0

-- Some sanity checks
#eval get_vertices graphA
#eval successors graphA 0
#eval successors graphA 1
#eval successors graphA 2
#eval successors graphA 3
#eval predecessors graphA 0
#eval predecessors graphA 1
#eval predecessors graphA 2
#eval predecessors graphA 3
#eval hasEdge graphA 1 2
#eval hasEdge graphA 1 3
#eval hasEdge graphA 4 2
#eval getEdgeWeight graphA 1 2
#eval getEdgeWeight graphA 1 3
#eval getEdgeWeight graphA 4 2


inductive hasPath (g : Graph ℕ Float) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      hasPath g u u
  | from_path {u v w : ℕ} : 
      hasPath g u v → hasEdge g v w → hasPath g u w

/-
TODO for later:  Make 'hasPath' computable so that we can execute
this code:
> #eval hasPath graphA 1 3

Some old code when I was trying to do this:

instance decPath : Decidable (hasPath g u v) :=
  sorry -- this should implement BFS!!!
  -- if h : u = v then
  --   isTrue (Eq.subst h hasPath.trivial)
  -- else if h : hasEdge g u v then
  --   isTrue (hasPath.from_path (hasPath.trivial) h)
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


--------------------------------------------------------------------
theorem hasPath_trans {u v w : ℕ} (g : Graph ℕ Float) :
  hasPath g u v → hasPath g v w → hasPath g u w := by
--------------------------------------------------------------------
  intro (h₁ : hasPath g u v)
  intro (h₂ : hasPath g v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y _ edge_xy path_ux => 
    exact hasPath.from_path path_ux edge_xy


def is_refl (g : Graph ℕ Float) : Prop := ∀ (u : ℕ), 
  u ∈ g.get_vertices → g.hasEdge u u

def is_symm (g : Graph ℕ Float) : Prop := ∀ (u v : ℕ), 
  g.hasEdge u v → g.hasEdge v u

def is_trans (g : Graph ℕ Float) : Prop := ∀ (u v w : ℕ),
  g.hasEdge u v → g.hasEdge v w → g.hasEdge u w

def is_acyclic (g : Graph ℕ Float) : Prop := ∀ (u v : ℕ),
  g.hasPath u v → g.hasPath v u → u = v

end Graph

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
-- def topol_sort (g : Graph ℕ Float) :=
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

-------------------------------------------------
-- Example:  Our graphA is acyclic
-- (We should just be able to call 'Topological Sort'
-- on the graph and check if that is successful.)
-------------------------------------------------
-- Put in examples file! (and figure it out later, we don't need
-- it right now)
-- 
-- theorem graphA_is_acyclic : graphA.is_acyclic := by
--   intro (u : ℕ) (v : ℕ)
--         (path_uv : hasPath graphA u v)
--         (path_vu : hasPath graphA v u)

--   sorry

-------------------------------------------------
-- Activation functions
-------------------------------------------------
def binary_step (x : Float) : Float :=
  if x > 0.0 then
    1.0
  else
    0.0

/-
TODO: If I want to do this the *right* way, I should define
a type of Real numbers that wrap around Floats.  I can *compute*
things at the Float level, and *prove* things at the Reals level,
but I should refuse to let the user *prove* things at the Float
level. i.e. they cannot prove things by evaluating Floats; this
is where Lean's Floats run into contradictions.
-/
axiom le_refl_float : ∀ (x : Float), x ≤ x
axiom lt_or_ge_float : ∀ (x y : Float), x < y ∨ x ≥ y
axiom le_not_lt_float : ∀ (x y : Float), x ≤ y → ¬ (y < x)
axiom lt_le_lt_float : ∀ (x y z : Float), x < y → y ≤ z → x < z
axiom zero_le_one_float : 0.0 ≤ 1.0

theorem binary_step_is_binary (x : Float) :
    (binary_step x = 0.0) ∨ (binary_step x = 1.0) :=
    by
      -- simp [binary_step]

      cases (lt_or_ge_float 0.0 x) with

      -- Case 1: 0.0 < x
      | inl case1 =>
          have (h : binary_step x = 1.0) :=
            by
              simp only [binary_step]
              rw [(if_pos case1)]
          exact Or.inr h

      -- Case 2: ¬ (0.0 < x)
      | inr case2 =>
          have (h : binary_step x = 0.0) := 
            by 
              simp only [binary_step]
              rw [(if_neg (le_not_lt_float x 0.0 case2))]
          exact Or.inl h

-- Proof that binary_step is nondecreasing
-- This is also a 'hello world' to see if I can
-- reason about a branching program.
theorem binary_step_nondecr (x₁ x₂ : Float) (hyp : x₁ ≤ x₂) :
  (binary_step x₁ ≤ binary_step x₂) := 
  by
    -- Simplify by applying the definition of binary_step.
    simp [binary_step]
    
    cases (lt_or_ge_float 0.0 x₁) with
    | inl case1 =>
      cases (lt_or_ge_float 0.0 x₂) with
      | inl case11 => 
          -- Both sides evaluate to 1.0,
          -- so we just prove that 1.0 ≤ 1.0.
          rw [(if_pos case1)]
          rw [(if_pos case11)]
          exact le_refl_float 1.0
      | inr case12 => 
          -- We have 0.0 < x₁ ≤ x₂ < 0.0,
          -- so this case is absurd. 
          exact absurd
            (lt_le_lt_float 0.0 x₁ x₂ case1 hyp) -- library_search!!! 
            (le_not_lt_float x₂ 0.0 case12)
    | inr case2 => 
      cases (lt_or_ge_float 0.0 x₂) with
      | inl case21 => 
          -- We are in the second and first cases.
          rw [(if_neg (le_not_lt_float x₁ 0.0 case2))]
          rw [(if_pos case21)]
          exact zero_le_one_float
      | inr case22 => 
          rw [(if_neg (le_not_lt_float x₁ 0.0 case2))]
          rw [(if_neg (le_not_lt_float x₂ 0.0 case22))]
          exact le_refl_float 0.0 -- library_search!!!

-------------------------------------------------
-- Feedforward neural nets
-------------------------------------------------
structure Net where
  graph : Graph ℕ Float
  activation : Float → Float
  rate : Float -- learning rate

structure BFNN extends Net where 
  -- The activation function is binary
  binary : ∀ (x : Float), 
    (activation x = 0.0) ∨ (activation x = 1.0)

  -- Our graph is acyclic
  acyclic : graph.is_acyclic

  -- The activation function is nondecreasing
  activ_nondecr : ∀ (x₁ x₂ : Float),
    x₁ ≤ x₂ → activation x₁ ≤ activation x₂

  -- There is *some* x for which the activation is 1.0
  activ_pos : ∃ (x : Float), activation x = 1.0

-- Put in examples file!  (We don't need to figure it out
-- right now!)
-- def myBFNN : BFNN :=
--   {
--     graph := graphA
--     activation := binary_step
--     rate := 1.0

--     binary := binary_step_is_binary
--     -- sort := (topSortUnsafe graphA).toList.reverse
--     acyclic := sorry -- graphA_is_acyclic
--     activ_nondecr := binary_step_nondecr
--     activ_pos := sorry
--   }

-- inductive Layer (net : BFNN) : List ℕ → Prop where
--   | initial_layer : Layer net N₀
--   | next_layer : ∀ (n : ℕ), (n ∈ N → 
--     ∃ (m : ℕ), m ∈ Nᵢ ∧ Layer net Nᵢ) → Layer net N

variable (net : BFNN)

-------------------------------------------------
-- Playing around with Sets
-------------------------------------------------

def setA : Set ℕ :=
  {n | n ≤ 10}

def setB : Set ℕ :=
  {n ∈ setA | n > 5}

def setC : Set ℕ :=
  {n | n ≤ 5}

#check setA

-- Example proof of a subset, just to make
-- sure I can do it.
example : setB ⊆ setA := by
  intro (n : ℕ)
  intro (h : n ∈ setB)

  exact show n ∈ setA from h.left

-- Another example proof of a subset, this
-- time using the RHS of the set comprehension.
example : setC ⊆ setA := by
  intro (n : ℕ)
  intro (h₁ : n ∈ setC)

  have (h₂ : n ≤ 5) := h₁
  have (h₃ : 5 ≤ 10) := (by native_decide)
  exact show n ∈ setA from le_trans h₂ h₃

-- Prove that a set is contained in its powerset
example : ∀ (S : Set α), S ∈ 𝒫 S := by
  intro (S : Set α)
  intro (a : α)
  intro (h : a ∈ S)
  exact h

-- TODO Next: Define graph reachability and propagate
-- Prove that the above BFNN is acyclic, just to make sure
-- we have the right tools for the job.


theorem setExample : 3 ∈ setC := by 
  have (h₁ : 3 ≤ 4) := by native_decide
  constructor
  exact h₁

/-══════════════════════════════════════════════════════════════════
  Forward propagation in a net
══════════════════════════════════════════════════════════════════-/

def weighted_sum (weights : List Float) (lst : List Float) : Float :=
  List.sum [w * x | for w in weights, for x in lst]

#eval weighted_sum [] []
#eval weighted_sum [1.0] [3.0]
#eval weighted_sum [1.0, 2.0, 3.0] [5.0, 5.0, 5.0]

-- Not well-defined behavior (we expect the weights and lst to be of equal size,
-- but this is left implicit.)
#eval weighted_sum [1.0, 2.0] [3.0]

-- WARNING:
-- This is actually FALSE!  For infinite sets, l[i] is not provably
-- in l (as far as I can figure.)
-- TODO: In the future, when making all this computable, I will
-- be using finite sets, and then I can use get instead of get!,
-- and get_mem in the standard library.
axiom get!_mem {α : Type} [Inhabited α] : 
  ∀ (l : List α) i, (l.get! i) ∈ l

@[simp]
def preds (net : BFNN) (n : ℕ): List ℕ :=
  net.graph.predecessors n

--------------------------------------------------------------------
theorem edge_from_preds (net : BFNN) (m n : ℕ) :
  m ∈ preds net n ↔ net.graph.hasEdge m n := by
--------------------------------------------------------------------
  simp only [preds, Graph.hasEdge]
  rw [Bool.decide_iff]


-- (Weightless) *minimal* graph distance from node m to n.  Just count
-- the number of edges, i.e. don't apply weights.
-- (just here in order to define layer -- but if there's
--  a better way, I should use it!)
-- def distance (graph : Graph ℕ Float) (m n : ℕ) : ℕ :=
--   sorry

/-
def my_argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none
-/

-- The layer of n.
-- We get all predecessors of n, and take the predecessor m
-- with the *maximum* layer.  Then layer(n) = layer(m) + 1.
-- If n has no predecessors, then layer(n) = 0.
-- 
-- TODO: Prove terminating if I can!  (What exactly is decreasing
--       here...)
-- def layer (net : BFNN) (n : ℕ) : ℕ :=
--   sorry
-- partial

-- TODO: I can do away with this axiom, and define 'layer'
-- more naturally if I define acyclic graphs recursively
-- in the first place!  Then I can do induction on 'net.graph'!
axiom graph_ascending_order : ∀ (g : Graph ℕ Float) (m n : ℕ), 
  m ∈ g.predecessors n → m < n

-- Accumulator-style helper function for 'layer'
-- Defined recursively on the *reverse* of the vertex list
-- (this means we are looking at vertices backwards -- each
--  vertex can only "see" the vertices preceding it.)
def layer_acc (net : BFNN) (n : ℕ) (ls : List (Vertex ℕ Float)) : ℕ :=
  match ls with -- net.graph.vertices.reverse
  | [] => 0
  | ⟨_, _⟩ :: rest =>
      let layers := List.map (fun x => layer_acc net x rest) (preds net n)
      let max := layers.maximum
      
      match max with
      | some L => L + 1
      | none => 0

def layer (net : BFNN) (n : ℕ) : ℕ :=
  layer_acc net n (net.graph.vertices.reverse)

/- -- Put in test file!
-- 0 jumps to 2, 1 jumps to 3, short connection from 1 to 2
def layer_test_graph : Graph ℕ Float :=
  ⟨[⟨0, [⟨2, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨1, [⟨2, 0.5⟩, ⟨3, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨2, []⟩, -- ⟨4, 0.5⟩
    ⟨3, [⟨4, 0.5⟩]⟩, -- remove ⟨4, 0.5⟩
    
    -- Add a new edge, and toggle which previous edge jumps to it.
    ⟨4, []⟩]⟩

def layer_test_net : BFNN :=
  { graph := layer_test_graph, activation := binary_step, rate := 1.0,
    binary := binary_step_is_binary, acyclic := sorry,
    activ_nondecr := binary_step_nondecr, activ_pos := sorry
  }

#eval layer layer_test_net 0
#eval layer layer_test_net 1
#eval layer layer_test_net 2
#eval layer layer_test_net 3
#eval layer layer_test_net 4
-/

-- AXIOM: We assume the net is fully connected!
-- This is essentially the statement we need, which might
-- follow from being fully connected.
-- TODO: Put this in the definition of BFNN!!!
axiom connected : ∀ (net : BFNN) (m n : ℕ), 
  layer net m < layer net n → net.graph.hasEdge m n

-- If m is a predecessor of n, then it must be in a previous layer.
-- Proof idea:
-- layer(m)  ≤  max({layer(v) | v ∈ preds(n)})  <  layer(n)
--------------------------------------------------------------------
lemma preds_decreasing (net : BFNN) (m n : ℕ) :
  m ∈ preds net n 
  → layer net m < layer net n := by
--------------------------------------------------------------------
  intro h₁
  simp only [layer]

  generalize hls : net.graph.vertices.reverse = ls
  induction ls
  case nil =>
    -- This case is impossible;
    -- m ∈ preds(n) means that there is *something* in the graph.
    -- This contradicts the fact that the graph is empty!
    have h₂ : net.graph.vertices = [] := sorry

    simp [preds, Graph.predecessors, Graph.get_vertices] at h₁
    rw [h₂] at h₁
    rw [List.map_nil] at h₁
    rw [List.filter_nil] at h₁
    exact False.elim ((List.mem_nil_iff _).mp h₁)

  case cons vertex rest IH =>
    generalize hmax : (List.map (fun x => layer_acc net x rest) (preds net n)).maximum = max
    -- generalize hmax_m : (List.map (fun x => layer_acc net x rest) (preds net m)).maximum = max_m
    -- let max := layers.maximum
    
    simp only [layer_acc]
    match max with
    | none =>
        -- This case is also impossible;
        -- m ∈ preds(n) means that there is *some* maximum in preds(n),
        -- which contradicts the fact that the max is empty. 
        rw [hmax]
        conv => rhs; simp

        sorry

    | some L =>
        -- layer(m)  ≤  max({layer(v) | v ∈ preds(n)})  <  layer(n)
        rw [hmax]
        conv => rhs; simp
        sorry
        
        -- I'm not sure how to proceed...
        

noncomputable
def activ (net : BFNN) (prev_activ : List Float) (n : ℕ) : Prop :=
  let preds := preds net n
  let weights := do
    let i <- List.range preds.length
    let m := preds.get! i
    return net.graph.getEdgeWeight m n
  let weight_sum := weighted_sum weights prev_activ
  let curr_activ := net.activation weight_sum
  curr_activ = 1.0


-- FORWARD PROPAGATION IN A NET
-- By recursion on the layers of our feedforward network.
-- (_acc indicates that we are using the layer as an accumulator
--  to do recursion.)
-- 
-- n ∈ propagate_acc(S) iff either:
--   Base Case (L=0): n ∈ S
--   Rcrs Case (L≥0): n ∈ S, or the nodes m preceding n activate n.
--     (We check their activation values via propagate_acc on m)
-- 
-- TODO: Make this computable!!!
-- change return type to 'Bool' instead of 'Prop'
-- and change 'Set' to be a finite set
-- and change net.graph to be finite as well!
-- 
-- Then unit-test all this with #eval!
@[simp]
def propagate_acc (net : BFNN) (S : Set ℕ) (n : ℕ) (L : ℕ) : Prop :=
  match L with
  | Nat.zero => n ∈ S
  | Nat.succ _ =>
    let preds := preds net n
    let prev_activ := do
      let i <- List.range preds.length
      let m := preds.get! i
      return if propagate_acc net S m (layer net m) then 1.0 else 0.0
    n ∈ S ∨ activ net prev_activ n
termination_by propagate_acc net S n L => layer net n
decreasing_by exact preds_decreasing net m n (get!_mem preds i)


-- Set variation of propagate
@[simp]
def propagate (net : BFNN) (S : Set ℕ) : Set ℕ :=
  fun n => propagate_acc net S n (layer net n)

-------------------------------------------------
-- Some helper lemmas
-- (just to clean up the monstrous proofs ahead!)
-- 
-- TODO: Clean these up with nicer @simp lemmas about
-- propagate and activ
-------------------------------------------------

--------------------------------------------------------------------
lemma simp_propagate_acc (net : BFNN) :
  n ∉ S
  → propagate_acc net S n (Nat.succ L) =
  let preds := preds net n
  let prev_activ := do
    let i <- List.range preds.length
    let m := preds.get! i
    return if propagate_acc net S m (layer net m) then 1.0 else 0.0
  activ net prev_activ n := by
--------------------------------------------------------------------
  intro (h₁ : n ∉ S)
  apply Iff.to_eq
  apply Iff.intro

  case mp => 
    intro h₂
    simp only [propagate_acc]
    simp only [propagate_acc] at h₂
    
    cases h₂
    case inl h₃ => contradiction
    case inr h₃ => exact h₃ 
  
  case mpr => 
    intro h₂
    simp only [propagate_acc]
    simp only [propagate_acc] at h₂
    exact Or.inr h₂

-- -- If A and B agree on all the predecessors of n, then they agree on n.
-- -- TODO: We don't seem to need this lemma anymore!
-- lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   (∀ (m : ℕ), m ∈ preds → (m ∈ A ↔ m ∈ B))
--   → activ net A n
--   → activ net B n := by

-- If A and B agree on all the predecessors of n, then they agree on n.
--------------------------------------------------------------------
-- lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   let prev₁ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ A then 1.0 else 0.0
--   let prev₂ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ B then 1.0 else 0.0

--   (∀ (m : ℕ), m ∈ preds → (m ∈ A ↔ m ∈ B))
--   → activ net prev₁ n
--   → activ net prev₂ n := by
-- --------------------------------------------------------------------
--   -- let preds := preds net n
--   intro preds
--   intro prev₁
--   intro prev₂
--   intro (h₁ : ∀ (m : ℕ), m ∈ preds → (m ∈ A ↔ m ∈ B))
--   intro (h₂ : activ net prev₁ n)
  
--   simp only [activ]
--   simp only [activ] at h₂
--   convert ← h₂ using 7

--   rename_i i
--   let m := preds.get! i
--   have h₃ : m ∈ preds := get!_mem preds i
--   exact h₁ m h₃

-- If A and B agree on all the predecessors of n, then they agree on n.
--------------------------------------------------------------------
-- lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
--   (∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
  
--   → (let preds := preds net n
--   let prev_activ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ A then 1.0 else 0.0
--   activ net prev_activ n)
  
--   → (let preds := preds net n
--   let prev_activ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ B then 1.0 else 0.0
--   activ net prev_activ n) := by
-- --------------------------------------------------------------------
--   -- Just go in and subsitute m ∈ A for m ∈ B.
--   intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
--   intro h₂
  
--   simp
--   simp at h₂
--   convert h₂ using 5
--   rename_i i
--   generalize hm : List.get! (predecessors net.graph n).data i = m
--   -- generalize hLm : layer net m = Lm

--   have h₃ : m ∈ preds net n := by
--     rw [symm hm]
--     simp [preds]
--     exact get!_mem (predecessors net.graph n).data i
--   have h₄ : layer net m ≤ layer net n := by
--     apply le_of_lt
--     exact preds_decreasing net m n h₃
--   exact (symm (h₁ m h₄).to_eq).to_iff

-- If A and B agree on all the predecessors of n, 
-- then the corresponding activ's agree on n.
-- lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
--   (∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
  
--   → (activ net
--       (List.bind (List.range (preds net n).length) fun i =>
--         pure (if propagate_acc net 
--               (fun n => propagate_acc net S n (layer net n)) ((preds net n).get! i)
--                     (layer net ((preds net n).get! i)) 
--               then 1.0 else 0.0)) n)
  
--   → (activ net
--       (List.bind (List.range (List.length (preds net n))) fun i =>
--         pure (if propagate_acc net S ((preds net n).get! i)
--               (layer net ((preds net n).get! i)) 
--               then 1.0 else 0.0)) n) := by
-- --------------------------------------------------------------------
--   intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
--   intro h₂

--   convert h₂ using 5
--   rename_i i
--   generalize hm : List.get! (predecessors net.graph n).data i = m
--   sorry
  -- -- Just go in and subsitute m ∈ A for m ∈ B.
  -- intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
  -- intro h₂
  
  -- simp
  -- simp at h₂
  -- convert h₂ using 5
  -- rename_i i
  -- generalize hm : List.get! (predecessors net.graph n).data i = m
  -- -- generalize hLm : layer net m = Lm

  -- have h₃ : m ∈ preds net n := by
  --   rw [symm hm]
  --   simp [preds]
  --   exact get!_mem (predecessors net.graph n).data i
  -- have h₄ : layer net m ≤ layer net n := by
  --   apply le_of_lt
  --   exact preds_decreasing net m n h₃
  -- exact (symm (h₁ m h₄).to_eq).to_iff

/-══════════════════════════════════════════════════════════════════
  Properties of Propagation
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
lemma prop_layer_zero (net : BFNN) : ∀ (S : Set ℕ) (n : ℕ),
  layer net n = 0
  → n ∈ propagate net S
  → n ∈ S := by
--------------------------------------------------------------------
  intro (S : Set ℕ) (n : ℕ)
        (hL : layer net n = 0)
        (h₁ : n ∈ propagate net S)

  simp only [propagate, Membership.mem, Set.Mem] at h₁
  rw [hL] at h₁
  simp only [propagate_acc] at h₁
  exact h₁

--------------------------------------------------------------------
theorem propagate_is_extens : 
  ∀ (S : Set ℕ),
  S ⊆ propagate net S := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
        (n : ℕ) (h₁ : n ∈ S)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L

  -- Base Step
  case zero => 
    simp only [propagate_acc]
    exact h₁
  
  -- Inductive Step
  case succ k _ => 
    simp only [propagate_acc]
    exact Or.inl h₁

-- Corollary: The same statement, but for propagate_acc
-- (this is a helper lemma for the properties that follow.)
-------------------------------------------------
lemma propagate_acc_is_extens :
  ∀ (S : Set ℕ),
  n ∈ S → propagate_acc net S n (layer net n) := by
-------------------------------------------------
  intro (S : Set ℕ)
  intro (h₁ : n ∈ S)
  have h₂ : n ∈ propagate net S := propagate_is_extens _ _ h₁
  simp only [Membership.mem, Set.Mem, propagate] at h₂
  exact h₂
  

--------------------------------------------------------------------
theorem propagate_is_idempotent : 
  ∀ (S : Set ℕ),
  propagate net S = 
    propagate net (propagate net S) := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
  apply ext
  intro (n : ℕ)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By strong induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  -- Base Step
  case hz =>
    simp only [Membership.mem, Set.Mem, propagate_acc]
    conv in (layer net n) => rw [hL]
    simp only [propagate_acc]
    exact ⟨fun x => x, fun x => x⟩
  
  -- Inductive Step
  case hi k IH =>
    apply Iff.intro
    
    -- Forward direction is easy, just apply extensive
    case mp =>
      intro h₁
      rw [symm hL]
      rw [symm hL] at h₁
      exact @propagate_acc_is_extens net _ _ h₁

    -- Backwards direction is trickier
    case mpr => 
      intro h₁
      
      -- By cases; either n ∈ S or n ∉ S
      -- Again; either n ∈ propagate S or n ∉ propagate S 
      by_cases n ∈ S
      case pos => 
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h
      case neg => 
        by_cases propagate_acc net S n (layer net n)
        case pos => 
          rw [symm hL]
          exact h
        case neg =>
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_S
          rw [simp_propagate_acc net n_not_in_S]
          
          have h₂ : ¬n ∈ propagate net S := h
          simp [propagate] at h₂
          rw [simp_propagate_acc net h₂] at h₁
          
          -- -- activ_agrees lemma goes here
          -- TODO: Having lots of trouble with the activ_agrees lemma atm...
          
          simp
          simp at h₁
          convert h₁ using 5
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₄ : Lm ≤ k := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₃
          exact IH Lm h₄ m hLm
          


-- This is essentially Hannes' proof.
--------------------------------------------------------------------
theorem propagate_is_cumulative :
  ∀ (A B : Set ℕ), A ⊆ B
  → B ⊆ propagate net A
  → propagate net A = propagate net B := by
--------------------------------------------------------------------
  intro (A : Set ℕ) (B : Set ℕ)
        (h₁ : A ⊆ B)
        (h₂ : B ⊆ propagate net A)
  apply ext
  intro (n : ℕ)
  simp only [Membership.mem, Set.Mem, propagate]
  simp only [Membership.mem, Set.Mem, propagate] at h₂

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  -- Base Step
  case hz =>
    simp only [propagate_acc]
    apply Iff.intro
    case mp => exact fun h₃ => h₁ h₃
    case mpr =>
      intro h₃
      have h₄ : propagate_acc net A n (layer net n) := h₂ h₃
      conv at h₄ in (layer net n) => rw [hL]
      simp only [propagate_acc] at h₄
      exact h₄

  -- Inductive Step
  case hi k IH => 
    apply Iff.intro

    -- Forward Direction
    case mp => 
      intro h₃

      -- By cases; either n ∈ B or n ∉ B.
      -- Similarly, either n ∈ A or n ∉ A. 
      by_cases n ∈ B
      case pos =>
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg =>
        by_cases n ∈ A
        case pos => 
          rename_i n_not_in_B 
          exact absurd (h₁ h) n_not_in_B
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_B
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_B]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 5
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₄ : Lm ≤ k := by 
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₃
          exact (symm (IH Lm h₄ m hLm).to_eq).to_iff

    -- Backwards Direction (should be very similar)
    case mpr => 
      intro h₃

      -- By cases; either n ∈ A or n ∉ A
      by_cases n ∈ A
      case pos => 
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg => 
        by_cases n ∈ B
        case pos => 
          rename_i n_not_in_A
          rw [symm hL]
          exact h₂ h
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_A
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_A]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 5
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₄ : Lm ≤ k := by 
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₃
          exact IH Lm h₄ m hLm


-- #check propagate myBFNN {n : ℕ | n ≤ 4}
-- #eval propagate myBFNN {n : ℕ | n ≤ 4}
-- need to make sets finite in order to evaluate???
-- 
-- It's important for everything to be evaluatable, since:
-- 1) I will want to verify that a *specific*
--    neural network has certain properties
-- 2) #eval helps me debug errors


/-══════════════════════════════════════════════════════════════════
  Conditional Graph Reachability
══════════════════════════════════════════════════════════════════-/
-- reachable(A, B) is the set of all nodes reachable from B
-- using a path where all nodes are inside A (i.e. there is a 
-- focusedPath from B to n).
-- 
-- This is *precisely* what Van Benthem refers to as "conditional
-- common knowledge" (although here we don't need the word "common"
-- because we don't have group dynamics.)  
-- Quote:
-- CG(A, B) "is true in all worlds reachable via some finite path
-- of accessibilities running entirely through worlds satisfying A"
-- [Van Benthem, Belief Revision and Dynamic Logic, page 6]
-- In this paper, he also talks about "pre-encoding" future
-- information in order to get a reduction, which is exactly
-- what we're doing here!
-- 
-- I don't know what the complete axioms are for this conditional
-- knowledge.  But this isn't the main focus here.  I'll just
-- prove a few sound things to give an idea about what it's like.

-- A focused path is a path where every node is contained
-- within the set S.
inductive focusedPath (g : Graph ℕ Float) (S : Set ℕ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      u ∈ S → focusedPath g S u u
  | from_path {u v w : ℕ} : 
      focusedPath g S u v → g.hasEdge v w → w ∈ S → focusedPath g S u w

-- focusedPath is transitive
theorem focusedPath_trans {u v w : ℕ} (g : Graph ℕ Float) (A : Set ℕ) :
  focusedPath g A u v → focusedPath g A v w → focusedPath g A u w := by

  intro (h₁ : focusedPath g A u v)
  intro (h₂ : focusedPath g A v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y _ edge_xy hy path_ux => 
    exact focusedPath.from_path path_ux edge_xy hy


-- This is the set of all nodes reachable from B using
-- paths where *every* node in the path is within A
-- (including the initial and final nodes)
def reachable (net : BFNN) (A B : Set ℕ) : Set ℕ :=
  fun (n : ℕ) =>
    ∃ (m : ℕ), m ∈ B ∧ focusedPath net.graph A m n

-- Argument: If there is a path from B to n, but n is in
-- layer 0 -- there are *no* incoming nodes -- then the path
-- must be of length 0.  So n must be that n ∈ B with
-- a path to n, i.e. n ∈ B.
--------------------------------------------------------------------
lemma reach_layer_zero (net : BFNN) : ∀ (A B : Set ℕ) (n : ℕ),
  layer net n = 0
  → n ∈ reachable net A B
  → n ∈ B := by
--------------------------------------------------------------------
  intro (A : Set ℕ)
        (B : Set ℕ)
        (n : ℕ) (hL : layer net n = 0)
        (h₁ : n ∈ reachable net A B)
  
  match h₁ with
  | ⟨m, h₂⟩ => 
    -- By induction on the length of the path from B to n.
    --   path length = 0 => m ∈ B means n ∈ B
    --   path length ≥ 0 => this case should be impossible,
    --                      because at layer 0 n has *no predecessors*! 
    induction h₂.2
    case trivial _ => exact h₂.1
    case from_path x y _ edge_xy _ _ =>
      -- Contradiction; y's layer is 0, but there is an edge from x to y!
      -- (layer net x < layer net y, but that means layer net x < 0) 
      have h₃ : layer net x < layer net y :=
        preds_decreasing net x y ((edge_from_preds _ _ _).mpr edge_xy)
      
      exact absurd hL (Nat.not_eq_zero_of_lt h₃)


--------------------------------------------------------------------
theorem reach_subset (net : BFNN) : ∀ (A B : Set ℕ),
  reachable net A B ⊆ A := by
--------------------------------------------------------------------
  intro (A : Set ℕ)
        (B : Set ℕ)
        (n : ℕ) (h₁ : n ∈ reachable net A B)
  
  simp only [Membership.mem, Set.Mem] at h₁
  match h₁ with
  | ⟨m, hm⟩ => 
    induction hm.2
    case trivial hbase => exact hbase
    case from_path _ y _ _ hy _ => exact hy 


-- This is like propag_is_extens, except we also have to ensure
-- that n ∈ A.
--------------------------------------------------------------------
theorem reach_is_extens (net : BFNN) : ∀ (A B : Set ℕ),
  (A ∩ B) ⊆ reachable net A B := by
--------------------------------------------------------------------
  intro (A : Set ℕ)
        (B : Set ℕ)
        (n : ℕ) (h₁ : n ∈ A ∩ B)

  have (h₂ : focusedPath net.graph A n n) := 
    focusedPath.trivial h₁.1
  exact ⟨n, ⟨h₁.2, h₂⟩⟩


--------------------------------------------------------------------
theorem reach_is_idempotent (net : BFNN) : ∀ (A B : Set ℕ),
  reachable net A B = reachable net A (reachable net A B) := by
--------------------------------------------------------------------
  intro (A : Set ℕ)
        (B : Set ℕ)
  
  exact Set.ext (fun (n : ℕ) =>
    -- ⊆ direction; easy, just apply reach_subset and reach_is_extens
    ⟨(fun (h₁ : n ∈ reachable net A B) => 
      have h₂ : n ∈ A := reach_subset _ _ _ h₁
      reach_is_extens _ _ _ ⟨h₂, h₁⟩),

    -- ⊇ direction
    (fun (h₁ : n ∈ reachable net A (reachable net A B)) =>
      match h₁ with
      | ⟨x, h₂⟩ => 
        match h₂.1 with
        | ⟨m, h₃⟩ =>
          ⟨m, ⟨h₃.1, focusedPath_trans _ A h₃.2 h₂.2⟩⟩)⟩)


--------------------------------------------------------------------
theorem reach_is_monotone (net : BFNN) : ∀ (S A B : Set ℕ),
  A ⊆ B → reachable net S A ⊆ reachable net S B := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
        (A : Set ℕ)
        (B : Set ℕ)
        (h₁ : A ⊆ B)
        (n : ℕ) (h₂ : n ∈ reachable net S A)
  
  exact match h₂ with
    | ⟨m, hm⟩ => ⟨m, ⟨h₁ hm.1, hm.2⟩⟩


/-══════════════════════════════════════════════════════════════════
  Reach-Prop Interaction Properties
══════════════════════════════════════════════════════════════════-/

-- --------------------------------------------------------------------
-- theorem propagate_reach_inclusion (net : BFNN) : ∀ (S : Set ℕ),
--   propagate net S ⊆ reachable net S := by
-- --------------------------------------------------------------------
--   sorry

-- --------------------------------------------------------------------
-- lemma minimal_cause_helper (net : BFNN) : ∀ (A B : Set ℕ), ∀ (n : ℕ),
--   n ∈ reachedby net B
--   → (n ∈ propagate net A
--   ↔ n ∈ propagate net (A ∩ reachedby net B)) := by
-- --------------------------------------------------------------------
--   intro (A : Set ℕ) (B : Set ℕ)
--   intro (n : ℕ)
--   intro (h₁ : n ∈ reachedby net B)
--   simp only [Membership.mem, Set.Mem, propagate]

--   -- By induction on the layer of the net containing n
--   generalize hL : layer net n = L
--   induction L using Nat.case_strong_induction_on generalizing n
  
--   -- Base Step
--   case hz => 
--     apply Iff.intro
--     case mp => 
--       intro h₂
--       simp only [propagate_acc]
--       simp only [propagate_acc] at h₂
--       exact ⟨h₂, h₁⟩

--     case mpr => 
--       intro h₂
--       simp only [propagate_acc]
--       simp only [propagate_acc] at h₂
--       exact h₂.1

--   -- Inductive Step
--   case hi k IH => 
--     apply Iff.intro

--     -- Forward Direction
--     case mp => 
--       intro h₂

--       -- By cases; either n ∈ A or not.
--       by_cases n ∈ A
--       case pos => 
--         -- This case is trivial (just apply Extens)
--         rw [symm hL]
--         have h₃ : n ∈ A ∩ reachedby net B := ⟨h, h₁⟩ 
--         exact @propagate_acc_is_extens net _ _ h₃
--       case neg => 
--         -- If n ∉ A, then n ∉ A ∩ reachedby net B
--         have h₃ : n ∉ A ∩ reachedby net B := 
--           fun n_in_A => absurd n_in_A.1 h
        
--         -- Just some simplifications and rewriting definitions
--         rw [simp_propagate_acc net h] at h₂
--         rw [simp_propagate_acc net h₃]

--         -- TODO: This is the stuff that should go in the activ_agree lemma!
--         simp
--         simp at h₂
--         convert h₂ using 5
--         rename_i i
--         generalize hm : List.get! (predecessors net.graph n).data i = m
--         generalize hLm : layer net m = Lm

--         -- Apply the inductive hypothesis!
--         have h₄ : m ∈ preds net n := by
--           rw [symm hm]
--           simp [preds]
--           exact get!_mem (predecessors net.graph n).data i
--         have h₅ : Lm ≤ k := by
--           rw [symm hLm]
--           apply Nat.lt_succ.mp
--           rw [symm hL]
--           exact preds_decreasing net m n h₄
--         have h₆ : m ∈ reachedby net B :=
--           match h₁ with
--           | ⟨x, hx⟩ => ⟨x, ⟨hx.1, hasPath_trans _ (preds_path _ h₄) hx.2⟩⟩
--         exact (symm (IH Lm h₅ m h₆ hLm).to_eq).to_iff

--     -- Backwards Direction (should be similar)
--     case mpr =>
--       intro h₂

--       -- By cases; either n ∈ A or not.
--       by_cases n ∈ A
--       case pos => 
--         -- This case is trivial (just apply Extens)
--         rw [symm hL]
--         exact @propagate_acc_is_extens net _ _ h
--       case neg => 
--         -- If n ∉ A, then n ∉ A ∩ reachedby net B
--         have h₃ : n ∉ A ∩ reachedby net B := 
--           fun n_in_A => absurd n_in_A.1 h
        
--         -- Just some simplifications and rewriting definitions
--         rw [simp_propagate_acc net h₃] at h₂
--         rw [simp_propagate_acc net h]

--         -- TODO: This is the stuff that should go in the activ_agree lemma!
--         simp
--         simp at h₂
--         convert h₂ using 5
--         rename_i i
--         generalize hm : List.get! (predecessors net.graph n).data i = m
--         generalize hLm : layer net m = Lm

--         -- Apply the inductive hypothesis!
--         have h₄ : m ∈ preds net n := by
--           rw [symm hm]
--           simp [preds]
--           exact get!_mem (predecessors net.graph n).data i
--         have h₅ : Lm ≤ k := by
--           rw [symm hLm]
--           apply Nat.lt_succ.mp
--           rw [symm hL]
--           exact preds_decreasing net m n h₄
--         have h₆ : m ∈ reachedby net B :=
--           match h₁ with
--           | ⟨x, hx⟩ => ⟨x, ⟨hx.1, hasPath_trans _ (preds_path _ h₄) hx.2⟩⟩
--         exact IH Lm h₅ m h₆ hLm


-- -- This is the actual property I want, re-written with conditionals
-- -- in mind
-- --------------------------------------------------------------------
-- theorem minimal_cause (net : BFNN) : ∀ (A B : Set ℕ),
--   B ⊆ propagate net A
--   ↔ B ⊆ propagate net (A ∩ reachedby net B) := by
-- --------------------------------------------------------------------
--   intro (A : Set ℕ) (B : Set ℕ)
--   apply Iff.intro
--   case mp => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
--     (reachedby_is_extens _ _ h₂)).mp (h₁ h₂)
--   case mpr => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
--     (reachedby_is_extens _ _ h₂)).mpr (h₁ h₂)

/-══════════════════════════════════════════════════════════════════
  Update Policy: "Make neurons fire together"
  (without regard for the edges of the net)
══════════════════════════════════════════════════════════════════-/

/-
*Notes*
The basic idea is that we take a subset A of the graph, and
increase our preference for nodes in A as much as possible.
We do this by: 1) completing the graph A, and 2) maximizing all
of the edges within this completed graph.  The overall effect
is that for all neurons m, n ∈ A, m fires exactly when n fires.

But this operation results in a graph with cycles -- so [A] Prop(B)
is not well-defined!  But we can do something equivalent:
Take all the nodes in A, and quotient them.  This results in a
net where all the nodes m, n ∈ A "fire as one".

So we need:
  [Def] Define 'complete_and_max' update
  [Def] Define 'fire_together' update (the quotient structure)
  [Thm] Prove that the two updates are equivalent.
        (We can't use Prop for this -- maybe I can prove
         that the 'activ' for both nets agrees?)
  [Thm] Find a reduction for 'fire_together' and prove it.
        (It should look like the dual of Lexicographic Upgrade)
  [Cor] 'fire_together' is the dual of Lexicographic Upgrade
    [Depends] 
      Preference Models
      Lexicographic Upgrade
      Lexicographic Upgrade reduction
      Model translation from pref models ⟷ nets
-/

-- def complete_and_max (net : BFNN) (A : Set ℕ) : BFNN :=
--   sorry

-- def fire_together (net : BFNN) (A : Set ℕ) : BFNN :=
-- { net with
--   graph := sorry
--   activation := sorry
--   rate := sorry

--   -- binary := sorry
--   binary := sorry
--   acyclic := sorry
--   activ_nondecr := sorry
--   activ_pos := sorry
-- }



/-══════════════════════════════════════════════════════════════════
  Naive (Unstable) Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- A function to map edges in the graph.  
-- We update the edge weight x₁ ⟶ x₂, but we also allow information 
-- about the *nodes* x₁ and x₂.
-- Credit to Peter Kementzey for the original mapEdges function.
def map_edges (g : Graph ℕ Float) (f : ℕ → ℕ → Float → Float) : Graph ℕ Float := ⟨
  g.vertices.map (fun vertex => 
    { vertex with successors := vertex.successors.map (fun 
      ⟨target, weight⟩ => ⟨target, f vertex.label target weight⟩
  )})
⟩

-- For every m ⟶ n where m, n ∈ Prop(S), increase the weight
-- of that edge by η * act(m) * act(n).
noncomputable
def graph_update (net : BFNN) (g : Graph ℕ Float) (S : Set ℕ) : Graph ℕ Float :=
  map_edges g (fun m n weight => 
    let activ_m := if m ∈ propagate net S then 1.0 else 0.0
    let activ_n := if n ∈ propagate net S then 1.0 else 0.0
    weight + (net.rate * activ_m * activ_n))

-- This graph update does not affect the vertices of the graph.
--------------------------------------------------------------------
lemma graph_update_vertices (net : BFNN) (g : Graph ℕ Float) (S : Set ℕ) :
  (graph_update net net.graph S).get_vertices = net.graph.get_vertices := by
--------------------------------------------------------------------
  simp only [graph_update, map_edges]
  simp only [Graph.get_vertices]

  -- Go in and compose the maps.  This seems to do the trick.
  conv => lhs; rw [List.map_map]


-- This graph update does not affect the *successor/edge* structure
-- of the graph (it only affects weights!!!)
--------------------------------------------------------------------
lemma graph_update_successors (net : BFNN) (g : Graph ℕ Float) (S : Set ℕ) (n : ℕ) :
  (graph_update net net.graph S).successors n = net.graph.successors n := by
--------------------------------------------------------------------
  simp only [graph_update, map_edges] -- map_edges
  simp only [Graph.successors]

  -- Go in and rewrite the 'unzip' as a 'map'
  rw [List.unzip_eq_map]
  rw [List.unzip_eq_map]
  simp only [Prod.fst]

  -- Now go in and compose the maps.
  -- conv => lhs; rw [List.map_map]
  sorry -- Why the FUCK won't this rewrite work???


-- A single step of Hebbian update.
-- Propagate S through the net, and then increase the weights
-- of all the edges x₁ ⟶ x₂ involved in that propagation
-- by η * x₁ * x₂.
noncomputable
def hebb (net : BFNN) (S : Set ℕ) : BFNN :=
{ net with
  graph := graph_update net net.graph S

  -- We have to ensure that the update doesn't create any cycles
  -- (In this case, we're only changing the weights.)
  acyclic := sorry
}


-- Takes a graph update function 'f' (e.g. graph_update for Hebb)
-- and iterates it 'no_times' times.
-- netᵢ and Sᵢ are the initial inputs.
def iterate (f : Graph ℕ Float → Set ℕ → Graph ℕ Float) 
  (no_times : ℕ) (gᵢ : Graph ℕ Float) (Sᵢ : Set ℕ) : Graph ℕ Float :=
  match no_times with
  | Nat.zero => gᵢ
  | Nat.succ k => f (iterate f k gᵢ Sᵢ) Sᵢ


-- We score neurons by the total sum of *negative* weights coming 
-- into them.  The neuron with the lowest score is the least likely
-- to activate (in the worst case where all of its negative signals
-- activate but none of its positive ones do).  If a neuron has
-- no negative incoming weights, we give it a score of 0.
def neg_weight_score (net : BFNN) (n : ℕ) : Float :=
  sorry


-- This is the exact number of iterations of Hebbian learning
-- on 'net' and 'S' that we need to make the network unstable,
-- i.e. any activation involved within Prop(S) simply goes through.
-- 
-- This is the trickiest part to get right -- we actually need
-- to *construct* this number, based on the net's activation
-- function and the edge weights within Prop(S)!
-- 
-- We first pick the neuron with the lowest 'neg_weight_score' n_min.
-- The number of iterations is that number which would (in the worst
-- case) guarantee that n_min gets activated.
-- 
-- If n_score is n_min's score, and X is that point at which
-- our activation function is guranteed to be 1.0, and η is the
-- learning rate, then we return
-- 
-- (X - n_score) / η   *(I think!)*
def hebb_unstable_point (net : BFNN) (S : Set ℕ) : ℕ :=
  sorry
  -- let x := choose net.activ_pos
  -- have h₁ : net.activation x = 1.0 := sorry

  -- let n_min := @List.minimum (Vertex ℕ Float) sorry sorry net.graph.vertices.toList
  -- let n_score := sorry
  -- sorry

-- Iterated hebbian update, up to a certain fixed point.
-- We implement this as a new net, whose graph is
-- 'graph_update' iterated 'hebb_unstable_point'
-- number of times.
-- FUTURE: Consider re-doing this using limits of graphs/categories
noncomputable
def hebb_star (net : BFNN) (S : Set ℕ) : BFNN := 
{ net with
  graph := iterate (graph_update net) (hebb_unstable_point net S) net.graph S
  
  -- We have to ensure that the update doesn't create any cycles
  -- (In this case, we're only changing the weights.)
  acyclic := sorry
}



/-══════════════════════════════════════════════════════════════════
  Properties of Unstable Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- A net net₁ is a subnet of net₂ (net₁ ≼ net₂) iff for all
-- sets S, every node activated in the propagation of S
-- in net₁ is activated in the propagation of S in net₂.
-- (They both have the same *propagation structure*)
def subnet (net₁ net₂ : BFNN) : Prop :=
  ∀ (S : Set ℕ), propagate net₁ S ⊆ propagate net₂ S

infixl:65   " ≼ " => subnet


-- Two nets are equivalent if they have the same 
-- *propagation structure* (i.e. if their propagations agree 
-- for every set S)
def net_eq (net₁ net₂ : BFNN) : Prop :=
  net₁ ≼ net₂ ∧ net₂ ≼ net₁

infixl:65   " ≡ " => net_eq


-- A super easy example, just to briefly test ≼ and ≡
example : example_net ≡ example_net :=
  ⟨fun S n h => h, fun S n h => h⟩  


-- propagate_N (S) = propagate_hebb(N, S) (S)
-- This essentially says that repeated hebbian update
-- is well-defined; *after* updating on S, we can update
-- on S again and increase weights within the same propagation.
-- (The propagation of S doesn't suddenly change, which is
--  something we might be worried about.)
-- TODO: Not sure if I need this anymore!
-- It's somewhat interesting, but might not help with the
-- reduction.
-- --------------------------------------------------------------------
-- theorem hebb_iteration_is_well_defined (net : BFNN) (S : Set ℕ) : 
--   propagate (hebb net S) S = propagate net S := by
-- --------------------------------------------------------------------
--   apply ext
--   intro (n : ℕ)
--   simp only [Membership.mem, Set.Mem, propagate]

--   -- By induction on the layer of the net containing n
--   generalize hL : layer net n = L
--   induction L using Nat.case_strong_induction_on generalizing n

--   -- Base Step
--   case hz =>
--     apply Iff.intro
--     case mp => 
--       simp only [propagate_acc]
--       exact fun x => x
--     case mpr => 
--       simp only [propagate_acc]
--       exact fun x => x

--   -- Inductive Step
--   case hi k IH => 
--     apply Iff.intro

--     -- Forward Direction
--     case mp => 
--       intro h₁
--       simp only [propagate_acc] at h₁
--       simp only [propagate_acc]

--       cases h₁
--       case inl h₂ => exact Or.inl h₂
--       case inr h₂ =>
--         apply Or.inr

--         -- TODO: This is the stuff that should go in the activ_agree lemma!        
--         simp
--         simp at h₂
--         sorry
--         -- I do not have the tools to show this at this point.
--         -- I need a lemma about activations in the hebbian updated net.

--         -- show_term convert h₂

--     -- Backwards Direction
--     case mpr => sorry

-- This says that 'hebb_star' is a fixed point of 'hebb'
-- (with respect to ≡).  i.e. in the following sense, f(X) = X:
--   hebb(X, S) ≡ X,
-- where X = hebb_star net S
-- 
-- I may need additional lemmas (e.g. an activation function
-- within Prop(S) in hebb_star will simply go through.)
-- 
-- One important lemma:  If an edge is not in the propagation of S,
-- its weight is unaffected.
--------------------------------------------------------------------
theorem hebb_star_is_fixed_point (net : BFNN) (S : Set ℕ) : 
  hebb (hebb_star net S) S ≡ hebb_star net S := by 
--------------------------------------------------------------------
  sorry

/-══════════════════════════════════════════════════════════════════
  Properties of Single-Iteration Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- A single round of Hebbian update does not affect the predecessors
-- of any node.  To prove this, we just show that Hebbian update
-- does not affect the vertices of the graph, or the successor
-- structure of the graph.
--------------------------------------------------------------------
theorem hebb_once_preds (net : BFNN) (S : Set ℕ) (n : ℕ) : 
  preds (hebb net S) n = preds net n := by
--------------------------------------------------------------------
  simp only [preds, hebb]
  simp only [Graph.predecessors]
  congr 1

  -- graph_update doesn't affect successors of a node
  case _ => 
    funext v
    congr 2
    exact graph_update_successors _ (net.graph) _ v

  -- graph_update doesn't affect vertices of the graph
  case _ => exact graph_update_vertices _ (net.graph) _

  
-- A single round of Hebbian update hebb does not affect which 
-- neurons are on which layer of the net.
-- TODO: Try induction on the graph, the way I usually prove
-- things about the layers???
--------------------------------------------------------------------
theorem hebb_once_layers (net : BFNN) (S : Set ℕ) : 
  layer (hebb net S) n = layer net n := by
--------------------------------------------------------------------
  sorry

-- A single round of Hebbian update hebb does not affect the 
-- activation function.
--------------------------------------------------------------------
theorem hebb_once_activation (net : BFNN) (S : Set ℕ) : 
  (hebb net S).activation = net.activation := by 
--------------------------------------------------------------------
  exact rfl

-- A single round of Hebbian update hebb does not affect graph 
-- reachability (It only affects the edge weights)
--------------------------------------------------------------------
theorem hebb_once_reach (net : BFNN) (A B : Set ℕ) : 
  reachable (hebb net A) A B = reachable net A B := by 
--------------------------------------------------------------------
  apply ext
  intro (n : ℕ)
  -- simp only [reachable]
  
  apply Iff.intro
  case mp => 
    intro h₁
    exact match h₁ with
    | ⟨m, hm⟩ => by -- ⟨m, ⟨hm.1, _⟩⟩ 
      induction hm.2
      case trivial => exact ⟨m, ⟨hm.1, sorry⟩⟩  
      case from_path x y path_mx edge_xy hy IH =>
        -- Drop the path and edge from (hebb net) to the original net.
        -- Wait -- where do we apply the IH???
        -- have h₂ : focusedPath (hebb net A).toNet.graph A m x := sorry -- use path_mx
        -- have h₃ : Graph.hasEdge net.graph x y = true := sorry -- use edge_xy
        
        have h₂ : x ∈ reachable net A B := sorry -- Apply IH!
        have h₃ : Graph.hasEdge net.graph x y = true := sorry
        exact ⟨m, ⟨hm.1, (focusedPath.from_path sorry h₃ hy)⟩⟩ 
  case mpr => sorry


-- This lemma allows us to "lift" equational properties of hebb 
-- to hebb_star.  (This holds *because* hebb_star is the fixed point
-- of hebb.)
--------------------------------------------------------------------
theorem hebb_lift (net : BFNN) (S : Set ℕ) (P : BFNN → α) : 
  (P (hebb net S) = P net)
  → (P (hebb_star net S) = P net) := by 
--------------------------------------------------------------------
  sorry


/-══════════════════════════════════════════════════════════════════
  Properties of "Iterated" Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- Hebbian update hebb_star does not affect the predecessors
-- of any node.
-- [LIFTED from hebb_once_preds]
--------------------------------------------------------------------
theorem hebb_preds (net : BFNN) (S : Set ℕ) : 
  preds (hebb_star net S) n = preds net n := by
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => preds x n) (hebb_once_preds _ _ _)
  
-- Hebbian update hebb_star does not affect which neurons are
-- on which layer of the net.
-- [LIFTED from hebb_once_layers]
--------------------------------------------------------------------
theorem hebb_layers (net : BFNN) (S : Set ℕ) : 
  layer (hebb_star net S) n = layer net n := by
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => layer x n) (hebb_once_layers _ _)


-- Hebbian update hebb_star does not affect the activation function.
-- [LIFTED from hebb_once_activation]
--------------------------------------------------------------------
theorem hebb_activation (net : BFNN) (S : Set ℕ) : 
  (hebb_star net S).activation = net.activation := by 
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => x.activation) (hebb_once_activation _ _)


-- Hebbian update hebb_star does not affect graph reachability
-- (It only affects the edge weights)
-- -- [LIFTED from hebb_once_reach]
--------------------------------------------------------------------
theorem hebb_reach (net : BFNN) (A B : Set ℕ) : 
  reachable (hebb_star net A) A B = 
    reachable net A B := by 
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => reachable x A B) (hebb_once_reach _ _ _)
  
-- Every net N is a subnet of (hebb_star N)
-- (i.e. hebb_star includes the previous propagations)
-- (We had this property in The Logic of Hebbian Learning)
-- TODO: Can we lift this from single-iteration hebb???
--------------------------------------------------------------------
theorem hebb_extensive (net : BFNN) (A : Set ℕ) : 
  net ≼ (hebb_star net A) := by 
--------------------------------------------------------------------
  intro (B : Set ℕ)
  intro (n : ℕ)
  intro (h₁ : n ∈ propagate net B)
  simp only [Membership.mem, Set.Mem, propagate]
  simp only [Membership.mem, Set.Mem, propagate] at h₁
  
  -- By induction on the layer of the 
  generalize hL : layer net n = L
  induction L

  --------------------------------
  -- Base Step
  --------------------------------
  case zero => 
    rw [hebb_layers]
    rw [hL] at h₁
    rw [hL]
    simp only [propagate_acc]
    simp only [propagate_acc] at h₁
    exact h₁

  --------------------------------
  -- Inductive Step
  --------------------------------
  case succ k IH => 
    -- By cases, to later simplify propagate_acc
    by_cases n ∈ B
    case pos => 
      rw [hebb_layers]
      rw [← hebb_layers net A]
      exact propagate_acc_is_extens _ _ h  
    
    case neg => 
      -- Do simplifications and rewriting
      rw [hebb_layers]
      rw [hL]
      rw [hL] at h₁
      rw [simp_propagate_acc _ h]
      rw [simp_propagate_acc _ h] at h₁

      sorry -- need to argue here that 'activ' is *nondecreasing*
            -- i.e. never decreases a weight.


--------------------------------------------------------------------
lemma hebb_acc_is_extens (net : BFNN) (A B : Set ℕ) (n : ℕ) :
  propagate_acc net B n (layer net n) → 
  propagate_acc (hebb_star net A) B n (layer net n) := by
-------------------------------------------------------------------- 
  intro h₁
  have h₂ : n ∈ propagate (hebb_star net A) B := hebb_extensive _ _ _ h₁
  simp only [Membership.mem, Set.Mem, propagate] at h₂
  rw [hebb_layers] at h₂
  exact h₂



/-══════════════════════════════════════════════════════════════════
  The more interesting/crucial properties
══════════════════════════════════════════════════════════════════-/

-- If n ∉ Prop(A), then the weights in the updated net are the same
-- as the weights in the original net.
-- IDEA: Lift this from single-iteration hebb!
-- Then just go into the definition of hebb.
--------------------------------------------------------------------
theorem hebb_weights₁ (net : BFNN) : 
  n ∉ propagate net A
  → ∀ (i : ℕ),
    ((hebb_star net A).toNet.graph.getEdgeWeight ((preds net n).get! i) n =
    net.graph.getEdgeWeight ((preds net n).get! i) n) := by
--------------------------------------------------------------------
  intro h₁
  intro i
  apply hebb_lift _ _ (fun x => x.toNet.graph.getEdgeWeight ((preds net n).get! i) n)
  simp only [hebb, graph_update]

  sorry


-- If all predecessors of n ∉ Prop(A), then the weights in the 
-- updated net are the same as the weights in the original net.
-- TODO: Can we lift this from single-iteration hebb?
--------------------------------------------------------------------
theorem hebb_weights₂ (net : BFNN) : 
  (∀ x, x ∈ preds net n → x ∉ propagate net A)
  → ∀ (i : ℕ),
    ((hebb_star net A).toNet.graph.getEdgeWeight ((preds net n).get! i) n =
    net.graph.getEdgeWeight ((preds net n).get! i) n) := by
--------------------------------------------------------------------
  intro h₁
  intro i
  apply hebb_lift _ _ (fun x => x.toNet.graph.getEdgeWeight ((preds net n).get! i) n)
  sorry


-- If n ∉ Prop(A), then activ (hebb_star net A) _ n = activ net _ n.
--------------------------------------------------------------------
theorem hebb_activ₁ (net : BFNN) (A : Set ℕ) (prev_activ : List Float) :
  n ∉ propagate net A
  → activ (hebb_star net A) prev_activ n = activ net prev_activ n := by
--------------------------------------------------------------------
  intro h₁
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  conv =>
    lhs; enter [1, 2, 1, 2, i, 1]
    rw [hebb_weights₁ _ h₁]


-- If every predecessor of n ∉ Prop(A), then
-- activ (hebb_star net A) _ n = activ net _ n.
--------------------------------------------------------------------
theorem hebb_activ₂ (net : BFNN) (A : Set ℕ) (prev_activ : List Float) :
  (∀ x, x ∈ preds net n → x ∉ propagate net A)
  → activ (hebb_star net A) prev_activ n = activ net prev_activ n := by
--------------------------------------------------------------------
  intro h₁
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  conv =>
    lhs; enter [1, 2, 1, 2, i, 1]
    rw [hebb_weights₂ _ h₁]


-- -- If *some* predecessor of n is ∈ Prop(A), and n ∈ Prop(A), then
-- -- if m is activated in (hebb_star net) then n is too
-- -- (the activation automatically goes through in (hebb_star net))
-- --------------------------------------------------------------------
-- theorem hebb_activ₃ (net : BFNN) :
--   n ∈ propagate net A
--   → m ∈ preds net n ∧ m ∈ propagate net A
--   → m ∈ propagate (hebb_star net A) B
--   → activ (hebb_star net A) prev_activ m := by
-- --------------------------------------------------------------------
--   sorry



-- If there is a path within Prop(A) from B to n, then, since this
-- path is updated in hebb_star, n ∈ Prop(B).
--------------------------------------------------------------------
theorem hebb_updated_path (net : BFNN) (A B : Set ℕ) :
  reachable net (propagate net A) (propagate net B)
  ⊆ propagate (hebb_star net A) B := by
--------------------------------------------------------------------
  intro (n : ℕ)
  intro h₁
  
  -- We have a path from Prop(B) to n, going through Prop(A).
  match h₁ with
  | ⟨m, hm⟩ => 

    -- By induction on the length of this path
    induction hm.2
    case trivial path_mm => exact hebb_extensive _ _ _ hm.1
    case from_path v w path_mv edge_vw w_in_propA IH => 
      -- This edge from v to w is key;
      -- Got to go inside hebb_star to see what it's updating.
      sorry


/-══════════════════════════════════════════════════════════════════
  Reduction for Unstable Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- These two are the big theorems.
-- They explain what hebb_star learns in terms of what the net
-- believed *before* update -- it turns out that we can completely
-- reduce the dynamic behavior to the static behavior.
--------------------------------------------------------------------
theorem hebb_reduction_empty (net : BFNN) (A B : Set ℕ) : 
  propagate net A ∩ propagate net B = ∅ →

  propagate (hebb_star net A) B = propagate net B := by 
--------------------------------------------------------------------
  intro h_empty
  apply ext
  intro (n : ℕ)

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  -- Easy; after simplifying, show that B = B.
  case hz =>
    simp only [Membership.mem, Set.Mem, propagate]
    rw [hebb_layers net A]
    rw [hL]
    simp only [propagate_acc]

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    -- Backwards direction is easy;
    -- As for forward direction, TODO
    apply Iff.intro
    case mpr => exact fun h₁ => hebb_extensive _ _ _ h₁
    case mp =>
      -- Split by whether n ∈ B, in order to simplify propagate_acc
      by_cases n ∈ B
      case pos => exact fun h₁ => propagate_is_extens _ _ h
      case neg => 
        intro h₁

        -- From here, we split *again*, depending on whether n ∈ Prop(A).
        by_cases n ∈ propagate net A

        ---------------------
        -- Case 1: n ∈ Prop(A)
        ---------------------
        case pos => sorry

        ---------------------
        -- Case 1: n ∉ Prop(A)
        ---------------------
        case neg => sorry


  -- -- Backwards direction is easy;
  -- -- As for forward direction, TODO
  -- apply Iff.intro
  -- case mpr => exact fun h₁ => hebb_extensive _ _ _ h₁
  -- case mp => 
  --   intro h₁
  --   sorry -- need to do induction!!!  (still easier than the big reduction)


--------------------------------------------------------------------
theorem hebb_reduction_nonempty (net : BFNN) (A B : Set ℕ) : 
  propagate net A ∩ propagate net B ≠ ∅ →

  propagate (hebb_star net A) B =
  propagate net (B ∪ reachable net (propagate net A) (propagate net B)) := by 
--------------------------------------------------------------------
  intro h_nonempty
  apply ext
  intro (n : ℕ)
  simp only [Membership.mem, Set.Mem, propagate]
  
  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  case hz => 
    -- First, do the base case simplifications
    rw [hebb_layers]
    rw [hL]
    simp only [propagate_acc]
    simp only [Union.union, Set.union, Membership.mem, Set.Mem, setOf]

    -- Forward direction is the easy part, so we do it first.
    -- Backwards direction relies on reach_layer_zero,
    -- a fact about paths when we know n is at layer 0.
    apply Iff.intro
    case mp => exact fun h₁ => Or.inl h₁
    case mpr => 
      intro h₁

      -- Either n ∈ B or n is reachable from Prop(B) using only
      -- paths within Prop(A).  At layer 0, this means n ∈ B.
      cases h₁
      case inl h₂ => exact h₂
      case inr h₂ => 
        have heq : layer net n = 0 := 
          Eq.trans (symm (hebb_layers net A)) (Eq.trans (hebb_layers _ _) hL)
        exact prop_layer_zero _ _ _ heq (reach_layer_zero _ _ _ _ heq h₂)

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    apply Iff.intro
    
    ---------------------
    -- Backward Direction
    ---------------------
    case mpr =>
      intro h₁
      
      -- By cases; either n ∈ B ∪ Reach(Prop(A), Prop(B)), or not.
      by_cases n ∈ B ∪ reachable net (propagate net A) (propagate net B)
      case pos =>
        -- From here, we split again; either:
        --    1. n ∈ B, and by extens n ∈ Prop(B) in (hebb_star net)
        --    2. n ∈ Reach(Prop(A), Prop(B)).  In this case, this path
        --       has been updated in the (hebb_star net), so of course
        --       n ∈ Prop(B) in (hebb_star_net)
        --       i.e. apply [hebb_updated_path]! 
        cases h
        case inl h₂ => exact propagate_acc_is_extens _ _ h₂
        case inr h₂ =>
          have h₃ : n ∈ propagate (hebb_star net A) B := 
            hebb_updated_path _ _ _ h₂
          simp only [propagate, Membership.mem, Set.Mem] at h₃
          exact h₃

      case neg h₂ =>
        -- From here, we split *again*, depending on whether n ∈ Prop(A).
        by_cases n ∈ propagate net A 

        ---------------------
        -- Case 1: n ∈ Prop(A)
        ---------------------
        case pos => 
          -- Since Prop(A) ∩ Prop(B) is nonempty, there is an m
          -- in the intersection.
          have h₃ : ∃ m, m ∈ propagate net A ∧ m ∈ propagate net B :=
            Set.inter_nonempty_iff_exists_left.mp
              (Set.nonempty_iff_ne_empty.mpr h_nonempty)

          match h₃ with
          | ⟨m, hm⟩ => 
            -- Moreover, we can assume this m is the *smallest* such
            -- m ∈ Prop(A)!  (Via the well-ordering principle)
            have h₄ : ∀ x, x ∈ propagate net A →
              layer net m ≤ layer net x := by
              sorry
            
            cases eq_or_lt_of_le (h₄ n h)
            
            ---------------------
            -- Case 1.1: n ∈ Prop(A)
            -- and layer[m] < layer[n]
            ---------------------
            -- In this case, since the net is transitively closed
            -- (fully connected), we have an edge from m ∈ Prop(A) ∩ Prop(B)
            -- to n ∈ Prop(A).  This gives us n ∈ Reach(Prop(A), Prop(B)).
            case inr h₅ =>
              -- We just provide the path from m⟶n.
              have h₆ : n ∈ reachable net (propagate net A) (propagate net B) := by
                exact ⟨m, ⟨hm.2, 
                  focusedPath.from_path (focusedPath.trivial hm.1) 
                    (connected _ m n h₅) h⟩⟩

              -- In this case, we conclude that n ∈ Prop(B) in
              -- the updated net by 'hebb_updated_path'
              have h₇ : n ∈ propagate (hebb_star net A) B := by
                exact hebb_updated_path _ _ _ h₆
              
              simp only [propagate, Membership.mem, Set.Mem] at h₇
              exact h₇

            ---------------------
            -- Case 1.2: n ∈ Prop(A)
            -- and layer[m] = layer[n]
            ---------------------
            -- In this case, the activ's are the same, so
            -- we can straightforwardly apply our inductive
            -- hypothesis.
            case inl h₅ =>
              -- First, we show that any predecessor of n
              -- cannot be in Prop(A).
              have h₆ : ∀ x, x ∈ preds net n → x ∉ propagate net A := by
                rw [h₅] at h₄
                exact fun x hx x_in_propA => 
                  absurd (h₄ x x_in_propA) (not_le.mpr (preds_decreasing _ _ _ hx))

              -- We get ready to simplify propagate_acc
              rename_i n_not_in_reach
              have n_not_in_B : n ∉ B :=
                fun n_in_B => absurd (Set.mem_union_left _ n_in_B) n_not_in_reach

              -- Simplifications and rewriting, to prepare for IH
              -- We also rewrite the 'preds', 'layers', and 'activ'
              -- for (hebb_star net) in terms of the original 'net'.
              rw [hebb_layers]
              rw [hL]
              simp only [propagate] at n_not_in_reach
              rw [simp_propagate_acc _ n_not_in_B]
              rw [simp_propagate_acc _ n_not_in_reach] at h₁
              
              -- TODO: Use hebb_activ₂, which says that if all
              -- of the preds ∉ Prop(A), the activ's are the same.
              rw [hebb_activ₂ _ _ _ h₆] -- rewrite 'activ'
              rw [hebb_preds net A] -- rewrite 'preds'
              conv => -- rewrite 'layers'
                enter [2, 2, i, m, 1]
                rw [hebb_layers net A]
              simp
              simp at h₁
              convert h₁ using 5
              rename_i i
              generalize hm : List.get! (net.graph.predecessors n) i = m
              generalize hLm : layer net m = Lm
              conv at IH => -- rewrite 'layers' in IH
                enter [L, hL, m, hLm, 1]
                rw [hebb_layers]
                rw [hLm]
              
              -- We are now ready to apply our inductive hypothesis!
              have h₇ : m ∈ preds net n := by
                rw [symm hm]
                simp [preds]
                exact get!_mem (net.graph.predecessors n) i
              have h₈ : Lm ≤ L := by
                rw [symm hLm]
                apply Nat.lt_succ.mp
                rw [symm hL]
                exact preds_decreasing net m n h₇
              exact IH Lm h₈ m hLm

        ---------------------
        -- Case 2: n ∉ Prop(A)
        ---------------------
        -- In this case, the activ's are the same, so we can
        -- straightforwardly apply our inductive hypothesis.
        case neg =>
          -- We get ready to simplify propagate_acc
          rename_i n_not_in_reach
          have n_not_in_B : n ∉ B :=
            fun n_in_B => absurd (Set.mem_union_left _ n_in_B) n_not_in_reach

          -- Simplifications and rewriting, to prepare for IH
          -- We also rewrite the 'preds', 'layers', and 'activ'
          -- for (hebb_star net) in terms of the original 'net'.
          rw [hebb_layers]
          rw [hL]
          simp only [propagate] at n_not_in_reach
          rw [simp_propagate_acc _ n_not_in_B]
          rw [simp_propagate_acc _ n_not_in_reach] at h₁
          
          rw [hebb_activ₁ _ _ _ h] -- rewrite 'activ'
          rw [hebb_preds net A] -- rewrite 'preds'
          conv => -- rewrite 'layers'
            enter [2, 2, i, m, 1]
            rw [hebb_layers net A]
          simp
          simp at h₁
          convert h₁ using 5
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm
          conv at IH => -- rewrite 'layers' in IH
            enter [L, hL, m, hLm, 1]
            rw [hebb_layers]
            rw [hLm]
          
          -- We are now ready to apply our inductive hypothesis!
          have h₂ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₃ : Lm ≤ L := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₂
          exact IH Lm h₃ m hLm

    ---------------------
    -- Forward Direction
    -- (similar, but differs slightly in Case 1)
    ---------------------
    -- This direction is a bit more tricky. This
    -- is where we rely on the net being fully
    -- connected & transitively closed.
    case mp => 
      intro h₁
      
      -- By cases; either n ∈ B ∪ reachable net (propagate net A) B, 
      -- or not.
      by_cases n ∈ B ∪ reachable net (propagate net A) (propagate net B)
      case pos => 
        -- In this case, just apply propagate_is_extens
        rw [← hL]
        simp only [propagate] at h
        exact propagate_acc_is_extens _ _ h

      case neg h₂ => 
        -- From here, we split *again*, depending on whether n ∈ Prop(A).
        by_cases n ∈ propagate net A

        ---------------------
        -- Case 1: n ∈ Prop(A)
        ---------------------
        case pos => 
          -- Since Prop(A) ∩ Prop(B) is nonempty, there is an m
          -- in the intersection.
          have h₃ : ∃ m, m ∈ propagate net A ∧ m ∈ propagate net B :=
            Set.inter_nonempty_iff_exists_left.mp
              (Set.nonempty_iff_ne_empty.mpr h_nonempty)
          
          match h₃ with
          | ⟨m, hm⟩ => 
            -- Moreover, this m is the *smallest* such m ∈ Prop(A)
            have h₄ : ∀ x, x ∈ propagate net A →
              layer net m ≤ layer net x := by
              sorry
            
            cases eq_or_lt_of_le (h₄ n h)
            
            ---------------------
            -- Case 1.1: n ∈ Prop(A)
            -- and layer[m] < layer[n]
            ---------------------
            -- In this case, since the net is transitively closed
            -- (fully connected), we have an edge from m ∈ Prop(A) ∩ Prop(B)
            -- to n ∈ Prop(A).  This gives us n ∈ Reach(Prop(A), Prop(B)).
            case inr h₅ =>
              -- Since the net is fully connected, there is an edge m⟶n.
              -- So we just provide the path from m⟶n.
              have h₆ : n ∈ reachable net (propagate net A) (propagate net B) := by
                exact ⟨m, ⟨hm.2, 
                  focusedPath.from_path (focusedPath.trivial hm.1) 
                    (connected _ m n h₅) h⟩⟩

              -- Since n ∈ Reach(...),
              -- We conclude that n ∈ Prop(B ∪ Reach(...))
              simp only [propagate] at h₆
              rw [← hL]
              exact propagate_acc_is_extens net _ 
                (Set.mem_union_right _ h₆)

            ---------------------
            -- Case 1.2: n ∈ Prop(A)
            -- and layer[m] = layer[n]
            ---------------------
            -- In this case, the activ's are the same, so
            -- we can straightforwardly apply our inductive
            -- hypothesis.
            case inl h₅ => 
              -- First, we show that any predecessor of n
              -- cannot be in Prop(A).
              have h₆ : ∀ x, x ∈ preds net n → x ∉ propagate net A := by
                rw [h₅] at h₄
                exact fun x hx x_in_propA => 
                  absurd (h₄ x x_in_propA) (not_le.mpr (preds_decreasing _ _ _ hx))

              -- We get ready to simplify propagate_acc
              rename_i n_not_in_reach
              have n_not_in_B : n ∉ B :=
                fun n_in_B => absurd (Set.mem_union_left _ n_in_B) n_not_in_reach

              -- Simplifications and rewriting, to prepare for IH
              -- We also rewrite the 'preds', 'layers', and 'activ'
              -- for (hebb_star net) in terms of the original 'net'.
              rw [hebb_layers] at h₁
              rw [hL] at h₁
              simp only [propagate] at n_not_in_reach
              rw [simp_propagate_acc _ n_not_in_B] at h₁
              rw [simp_propagate_acc _ n_not_in_reach]
              
              -- TODO: Use hebb_activ₂, which says that if all
              -- of the preds ∉ Prop(A), the activ's are the same.
              rw [hebb_activ₂ _ _ _ h₆] at h₁ -- rewrite 'activ'
              rw [hebb_preds net A] at h₁ -- rewrite 'preds'
              conv at h₁ => -- rewrite 'layers'
                enter [2, 2, i, m, 1]
                rw [hebb_layers net A]
              simp
              simp at h₁
              convert h₁ using 5
              rename_i i
              generalize hm : List.get! (net.graph.predecessors n) i = m
              generalize hLm : layer net m = Lm
              conv at IH => -- rewrite 'layers' in IH
                enter [L, hL, m, hLm, 1]
                rw [hebb_layers]
                rw [hLm]
              
              -- We are now ready to apply our inductive hypothesis!
              have h₇ : m ∈ preds net n := by
                rw [symm hm]
                simp [preds]
                exact get!_mem (net.graph.predecessors n) i
              have h₈ : Lm ≤ L := by
                rw [symm hLm]
                apply Nat.lt_succ.mp
                rw [symm hL]
                exact preds_decreasing net m n h₇
              exact (symm (IH Lm h₈ m hLm).to_eq).to_iff
        
        ---------------------
        -- Case 2: n ∉ Prop(A)
        ---------------------
        -- In this case, the activ's are the same, so we can
        -- straightforwardly apply our inductive hypothesis.

        case neg =>
          -- We get ready to simplify propagate_acc
          rename_i n_not_in_reach
          have n_not_in_B : n ∉ B :=
            fun n_in_B => absurd (Set.mem_union_left _ n_in_B) n_not_in_reach

          -- Simplifications and rewriting, to prepare for IH
          -- We also rewrite the 'preds', 'layers', and 'activ'
          -- for (hebb_star net) in terms of the original 'net'.
          rw [hebb_layers] at h₁
          rw [hL] at h₁
          simp only [propagate] at n_not_in_reach
          rw [simp_propagate_acc _ n_not_in_B] at h₁
          rw [simp_propagate_acc _ n_not_in_reach]
          
          rw [hebb_activ₁ _ _ _ h] at h₁ -- rewrite 'activ'
          rw [hebb_preds net A] at h₁ -- rewrite 'preds'
          conv at h₁ => -- rewrite 'layers'
            enter [2, 2, i, m, 1]
            rw [hebb_layers net A]
          simp
          simp at h₁
          convert h₁ using 5
          rename_i i
          generalize hm : List.get! (net.graph.predecessors n) i = m
          generalize hLm : layer net m = Lm
          conv at IH => -- rewrite 'layers' in IH
            enter [L, hL, m, hLm, 1]
            rw [hebb_layers]
            rw [hLm]

          -- We are now ready to apply our inductive hypothesis!
          have h₂ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (net.graph.predecessors n) i
          have h₃ : Lm ≤ L := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₂
          exact (symm (IH Lm h₃ m hLm).to_eq).to_iff
        

-- TODO: Prove that we can unravel these nets into ordinary
-- feedforward nets
-- 
-- TODO: Email David Sprunger about follow-up papers to
-- "backprop as a functor"

/-══════════════════════════════════════════════════════════════════
  The Logic (Language and Semantics)
══════════════════════════════════════════════════════════════════-/



/-══════════════════════════════════════════════════════════════════
  Inference Rules and Proof System
══════════════════════════════════════════════════════════════════-/




/-══════════════════════════════════════════════════════════════════
  Soundness
══════════════════════════════════════════════════════════════════-/



