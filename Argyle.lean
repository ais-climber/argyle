import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NthRewrite
import Mathlib.Mathport.Syntax

import Lean.Parser.Tactic
import Graph.Graph
import Graph.TopologicalSort
import Mathlib.Init.Set
import Mathlib.Data.List.Defs
import Mathlib.Init.Propext
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

open Graph
open Set
open Tactic
open Classical

-- set_option maxHeartbeats 2000000

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
-- Graphs
-------------------------------------------------
-- This is a graph with ℕ nodes
-- and Float edge weights.
def graphA : Graph ℕ Float :=
  ⟨#[
    ⟨0, #[⟨1, 0.5⟩, ⟨2, 0.6⟩, ⟨3, 0.7⟩]⟩, 
    ⟨1, #[⟨2, 0.8⟩, ⟨3, 0.9⟩]⟩, 
    ⟨2, #[⟨3, 1.0⟩, ⟨3, 5.0⟩]⟩, 
    ⟨3, #[]⟩
  ]⟩

#check graphA
#eval graphA
#eval graphA.edgeCount   -- evals to 7
#eval graphA.order       -- evals to 4
#eval graphA.toArray     -- evals to #[0, 1, 2, 3]

#eval graphA.inDegree 1      -- evals to 1
#eval graphA.outDegree 1     -- evals to 2
#eval graphA.successors 1    -- evals to #[2, 3]
#eval graphA.predecessors 1  -- evals to #[0]

#eval graphA.inDegree 2      -- evals to 2
#eval graphA.outDegree 2     -- evals to 2
#eval graphA.successors 2    -- evals to #[3, 3]
#eval graphA.predecessors 2  -- evals to #[0, 1]

-------------------------------------------------
-- My own graph functions and convenience
-- properties
-------------------------------------------------
namespace Graph
variable {α : Type} [Inhabited α] {β : Type}

def hasNode (g : Graph α β) (v : ℕ) : Bool :=
  g.getAllVertexIDs.contains v

def hasEdge (g : Graph α β) (u v : ℕ) : Bool :=
  (g.successors u).contains v

#eval hasEdge graphA 1 2
#eval hasEdge graphA 1 3
#eval hasEdge graphA 4 2

def getEdgeWeight (g : Graph α β) (u v : ℕ) : β :=
  sorry

inductive hasPath (g : Graph ℕ β) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      hasPath g u u
  | from_path {u v w : ℕ} : 
      hasPath g u v → hasEdge g v w → hasPath g u w

instance decPath : Decidable (hasPath g u v) :=
  sorry -- this should implement BFS!!!
  -- if h : u = v then
  --   isTrue (Eq.subst h hasPath.trivial)
  -- else if h : hasEdge g u v then
  --   isTrue (hasPath.from_path (hasPath.trivial) h)
  -- else
  --   sorry

/-
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


  -- deriving DecidableEq
  -- TODO: Make graph computable so that we can execute this code:
  -- #eval hasPath graphA 1 3

theorem hasPath_trans {u v w : ℕ} (g : Graph ℕ β) :
  hasPath g u v → hasPath g v w → hasPath g u w := by

  intro (h₁ : hasPath g u v)
  intro (h₂ : hasPath g v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y path_vx edge_xy path_ux => 
    exact hasPath.from_path path_ux edge_xy


def is_refl (g : Graph α β) : Prop :=
  ∀ (u : ℕ),
    g.hasNode u → g.hasEdge u u

def is_symm (g : Graph α β) : Prop :=
  ∀ (u v : ℕ),
    g.hasEdge u v → g.hasEdge v u

def is_trans (g : Graph α β) : Prop :=
  ∀ (u v w : ℕ),
    g.hasEdge u v → g.hasEdge v w → g.hasEdge u w

def is_acyclic (g : Graph ℕ β) : Prop :=
  ∀ (u v : ℕ),
    g.hasPath u v → g.hasPath v u → u = v

end Graph

namespace TopologicalSort

-- match net.graph with
--   | _ => true if ... false ow
--   | _ => true if ... false ow

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

-------------------------------------------------
-- Example:  Our graphA is acyclic
-------------------------------------------------
theorem graphA_is_acyclic : graphA.is_acyclic := by
  intro (u : ℕ) (v : ℕ)
        (path_uv : hasPath graphA u v)
        (path_vu : hasPath graphA v u)

  sorry

  -- TODO: Is there a way to just do cases on the specific
  -- elements of 'graphA'?  Probably if I restrict it to 'Fin'...

  -- induction path_uv
  -- case trivial => rfl
  -- case from_path x₁ y₁ path_ux₁ edge_x₁y₁ IH₁ => 
    
  --   induction path_vu
  --   case trivial => rfl
  --   case from_path x₂ y₂ path_y₁x₂ edge_x₂y₂ IH₂ => 
  --     sorry

-- exact have (path_xu : hasPath graphA x u) := sorry

-------------------------------------------------
-- Activation functions
-------------------------------------------------
def binary_step (x : Float) : Float :=
  if x > 0.0 then
    1.0
  else
    0.0

axiom le_refl_float : ∀ (x : Float), x ≤ x
axiom lt_or_ge_float : ∀ (x y : Float), x < y ∨ x ≥ y
axiom le_not_lt_float : ∀ (x y : Float), x ≤ y → ¬ (y < x)
axiom lt_le_lt_float : ∀ (x y z : Float), x < y → y ≤ z → x < z
axiom zero_le_one : 0.0 ≤ 1.0

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
          exact zero_le_one
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

def myBFNN : BFNN :=
  {
    graph := graphA
    activation := binary_step

    binary := binary_step_is_binary
    -- sort := (topSortUnsafe graphA).toList.reverse
    acyclic := graphA_is_acyclic
    activ_nondecr := binary_step_nondecr
    activ_pos := sorry
  }

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
  (predecessors net.toNet.graph n).toList

-- inductive hasPath (g : Graph ℕ β) : ℕ → ℕ → Prop where
--   | trivial {u : ℕ} :
--       hasPath g u u
--   | from_path {u v w : ℕ} : 
--       hasPath g u v → hasEdge g v w → hasPath g u w

-- -- OLD ACTIV FUNCTION
-- noncomputable
-- def activ (S : Set ℕ) (n : ℕ) : Bool :=
--   let preds := preds net n
--   -- We use 'do' to do a list comprehension.
--   -- Notice that we're collecting the *indices*.  This gives
--   -- us more information later;
--   -- to prove m ∈ preds, we can instead prove preds[i] ∈ preds.
--   let prev_activ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ S then 1.0 else 0.0
--   let weights := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return net.graph.getEdgeWeight m n
--   let weight_sum := weighted_sum weights prev_activ
--   let curr_activ := net.activation weight_sum
--   if curr_activ = 1.0 then 
--     true
--   else false

-- -- We need another lemma about 'activ'...!

-- -- If S₁ and S₂ agree on all the predecessors of n, then they agree on n.
-- -- TODO: We don't seem to need this lemma anymore!
-- lemma activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   (∀ (m : ℕ), m ∈ preds → (m ∈ S₁ ↔ m ∈ S₂))
--   → activ net S₁ n
--   → activ net S₂ n := by

--   intro preds
--         (h₁ : ∀ (m : ℕ), m ∈ preds → (m ∈ S₁ ↔ m ∈ S₂))
--         (h₂ : activ net S₁ n)

--   -- The two are definitionally equal; just go in and
--   -- substitute all of the preceding m's 
--   simp only [activ]
--   simp only [activ] at h₂
--   convert ← h₂ using 7
  
--   rename_i i
--   let m := preds.get! i
--   have h₃ : m ∈ preds := get!_mem preds i
--   congr 2
--   apply Iff.to_eq
--   exact h₁ m h₃


-- OLD PROPAGATION
-- For a single node, propagateₚ holds iff that node is n ∈ S. 
-- Otherwise, check if we are looking at n.  If so,
-- propagateₚ holds iff either:
--   1. n ∈ S, or
--   2. The nodes m preceding n activate n.
--      (We check their activation values via propagateₚ on m)
-- If we aren't looking at n, just continue recursively.
-- 
-- This is recursion on the topological ordering of the graph!!!
-- (We can only do this because the graph is acyclic, but
--  that fact is implicit if we use topSortUnsafe.)
-- 
-- TODO: Make this computable!!!
-- change return type to 'Bool' instead of 'Prop'
-- and change 'Set' to be a finite set
-- and change net.graph to be finite as well!
-- 
-- Then unit-test all this with #eval!

-- Can I make this into an inductive type, and then do
-- induction over it?  (That gives me an IH; match does not.)

-- Note that Set ℕ is just defined as ℕ → Prop!
-- This simplifies our definitions.
-- @[simp]
-- def propagate (net : BFNN) (S : Set ℕ) (sort : List ℕ) : Set ℕ :=
--   fun (n : ℕ) =>
--     match sort with
--     | [] => n ∈ S
--     | x :: xs => 
--       if x = n then
--         n ∈ S ∨ activ net {m | m ∈ propagate net S xs} n
--       else
--         n ∈ propagate net S xs

-- (Weightless) graph distance from node m to n.  Just count
-- the number of edges, i.e. don't apply weights.
def distance (graph : Graph ℕ Float) (m n : ℕ) : ℕ :=
  sorry

def layer (net : BFNN) (n : ℕ) : ℕ :=
  sorry

-- If m is a predecessor of n, then there is a path
-- from m to n.
lemma preds_path (net : BFNN) :
  m ∈ preds net n
  → hasPath net.graph m n := by
  sorry

-- If m is a predecessor of n, then it must be in a previous layer.
lemma preds_decreasing (net : BFNN) (m n : ℕ) :
  m ∈ preds net n 
  → layer net m < layer net n := by
  sorry

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

-- Accumulator variation of propagate
-- (We accumulate the layer of the net that n is in)
@[simp]
def propagate_acc (net : BFNN) (S : Set ℕ) (n : ℕ) (L : ℕ) : Prop :=
  match L with
  | Nat.zero => n ∈ S
  | Nat.succ k =>
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

-- @[simp]
-- def topol_sort (g : Graph ℕ Float) :=
--   (topSortUnsafe g).toList.reverse

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


-- -- If S₁ and S₂ agree on all the predecessors of n, then they agree on n.
-- -- TODO: We don't seem to need this lemma anymore!
-- lemma activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   (∀ (m : ℕ), m ∈ preds → (m ∈ S₁ ↔ m ∈ S₂))
--   → activ net S₁ n
--   → activ net S₂ n := by

-- If S₁ and S₂ agree on all the predecessors of n, then they agree on n.
--------------------------------------------------------------------
-- lemma activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   let prev₁ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ S₁ then 1.0 else 0.0
--   let prev₂ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ S₂ then 1.0 else 0.0

--   (∀ (m : ℕ), m ∈ preds → (m ∈ S₁ ↔ m ∈ S₂))
--   → activ net prev₁ n
--   → activ net prev₂ n := by
-- --------------------------------------------------------------------
--   -- let preds := preds net n
--   intro preds
--   intro prev₁
--   intro prev₂
--   intro (h₁ : ∀ (m : ℕ), m ∈ preds → (m ∈ S₁ ↔ m ∈ S₂))
--   intro (h₂ : activ net prev₁ n)
  
--   simp only [activ]
--   simp only [activ] at h₂
--   convert ← h₂ using 7

--   rename_i i
--   let m := preds.get! i
--   have h₃ : m ∈ preds := get!_mem preds i
--   exact h₁ m h₃

-- If S₁ and S₂ agree on all the predecessors of n, then they agree on n.
--------------------------------------------------------------------
-- lemma activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
--   (∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ S₁ ↔ m ∈ S₂))
  
--   → (let preds := preds net n
--   let prev_activ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ S₁ then 1.0 else 0.0
--   activ net prev_activ n)
  
--   → (let preds := preds net n
--   let prev_activ := do
--     let i <- List.range preds.length
--     let m := preds.get! i
--     return if m ∈ S₂ then 1.0 else 0.0
--   activ net prev_activ n) := by
-- --------------------------------------------------------------------
--   -- Just go in and subsitute m ∈ S₁ for m ∈ S₂.
--   intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ S₁ ↔ m ∈ S₂))
--   intro h₂
  
--   simp
--   simp at h₂
--   convert h₂ using 5
--   rename_i i
--   generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
--   -- generalize hLm : layer net m = Lm

--   have h₃ : m ∈ preds net n := by
--     rw [symm hm]
--     simp [preds]
--     exact get!_mem (predecessors net.toNet.graph n).data i
--   have h₄ : layer net m ≤ layer net n := by
--     apply le_of_lt
--     exact preds_decreasing net m n h₃
--   exact (symm (h₁ m h₄).to_eq).to_iff

-- If S₁ and S₂ agree on all the predecessors of n, 
-- then the corresponding activ's agree on n.
-- lemma activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
--   (∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ S₁ ↔ m ∈ S₂))
  
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
--   intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ S₁ ↔ m ∈ S₂))
--   intro h₂

--   convert h₂ using 5
--   rename_i i
--   generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
--   sorry
  -- -- Just go in and subsitute m ∈ S₁ for m ∈ S₂.
  -- intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ S₁ ↔ m ∈ S₂))
  -- intro h₂
  
  -- simp
  -- simp at h₂
  -- convert h₂ using 5
  -- rename_i i
  -- generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
  -- -- generalize hLm : layer net m = Lm

  -- have h₃ : m ∈ preds net n := by
  --   rw [symm hm]
  --   simp [preds]
  --   exact get!_mem (predecessors net.toNet.graph n).data i
  -- have h₄ : layer net m ≤ layer net n := by
  --   apply le_of_lt
  --   exact preds_decreasing net m n h₃
  -- exact (symm (h₁ m h₄).to_eq).to_iff

/-══════════════════════════════════════════════════════════════════
  Properties of Propagation
══════════════════════════════════════════════════════════════════-/

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
  case succ k IH => 
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
          simp
          simp at h₁

          -- -- Apply the inductive hypothesis!
          -- have h₃ : ∀ (m : ℕ), layer net m ≤ layer net n → 
          --   ((fun n => propagate_acc net S n (layer net n)) m ↔ S m) := by
          --   sorry
          -- exact activ_agree net _ _ n h₃ h₁

          
          -- TODO: Having lots of trouble with the activ_agrees lemma atm...
          simp
          simp at h₁
          convert h₁ using 5
          rename_i i
          generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (predecessors net.toNet.graph n).data i
          have h₄ : Lm ≤ k := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₃
          exact IH Lm h₄ m hLm


-- This is essentially Hannes' proof.
--------------------------------------------------------------------
theorem propagate_is_cumulative :
  ∀ (S₁ S₂ : Set ℕ), S₁ ⊆ S₂
  → S₂ ⊆ propagate net S₁
  → propagate net S₁ = propagate net S₂ := by
--------------------------------------------------------------------
  intro (S₁ : Set ℕ) (S₂ : Set ℕ)
        (h₁ : S₁ ⊆ S₂)
        (h₂ : S₂ ⊆ propagate net S₁)
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
      have h₄ : propagate_acc net S₁ n (layer net n) := h₂ h₃
      conv at h₄ in (layer net n) => rw [hL]
      simp only [propagate_acc] at h₄
      exact h₄

  -- Inductive Step
  case hi k IH => 
    apply Iff.intro

    -- Forward Direction
    case mp => 
      intro h₃

      -- By cases; either n ∈ S₂ or n ∉ S₂.
      -- Similarly, either n ∈ S₁ or n ∉ S₁. 
      by_cases n ∈ S₂
      case pos =>
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg =>
        by_cases n ∈ S₁
        case pos => 
          rename_i n_not_in_S₂ 
          exact absurd (h₁ h) n_not_in_S₂
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_S₂
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_S₂]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 5
          rename_i i
          generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (predecessors net.toNet.graph n).data i
          have h₄ : Lm ≤ k := by 
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n h₃
          exact (symm (IH Lm h₄ m hLm).to_eq).to_iff

    -- Backwards Direction (should be very similar)
    case mpr => 
      intro h₃

      -- By cases; either n ∈ S₁ or n ∉ S₁
      by_cases n ∈ S₁
      case pos => 
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h -- TODO: replace acc variation
      case neg => 
        by_cases n ∈ S₂
        case pos => 
          rename_i n_not_in_S₁
          rw [symm hL]
          exact h₂ h
        case neg => 
          -- Just some simplifications and rewriting definitions
          rename_i n_not_in_S₁
          rw [simp_propagate_acc net h] at h₃
          rw [simp_propagate_acc net n_not_in_S₁]

          -- Just try to prove it and turn it into an 'activ_agree'
          -- lemma later!
          -- Go into 'prev_activ' and substitute using our IH.
          -- Then try to prove what's left.
          simp
          simp at h₃
          convert h₃ using 5
          rename_i i
          generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
          generalize hLm : layer net m = Lm

          -- Apply the inductive hypothesis!
          have h₃ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (predecessors net.toNet.graph n).data i
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
  Properties of Graph-reachability
══════════════════════════════════════════════════════════════════-/

/-
-- NOTE: I think we only need *reverse* graph-reachability,
-- and adding in graph-reachability only makes things complicated
-- in the logic.

def reachable (net : BFNN) (S : Set ℕ) : Set ℕ :=
  fun (n : ℕ) =>
    ∃ (m : ℕ), (m ∈ S ∧ net.graph.hasPath m n)

--------------------------------------------------------------------
theorem reach_is_extens (net : BFNN) : ∀ (S : Set ℕ),
  S ⊆ reachable net S := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
        (n : ℕ) (h₁ : n ∈ S)

  have (h₂ : hasPath net.toNet.graph n n) := hasPath.trivial
  exact ⟨n, ⟨h₁, h₂⟩⟩
  
--------------------------------------------------------------------
theorem reach_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
  reachable net S = reachable net (reachable net S) := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
  
  exact Set.ext (fun (n : ℕ) =>
    -- ⊆ direction (the easy direction; just apply 'extensive')
    ⟨(fun (h₁ : n ∈ reachable net S) => 
      let S_reach := reachable net S
      reach_is_extens net S_reach h₁),

    -- ⊇ direction
    (fun (h₁ : n ∈ reachable net (reachable net S)) =>
      match h₁ with
      | ⟨x, h₂⟩ => 
        match h₂.1 with
        | ⟨m, h₃⟩ =>
          have (h₄ : hasPath net.graph m n) := 
            hasPath_trans net.graph h₃.2 h₂.2
          ⟨m, ⟨h₃.1, h₄⟩⟩)⟩)

--------------------------------------------------------------------
theorem reach_is_monotone (net : BFNN) : ∀ (S₁ S₂ : Set ℕ),
  S₁ ⊆ S₂ → reachable net S₁ ⊆ reachable net S₂ := by
--------------------------------------------------------------------
  intro (S₁ : Set ℕ) (S₂ : Set ℕ)
        (h₁ : S₁ ⊆ S₂)
        (n : ℕ) (h₂ : n ∈ reachable net S₁)

  exact match h₂ with
    | ⟨m, h₃⟩ => ⟨m, ⟨h₁ h₃.1, h₃.2⟩⟩ 
-/

/-══════════════════════════════════════════════════════════════════
  Properties of Reverse Graph-reachability ("reached by")
══════════════════════════════════════════════════════════════════-/

def reachedby (net : BFNN) (S : Set ℕ) : Set ℕ :=
  fun (m : ℕ) =>
    ∃ (n : ℕ), (n ∈ S ∧ net.graph.hasPath m n)

--------------------------------------------------------------------
theorem reachedby_is_extens (net : BFNN) : ∀ (S : Set ℕ),
  S ⊆ reachedby net S := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
        (n : ℕ) (h₁ : n ∈ S)

  have (h₂ : hasPath net.toNet.graph n n) := hasPath.trivial
  exact ⟨n, ⟨h₁, h₂⟩⟩
  
--------------------------------------------------------------------
theorem reachedby_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
  reachedby net S = reachedby net (reachedby net S) := by
--------------------------------------------------------------------
  intro (S : Set ℕ)
  apply ext
  intro (m : ℕ)
  apply Iff.intro

  -- Forward direction (easy; just apply Extensive)
  case mp => 
    exact fun h₁ => reachedby_is_extens net (reachedby net S) h₁

  -- Backwards direction
  case mpr => 
    intro (h₁ : m ∈ reachedby net (reachedby net S))
    match h₁ with
    | ⟨x, h₂⟩ => 
      match h₂.1 with
      | ⟨n, h₃⟩ => 
        exact ⟨n, ⟨h₃.1, hasPath_trans _ h₂.2 h₃.2⟩⟩

--------------------------------------------------------------------
theorem reachedby_is_monotone (net : BFNN) : ∀ (S₁ S₂ : Set ℕ),
  S₁ ⊆ S₂ → reachedby net S₁ ⊆ reachedby net S₂ := by
--------------------------------------------------------------------
  intro (S₁ : Set ℕ) (S₂ : Set ℕ)
        (h₁ : S₁ ⊆ S₂)
        (n : ℕ) (h₂ : n ∈ reachedby net S₁)

  exact match h₂ with
  | ⟨n, h₃⟩ => ⟨n, ⟨h₁ h₃.1, h₃.2⟩⟩  


/-══════════════════════════════════════════════════════════════════
  Reach-Prop Interaction Properties
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
lemma minimal_cause_helper (net : BFNN) : ∀ (S₁ S₂ : Set ℕ), ∀ (n : ℕ),
  n ∈ reachedby net S₂
  → (n ∈ propagate net S₁
  ↔ n ∈ propagate net (S₁ ∩ reachedby net S₂)) := by
--------------------------------------------------------------------
  intro (S₁ : Set ℕ) (S₂ : Set ℕ)
  intro (n : ℕ)
  intro (h₁ : n ∈ reachedby net S₂)
  simp only [Membership.mem, Set.Mem, propagate]

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n
  
  -- Base Step
  case hz => 
    apply Iff.intro
    case mp => 
      intro h₂
      simp only [propagate_acc]
      simp only [propagate_acc] at h₂
      exact ⟨h₂, h₁⟩

    case mpr => 
      intro h₂
      simp only [propagate_acc]
      simp only [propagate_acc] at h₂
      exact h₂.1

  -- Inductive Step
  case hi k IH => 
    apply Iff.intro

    -- Forward Direction
    case mp => 
      intro h₂

      -- By cases; either n ∈ S₁ or not.
      by_cases n ∈ S₁
      case pos => 
        -- This case is trivial (just apply Extens)
        rw [symm hL]
        have h₃ : n ∈ S₁ ∩ reachedby net S₂ := ⟨h, h₁⟩ 
        exact @propagate_acc_is_extens net _ _ h₃
      case neg => 
        -- If n ∉ S₁, then n ∉ S₁ ∩ reachedby net S₂
        have h₃ : n ∉ S₁ ∩ reachedby net S₂ := 
          fun n_in_S₁ => absurd n_in_S₁.1 h
        
        -- Just some simplifications and rewriting definitions
        rw [simp_propagate_acc net h] at h₂
        rw [simp_propagate_acc net h₃]

        -- TODO: This is the stuff that should go in the activ_agree lemma!
        simp
        simp at h₂
        convert h₂ using 5
        rename_i i
        generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
        generalize hLm : layer net m = Lm

        -- Apply the inductive hypothesis!
        have h₄ : m ∈ preds net n := by
          rw [symm hm]
          simp [preds]
          exact get!_mem (predecessors net.toNet.graph n).data i
        have h₅ : Lm ≤ k := by
          rw [symm hLm]
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net m n h₄
        have h₆ : m ∈ reachedby net S₂ :=
          match h₁ with
          | ⟨x, hx⟩ => ⟨x, ⟨hx.1, hasPath_trans _ (preds_path _ h₄) hx.2⟩⟩
        exact (symm (IH Lm h₅ m h₆ hLm).to_eq).to_iff

    -- Backwards Direction (should be similar)
    case mpr =>
      intro h₂

      -- By cases; either n ∈ S₁ or not.
      by_cases n ∈ S₁
      case pos => 
        -- This case is trivial (just apply Extens)
        rw [symm hL]
        exact @propagate_acc_is_extens net _ _ h
      case neg => 
        -- If n ∉ S₁, then n ∉ S₁ ∩ reachedby net S₂
        have h₃ : n ∉ S₁ ∩ reachedby net S₂ := 
          fun n_in_S₁ => absurd n_in_S₁.1 h
        
        -- Just some simplifications and rewriting definitions
        rw [simp_propagate_acc net h₃] at h₂
        rw [simp_propagate_acc net h]

        -- TODO: This is the stuff that should go in the activ_agree lemma!
        simp
        simp at h₂
        convert h₂ using 5
        rename_i i
        generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
        generalize hLm : layer net m = Lm

        -- Apply the inductive hypothesis!
        have h₄ : m ∈ preds net n := by
          rw [symm hm]
          simp [preds]
          exact get!_mem (predecessors net.toNet.graph n).data i
        have h₅ : Lm ≤ k := by
          rw [symm hLm]
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net m n h₄
        have h₆ : m ∈ reachedby net S₂ :=
          match h₁ with
          | ⟨x, hx⟩ => ⟨x, ⟨hx.1, hasPath_trans _ (preds_path _ h₄) hx.2⟩⟩
        exact IH Lm h₅ m h₆ hLm


-- This is the actual proparty I want, re-written with conditionals
-- in mind
--------------------------------------------------------------------
theorem minimal_cause (net : BFNN) : ∀ (S₁ S₂ : Set ℕ),
  S₂ ⊆ propagate net S₁
  ↔ S₂ ⊆ propagate net (S₁ ∩ reachedby net S₂) := by
--------------------------------------------------------------------
  intro (S₁ : Set ℕ) (S₂ : Set ℕ)
  apply Iff.intro
  case mp => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
    (reachedby_is_extens _ _ h₂)).mp (h₁ h₂)
  case mpr => exact fun h₁ n h₂ => (minimal_cause_helper net _ _ _ 
    (reachedby_is_extens _ _ h₂)).mpr (h₁ h₂)

/-══════════════════════════════════════════════════════════════════
  Naive (Unstable) Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- *hebb* -- The easiest thing to do is to give some 'infinite'
--  weight value, and then update the weights to be that.

-- We need an 'infinity' value for Floats,
-- that is greater than all other Floats.
axiom inf : Float

-- Propagate S through the net, and then update the weights
-- of all the edges involved in that propagation.
-- 
-- We update the weights *maximally*, i.e. rather than
-- incrementing them we just set them to a value that
-- is *guaranteed* to activate the next one.
-- 
-- (actually, this value is just the one given by activ_pos)

def max_weight (net : BFNN) : Float := 
  sorry

def hebb (net : BFNN) (S : Set ℕ) : BFNN :=
  {
    graph := sorry
    activation := net.activation

    binary := net.binary
    acyclic := sorry
    activ_nondecr := net.activ_nondecr
    activ_pos := net.activ_pos
  }

/-
Graph example
⟨#[
    ⟨0, #[⟨1, 0.5⟩, ⟨2, 0.6⟩, ⟨3, 0.7⟩]⟩, 
    ⟨1, #[⟨2, 0.8⟩, ⟨3, 0.9⟩]⟩, 
    ⟨2, #[⟨3, 1.0⟩, ⟨3, 5.0⟩]⟩, 
    ⟨3, #[]⟩
  ]⟩
-/
/-
Update example
def updateVertexPayload (g : Graph α β) (id : Nat) (payload : α) : Graph α β := {
  g with vertices := g.vertices.modify id (λ vertex => { vertex with payload := payload })
}
-/