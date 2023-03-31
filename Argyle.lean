import Mathlib.Tactic.LibrarySearch

import Lean.Parser.Tactic
import Graph.Graph
import Graph.TopologicalSort
import Mathlib.Init.Set
import Mathlib.Data.List.Defs

open Graph
open Set
open Classical

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
  binary : ∀ (x : Float), 
    (activation x = 0.0) ∨ (activation x = 1.0)
  
  acyclic : graph.is_acyclic
  
  activ_nondecr : ∀ (x₁ x₂ : Float),
    x₁ ≤ x₂ → activation x₁ ≤ activation x₂

def myBFNN : BFNN :=
  {
    graph := graphA
    activation := binary_step

    binary := binary_step_is_binary
    acyclic := graphA_is_acyclic
    activ_nondecr := binary_step_nondecr
  }

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



-------------------------------------------------
-- Forward propagation in a net
-------------------------------------------------

def weighted_sum (weights : List Float) (lst : List Float) : Float :=
  List.sum [w * x | for w in weights, for x in lst]

#eval weighted_sum [] []
#eval weighted_sum [1.0] [3.0]
#eval weighted_sum [1.0, 2.0, 3.0] [5.0, 5.0, 5.0]

-- Not well-defined behavior (we expect the weights and lst to be of equal size,
-- but this is left implicit.)
#eval weighted_sum [1.0, 2.0] [3.0]

-- Function that gives n's activation value *immediately* 
-- following its predecessor's activation values, under set S.
-- (Compute the current activation from the previous 
-- activation of all the predecessors of n.
def activ (net : BFNN) (S : Set ℕ) (n : ℕ) : Prop :=
  let preds := (predecessors net.graph n).toList
  let prev_activ := [if m ∈ S then 1.0 else 0.0 | for m in preds]
  let weights := [net.graph.getEdgeWeight m n | for m in preds]
  let weight_sum := weighted_sum weights prev_activ
  let curr_activ := net.activation weight_sum
  curr_activ = 1.0

-- If S₁ and S₂ agree on all the predecessors of n,
-- then they agree on n.
theorem activ_agree (net : BFNN) (S₁ S₂ : Set ℕ) (n : ℕ) :
  let preds := (predecessors net.graph n).toList
  List.all preds (fun m => activ net S₁ n ↔ activ net S₂ n) -- how to say S₁ and S₂ agree on *all* m ∈ preds??? 
  → (activ net S₁ n ↔ activ net S₂ n) := by

  intro preds
  intro h₁
  apply Iff.intro
  -- Forward Direction
  { intro h₂
    sorry
  }

  -- Backwards Direction
  { intro h₂
    sorry
  }


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
def propagateₚ (net : BFNN) (S : Set ℕ) (n : ℕ) 
               (topol_sorted_reverse : List ℕ) : Prop :=
  match topol_sorted_reverse with
  | [] => n ∈ S
  | x :: xs => 
    if x = n then
      n ∈ S ∨ activ net {m | (propagateₚ net S m xs)} n
    else
      propagateₚ net S n xs

def propagate (net : BFNN) (S : Set ℕ) : Set ℕ :=
  let topol_sorted_reverse := (topSortUnsafe net.graph).toList.reverse
  {n : ℕ | propagateₚ net S n topol_sorted_reverse}

-------------------------------------------------
-- Properties of propagation, using function
-- notation
-------------------------------------------------

def topol_sort (g : Graph ℕ Float) :=
  (topSortUnsafe g).toList.reverse

theorem propagateₚ_is_extens (net : BFNN) : ∀ (S : Set ℕ) (n : ℕ),
  let sort := (topol_sort net.graph)
  n ∈ S → propagateₚ net S n sort := by
  
  intro (S : Set ℕ)
  intro (n : ℕ)
  intro sort
  intro (h₁ : n ∈ S)

  induction sort
  case nil => exact h₁
  case cons x xs IH => 
    -- Inductive Step
    simp only [propagateₚ]
    
    split_ifs
    case inl _ => exact Or.inl h₁
    case inr _ => exact IH

theorem propagateₚ_is_idempotent (net : BFNN) : ∀ (S : Set ℕ) (n : ℕ),
  let sort := (topol_sort net.graph)
  propagateₚ net S n sort ↔ 
    propagateₚ net {n : ℕ | propagateₚ net S n sort} n sort := by

  intro (S : Set ℕ)
  intro (n : ℕ)
  intro sort
  
  induction sort generalizing n
  case nil => exact ⟨fun x => x, fun x => x⟩
  case cons x xs IH => 
    -- Inductive Step
    apply Iff.intro

    -- Forward Direction (do the same thing we did for 'extensive')
    { intro h₁
      simp only [propagateₚ]
      
      split_ifs
      case inl _ => exact Or.inl h₁
      case inr _ => sorry
      -- need to substitute if x = n then n ∈ S ∨ activ net { m | propagateₚ net S m xs }
      -- and then it's just our IH.
    }
    -- Backwards Direction
    { simp only [propagateₚ]

      split_ifs
      case inl x_eq_n =>
        intro h₁
        apply Or.inr _
        -- This is the actually tricky part!
        sorry
      case inr x_not_n =>
        intro h₁
        sorry
        -- need to substitute if x = n then n ∈ S ∨ activ net { m | propagateₚ net S m xs }
      -- and then it's just our IH.
    }

-------------------------------------------------
-- Properties of propagation, using set notation
-------------------------------------------------

#check propagate myBFNN {n : ℕ | n ≤ 4}
-- #eval propagate myBFNN {n : ℕ | n ≤ 4}
-- need to make sets finite in order to evaluate???
-- 
-- It's important for everything to be evaluatable, since:
-- 1) I will want to verify that a *specific*
--    neural network has certain properties
-- 2) #eval helps me debug errors

theorem propag_is_extens (net : BFNN) : ∀ (S : Set ℕ),
  S ⊆ propagate net S := 

  fun (S : Set ℕ) => fun (n : ℕ) => 
    propagateₚ_is_extens net S n

theorem propag_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
  propagate net S = propagate net (propagate net S) := by
  
  intro (S : Set ℕ)
  apply ext _
  intro (n : ℕ)
  apply Iff.intro

  case mp => exact (propagateₚ_is_idempotent net S n).mp
  case mpr => exact (propagateₚ_is_idempotent net S n).mpr

-------------------------------------------------
-- Graph-reachability
-------------------------------------------------

def reachable (net : BFNN) (S : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ (m : ℕ), (m ∈ S ∧ net.graph.hasPath m n) }


theorem reach_is_extens (net : BFNN) : ∀ (S : Set ℕ),
  S ⊆ reachable net S := by
  
  intro (S : Set ℕ)
  intro (n : ℕ)
  intro (h₁ : n ∈ S)

  have (h₂ : hasPath net.toNet.graph n n) := hasPath.trivial
  exact ⟨n, ⟨h₁, h₂⟩⟩
  

theorem reach_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
  reachable net S = reachable net (reachable net S) := by

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


theorem reach_is_monotone (net : BFNN) : ∀ (S₁ S₂ : Set ℕ),
  S₁ ⊆ S₂ → reachable net S₁ ⊆ reachable net S₂ := by

  intro (S₁ : Set ℕ)
  intro (S₂ : Set ℕ)
  intro (h₁ : S₁ ⊆ S₂)
  intro (n : ℕ)
  intro (h₂ : n ∈ reachable net S₁)

  exact match h₂ with
    | ⟨m, h₃⟩ => ⟨m, ⟨h₁ h₃.1, h₃.2⟩⟩ 





