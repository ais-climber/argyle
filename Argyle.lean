import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NthRewrite
import Mathlib.Mathport.Syntax
import Std.Tactic.ShowTerm
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Tactic.Basic

import Lean.Parser.Tactic
import Graph.Graph
import Graph.TopologicalSort
import Mathlib.Init.Set
import Mathlib.Data.List.Defs
import Mathlib.Init.Propext
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

open Graph
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
-- Extract Lets Tactic
-------------------------------------------------
/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

/-!
# The `extract_lets at` tactic
This module defines a tactic `extract_lets ... at h` that can be used to (in essence) do `cases`
on a `let` expression.
-/


-- open Lean Elab Parser Meta Tactic

-- /-- Given a local hypothesis whose type is a `let` expression, then lift the `let` bindings to be
-- a new local definition. -/
-- def Lean.MVarId.extractLetsAt (mvarId : MVarId) (fvarId : FVarId) (names : Array Name) :
--     MetaM (Array FVarId × MVarId) := do
--   mvarId.checkNotAssigned `extractLetAt
--   mvarId.withReverted #[fvarId] fun mvarId fvarIds => mvarId.withContext do
--     let mut mvarId := mvarId
--     let mut fvarIds' := #[]
--     for name in names do
--       let ty ← Lean.instantiateMVars (← mvarId.getType)
--       mvarId ← match ty with
--         | .letE n t v b ndep => process mvarId t (.letE n · v b ndep)
--         | .forallE n t v b   => process mvarId t (.forallE n · v b)
--         | _ => throwTacticEx `extractLetAt mvarId "unexpected auxiliary target"
--       let (fvarId', mvarId') ← mvarId.intro name
--       fvarIds' := fvarIds'.push fvarId'
--       mvarId := mvarId'
--     return (fvarIds', fvarIds.map .some, mvarId)
-- where
--   /-- Check that `t` is a `let` and then do what's necessary to lift it over the binding
--   described by `mk`. -/
--   process (mvarId : MVarId) (t : Expr) (mk : Expr → Expr) : MetaM MVarId := do
--     let .letE n' t' v' b' _ := t.cleanupAnnotations
--       | throwTacticEx `extractLetAt mvarId "insufficient number of `let` expressions"
--     -- Lift the let
--     withLetDecl n' t' v' fun fvar => do
--       let b' := b'.instantiate1 fvar
--       let ty' ← mkLetFVars #[fvar] <| mk b'
--       mvarId.change ty'

-- /-- Counts the immediate depth of a nested `let` expression. -/
-- def Lean.Expr.letDepth : Expr → Nat
--   | .letE _ _ _ b _ => b.letDepth + 1
--   | _ => 0

-- /-- A more limited version of `Lean.MVarId.introN` that ensures the goal is a
-- nested `let` expression. -/
-- def Lean.MVarId.extractLets (mvarId : MVarId) (names : Array Name) :
--     MetaM (Array FVarId × MVarId) :=
--   mvarId.withContext do
--     let ty := (← Lean.instantiateMVars (← mvarId.getType)).cleanupAnnotations
--     if ty.letDepth < names.size then
--       throwTacticEx `extractLet mvarId "insufficient number of `let` expressions"
--     mvarId.introN names.size names.toList

-- namespace Mathlib

-- /-- The `extract_lets at h` tactic takes a local hypothesis of the form `h : let x := v; b`
-- and introduces a new local definition `x := v` while changing `h` to be `h : b`.  It can be thought
-- of as being a `cases` tactic for `let` expressions. It can also be thought of as being like
-- `intros at h` for `let` expressions.
-- For example, if `h : let x := 1; x = x`, then `extract_lets x at h` introduces `x : Nat := 1` and
-- changes `h` to `h : x = x`.
-- Just like `intros`, the `extract_lets` tactic either takes a list of names, in which case
-- that specifies the number of `let` bindings that must be extracted, or it takes no names, in which
-- case all the `let` bindings are extracted.
-- The tactic `extract_let at ⊢` is a weaker form of `intros` that only introduces obvious `let`s. -/
-- syntax (name := extractLets) "extract_lets " (colGt (ident <|> hole))* (ppSpace location) : tactic

-- @[tactic Mathlib.extractLets] def evalExtractLet : Tactic := fun stx => do
--   match stx with
--   | `(tactic| extract_lets $loc:location)         => doExtract none loc
--   | `(tactic| extract_lets $hs* $loc:location)    => doExtract hs loc
--   | _ => throwUnsupportedSyntax
-- where
--   setupNames (ids? : Option (TSyntaxArray [`ident, `Lean.Parser.Term.hole])) (ty : Expr) :
--       MetaM (Array Name) := do
--     if let some ids := ids? then
--       return ids.map getNameOfIdent'
--     else
--       return Array.mkArray (← instantiateMVars ty).cleanupAnnotations.letDepth `_
--   doExtract (ids? : Option (TSyntaxArray [`ident, `Lean.Parser.Term.hole]))
--       (loc : TSyntax `Lean.Parser.Tactic.location) :
--       TacticM Unit := do
--     let process (f : MVarId → Array Name → MetaM (Array FVarId × MVarId))
--         (ty : MVarId → MetaM Expr) : TacticM Unit := do
--       let fvarIds ← liftMetaTacticAux fun mvarId => do
--         let ids ← setupNames ids? (← ty mvarId)
--         let (fvarIds, mvarId) ← f mvarId ids
--         return (fvarIds, [mvarId])
--       if let some ids := ids? then
--         withMainContext do
--           for stx in ids, fvarId in fvarIds do
--             Term.addLocalVarInfo stx (.fvar fvarId)
--     withLocation (expandOptLocation (mkOptionalNode loc))
--       (atLocal := fun h ↦ do
--         process (fun mvarId ids => mvarId.extractLetsAt h ids) (fun _ => h.getType))
--       (atTarget := do
--         process (fun mvarId ids => mvarId.extractLets ids) (fun mvarId => mvarId.getType))
--       (failed := fun _ ↦ throwError "extract_let tactic failed")

-- end Mathlib


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
-- intro_lets tactic
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Pulling.20.60let.60s.20to.20the.20outside.20of.20a.20statement/near/315581119
-- Courtesy of Eric Wieser
-- 
-------------------------------------------------
-- This is written in Lean 3!
-- I need this but for Lean 4...

-- meta def mk_local_lets : expr → tactic (list expr × expr)
-- | (expr.elet n d v b) := do
--   p ← tactic.definev n d v,
--   (ps, r) ← mk_local_lets (expr.instantiate_var b p),
--   return ((p :: ps), r)
-- | (expr.app f x) := do
--     (fargs, f) ← mk_local_lets f,
--     (xargs, x) ← mk_local_lets x,
--     pure (fargs ++ xargs, f.app x)
-- | e := return ([], e)

-- meta def tactic.interactive.lift_lets : tactic unit :=
-- do
--   (lets, t) ← tactic.target >>= mk_local_lets,
--   tactic.change t

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

def myBFNN : BFNN :=
  {
    graph := graphA
    activation := binary_step
    rate := 1.0

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

-- -- If A and B agree on all the predecessors of n, then they agree on n.
-- -- TODO: We don't seem to need this lemma anymore!
-- lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
--   let preds := preds net n
--   (∀ (m : ℕ), m ∈ preds → (m ∈ A ↔ m ∈ B))
--   → activ net A n
--   → activ net B n := by

--   intro preds
--         (h₁ : ∀ (m : ℕ), m ∈ preds → (m ∈ A ↔ m ∈ B))
--         (h₂ : activ net A n)

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

-- AXIOM: We assume the net is fully connected!
-- This is essentially the statement we need, which might
-- follow from being fully connected.
-- TODO: Put this in the definition of BFNN!!!
axiom connected : ∀ (net : BFNN) (m n : ℕ), 
  layer net m < layer net n → net.graph.hasEdge m n

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

/-
activ net
  (List.bind (List.range (List.length (predecessors net.toNet.graph n).data)) fun i =>
    pure
      (if
          propagate_acc net (fun n => propagate_acc net S n (layer net n))
            (List.get! (predecessors net.toNet.graph n).data i)
            (layer net (List.get! (predecessors net.toNet.graph n).data i)) then
        OfScientific.ofScientific 10 true 1
      else OfScientific.ofScientific 0 true 1))
  n
-/

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
--   generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
--   sorry
  -- -- Just go in and subsitute m ∈ A for m ∈ B.
  -- intro (h₁ : ∀ (m : ℕ), layer net m ≤ layer net n → (m ∈ A ↔ m ∈ B))
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
lemma prop_layer_zero (net : BFNN) : ∀ (S : Set ℕ) (n : ℕ),
  layer net n = 0
  → n ∈ propagate net S
  → n ∈ S := by
--------------------------------------------------------------------
  sorry

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
          
          -- -- activ_agrees lemma goes here
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

-- def reachable (net : BFNN) (S : Set ℕ) : Set ℕ :=
--   fun (n : ℕ) =>
--     ∃ (m : ℕ), (m ∈ S ∧ net.graph.hasPath m n)

-- -- hL: layer net n = 0
-- -- h₁: n ∈ B ∨ n ∈ A ∧ reachable net B n
-- -- ⊢ n ∈ B

-- -- Argument: If there is a path from S to n, but n is in
-- -- layer 0 -- there are *no* incoming nodes, so the path
-- -- must be of length 0.  So n must be that n ∈ S with
-- -- a path to n, i.e. n ∈ S.
-- --------------------------------------------------------------------
-- lemma reach_layer_zero (net : BFNN) : ∀ (S : Set ℕ) (n : ℕ),
--   layer net n = 0
--   → n ∈ reachable net S
--   → n ∈ S := by
-- --------------------------------------------------------------------
--   sorry

-- --------------------------------------------------------------------
-- theorem reach_is_extens (net : BFNN) : ∀ (S : Set ℕ),
--   S ⊆ reachable net S := by
-- --------------------------------------------------------------------
--   intro (S : Set ℕ)
--         (n : ℕ) (h₁ : n ∈ S)

--   have (h₂ : hasPath net.toNet.graph n n) := hasPath.trivial
--   exact ⟨n, ⟨h₁, h₂⟩⟩
  
-- --------------------------------------------------------------------
-- theorem reach_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
--   reachable net S = reachable net (reachable net S) := by
-- --------------------------------------------------------------------
--   intro (S : Set ℕ)
  
--   exact Set.ext (fun (n : ℕ) =>
--     -- ⊆ direction (the easy direction; just apply 'extensive')
--     ⟨(fun (h₁ : n ∈ reachable net S) => 
--       let S_reach := reachable net S
--       reach_is_extens net S_reach h₁),

--     -- ⊇ direction
--     (fun (h₁ : n ∈ reachable net (reachable net S)) =>
--       match h₁ with
--       | ⟨x, h₂⟩ => 
--         match h₂.1 with
--         | ⟨m, h₃⟩ =>
--           have (h₄ : hasPath net.graph m n) := 
--             hasPath_trans net.graph h₃.2 h₂.2
--           ⟨m, ⟨h₃.1, h₄⟩⟩)⟩)

-- --------------------------------------------------------------------
-- theorem reach_is_monotone (net : BFNN) : ∀ (A B : Set ℕ),
--   A ⊆ B → reachable net A ⊆ reachable net B := by
-- --------------------------------------------------------------------
--   intro (A : Set ℕ) (B : Set ℕ)
--         (h₁ : A ⊆ B)
--         (n : ℕ) (h₂ : n ∈ reachable net A)

--   exact match h₂ with
--     | ⟨m, h₃⟩ => ⟨m, ⟨h₁ h₃.1, h₃.2⟩⟩ 


/-══════════════════════════════════════════════════════════════════
  Properties of Reverse Graph-reachability ("reached by")
══════════════════════════════════════════════════════════════════-/

-- def reachedby (net : BFNN) (S : Set ℕ) : Set ℕ :=
--   fun (m : ℕ) =>
--     ∃ (n : ℕ), (n ∈ S ∧ net.graph.hasPath m n)

-- --------------------------------------------------------------------
-- theorem reachedby_is_extens (net : BFNN) : ∀ (S : Set ℕ),
--   S ⊆ reachedby net S := by
-- --------------------------------------------------------------------
--   intro (S : Set ℕ)
--         (n : ℕ) (h₁ : n ∈ S)

--   have (h₂ : hasPath net.toNet.graph n n) := hasPath.trivial
--   exact ⟨n, ⟨h₁, h₂⟩⟩
  
-- --------------------------------------------------------------------
-- theorem reachedby_is_idempotent (net : BFNN) : ∀ (S : Set ℕ),
--   reachedby net S = reachedby net (reachedby net S) := by
-- --------------------------------------------------------------------
--   intro (S : Set ℕ)
--   apply ext
--   intro (m : ℕ)
--   apply Iff.intro

--   -- Forward direction (easy; just apply Extensive)
--   case mp => 
--     exact fun h₁ => reachedby_is_extens net (reachedby net S) h₁

--   -- Backwards direction
--   case mpr => 
--     intro (h₁ : m ∈ reachedby net (reachedby net S))
--     match h₁ with
--     | ⟨x, h₂⟩ => 
--       match h₂.1 with
--       | ⟨n, h₃⟩ => 
--         exact ⟨n, ⟨h₃.1, hasPath_trans _ h₂.2 h₃.2⟩⟩

-- --------------------------------------------------------------------
-- theorem reachedby_is_monotone (net : BFNN) : ∀ (A B : Set ℕ),
--   A ⊆ B → reachedby net A ⊆ reachedby net B := by
-- --------------------------------------------------------------------
--   intro (A : Set ℕ) (B : Set ℕ)
--         (h₁ : A ⊆ B)
--         (n : ℕ) (h₂ : n ∈ reachedby net A)

--   exact match h₂ with
--   | ⟨n, h₃⟩ => ⟨n, ⟨h₁ h₃.1, h₃.2⟩⟩  


/-══════════════════════════════════════════════════════════════════
  Conditional Graph Reachability
══════════════════════════════════════════════════════════════════-/



-- A focused path is a path where every node is contained
-- within the set S.
inductive focusedPath (g : Graph ℕ β) (S : Set ℕ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      u ∈ S → focusedPath g S u u
  | from_path {u v w : ℕ} : 
      focusedPath g S u v → hasEdge g v w → w ∈ S → focusedPath g S u w


-- Updated version!
-- This is the set of all nodes reachable from B using
-- paths where *every* node in the path is within A
-- (including the initial and final nodes)
def reachable (net : BFNN) (A B : Set ℕ) : Set ℕ :=
  fun (n : ℕ) =>
    -- This is the actual definition, I got it wrong before
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
  sorry


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

-- --------------------------------------------------------------------
-- theorem reach_within (net : BFNN) : ∀ (A B : Set ℕ),
--   reachable net A B ⊆ A := by
-- --------------------------------------------------------------------
--   sorry

-- TODO: Prove stuff about reachable.
-- It looks like
-- reachable A B ⊆ A,
-- but I'm not sure about the complete rules surrounding it.
-- 
-- NOTE:
-- Van Benthem describes "conditional common knowledge" as
-- CG(A, B) "is true in all worlds reachable via some finite path
-- of accessibilities running entirely through worlds satisfying A"
-- [Van Benthem, Belief Revision and Dynamic Logic, page 6]
-- 
-- This is *exactly* what reachable is doing!!!
-- In this paper, he also talks about "pre-encoding" future
-- information in order to get a reduction, which is exactly
-- what we're doing here!

--------------------------------------------------------------------
theorem reach_subset (net : BFNN) : ∀ (A B : Set ℕ),
  reachable net A B ⊆ A := by
--------------------------------------------------------------------
  sorry


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
--         generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
--         generalize hLm : layer net m = Lm

--         -- Apply the inductive hypothesis!
--         have h₄ : m ∈ preds net n := by
--           rw [symm hm]
--           simp [preds]
--           exact get!_mem (predecessors net.toNet.graph n).data i
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
--         generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
--         generalize hLm : layer net m = Lm

--         -- Apply the inductive hypothesis!
--         have h₄ : m ∈ preds net n := by
--           rw [symm hm]
--           simp [preds]
--           exact get!_mem (predecessors net.toNet.graph n).data i
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

-- Increase the weight on the given edge x₁ ⟶ x₂  by
-- η * act(x₁) * act(x₂), *only if* the nodes are both within
-- propagate net S.
noncomputable
def weight_update (net : BFNN) (S : Set ℕ) 
  (x₁ : ℕ) (edge : Edge Float) : Float := 
  let x₂ := edge.target
  let activ₁ := if x₁ ∈ propagate net S then 1.0 else 0.0
  let activ₂ := if x₂ ∈ propagate net S then 1.0 else 0.0
  edge.weight + (net.rate * activ₁ * activ₂)

noncomputable
def graph_update (net : BFNN) (g : Graph ℕ Float) (S : Set ℕ) : Graph ℕ Float :=
  { vertices := Array.map (fun v => 
    { v with adjacencyList := Array.map (fun edge => 
      { edge with weight := weight_update net S v.payload edge}) v.adjacencyList}) g.vertices }

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
  Properties of Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- Hebbian update hebb_star does not affect the predecessors
-- of any node.
--------------------------------------------------------------------
theorem hebb_preds (net : BFNN) (S : Set ℕ) : 
  preds (hebb_star net S) n = preds net n := by
--------------------------------------------------------------------
  sorry


-- Hebbian update hebb_star does not affect which neurons are
-- on which layer of the net.
--------------------------------------------------------------------
theorem hebb_layers (net : BFNN) (S : Set ℕ) : 
  layer (hebb_star net S) n = layer net n := by
--------------------------------------------------------------------
  exact rfl


-- Hebbian update hebb_star does not affect the activation function.
--------------------------------------------------------------------
theorem hebb_activation (net : BFNN) (S : Set ℕ) : 
  (hebb_star net S).activation = net.activation := by 
--------------------------------------------------------------------
  exact rfl


-- Hebbian update hebb_star does not affect graph reachability
-- (It only affects the edge weights)
--------------------------------------------------------------------
theorem hebb_reach (net : BFNN) (A B : Set ℕ) : 
  reachable (hebb_star net A) B = 
    reachable net B := by 
--------------------------------------------------------------------
  sorry
  
  
-- Every net N is a subnet of (hebb_star N)
-- (i.e. hebb_star includes the previous propagations)
-- (We had this property in The Logic of Hebbian Learning)
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
    rw [hL] at h₁
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
      rw [← hL]
      rw [← hebb_layers net A]
      exact propagate_acc_is_extens _ _ h  
    
    case neg => 
      -- Do simplifications and rewriting
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
  exact h₂



/-══════════════════════════════════════════════════════════════════
  The more interesting/crucial properties
══════════════════════════════════════════════════════════════════-/

-- If n ∉ Prop(A), then the weights in the updated net are the same
-- as the weights in the original net.
--------------------------------------------------------------------
theorem hebb_weights₁ (net : BFNN) : 
  n ∉ propagate net A
  → ∀ (i : ℕ),
    (getEdgeWeight (hebb_star net A).toNet.graph ((preds net n).get! i) n =
    getEdgeWeight net.toNet.graph ((preds net n).get! i) n) := by
--------------------------------------------------------------------
  sorry


-- If all predecessors of n ∉ Prop(A), then the weights in the 
-- updated net are the same as the weights in the original net.
--------------------------------------------------------------------
theorem hebb_weights₂ (net : BFNN) : 
  (∀ x, x ∈ preds net n → x ∉ propagate net A)
  → ∀ (i : ℕ),
    (getEdgeWeight (hebb_star net A).toNet.graph ((preds net n).get! i) n =
    getEdgeWeight net.toNet.graph ((preds net n).get! i) n) := by
--------------------------------------------------------------------
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
  generalize hL : layer (hebb_star net A) n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  case hz => 
    -- First, do the base case simplifications
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
        have heq : layer net n = 0 := Eq.trans (symm (hebb_layers net A)) hL
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
        rw [← hL]
        rw [hebb_layers]

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
              rw [← hL]
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
              generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
              generalize hLm : layer net m = Lm
              
              -- We are now ready to apply our inductive hypothesis!
              have h₇ : m ∈ preds net n := by
                rw [symm hm]
                simp [preds]
                exact get!_mem (predecessors net.toNet.graph n).data i
              have h₈ : Lm ≤ L := by
                rw [symm hLm]
                apply Nat.lt_succ.mp
                rw [symm hL]
                rw [hebb_layers net A]
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
          generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
          generalize hLm : layer net m = Lm
          
          -- We are now ready to apply our inductive hypothesis!
          have h₂ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (predecessors net.toNet.graph n).data i
          have h₃ : Lm ≤ L := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            rw [hebb_layers net A]
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
        rw [hebb_layers]
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
              generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
              generalize hLm : layer net m = Lm
              
              -- We are now ready to apply our inductive hypothesis!
              have h₇ : m ∈ preds net n := by
                rw [symm hm]
                simp [preds]
                exact get!_mem (predecessors net.toNet.graph n).data i
              have h₈ : Lm ≤ L := by
                rw [symm hLm]
                apply Nat.lt_succ.mp
                rw [symm hL]
                rw [hebb_layers net A]
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
          generalize hm : List.get! (predecessors net.toNet.graph n).data i = m
          generalize hLm : layer net m = Lm
          
          -- We are now ready to apply our inductive hypothesis!
          have h₂ : m ∈ preds net n := by
            rw [symm hm]
            simp [preds]
            exact get!_mem (predecessors net.toNet.graph n).data i
          have h₃ : Lm ≤ L := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            rw [hebb_layers net A]
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



