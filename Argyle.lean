import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.NthRewrite
import Mathlib.Mathport.Syntax
import Std.Tactic.ShowTerm
import Lean.Meta.Tactic.Simp.Main
import Mathlib.Tactic.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.Real.Basic

import Lean.Parser.Tactic
import Mathlib.Init.Set
import Mathlib.Data.List.Defs
import Mathlib.Init.Propext
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic

open Set
open Tactic
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
def graphA : Graph ℕ ℚ :=
  ⟨[⟨0, [⟨1, 0.5⟩, ⟨2, 0.6⟩, ⟨3, 0.7⟩]⟩, 
    ⟨1, [⟨2, 0.8⟩, ⟨3, 0.9⟩]⟩, 
    ⟨2, [⟨3, 1⟩, ⟨3, 3.0⟩]⟩, 
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

def get_vertices (g : Graph ℕ ℚ) : List ℕ :=
  List.map (fun ⟨label, _⟩ => label) g.vertices

-- Helper function to collect the List of pairs of n's successors
def successor_pairs (vertices : List (Vertex ℕ ℚ)) (n : ℕ) : List (ℕ × ℚ) :=
  match vertices with
  | [] => []
  | ⟨vertex, succ⟩ :: rest => 
    if vertex = n then succ 
    else successor_pairs rest n

-- We get all vertices that are in n's successor list
def successors (g : Graph ℕ ℚ) (n : ℕ) : List ℕ :=
  List.filter 
    (fun m => m ∈ (successor_pairs g.vertices n).unzip.1) 
    g.get_vertices

  -- List.get n g.vertices -- successors.unzip.1
  -- g.vertices[n]!.successors.unzip.1


def predecessors (g : Graph ℕ ℚ) (n : ℕ) : List ℕ :=
  List.filter (fun v => n ∈ (g.successors v)) g.get_vertices
  
  -- List.map (fun ⟨label, _⟩ => label) 
  --   (List.filter (fun v => n ∈ (g.successors v)) g.vertices)

  -- List.filter 
  --   (fun m => n ∈ (g.successors m)) 
  --   g.get_vertices

-- Using 'predecessors' is slower than 'successors',
-- but we will tend to look backwards from a node rather
-- than forwards.
def hasEdge (g : Graph ℕ ℚ) (m n : ℕ) : Bool :=
  m ∈ (g.predecessors n)

-- Returns the weight of the edge m ⟶ n, if it exists.
-- If it does not exist, we say the weight is 0
-- TODO: In the future, it's better to use Option here
-- and return none if none!!!
def getEdgeWeight (g : Graph ℕ ℚ) (m n : ℕ) : ℚ :=
  match g.vertices[m]!.successors.find? (fun ⟨label, _⟩ => label = n) with
  | some ⟨_, weight⟩ => weight
  | none => 0

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



inductive hasPath (g : Graph ℕ ℚ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      hasPath g u u
  | from_path {u v w : ℕ} : 
      hasPath g u v → hasEdge g v w → hasPath g u w

--------------------------------------------------------------------
theorem hasPath_trans {u v w : ℕ} (g : Graph ℕ ℚ) :
  hasPath g u v → hasPath g v w → hasPath g u w := by
--------------------------------------------------------------------
  intro (h₁ : hasPath g u v)
  intro (h₂ : hasPath g v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y _ edge_xy path_ux => 
    exact hasPath.from_path path_ux edge_xy


def is_refl (g : Graph ℕ ℚ) : Prop := ∀ (u : ℕ), 
  u ∈ g.get_vertices → g.hasEdge u u

def is_symm (g : Graph ℕ ℚ) : Prop := ∀ (u v : ℕ), 
  g.hasEdge u v → g.hasEdge v u

def is_trans (g : Graph ℕ ℚ) : Prop := ∀ (u v w : ℕ),
  g.hasEdge u v → g.hasEdge v w → g.hasEdge u w

def is_acyclic (g : Graph ℕ ℚ) : Prop := ∀ (u v : ℕ),
  g.hasPath u v → g.hasPath v u → u = v

end Graph

-------------------------------------------------
-- Activation functions
-------------------------------------------------
def binary_step (x : ℚ) : ℚ :=
  if x > 0 then 1 else 0

--------------------------------------------------------------------
theorem binary_step_is_binary (x : ℚ) :
    (binary_step x = 0) ∨ (binary_step x = 1) := by
--------------------------------------------------------------------
      -- simp [binary_step]

      cases (lt_or_ge 0 x) with

      -- Case 1: 0 < x
      | inl case1 =>
          have (h : binary_step x = 1) :=
            by
              simp only [binary_step]
              rw [(if_pos case1)]
          exact Or.inr h

      -- Case 2: ¬ (0 < x)
      | inr case2 =>
          have (h : binary_step x = 0) := 
            by 
              simp only [binary_step]
              rw [(if_neg (not_lt_of_le case2))]
          exact Or.inl h

-- Proof that binary_step is nondecreasing
-- This is also a 'hello world' to see if I can
-- reason about a branching program.
--------------------------------------------------------------------
theorem binary_step_nondecr (x₁ x₂ : ℚ) (hyp : x₁ ≤ x₂) :
  (binary_step x₁ ≤ binary_step x₂) := by
--------------------------------------------------------------------
    -- Simplify by applying the definition of binary_step.
    simp [binary_step]
    
    cases (lt_or_ge 0 x₁) with
    | inl case1 =>
      cases (lt_or_ge 0 x₂) with
      | inl case11 => 
          -- Both sides evaluate to 1,
          -- so we just prove that 1 ≤ 1.
          rw [(if_pos case1)]
          rw [(if_pos case11)]
      | inr case12 => 
          -- We have 0 < x₁ ≤ x₂ < 0,
          -- so this case is absurd. 
          exact absurd
            (lt_of_lt_of_le case1 hyp)
            (not_lt_of_le case12)
    | inr case2 => 
      cases (lt_or_ge 0 x₂) with
      | inl case21 => 
          -- We are in the second and first cases.
          rw [(if_neg (not_lt_of_le case2))]
          rw [(if_pos case21)]
          exact (le_of_lt rfl)
      | inr case22 => 
          rw [(if_neg (not_lt_of_le case2))]
          rw [(if_neg (not_lt_of_le case22))]

-------------------------------------------------
-- Feedforward neural nets
-------------------------------------------------
structure Net where
  graph : Graph ℕ ℚ
  activation : ℚ → ℚ
  rate : ℚ -- learning rate

structure BFNN extends Net where 
  -- The activation function is binary
  binary : ∀ (x : ℚ), 
    (activation x = 0) ∨ (activation x = 1)

  -- The activation function is nondecreasing
  activ_nondecr : ∀ (x₁ x₂ : ℚ),
    x₁ ≤ x₂ → activation x₁ ≤ activation x₂

  -- There is *some* input for which the activation is 1
  active_input : ℚ
  activ_pos : activation (is_active) = 1


-- Because our activation function is bounded above by 1,
-- if act(x₁) = 1
-- then any act(x₂) greater than act(x₁) also = 1
--------------------------------------------------------------------
lemma activation_from_inequality (net : BFNN) (x₁ x₂ : ℚ) :
  net.activation x₁ ≤ net.activation x₂
  → net.activation x₁ = 1 → net.activation x₂ = 1 := by
--------------------------------------------------------------------
  intro h₁ h₂
  cases net.binary x₂
  case inr actx₂_is_one => exact actx₂_is_one
  case inl actx₂_is_zero => 
    -- This case is impossible! 1 is not ≤ 0!
    rw [h₂] at h₁
    rw [actx₂_is_zero] at h₁
    exact absurd h₁ (by native_decide)

-- Put in examples file!  (We don't need to figure it out
-- right now!)
-- def myBFNN : BFNN :=
--   {
--     graph := graphA
--     activation := binary_step
--     rate := 1

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

/-══════════════════════════════════════════════════════════════════
  Forward propagation in a net
══════════════════════════════════════════════════════════════════-/

-- I would like to write 
--     List.sum [w * x | for w in weights, for x in lst],
-- but list comprehensions are harder to reason about.
def weighted_sum (weights : List ℚ) (lst : List ℚ) : ℚ :=
  List.foldr (· + ·) 0 (List.zipWith (· * ·) weights lst)


#eval weighted_sum [] []
#eval weighted_sum [1] [3.0]
#eval weighted_sum [1, 2.0, 3.0] [5.0, 5.0, 5.0]

-- Not well-defined behavior (we expect the weights and lst to be of equal size,
-- but this is left implicit.)
#eval weighted_sum [1, 2.0] [3.0]


--------------------------------------------------------------------
lemma weighted_sum_eq (fw₁ fw₂ fx₁ fx₂ : ℕ → ℚ) (ls : List ℕ) :
  let x₁ : List ℚ := List.map (fun i => fx₁ i) (List.range ls.length)
  let x₂ : List ℚ := List.map (fun i => fx₂ i) (List.range ls.length)
  let w₁ : List ℚ := List.map (fun i => fw₁ i) (List.range ls.length)
  let w₂ : List ℚ := List.map (fun i => fw₂ i) (List.range ls.length)
  
  (∀ i, (fw₁ i) * (fx₁ i) = (fw₂ i) * (fx₂ i))
  → weighted_sum w₁ x₁ = weighted_sum w₂ x₂ := by
--------------------------------------------------------------------
  -- Simplify the weighted sum down to 
  -- fw₁ i * fx₁ j = fw₂ i * fx₂ j
  intro x₁ x₂ w₁ w₂ h₁
  simp only [weighted_sum]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_right]
  rw [List.zipWith_map_right]
  simp
  congr 2

  -- Now we just need to show 
  -- fw₁ i * fx₁ i = fw₂ i * fx₂ i,
  -- but this was exactly our assumption.
  exact funext fun i => h₁ i
  
--------------------------------------------------------------------
lemma weighted_sum_le (fw₁ fw₂ fx₁ fx₂ : ℕ → ℚ) (ls : List ℕ) :
  let x₁ : List ℚ := List.map (fun i => fx₁ i) (List.range ls.length)
  let x₂ : List ℚ := List.map (fun i => fx₂ i) (List.range ls.length)
  let w₁ : List ℚ := List.map (fun i => fw₁ i) (List.range ls.length)
  let w₂ : List ℚ := List.map (fun i => fw₂ i) (List.range ls.length)
  
  (∀ i, (fw₁ i) * (fx₁ i) ≤ (fw₂ i) * (fx₂ i))
  → weighted_sum w₁ x₁ ≤ weighted_sum w₂ x₂ := by
--------------------------------------------------------------------
  intro x₁ x₂ w₁ w₂ h₁
  simp only [weighted_sum]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_left]
  rw [List.zipWith_map_right]
  rw [List.zipWith_map_right]
  simp
  rw [List.foldr_map]
  rw [List.foldr_map]
  
  -- By induction on the length of the list we're foldr-ing
  induction List.range (List.length ls)
  case nil => simp only [List.foldr]
  case cons i is IH => 
    simp only [List.foldr]
    exact add_le_add (h₁ i) IH

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
-- def distance (graph : Graph ℕ ℚ) (m n : ℕ) : ℕ :=
--   sorry


-- Accumulator-style helper function for 'layer'
-- Defined recursively on the *reverse* of the vertex list
-- (this means we are looking at vertices backwards -- each
--  vertex can only "see" the vertices preceding it.)
def layer_acc (net : BFNN) (n : ℕ) (ls : List ℕ) : ℕ :=
  match ls with
  | [] => 0
  | v :: rest =>
    if v = n then
      let layers := List.map (fun x => layer_acc net x rest) (preds net n)
      let max := layers.maximum

      match max with
      | some L => L + 1
      | none => 0

    else layer_acc net n rest

-- The layer of n in the net
def layer (net : BFNN) (n : ℕ) : ℕ :=
  layer_acc net n (net.graph.get_vertices.reverse)

-- The layer relation layer[m] ≤ layer[n] is well-founded
-- (i.e. it has a least element)
--------------------------------------------------------------------
lemma layer_wellfounded (net : BFNN) : 
  WellFounded (fun x y => layer net x ≤ layer net y) := by
--------------------------------------------------------------------
  exact WellFounded.wellFounded_iff_has_min.mpr 
    (fun S hS => sorry)


/-
-- Put in example file!
-- 0 jumps to 2, 1 jumps to 3, short connection from 1 to 2
def layer_test_graph : Graph ℕ ℚ :=
  ⟨[⟨0, [⟨2, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨1, [⟨2, 0.5⟩, ⟨3, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨2, []⟩, -- ⟨4, 0.5⟩
    ⟨3, [⟨4, 0.5⟩]⟩, -- remove ⟨4, 0.5⟩
    
    -- Add a new edge, and toggle which previous edge jumps to it.
    ⟨4, []⟩]⟩

def layer_test_net : BFNN :=
  { graph := layer_test_graph, activation := binary_step, rate := 1,
    binary := binary_step_is_binary,
    activ_nondecr := binary_step_nondecr, activ_pos := sorry
  }

#eval layer layer_test_net 0
#eval layer layer_test_net 1
#eval layer layer_test_net 2
#eval layer layer_test_net 3
#eval layer layer_test_net 4
-/

-- AXIOM: We assume the net is fully connected! 
-- (i.e. *transitively closed* in the paper, because
--  'fully connected' is often used in machine learning)
-- 
-- TODO: Write the equivalent 'transitively closed'
--   version, put it in the definition of BFNN,
--   and then prove this from that.
--   What I have here is the final statement I actually need.
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

  generalize hls : (List.reverse (Graph.get_vertices net.toNet.graph)) = ls
  induction ls
  case nil =>
    -- This case is impossible;
    -- m ∈ preds(n) means that there is *something* in the graph.
    -- This contradicts the fact that the graph is empty!
    simp [preds, Graph.predecessors, Graph.get_vertices] at h₁
    simp [Graph.get_vertices] at hls
    rw [hls] at h₁
    rw [List.map_nil] at h₁
    rw [List.filter_nil] at h₁
    exact False.elim ((List.mem_nil_iff _).mp h₁)
    

  case cons v rest IH =>
    simp only [layer_acc]
    generalize hmax_m : (List.map (fun x => layer_acc net x rest) (preds net m)).maximum = max_m
    generalize hmax_n : (List.map (fun x => layer_acc net x rest) (preds net n)).maximum = max_n

    -- We branch out all of the possible cases
    -- (we have 4 branches from the 'if-then-else's, 
    -- and more for the 'match'es)
    by_cases v = m
    case pos => 
      rw [if_pos h]
      by_cases v = n
      case pos => 
        rw [if_pos h]
        
        match max_n with
        | none => -- This case is also impossible;
          -- m ∈ preds(n) means that there is *some* maximum in preds(n),
          -- which contradicts the fact that the max is empty.
          sorry

        | some L => 
          match max_m with
          | none => exact Nat.succ_pos L
          | some K => -- This is the tricky case!
            simp
            sorry

      case neg => 
        rw [if_neg h]
        match max_m with
        | none => 
          simp
          sorry
        | some K => sorry

    case neg =>
      rw [if_neg h]
      by_cases v = n
      case pos => 
        rw [if_pos h]
        match max_n with
        | none => sorry
        | some L => sorry

      case neg => 
        rw [if_neg h]
        exact IH sorry

-- NOTE: Although 'do' notation might be more readable here,
--       I avoid it because it's hard to reason about.
noncomputable
def activ (net : BFNN) (prev_activ : List ℚ) (n : ℕ) : Prop :=
  let preds := preds net n
  let weights := List.map (fun i => 
      let m := preds.get! i
      net.graph.getEdgeWeight m n) 
    (List.range preds.length)
  let weight_sum := weighted_sum weights prev_activ
  let curr_activ := net.activation weight_sum
  curr_activ = 1


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
-- 
-- NOTE: Although 'do' notation might be more readable here,
--       I avoid it because it's hard to reason about.
@[simp]
def propagate_acc (net : BFNN) (S : Set ℕ) (n : ℕ) (L : ℕ) : Prop :=
  match L with
  | Nat.zero => n ∈ S
  | Nat.succ _ =>
    let preds := preds net n
    let prev_activ := List.map (fun i => 
      let m := preds.get! i
      if propagate_acc net S m (layer net m) then 1 else 0) 
        (List.range preds.length)
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
  let prev_activ := List.map (fun i => 
    let m := preds.get! i
    if propagate_acc net S m (layer net m) then 1 else 0) 
      (List.range preds.length)
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


-- If A and B agree on all the predecessors of n, then they agree on n.
-- This lemma is extremely inefficient to use.  In order to make it
-- remotely usable, we've simplified everything down to unreadable
-- garbage.  In order to make use of it, I recommend:
--   - Applying 'simp' to your 'activ' hypotheses (get rid of any let's)
--   - Use 'exact' instead of 'apply' (exit tactic mode)
-- 
--------------------------------------------------------------------
lemma activ_agree (net : BFNN) (A B : Set ℕ) (n : ℕ) :
  (∀ (m : ℕ), m ∈ preds net n → (m ∈ A ↔ m ∈ B))
  → activ net (List.map (fun i => 
      let m := (preds net n).get! i
      if A m then 1 else 0) 
        (List.range (preds net n).length)) n
  → activ net (List.map (fun i => 
      let m := (preds net n).get! i
      if B m then 1 else 0) 
        (List.range (preds net n).length)) n := by
--------------------------------------------------------------------
  intro h₁ h₂
  simp only [activ]
  simp only [activ] at h₂
  convert ← h₂ using 6

  rename_i i
  let m := (preds net n).get! i
  have h₃ : m ∈ (preds net n) := get!_mem (preds net n) i
  exact h₁ m h₃

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
  case hi L IH =>
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

          -- We abbreviate the two 'simp'ed sets for convenience.
          let S₁ := fun m => propagate_acc net (fun n => 
            propagate_acc net S n (layer net n)) m (layer net m)
          let S₂ := fun m => propagate_acc net S m (layer net m)
          
          -- Apply IH to the predecessors
          have h₂ : ∀ (m : ℕ), m ∈ preds net n → (S₁ m ↔ S₂ m) := by
            simp only [Membership.mem] -- really just want to unfold the let
            intro m hm
            generalize hLm : layer net m = Lm
            have h₃ : Lm ≤ L := by
              rw [symm hLm]
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact preds_decreasing net m n hm
            exact (symm (IH Lm h₃ m hLm).to_eq).to_iff

          -- Apply the activ_agree lemma
          simp
          simp at h₁
          exact activ_agree _ S₁ S₂ _ h₂ h₁


-- This is essentially Hannes' proof.
-- TODO: For consistency's sake, replace inner proof with
--   application of 'activ_agree'
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
          convert h₃ using 4
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
          convert h₃ using 4
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
inductive focusedPath (g : Graph ℕ ℚ) (S : Set ℕ) : ℕ → ℕ → Prop where
  | trivial {u : ℕ} :
      u ∈ S → focusedPath g S u u
  | from_path {u v w : ℕ} : 
      focusedPath g S u v → g.hasEdge v w → w ∈ S → focusedPath g S u w

-- focusedPath is transitive
--------------------------------------------------------------------
theorem focusedPath_trans {u v w : ℕ} (g : Graph ℕ ℚ) (A : Set ℕ) :
  focusedPath g A u v → focusedPath g A v w → focusedPath g A u w := by
--------------------------------------------------------------------
  intro (h₁ : focusedPath g A u v)
  intro (h₂ : focusedPath g A v w)

  induction h₂
  case trivial _ => exact h₁
  case from_path x y _ edge_xy hy path_ux => 
    exact focusedPath.from_path path_ux edge_xy hy

-- focusedPath is contained in A
--------------------------------------------------------------------
theorem focusedPath_subset {u v : ℕ} (g : Graph ℕ ℚ) (A : Set ℕ) :
  focusedPath g A u v → u ∈ A := by
--------------------------------------------------------------------
  intro h₁

  induction h₁
  case trivial hA => exact hA
  case from_path _ _ _ _ _ hA => exact hA

-- If there's a path from m to n,
-- then m's layer in the net cannot be bigger than n's layer.
-- WARNING: I think this is incorrect!!!
-- --------------------------------------------------------------------
-- lemma focusedPath_layer {m n : ℕ} (net : BFNN) (A : Set ℕ) :
--   focusedPath net.graph A m n
--   → layer net m < layer net n := by
-- --------------------------------------------------------------------
--   intro (h₁ : focusedPath net.graph A m n)

--   induction h₁
--   case trivial _ => sorry
--   case from_path x y _ edge_xy hy path_mx =>
--     sorry

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

-- If A ∩ B is empty, then there are no nodes reachable
-- from B within A.
-- (This does *not* follow from [reach_is_extens]!)
--------------------------------------------------------------------
theorem reach_empty_of_inter_empty (net : BFNN) : ∀ (A B : Set ℕ),
  (A ∩ B) = ∅ → reachable net A B = ∅ := by
--------------------------------------------------------------------
  intro A B
  rw [← Set.not_nonempty_iff_eq_empty]
  rw [← Set.not_nonempty_iff_eq_empty]
  
  -- Start a proof by contraposition, and simplify
  contrapose
  intro h₁
  rw [Classical.not_not]
  rw [Classical.not_not] at h₁

  -- Since Reach(A, B) is nonempty, we have n ∈ Reach(A, B).
  -- We argue that the m ∈ B that reaches n must be m ∈ A ∩ B.
  match h₁ with
  | ⟨n, hn⟩ => 
    match hn with
    | ⟨m, hm⟩ => 
      -- m ∈ B is easy; we show inductively that m ∈ A as well.
      induction hm.2
      case trivial hmA => exact ⟨m, ⟨hmA, hm.1⟩⟩
      case from_path x y path_mx _ _ IH => 
        exact IH ⟨m, ⟨hm.1, path_mx⟩⟩ ⟨hm.1, path_mx⟩


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


-- Reach is closed under union
-- (This is really a consequence of monotonicity)
--------------------------------------------------------------------
theorem reach_union (net : BFNN) : ∀ (S A B : Set ℕ),
  reachable net S (A ∪ B) = (reachable net S A) ∪ (reachable net S B) := by
--------------------------------------------------------------------
  intro S A B
  apply ext
  intro n
  apply Iff.intro
  
  -- Backwards direction
  -- (easy; A, B ⊆ A ∪ B, so we just apply monotonicity)
  case mpr => 
    intro h₁
    cases h₁
    case inl h₂ => exact reach_is_monotone _ _ _ _ (subset_union_left _ _) h₂
    case inr h₂ => exact reach_is_monotone _ _ _ _ (subset_union_right _ _) h₂

  -- Forward direction
  case mp => 
    intro h₁

    -- We have a path from m ∈ A ∪ B to n;
    -- from here we go by cases; either m ∈ A or m ∈ B.
    -- In either case, the path from m ⟶ n gives us n ∈ Reach(_).
    match h₁ with
    | ⟨m, hm⟩ => 
      cases hm.1
      case inl h₂ => exact Or.inl ⟨m, ⟨h₂, hm.2⟩⟩
      case inr h₂ => exact Or.inr ⟨m, ⟨h₂, hm.2⟩⟩


/-══════════════════════════════════════════════════════════════════
  Reach-Prop Interaction Properties
══════════════════════════════════════════════════════════════════-/

-- I actually don't need to assume anything in particular here...
-- which is odd, I suppose.  (I'd expect it to be different
-- from Elite Upgrade somehow...)
      
/-══════════════════════════════════════════════════════════════════
  Naive (Unstable) Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- A function to map edges in the graph.  
-- We update the edge weight x₁ ⟶ x₂, but we also allow information 
-- about the *nodes* x₁ and x₂.
-- Credit to Peter Kementzey for the original mapEdges function.
def map_edges (g : Graph ℕ ℚ) (f : ℕ → ℕ → ℚ → ℚ) : Graph ℕ ℚ := ⟨
  g.vertices.map (fun vertex => 
    { vertex with successors := vertex.successors.map (fun 
      ⟨target, weight⟩ => ⟨target, f vertex.label target weight⟩
  )})
⟩

--------------------------------------------------------------------
lemma map_edges_apply (g : Graph ℕ ℚ) (f : ℕ → ℕ → ℚ → ℚ) (m n : ℕ) :
  (map_edges g f).getEdgeWeight m n = (f m n (g.getEdgeWeight m n)) := by
--------------------------------------------------------------------
  -- I have no idea... this one's tough, and it's hard to see
  -- what's going on.
  -- TODO: Reasoning about weights is hard!  Redefine getEdgeWeight!
  simp only [Graph.getEdgeWeight]

  match List.find? (fun x => decide (x.fst = n)) g.vertices[m]!.successors with
  | none => sorry
  | some ⟨_, weight⟩ => sorry
  
  /-
  split
  case _ op₁ target₁ weight₁ hop₁ => 
    split
    case _ op₂ target₂ weight₂ hop₂ => sorry
    case _ op₂ hop₂ => sorry
  case _ op₁ hop₁ => 
    split
    case _ op₂ target₂ weight₂ hop₂ => sorry
    case _ op₂ hop₂ => sorry
  -/

-- For every m ⟶ n where m, n ∈ Prop(S), increase the weight
-- of that edge by η * act(m) * act(n).
noncomputable
def graph_update (net : BFNN) (g : Graph ℕ ℚ) (S : Set ℕ) : Graph ℕ ℚ :=
  map_edges g (fun m n weight => 
    let activ_m := if m ∈ propagate net S then 1 else 0
    let activ_n := if n ∈ propagate net S then 1 else 0
    weight + (net.rate * activ_m * activ_n))



-- This graph update does not affect the vertices of the graph.
--------------------------------------------------------------------
lemma graph_update_vertices (net : BFNN) (g : Graph ℕ ℚ) (S : Set ℕ) :
  (graph_update net g S).get_vertices = g.get_vertices := by
--------------------------------------------------------------------
  simp only [graph_update, map_edges]
  simp only [Graph.get_vertices]

  -- Go in and compose the maps.  This seems to do the trick.
  conv => lhs; rw [List.map_map]


-- This graph update does not affect the *successor/edge* structure
-- of the graph (it only affects weights!!!)
--------------------------------------------------------------------
lemma graph_update_successors (net : BFNN) (g : Graph ℕ ℚ) (S : Set ℕ) (n : ℕ) :
  (graph_update net g S).successors n = g.successors n := by
--------------------------------------------------------------------
  -- Simplify definitions
  simp only [Graph.successors]
  rw [graph_update_vertices]
  simp [graph_update, map_edges] 
  -- NOTE: FULL simp because there's a hidden dependent argument
  --   here we need to knock out.
  
  -- Rewrite 'unzip's as 'map's
  rw [List.unzip_eq_map _]
  rw [List.unzip_eq_map _]
  simp only [Prod.fst]

  -- Get to the heart of the expression
  congr
  funext m
  apply Bool.decide_congr

  -- Our goal is to now show that when we *only* consider the target
  -- vertices, the graph_update is essentially the identity function.
  -- By induction on the graph's list of vertices:
  induction g.vertices
  case nil => 
    simp only [Graph.successor_pairs]

  case cons v rest IH => 
    simp only [Graph.successor_pairs]

    -- By cases; either v.label = n or not.  If so, we go in
    -- and compose the maps.  Otherwise we just apply our IH.
    by_cases (v.label = n)
    case pos => 
      rw [if_pos h]
      rw [if_pos h]
      rw [List.map_map]
      simp

    case neg =>
      rw [if_neg h]
      rw [if_neg h]
      exact IH

-- This graph update preserves whether the graph is acyclic.
--------------------------------------------------------------------
lemma graph_update_acyclic (net : BFNN) (g : Graph ℕ ℚ) (S : Set ℕ) :
  (graph_update net g S).is_acyclic ↔ g.is_acyclic := by
--------------------------------------------------------------------
  simp only [Graph.is_acyclic]
  apply Iff.intro
  
  case mp => sorry
  case mpr =>
    intro g_acyclic
    intro u v
    intro path_uv
    intro path_vu

    -- We have a path in the updated graph from u to v
    -- and another path from v to u.
    -- We now need to show that u = v.
    -- By induction on the length of this first path.
    induction path_uv
    case trivial => exact rfl
    case from_path x y path_ux edge_xy IH => 
      sorry

-- A single step of Hebbian update.
-- Propagate S through the net, and then increase the weights
-- of all the edges x₁ ⟶ x₂ involved in that propagation
-- by η * x₁ * x₂.
noncomputable
def hebb (net : BFNN) (S : Set ℕ) : BFNN :=
{ net with
  graph := graph_update net net.graph S
}


/-══════════════════════════════════════════════════════════════════
  Properties of Single-Iteration Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- First, we check that a single round of hebb preserves whether
-- the graph is acyclic. (This is a rehash of graph_update_acyclic,
-- but it helps to write it out so we can lift it later to hebb_star.)
--------------------------------------------------------------------
lemma hebb_once_acyclic (net : BFNN) (S : Set ℕ) : 
  (hebb net S).graph.is_acyclic = net.graph.is_acyclic := by
--------------------------------------------------------------------
  simp only [hebb]
  rw [graph_update_acyclic]

-- A single round of Hebbian update does not affect the vertices
-- of the graph.
--------------------------------------------------------------------
theorem hebb_once_vertices (net : BFNN) (S : Set ℕ) : 
  (hebb net S).graph.get_vertices = net.graph.get_vertices := by
--------------------------------------------------------------------
  simp only [hebb]
  rw [graph_update_vertices]

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
--------------------------------------------------------------------
theorem hebb_once_layers (net : BFNN) (S : Set ℕ) : 
  layer (hebb net S) n = layer net n := by
--------------------------------------------------------------------
  simp only [layer]
  rw [hebb_once_vertices net S] -- vertices are the same

  -- By induction on the reverse of the graph's vertex list
  -- (We are looking at vertices backwards -- each
  --  vertex can only "see" the vertices preceding it.)
  induction List.reverse (Graph.get_vertices net.toNet.graph) generalizing n
  case nil => 
    simp only [layer_acc]
  case cons v rest IH => 
    simp only [layer_acc]

    -- By cases; either vertex.label = n or not.
    -- If so, this follows from our IH and the fact that the predecessors
    -- are the same in both nets.
    by_cases v = n
    case pos => 
      rw [if_pos h]
      rw [if_pos h]
      rw [hebb_once_preds]
      congr
      funext m
      exact @IH m

    -- If not, just apply our IH
    case neg => 
      rw [if_neg h]
      rw [if_neg h]
      exact IH

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

    -- There is some m with focused path from m to n in the *updated* net
    match h₁ with
    | ⟨m, hm⟩ =>
      induction hm.2
      case trivial hma => exact reach_is_extens _ _ _ ⟨hma, hm.1⟩
      case from_path x y path_mx edge_xy hy IH =>
        -- First, apply our IH to get x ∈ Reach(A, B)
        have h₂ : x ∈ reachable (hebb net A) A B := ⟨m, ⟨hm.1, path_mx⟩⟩
        have h₃ : x ∈ reachable net A B := IH h₂ ⟨hm.1, path_mx⟩

        -- So there is some u ∈ B with focused path from u to x
        -- (in the *original* net)
        -- We extend this path with the edge from x to y.
        match h₃ with
        | ⟨u, hu⟩ =>

          -- We have an edge from x to y in the *updated* net,
          -- but we have to bring it down to the *original* net.
          have h₄ : Graph.hasEdge net.graph x y = true := by
            rw [← edge_from_preds]
            rw [← edge_from_preds] at edge_xy
            convert edge_xy using 1
            exact symm (hebb_once_preds _ _ _)

          exact ⟨u, ⟨hu.1, (focusedPath.from_path hu.2 h₄ hy)⟩⟩

  -- This direction is very similar.
  case mpr => 
    intro h₁

    -- There is some m with focused path from m to n in the *original* net
    match h₁ with
    | ⟨m, hm⟩ =>
      induction hm.2
      case trivial hma => exact reach_is_extens _ _ _ ⟨hma, hm.1⟩
      case from_path x y path_mx edge_xy hy IH =>
        -- First, apply our IH to get x ∈ Reach(A, B)
        have h₂ : x ∈ reachable net A B := ⟨m, ⟨hm.1, path_mx⟩⟩
        have h₃ : x ∈ reachable (hebb net A) A B := IH h₂ ⟨hm.1, path_mx⟩
        
        -- So there is some u ∈ B with focused path from u to x
        -- (in the *updated* net)
        -- We extend this path with the edge from x to y.
        match h₃ with
        | ⟨u, hu⟩ =>

          -- We have an edge from x to y in the *original* net,
          -- but we have to bring it down to the *updated* net.
          have h₄ : Graph.hasEdge (hebb net A).graph x y = true := by
            rw [← edge_from_preds]
            rw [← edge_from_preds] at edge_xy
            convert edge_xy using 1
            exact hebb_once_preds _ _ _
            
          exact ⟨u, ⟨hu.1, (focusedPath.from_path hu.2 h₄ hy)⟩⟩

-- If m ∉ Prop(A) or n ∉ Prop(A), then the weight of m ⟶ n in 
-- the *once* updated net is the same as in the original net.
--------------------------------------------------------------------
theorem hebb_once_weights_eq (net : BFNN) :
  (m ∉ propagate net A ∨ n ∉ propagate net A)
  → (hebb net A).toNet.graph.getEdgeWeight m n =
    net.graph.getEdgeWeight m n := by
--------------------------------------------------------------------
  intro h₁
  simp only [hebb, graph_update]
  rw [map_edges_apply _ _ _ _]

  -- We have two cases; either m ∉ Prop(A) or n ∉ Prop(A).
  -- In either case, the term that we're updating by reduces 
  -- to weight + 0 = weight.
  cases h₁
  case inl h₂ => 
    rw [if_neg h₂]
    simp
  case inr h₂ => 
    rw [if_neg h₂]
    simp

-- The weights of the new net are nondecreasing
-- (One round of Hebbian update can only increase the weights)
--------------------------------------------------------------------
theorem hebb_once_weights_le (net : BFNN) :
  net.graph.getEdgeWeight m n ≤ 
  (hebb net A).toNet.graph.getEdgeWeight m n := by
--------------------------------------------------------------------
  simp only [hebb, graph_update]

  -- how do I just get the 'weight + blah' from the net??

  sorry -- Weights are hard to reason about,
        -- because of the 'match'!  Maybe redefine getEdgeWeights!

/-
intro h₁
simp only [hebb, graph_update]
rw [map_edges_apply _ _ _ _]

-- We have two cases; either m ∉ Prop(A) or n ∉ Prop(A).
-- In either case, the term that we're updating by reduces 
-- to weight + 0 = weight.
cases h₁
case inl h₂ => 
  rw [if_neg h₂]
  simp
case inr h₂ => 
  rw [if_neg h₂]
  simp
-/

/-══════════════════════════════════════════════════════════════════
  "Iterated"/Fixed-Point Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- We score neurons by the total sum of *negative* weights coming 
-- into them.  The neuron with the lowest score is the least likely
-- to activate (in the worst case where all of its negative signals
-- activate but none of its positive ones do).  If a neuron has
-- no negative incoming weights, we give it a score of 0.
def neg_weight_score (net : BFNN) (n : ℕ) : ℚ :=
  List.foldr (· + ·) 0 (List.map (fun m => 
    if net.graph.getEdgeWeight m n < 0 then 
      net.graph.getEdgeWeight m n
    else 0) 
    (preds net n))


-- NOTE: If there are no nodes to score, a value of 0 is fine.
def min_score (net : BFNN) : WithTop ℚ :=
  let scores := List.map (fun n => neg_weight_score net n) net.graph.get_vertices
  scores.minimum


-- For a *given* n, the neg_weight_score is smaller than
-- any possible weighted sum over activated predecessors of n.
-- (i.e. no matter what the activation list 'x' is.)
--------------------------------------------------------------------
lemma neg_weight_score_le (net : BFNN) (n : ℕ) (fx₁ : ℕ → Bool) :
  let x : List ℚ := List.map (fun m => if fx₁ m then 1 else 0) (preds net n)
  let w : List ℚ := List.map (fun m => 
    Graph.getEdgeWeight net.graph m n) (preds net n)
  
  (neg_weight_score net n) ≤ (weighted_sum w x) := by
--------------------------------------------------------------------
  intro x w
  simp only [neg_weight_score, weighted_sum]
  
  -- First, we simplify the foldr and zipWith
  rw [List.foldr_map]
  rw [List.zipWith_map]
  rw [List.zipWith_same]

  -- By induction on the predecessor list
  induction preds net n
  case nil => simp only [List.filter, List.foldr]
  case cons m ms IH => 
    simp only [List.foldr]

    -- We break up the if-statement.
    by_cases (net.graph.getEdgeWeight m n < 0)
    
    -- In this case, we need to show that
    --     weight ≤ weight * (fx₁ m),
    -- which is true because (fx₁ m) can only be 0 or 1,
    -- and weight < 0.
    case pos =>
      rw [if_pos h]

      by_cases (fx₁ m)
      case pos => 
        rw [if_pos h]
        apply add_le_add _ IH
        simp
      case neg => 
        rename_i neg_weight
        rw [if_neg h]
        apply add_le_add _ IH
        rw [Rat.mul_zero]
        exact le_of_lt neg_weight
      
    -- In this case, we need to show that
    --     0 ≤ weight * (fx₁ m),
    -- which is true because (fx₁ m) can only be 0 or 1,
    -- and weight ≥ 0! 
    case neg => 
      rw [if_neg h]

      by_cases (fx₁ m)
      case pos =>
        rename_i pos_weight
        rw [if_pos h]
        rw [Rat.mul_one]
        apply add_le_add _ IH
        exact le_of_not_lt pos_weight
      case neg =>
        rw [if_neg h]
        rw [Rat.mul_zero]
        exact add_le_add rfl IH

-- The *minimum* score is smaller than any possible weighted sum
-- (over activated predecessors of n) *for all n*.
--------------------------------------------------------------------
lemma min_score_le (net : BFNN) (n : ℕ) (fx₁ : ℕ → Bool) :
  let x : List ℚ := List.map (fun m => if fx₁ m then 1 else 0) (preds net n)
  let w : List ℚ := List.map (fun m => 
    Graph.getEdgeWeight net.graph m n) (preds net n)
  
  min_score net ≤ (weighted_sum w x) := by
--------------------------------------------------------------------
  intro x w
  simp only [min_score]
  apply le_of_not_lt
  apply List.not_lt_minimum_of_mem'
  
  sorry
  -- apply le_trans _ (neg_weight_score_le net n fx₁)


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
-- our activation function is guranteed to be 1, and η is the
-- learning rate, then we return
-- 
-- (X - n_score) / η   *(I think!)*
-- UPDATE: we can iterate a different number of times
-- FOR EACH m, n!  So we should take the *max* of all these!
def no_times (net : BFNN) (S : Set ℕ) : ℕ :=
  -- mcs is the "max composite score"
  let (comp_scores : List ℚ) := sorry
    -- net.active_input - sorry
  let (mcs : WithBot ℚ) := List.maximum comp_scores

  -- Ensure that the number of iterations is a *positive*
  -- natural number.
  if mcs > 0 then 
    sorry
    -- abs (round mcs)
  else 1

  -- HOW TO ROUND?  HOW TO DIVIDE?
  -- net.active_input
  
  -- match net.activ_pos with
  -- | ⟨t, ht⟩ => sorry 
  
  -- let x := choose net.activ_pos
  -- have h₁ : net.activation x = 1 := sorry

  -- let n_min := @List.minimum (Vertex ℕ ℚ) sorry sorry net.graph.vertices.toList
  -- let n_score := sorry
  -- sorry

lemma no_times_pos (net : BFNN) (S : Set ℕ) :
  0 < no_times net S := by
  sorry


-- For every m ⟶ n where m, n ∈ Prop(S), increase the weight
-- of that edge by (no_times) * η * act(m) * act(n).
noncomputable
def graph_update_star (net : BFNN) (g : Graph ℕ ℚ) (S : Set ℕ) : Graph ℕ ℚ :=
  map_edges g (fun m n weight => 
    let activ_m := if m ∈ propagate net S then 1 else 0
    let activ_n := if n ∈ propagate net S then 1 else 0
    weight + (↑(no_times net S) * net.rate * activ_m * activ_n))

-- Iterated Hebbian Update
-- 
-- First, note that if we iterate 'hebb' or 'graph_update' in the
-- usual way, all Prop(S) will change with each iteration.  
-- So instead, we bake the iteration into the weight update:
-- We keep adding to the weights relative to the *original* net's
-- Prop(S) values. 
-- 
-- Second, rather than iterating up to a fixed point, for unstable
-- Hebbian learning it's enough to take a specific finite number
-- of iterations.  In this case, that number is 'hebb_unstable_point'.
-- For more complicated learning algorithms, we would need to build
-- up lemmas about the fixed point of a graph.
-- 
-- FUTURE: Consider re-doing this using limits of graphs/categories
noncomputable
def hebb_star (net : BFNN) (S : Set ℕ) : BFNN :=
{ net with
  graph := graph_update_star net net.graph S
}


/-══════════════════════════════════════════════════════════════════
  Properties of "Iterated" Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- This lemma allows us to "lift" equational properties of hebb 
-- to hebb_star.  (This holds *because* hebb_star is the fixed point
-- of hebb.)
--------------------------------------------------------------------
theorem hebb_lift (net : BFNN) (S : Set ℕ) (P : BFNN → α) : 
  (P (hebb net S) = P net)
  → (P (hebb_star net S) = P net) := by
--------------------------------------------------------------------
  intro h₁
  
  -- By induction on the unstable point of the net
  -- (we don't actually need to know what the unstable point *is*
  --  for this lemma to hold.)
  generalize hpt : (no_times net S) = pt
  induction pt generalizing net
  case zero => 
    -- This case is impossible; hebb_unstable_point cannot be zero!
    exact absurd hpt (ne_of_gt (no_times_pos _ _))

  case succ k IH =>
    -- simp only [hebb] at h₁
    simp only [hebb_star]
    sorry
    -- rw [hpt]
    -- simp only [graph_update] at h₁
    -- simp only [graph_update_star]

    -- convert h₁ using 9
    -- convert h₁ using 3
    -- rename_i x₁ x₂ w

    -- sorry
    


-- Hebbian update hebb_star preserves the acyclicness of the graph.
-- (So the updated net is still acyclic.)
-- [LIFTED from hebb_once_acyclic]
--------------------------------------------------------------------
lemma hebb_acyclic (net : BFNN) (S : Set ℕ) : 
  (hebb_star net S).graph.is_acyclic = net.graph.is_acyclic := by
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => x.graph.is_acyclic) (hebb_once_acyclic _ _)

-- Hebbian update hebb_star does not affect the vertices of the graph.
--------------------------------------------------------------------
theorem hebb_vertices (net : BFNN) (S : Set ℕ) : 
  (hebb_star net S).graph.get_vertices = net.graph.get_vertices := by
--------------------------------------------------------------------
  exact hebb_lift _ _ (fun x => x.graph.get_vertices) (hebb_once_vertices _ _)

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


-- If m ∉ Prop(A) or n ∉ Prop(A), then the edge m ⟶ n was not
-- increased by Hebbian update.  So its weight in the updated
-- net is the same as its weight in the original net.
-- Lifted from hebb_once_weights
--------------------------------------------------------------------
theorem hebb_weights_eq (net : BFNN) : 
  (m ∉ propagate net A ∨ n ∉ propagate net A)
  → ((hebb_star net A).toNet.graph.getEdgeWeight m n =
    net.graph.getEdgeWeight m n) := by
--------------------------------------------------------------------
  intro h₁
  exact hebb_lift _ _ (fun x => x.toNet.graph.getEdgeWeight m n) 
    (hebb_once_weights_eq _ h₁)

 
-- The weights of the new net are nondecreasing
-- (Hebbian update can only increase the weights)
-- Note that we *cannot* lift this property straightforwardly,
-- since it's an inequality.
--------------------------------------------------------------------
theorem hebb_weights_le (net : BFNN) :
  net.graph.getEdgeWeight m n ≤ 
  (hebb_star net A).toNet.graph.getEdgeWeight m n := by
--------------------------------------------------------------------
  simp only [hebb_star]
  generalize hpt : (no_times net A) = pt
  
  -- By induction on the unstable point of the net
  induction pt
  case zero => 
    -- This case is impossible; hebb_unstable_point cannot be zero!
    exact absurd hpt (ne_of_gt (no_times_pos _ _))
  case succ k IH => 
    simp only [graph_update_star]
    sorry -- Graph weights are hard to reason about because of 'match'!


/-══════════════════════════════════════════════════════════════════
  The more interesting/crucial properties
══════════════════════════════════════════════════════════════════-/

-- The lemma for 'activ' and 'hebb', essentially:
-- activ net prev_activ n  ⟶  activ (hebb_star net A) prev_activ n
--------------------------------------------------------------------
lemma hebb_activ_nondecreasing (net : BFNN) (A S : Set ℕ) (n : ℕ) :
  activ net (List.map (fun i => 
      let m := (preds net n).get! i
      if S m then 1 else 0) 
        (List.range (preds net n).length)) n
  → activ (hebb_star net A) (List.map (fun i => 
      let m := (preds net n).get! i
      if S m then 1 else 0) 
        (List.range (preds net n).length)) n := by
--------------------------------------------------------------------
  simp only [activ]
  rw [hebb_preds]
  
  apply activation_from_inequality _ _ _
  apply net.activ_nondecr _ _
  apply weighted_sum_le _ _ _ _
  intro i
  
  -- We split by cases; either m ∉ B in the original net,
  -- and both sides reduce to 0;
  -- or m ∈ B, in which case we check that the weight for
  -- m ⟶ n in the original net is ≤ the updated net weight.  
  generalize hm : (List.get! (preds net n) i) = m
  by_cases (S m)
  case neg => 
    rw [if_neg h]
    simp
  case pos => 
    rw [if_pos h]
    simp [hebb_weights_le _]


-- If n ∉ Prop(A), then activ (hebb_star net A) _ n = activ net _ n.
--------------------------------------------------------------------
theorem hebb_activ_equal₁ (net : BFNN) (A : Set ℕ) (prev_activ : List ℚ) :
  n ∉ propagate net A
  → (activ (hebb_star net A) prev_activ n ↔ activ net prev_activ n) := by
--------------------------------------------------------------------
  intro h₁
  apply Eq.to_iff
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  conv =>
    lhs; enter [1, 2, 1, 1, i]
    rw [hebb_weights_eq _ (Or.inr h₁)]


-- If every *active* predecessor of n ∉ Prop(A), then
-- activ (hebb_star net A) _ n = activ net _ n.
-- Like activ_agree, we have to simplify the statement of this
-- lemma in order for Lean to be able to infer types efficiently.
--------------------------------------------------------------------
theorem hebb_activ_equal₂ (net : BFNN) (A S : Set ℕ) :
  (∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net S))

  → (activ (hebb_star net A) (List.map (fun i => 
      if propagate_acc net S ((Graph.predecessors net.toNet.graph n).get! i) 
        (layer net ((Graph.predecessors net.toNet.graph n).get! i)) 
      then 1 else 0) 
        (List.range (Graph.predecessors net.toNet.graph n).length)) n
  ↔ activ net (List.map (fun i =>
      if propagate_acc net S ((Graph.predecessors net.toNet.graph n).get! i) 
        (layer net ((Graph.predecessors net.toNet.graph n).get! i)) 
      then 1 else 0) 
        (List.range (Graph.predecessors net.toNet.graph n).length)) n) := by
--------------------------------------------------------------------
  intro h₁
  apply Eq.to_iff
  
  -- Do simplifications to get to the weighted sum
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  apply congr_arg (fun x => Net.activation net.toNet x = 1)

  -- The weighted sums are equal, ∑ w₁ x₁ = ∑ w₂ x₂,
  -- if all of their entries are equal, w₁ᵢ * x₁ᵢ = w₂ᵢ * x₂ᵢ
  apply weighted_sum_eq
  intro i
  generalize hm : List.get! (Graph.predecessors net.toNet.graph n) i = m

  -- We have two cases;
  by_cases m ∈ propagate net S

  -- In this case, the RHS's reduce to 1, and we
  -- just need to argue that the weights are the same
  case pos => 
    -- First, notice that m ∉ Prop(A).
    have h₂ : m ∈ preds net n := by
      rw [← hm]
      exact get!_mem _ _
    have h₃ : m ∉ propagate net A := by
      simp only [Inter.inter, Set.inter, Membership.mem, Set.Mem, setOf] at h₁
      conv at h₁ => enter [x, hx]; rw [not_and']
      exact h₁ m h₂ h
      
    -- Now we simplify and show that the weights are the same
    simp only [propagate, Membership.mem, Set.Mem] at h
    rw [if_pos h]
    simp [hebb_weights_eq _ (Or.inl h₃)]
    
  -- Otherwise, the RHS's reduce to 0, and so the
  -- weighted sums are trivially equal
  case neg => 
    simp only [propagate, Membership.mem, Set.Mem] at h
    rw [if_neg h]
    simp
    

/-
INTUITION:
Prop$(S) = propagate (hebb_star net A) B

m ∈ Prop$(B)
m, n ∈ Prop(A)
m ⟶ n
-------------
n ∈ Prop$(B)

∑ w*(mᵢ, n) * x_mᵢ = 
  w*(m, n) * x_m (=1) + ∑ rest
  w*(m, n) + ∑ rest
  ≥ w*(m, n) + (N - 1) * min_score
  = (w(m, n) + no_times * η) + (N - 1) * min_score
  [since w(m, n) ≥ min_score, always] 
  ≥  (min_score + no_times * η) + min_score * (N - 1)
  
  min_score + (no_times * η) + min_score * (N - 1) ≥ thres
  SOLVE FOR NO_TIMES:
  no_times = round ((thres - (N - 1) * min_score - min_score)  / η)
           = round ((thres - N * min_score) / η)  <<<-------------

min_score : minimum possible weighted sum across *all* n ∈ Net 
N : num nodes in Net

GOAL: thres ≤ ∑ w$(mᵢ, n) * x_mᵢ

Act (thres) = 1
Act (∑ w$(mᵢ, n) * x_mᵢ) = 1
GOAL: n activated by (active) mᵢ ∈ preds(n)
-----------------------
n ∈ Prop$(B)
-/


-- -- If *some* predecessor of n is ∈ Prop(A), and n ∈ Prop(A), then
-- -- if m is activated in (hebb_star net) then n is too
-- -- (the activation automatically goes through in (hebb_star net))
--------------------------------------------------------------------
theorem hebb_activated_by (net : BFNN) (A B : Set ℕ) :
  let preds := preds net n
  let prev_activ := List.map (fun i => 
    let m := preds.get! i
    if propagate_acc (hebb_star net A) B m (layer (hebb_star net A) m) 
    then 1 else 0) 
      (List.range preds.length)

  n ∈ propagate net A
  → m ∈ preds ∧ m ∈ propagate net A  
  → m ∈ propagate (hebb_star net A) B
  → activ (hebb_star net A) prev_activ n := by
--------------------------------------------------------------------
  intro preds
  intro prev_activ
  intro h₁
  intro h₂
  intro h₃

  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  
  -- NOTE: This is one of the most crucial steps of the whole proof!
  -- We have some point 't' at which the activation = 1.
  -- Since the activation function is nondecreasing, we just have
  -- to show that the inner weighted sum ≥ t. 
  
  -- 'net.active_input' is t; 'net.activ_pos' says that t is active.

  -- match net.activ_pos with
  -- | ⟨t, ht⟩ => 
  apply activation_from_inequality _ (net.active_input) _ _ (net.activ_pos)
  apply net.activ_nondecr _ _
  
  sorry

        -- I have the proof written on paper, I should consult that.
        -- Depends on things like the monotonicity of 'activation', etc.


-- If all predecessors of n (and all predecessors of those, etc.)
-- don't touch Prop(A) ∩ Prop(B), then n is activated in the
-- updated net iff it was in the original net.
--------------------------------------------------------------------
lemma hebb_before_intersection (net : BFNN) (A B : Set ℕ) (n : ℕ) :
  (∀ x, layer net x < layer net n → x ∉ propagate net A ∩ propagate net B) 
  → (n ∈ propagate (hebb_star net A) B ↔ n ∈ propagate net B) := by
--------------------------------------------------------------------
  intro h₁
  simp only [Membership.mem, Set.Mem, propagate]
  
  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  case hz =>
    -- After simplifications, just n ∈ B → n ∈ B.
    rw [hebb_layers]
    rw [hL]
    simp only [propagate_acc]

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    -- Both directions are similar; in both cases we just argue
    -- inductively that since the predecessors aren't in Prop(A) ∩ Prop(B),
    -- and their activation doesn't differ in the two nets, neither does n's.
    apply Iff.intro
    
    ---------------------
    -- Forward Direction
    ---------------------
    case mp => 
      -- By cases, in order to reduce propagate_acc
      by_cases n ∈ B
      case pos => 
        intro _
        rw [← hL]
        exact propagate_acc_is_extens _ _ h
      case neg =>
        intro h₂

        -- Since *every* node with layer < n is not in Prop(A) ∩ Prop(B),
        -- in particular this holds for n's predecessors.
        have h₃ : ∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net B) := by
          intro x hx
          exact h₁ _ (preds_decreasing _ _ _ hx)

        rw [hebb_layers] at h₂
        rw [hL] at h₂
        rw [simp_propagate_acc _ h] at h₂
        rw [simp_propagate_acc _ h]
        rw [hebb_preds] at h₂
        simp
        simp at h₂
        
        
        -- Get ready to apply IH
        -- We write down the usual lemmas for 'm', but we don't
        -- know what the index 'i' is we're grabbing yet.  So
        -- we write these for all i.
        generalize hm : List.get! (Graph.predecessors net.toNet.graph n) = m at h₂
        
        have h₄ : ∀ i, (m i) ∈ preds net n := by
          intro i
          rw [symm hm]
          simp [preds]
          exact get!_mem (net.graph.predecessors n) i

        have h₅ : ∀ i, (layer net (m i)) ≤ L := by
          intro i
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net (m i) n (h₄ i)
        
        have h₆ : ∀ (i x : ℕ), layer net x < layer net (m i) 
          → ¬x ∈ propagate net A ∩ propagate net B := by
          intro i x hx
          exact h₁ _ (lt_trans hx (preds_decreasing _ _ _ (h₄ i)))

        -- Go into h₂ and apply our inductive hypothesis
        conv at h₂ =>
          enter [2, 1, i]
          rw [IH (layer net (m i)) (h₅ i) (m i) (h₆ i) rfl]
        
        -- Unpack the (m i) term
        rw [← hm] at h₂
        rw [← hm]

        -- Finally, apply hebb_activ_equal₂.
        exact (hebb_activ_equal₂ net A B h₃).mp h₂

    ---------------------
    -- Backwards Direction
    ---------------------
    case mpr => 
      -- By cases, in order to reduce propagate_acc
      by_cases n ∈ B
      case pos => 
        intro h₂
        rw [← hL] at h₂
        exact propagate_acc_is_extens _ _ h
      case neg =>
        intro h₂
      
        -- Since *every* node with layer < n is not in Prop(A) ∩ Prop(B),
        -- in particular this holds for n's predecessors.
        have h₃ : ∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net B) := by
          intro x hx
          exact h₁ _ (preds_decreasing _ _ _ hx)

        rw [hebb_layers]
        rw [hL]
        rw [simp_propagate_acc _ h]
        rw [simp_propagate_acc _ h] at h₂
        rw [hebb_preds]
        simp
        simp at h₂
        
        -- Get ready to apply IH
        -- We write down the usual lemmas for 'm', but we don't
        -- know what the index 'i' is we're grabbing yet.  So
        -- we write these for all i.
        generalize hm : List.get! (Graph.predecessors net.toNet.graph n) = m
        
        
        have h₄ : ∀ i, (m i) ∈ preds net n := by
          intro i
          rw [symm hm]
          simp [preds]
          exact get!_mem (net.graph.predecessors n) i

        have h₅ : ∀ i, (layer net (m i)) ≤ L := by
          intro i
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net (m i) n (h₄ i)
        
        have h₆ : ∀ (i x : ℕ), layer net x < layer net (m i) 
          → ¬x ∈ propagate net A ∩ propagate net B := by
          intro i x hx
          exact h₁ _ (lt_trans hx (preds_decreasing _ _ _ (h₄ i)))

        -- Go into the goal and apply our inductive hypothesis
        conv =>
          enter [2, 1, i]
          rw [IH (layer net (m i)) (h₅ i) (m i) (h₆ i) rfl]

        -- Unpack the (m i) term
        rw [← hm]

        -- Finally, apply hebb_activ_equal₂.
        exact (hebb_activ_equal₂ net A B h₃).mpr h₂


-- The updated propagation at least contains Prop(A) ∩ Prop(B).
--------------------------------------------------------------------
theorem hebb_extens (net : BFNN) (A B : Set ℕ) :
  propagate net A ∩ propagate net B 
  ⊆ propagate (hebb_star net A) B := by
--------------------------------------------------------------------
  intro (n : ℕ)
  intro h₁
  
  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  -- Easy; after simplifications, show that A ∩ B ⊆ B
  case hz => 
    simp only [Membership.mem, Set.Mem, propagate]
    simp only [Inter.inter, Set.inter, setOf] at h₁
    simp only [Membership.mem, Set.Mem, propagate] at h₁
    rw [hebb_layers]
    rw [hL]
    rw [hL] at h₁
    simp only [propagate_acc]
    simp only [propagate_acc] at h₁
    exact h₁.2

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    -- First, we case on n ∈ B to prepare for simplifications.
    by_cases n ∈ B
    case pos => exact propagate_is_extens _ _ h
    case neg =>
      -- By the well-ordering principle, let m be the node
      -- in Prop(A) ∩ Prop(B) with the *smallest layer*
      generalize hS : (propagate net A ∩ propagate net B) = S
      have hn : n ∈ S := by
        rw [← hS]
        exact h₁
      have h_nonempty : Set.Nonempty S := ⟨n, hn⟩
      let m := WellFounded.min (layer_wellfounded net) S h_nonempty
      
      -- This m is both in the set, and is the smallest such m.
      have hm : m ∈ S ∧ ∀ x, x ∈ S → layer net m ≤ layer net x := 
        ⟨WellFounded.min_mem _ _ _,
        fun x hx => le_of_not_le (WellFounded.not_lt_min (layer_wellfounded net) _ _ hx)⟩
      
      -- Either layer[m] ≤ layer[n]   or  layer[m] = layer[n]
      cases lt_or_eq_of_le (hm.2 n hn)
      
      -------------------------------
      -- Case 1: layer[m] < layer[n]
      -------------------------------
      -- In this case, we have an edge m⟶n, and since
      -- m ∈ Prop(A), n ∈ Prop(A), m activated in the updated net,
      -- we have that m activates n in the updated net.
      case inl h₂ => 
        -- NOTE: This is where we apply the crucial fact that
        -- the net is fully connected / transitively closed
        -- to get an edge m⟶n.
        have h₃ : m ∈ preds net n := by
          rw [edge_from_preds]
          exact connected _ m n h₂
        
        -- We apply our IH to m
        rw [← hS] at hm
        have h₄ : layer net m ≤ L := by
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net m n h₃
        have h₅ : m ∈ propagate (hebb_star net A) B :=
          IH _ h₄ hm.1 rfl

        -- Simplify and apply simp_hebb_activ₃.
        simp only [Membership.mem, Set.Mem, propagate]
        rw [hebb_layers]
        rw [hL]
        rw [simp_propagate_acc _ h]
        rw [hebb_preds]
        exact hebb_activated_by net A B h₁.1 ⟨h₃, hm.1.1⟩ h₅

      -------------------------------
      -- Case 1: layer[m] = layer[n]
      -------------------------------
      -- In this case, we know that all predecessor weights are
      -- the same.  But we also have to argue (inductively) that
      -- all predecessor *activations* are the same.  We do this
      -- in a separate lemma [hebb_before_intersection].
      case inr h₂ =>
        -- All strict predecessors of m are not in Prop(A) ∩ Prop(B).
        -- (because m is the smallest)
        rw [← hS] at hm
        have h₃ : ∀ x, layer net x < layer net n → x ∉ propagate net A ∩ propagate net B := by
          intro x h₄ hx
          rw [← h₂] at h₄
          exact absurd h₄ (not_lt_of_le (hm.2 _ hx))

        exact (hebb_before_intersection _ _ _ n h₃).mpr h₁.2


-- If there is a path within Prop(A) from B to n, then, since this
-- path is updated in hebb_star, n ∈ Prop(B).
-- This is the key lemma for the backwards direction of the 
-- reduction; it expresses an upper bound for Reach(Prop(A), Prop(B))
--------------------------------------------------------------------
theorem hebb_updated_path (net : BFNN) (A B : Set ℕ) :
  reachable net (propagate net A) (propagate net B)
  ⊆ propagate (hebb_star net A) B := by
--------------------------------------------------------------------
  intro (n : ℕ)
  intro h₁
  
  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  -- Easy; at layer zero, show that B = B.
  case hz =>
    have h₂ : n ∈ propagate net B :=
      reach_layer_zero _ _ _ _ hL h₁

    simp only [Membership.mem, Set.Mem, propagate]
    simp only [Membership.mem, Set.Mem, propagate] at h₂
    rw [hebb_layers net A]
    rw [hL]
    rw [hL] at h₂
    simp only [propagate_acc]
    simp only [propagate_acc] at h₂
    exact h₂
    
  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH₁ => 
    -- We have a path from Prop(B) to n, going through Prop(A).
    match h₁ with
    | ⟨m, hm⟩ => 
      -- By induction on the length of this path
      induction hm.2

      case trivial hmA => exact hebb_extens _ _ _ ⟨hmA, hm.1⟩
      case from_path x y path_mx edge_xy hy _ => 
        -- Split by whether y ∈ B in order to simplify propagate_acc
        by_cases y ∈ propagate net B
        case pos => exact hebb_extens _ _ _ ⟨hy, h⟩
        case neg =>
          have y_not_in_B : y ∉ B := fun h_contr => 
            absurd (propagate_is_extens _ _ h_contr) h

          -- Simplifications and rewriting
          simp only [propagate, Membership.mem, Set.Mem]
          rw [hebb_layers]
          rw [hL]
          rw [simp_propagate_acc (hebb_star net A) y_not_in_B]
          rw [hebb_preds]
          simp

          -- Apply our inductive hypothesis: x ∈ Prop(B) in (hebb_star net) 
          have hpreds : x ∈ preds net y := (edge_from_preds _ _ _).mpr edge_xy
          have hpred_dec : layer net x ≤ L := 
            (Nat.lt_succ).mp (lt_of_lt_of_eq (preds_decreasing _ _ _ hpreds) hL)
          have hx_reachable : x ∈ reachable net (propagate net A) (propagate net B) :=
            ⟨m, ⟨hm.1, path_mx⟩⟩
          have hx_propA : x ∈ propagate net A := 
            reach_subset _ _ _ hx_reachable
          have hx_propB : x ∈ propagate (hebb_star net A) B := 
            IH₁ (layer net x) hpred_dec hx_reachable rfl
          
          -- Apply simp_hebb_activ₃, which says:
          --  x, y ∈ Prop(A)
          --  There's an edge from x ⟶ y
          --  x ∈ Prop(B) in (hebb_star net)
          --  -------------------------------
          --  y is activ in hebb_star net
          exact hebb_activated_by net A B hy ⟨hpreds, hx_propA⟩ hx_propB


-- Complementary to [hebb_updated_path]:
--     Reach(Prop(A), Prop(B)) ⊆ Prop*(B)
-- we have
--     Prop(A) ∩ Prop*(B) ⊆ Reach(Prop(A), Prop(B)).
-- This is the key lemma for the forward direction of the reduction;
-- it expresses a lower bound for Reach(Prop(A), Prop(B)).
--------------------------------------------------------------------
theorem reach_of_hebb_prop (net : BFNN) (A B : Set ℕ) :
  propagate net A ∩ propagate (hebb_star net A) B
  ⊆ reachable net (propagate net A) (propagate net B) := by
--------------------------------------------------------------------
  intro n h₁

  -- By induction on the layer of the net containing n
  generalize hL : layer net n = L
  induction L using Nat.case_strong_induction_on generalizing n

  --------------------------------
  -- Base Step
  --------------------------------
  -- Easy; after simplifications, show that A ∩ B ⊆ Reach(...)
  case hz =>
    simp only [Inter.inter, Set.inter, setOf] at h₁
    simp only [Membership.mem, Set.Mem, propagate] at h₁
    rw [hebb_layers] at h₁
    rw [hL] at h₁
    simp only [propagate_acc] at h₁
      
    exact reach_is_extens _ _ _ 
      ⟨propagate_is_extens _ _ h₁.1, propagate_is_extens _ _ h₁.2⟩

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    -- First, we case on n ∈ B to simplify propagate_acc.
    by_cases n ∈ B
    case pos => 
      exact reach_is_extens _ _ _ 
        ⟨h₁.1, propagate_is_extens _ _ h⟩
      
    case neg => 
      -- By the well-ordering principle, let m be the node
      -- in Prop(A) ∩ Prop*(B) with the *smallest layer*
      generalize hS : propagate net A ∩ propagate (hebb_star net A) B = S
      have hn : n ∈ S := by
        rw [← hS]
        exact h₁
      have h_nonempty : Set.Nonempty S := ⟨n, hn⟩
      let m := WellFounded.min (layer_wellfounded net) S h_nonempty
      
      -- This m is both in the set, and is the smallest such m.
      have hm : m ∈ S ∧ ∀ x, x ∈ S → layer net m ≤ layer net x := 
        ⟨WellFounded.min_mem _ _ _,
        fun x hx => le_of_not_le (WellFounded.not_lt_min (layer_wellfounded net) _ _ hx)⟩
      
      -- Either layer[m] ≤ layer[n]   or  layer[m] = layer[n]
      cases lt_or_eq_of_le (hm.2 n hn)
      
      -------------------------------
      -- Case 1: layer[m] < layer[n]
      -------------------------------
      -- In this case, we have an edge m⟶n, and since
      -- m ∈ Prop(A), n ∈ Prop(A), m ∈ Reach(Prop(A), Prop(B)),
      -- we have that n ∈ Reach(Prop(A), Prop(B)).
      case inl h₂ =>
        -- NOTE: This is where we apply the crucial fact that
        -- the net is fully connected / transitively closed
        -- to get an edge m⟶n.
        have h₃ : m ∈ preds net n := by
          rw [edge_from_preds]
          exact connected _ m n h₂

        have hedge : Graph.hasEdge net.toNet.graph m n :=
              (edge_from_preds _ _ _).mp h₃
        
        -- We apply our IH to m
        rw [← hS] at hm
        have h₄ : layer net m ≤ L := by
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact preds_decreasing net m n h₃
        have h₅ : m ∈ reachable net (propagate net A) (propagate net B) :=
          IH _ h₄ hm.1 rfl

        -- n is reachable from the same x ∈ Prop(A) ∩ Prop(B)
        -- that m is reachable by.
        rw [← hS] at hn
        match h₅ with
        | ⟨x, hx⟩ => exact ⟨x, ⟨hx.1, focusedPath.from_path hx.2 hedge hn.1⟩⟩

      -------------------------------
      -- Case 2: layer[m] = layer[n]
      -------------------------------
      -- In this case, we know that all predecessor weights are
      -- the same.  But we also have to argue (inductively) that
      -- all predecessor *activations* are the same.  We do this
      -- in a separate lemma [hebb_before_intersection].
      case inr h₂ => 
        -- All strict predecessors of m are not in Prop(A) ∩ Prop(B).
        -- (because m is the smallest)
        rw [← hS] at hm
        have h₃ : ∀ x, layer net x < layer net n → x ∉ propagate net A ∩ propagate net B := by
          intro x h₄ hx
          rw [← h₂] at h₄
          exact absurd h₄ (not_lt_of_le (hm.2 _ ⟨hx.1, hebb_extens _ _ _ hx⟩))
        
        exact reach_is_extens _ _ _ 
          ⟨h₁.1, (hebb_before_intersection _ _ _ n h₃).mp h₁.2⟩


/-══════════════════════════════════════════════════════════════════
  Reduction for Unstable Hebbian Update
══════════════════════════════════════════════════════════════════-/

/-
Prop*(B) = propagate (hebb_star net A) B

Prop(A) ∩ Prop(B) ⊆ Prop*(B)
Reach(Prop(A), Prop(B)) ⊆ Prop*(B)
Prop(A) ∩ Prop*(B) ⊆ Reach(Prop(A), Prop(B))
--------------------
Prop*(B) = Prop(B ∪ Reach(Prop(A), Prop(B)))
-/
/-
⟦Tp⟧ = Propagate(⟦p⟧)
⟦K(p, q)⟧ = Reach(⟦p⟧, ⟦q⟧)
-/

--------------------------------------------------------------------
theorem hebb_reduction (net : BFNN) (A B : Set ℕ) : 
  propagate (hebb_star net A) B =
  propagate net (B ∪ reachable net (propagate net A) (propagate net B)) := by 
--------------------------------------------------------------------
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
        have h₃ : n ∈ propagate net B :=
          reach_layer_zero _ _ _ _ heq h₂

        simp only [propagate, Membership.mem, Set.Mem] at h₃
        rw [hL] at h₃
        simp only [propagate_acc] at h₃
        exact h₃

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH => 
    apply Iff.intro
    

    ---------------------
    -- Forward Direction
    ---------------------
    case mp => 
      intro h₁

      -- By cases in order to simplify propagate_acc
      by_cases n ∈ B ∪ reachable net (propagate net A) (propagate net B)
      case pos => 
        -- In this case, just apply propagate_is_extens
        rw [← hL]
        simp only [propagate] at h
        exact propagate_acc_is_extens _ _ h

      case neg h₂ =>
        -- From here, we have two cases.  Either:
        --   - n ∈ Prop(A) and ∃ an active predecessor m⟶n in Prop(A)
        --   - or n ∉ Prop(A) *or* all predecessors m⟶n ∉ Prop(A) ∩ Prop(...)
        by_cases (n ∈ propagate net A) 
                  ∧ (∃ m, m ∈ preds net n ∧ 
                    m ∈ propagate net A ∩ propagate net (B ∪ 
                      reachable net (propagate net A) (propagate net B)))
        
        ---------------------------------------
        -- Case 1: n ∈ Prop(A)
        -- and some m⟶n ∈ Prop(A) ∩ Prop(B ∪ ...)
        ---------------------------------------
        -- Since m ∈ Prop(B ∪ Reach(Prop(A), Prop(B))),
        --       m ∈ Prop(B) in the updated net. (by IH)
        -- But by [reach_of_hebb_prop], this means
        --       m ∈ Reach(Prop(A), Prop(B))
        -- Then, since m, n ∈ Prop(A) and m ⟶ n,
        --       n ∈ Reach(Prop(A), Prop(B)).
        case pos =>
          match h.2 with
          | ⟨m, hm⟩ =>
            -- Simplifications to prepare for IH
            simp only [propagate, Membership.mem, Set.Mem] at hm
            simp only [Inter.inter, Set.inter, setOf] at hm
            simp only [Membership.mem, Set.Mem] at hm

            have hlayer : layer net m ≤ L := by
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact preds_decreasing net m n hm.1

            conv at hm =>
              enter [2, 2]
              rw [← IH (layer net m) hlayer m rfl]
            
            -- We can now apply [reach_of_hebb_prop]
            have h₂ : m ∈ reachable net (propagate net A) (propagate net B) :=
              reach_of_hebb_prop _ _ _ hm.2 
            have hedge : Graph.hasEdge net.toNet.graph m n :=
              (edge_from_preds _ _ _).mp hm.1
            
            -- n is reachable from exactly that x ∈ Prop(A) ∩ Prop(B) 
            -- that m is reachable from.
            have h₃ : n ∈ reachable net (propagate net A) (propagate net B) :=
              match h₂ with
              | ⟨x, hx⟩ => ⟨x, ⟨hx.1, focusedPath.from_path hx.2 hedge h.1⟩⟩ 
            
            rw [← hL]
            exact propagate_acc_is_extens _ _ (Or.inr h₃)
            
        ---------------------------------------
        -- Case 2: n ∉ Prop(A)
        -- or all m⟶n ∉ Prop(A) ∩ Prop(B ∪ ...)  
        ---------------------------------------
        -- By [hebb_simp_activ₁] and [hebb_simp_activ₂],
        -- in either case the activations are the same and
        -- we just apply our IH.
        case neg =>
          -- First, we rewrite our hypothesis by pushing the
          -- negation through
          rw [not_and_or] at h
          rw [not_exists] at h
          conv at h => enter [2, x]; rw [not_and]

          -- We get ready to simplify propagate_acc
          rename_i h_reach
          have h_B : n ∉ B :=
            fun n_in_B => absurd (Set.mem_union_left _ n_in_B) h_reach

          -- Simplifications and rewriting, to prepare for IH
          rw [hebb_layers] at h₁
          rw [hL] at h₁
          simp only [propagate] at h_reach
          rw [simp_propagate_acc _ h_B] at h₁
          rw [simp_propagate_acc _ h_reach]
          rw [hebb_preds net A] at h₁

          -- We now split once more
          cases h

          ---------------------------------------
          -- Case 2.1: n ∉ Prop(A)
          -- or all m⟶n ∉ Prop(A) ∩ Prop(B ∪ ...)  
          ---------------------------------------
          case inl h₂ => 
            -- Apply [hebb_activ_equal₁]
            rw [hebb_activ_equal₁ _ _ _ h₂] at h₁
            
            -- More simplifications to get ready for IH
            simp
            simp at h₁
            convert h₁ using 4
            rename_i i
            generalize hm : List.get! (net.graph.predecessors n) i = m
            generalize hLm : layer net m = Lm

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

          ---------------------------------------
          -- Case 2.1: n ∉ Prop(A)
          -- or all m⟶n ∉ Prop(A) ∩ Prop(B ∪ ...)  
          ---------------------------------------
          case inr h₂ => 
            simp
            simp at h₁

            -- Get ready to apply IH
            -- We write down the usual lemmas for 'm', but we don't
            -- know what the index 'i' is we're grabbing yet.  So
            -- we write these for all i.
            generalize hm : List.get! (Graph.predecessors net.toNet.graph n) = m at h₁
            have h₄ : ∀ i, (m i) ∈ preds net n := by
              intro i
              rw [symm hm]
              simp [preds]
              exact get!_mem (net.graph.predecessors n) i

            have h₅ : ∀ i, (layer net (m i)) ≤ L := by
              intro i
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact preds_decreasing net (m i) n (h₄ i)

            -- Go into h₁ and apply our inductive hypothesis
            conv at h₁ =>
              enter [2, 1, i]
              rw [IH (layer net (m i)) (h₅ i) (m i) rfl]
            
            -- Unpack the (m i) term
            rw [← hm] at h₁
            rw [← hm]

            -- Apply [hebb_activ_equal₂]
            let S := (B ∪ reachable net (fun n => 
              propagate_acc net A n (layer net n)) fun n => 
                propagate_acc net B n (layer net n))
            rw [hebb_activ_equal₂ _ _ S h₂] at h₁
            exact h₁ 

    ---------------------
    -- Backward Direction
    ---------------------
    -- We've already worked for this direction; most of the work
    -- is used to prove [hebb_updated_path], which is the crucial lemma here.
    case mpr =>
      intro h₁
      
      -- By cases; either n ∈ B ∪ Reach(Prop(A), Prop(B)), or not.
      by_cases n ∈ B ∪ reachable net (propagate net A) (propagate net B)
      case pos =>
        -- From here, we split again; either:
        --    1. n ∈ B, and by extens n ∈ Prop(B) in (hebb_star net)
        --    2. n ∈ Reach(Prop(A), Prop(B)).  In this case, this path
        --       has been updated in the (hebb_star net), so of course
        --       n ∈ Prop(B) in (hebb_star_net) (by [hebb_updated_path]) 
        cases h
        case inl h₂ => exact propagate_acc_is_extens _ _ h₂
        case inr h₂ =>
          have h₃ : n ∈ propagate (hebb_star net A) B :=
            hebb_updated_path _ _ _ h₂
          simp only [propagate, Membership.mem, Set.Mem] at h₃
          exact h₃
          
      case neg =>
        -- We get ready to simplify propagate_acc
        have n_not_in_B : n ∉ B :=
          fun n_in_B => absurd (Set.mem_union_left _ n_in_B) h

        -- Simplifications and rewriting, to prepare for IH
        -- We also rewrite the 'preds', 'layers', and 'activ'
        -- for (hebb_star net) in terms of the original 'net'.
        rw [hebb_layers]
        rw [hL]
        simp only [propagate] at h
        rw [simp_propagate_acc _ n_not_in_B]
        rw [simp_propagate_acc _ h] at h₁
        rw [hebb_preds net A] -- rewrite 'preds'
        
        -- The plan is to now apply our inductive hypothesis
        -- and use the 'activ_agree' lemmas.
        -- We write the two sets as S₁ and S₂ for convenience 
        -- let S₁ := fun m => 
        --   propagate_acc net (B ∪ reachable net 
        --     (fun n => propagate_acc net A n (layer net n)) 
        --     (fun n => propagate_acc net B n (layer net n)))
        --     m (layer net m)
        let S₁ := fun m => 
          propagate_acc net (B ∪ reachable net 
            (fun n => propagate_acc net A n (layer net n)) 
            (fun n => propagate_acc net B n (layer net n))) m (layer net m)
        let S₂ := fun m => propagate_acc (hebb_star net A) B m (layer (hebb_star net A) m)

        -- Apply IH to the predecessors
        have h₂ : ∀ (m : ℕ), m ∈ preds net n → (S₁ m ↔ S₂ m) := by
          simp only [Membership.mem] -- really just want to unfold the let
          intro m hm
          generalize hLm : layer net m = Lm
          have h₃ : Lm ≤ L := by
            rw [symm hLm]
            apply Nat.lt_succ.mp
            rw [symm hL]
            exact preds_decreasing net m n hm
          exact (symm (IH Lm h₃ m hLm).to_eq).to_iff

        -- Argument: 
        -- By activ_agree, the predecessors m ∈ Prop(B) (over hebb_star)
        --   activate n *in the original net*
        -- But the weights in the updated net are either the same or
        --   increasing, so by [hebb_activ_nondecreasing], these same 
        --   predecessors activate n *in the updated net*.
        simp
        simp at h₁
        exact hebb_activ_nondecreasing net A S₂ _
          (activ_agree _ S₁ S₂ _ h₂ h₁)


-- COROLLARY: If we plug in Prop(A) ∩ Prop(B) = ∅,
-- then the update has no effect on the propagation!  
--------------------------------------------------------------------
theorem hebb_reduction_empty (net : BFNN) (A B : Set ℕ) : 
  propagate net A ∩ propagate net B = ∅ →

  propagate (hebb_star net A) B = propagate net B := by 
--------------------------------------------------------------------
  intro h_empty
  apply ext
  intro (n : ℕ)

  -- If Prop(A) ∩ Prop(B) = ∅,
  -- then Reach(Prop(A), Prop(B)) must be empty as well!
  -- (In order for there to be a path at all, there must
  --  be a path of length 0.)
  have h₁ : reachable net (propagate net A) (propagate net B) = ∅ :=
    reach_empty_of_inter_empty _ _ _ h_empty
  
  -- And now we just substitute ∅
  rw [hebb_reduction net A B]
  rw [h₁]
  rw [Set.union_empty B]


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
-- 
-- NOTE: Not sure if I need this before.  It's interesting,
-- but I'm not sure if it helps with the proof for the reduction.
-- --------------------------------------------------------------------
-- theorem hebb_star_is_fixed_point (net : BFNN) (S : Set ℕ) : 
--   hebb (hebb_star net S) S ≡ hebb_star net S := by 
-- --------------------------------------------------------------------
--   sorry


-- ANOTHER THEOREM
-- that I didn't end up using
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
--         convert h₂ using 4
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
--         convert h₂ using 4
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


-- /-══════════════════════════════════════════════════════════════════
--   Subnets
-- ══════════════════════════════════════════════════════════════════-/

-- -- A net net₁ is a subnet of net₂ (net₁ ≼ net₂) iff for all
-- -- sets S, every node activated in the propagation of S
-- -- in net₁ is activated in the propagation of S in net₂.
-- -- (They both have the same *propagation structure*)
-- def subnet (net₁ net₂ : BFNN) : Prop :=
--   ∀ (S : Set ℕ), propagate net₁ S ⊆ propagate net₂ S

-- infixl:65   " ≼ " => subnet


-- -- Two nets are equivalent if they have the same 
-- -- *propagation structure* (i.e. if their propagations agree 
-- -- for every set S)
-- def net_eq (net₁ net₂ : BFNN) : Prop :=
--   net₁ ≼ net₂ ∧ net₂ ≼ net₁

-- infixl:65   " ≡ " => net_eq


-- -- A super easy example, just to briefly test ≼ and ≡
-- example : example_net ≡ example_net :=
--   ⟨fun _ _ h => h, fun _ _ h => h⟩  


/-
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
-/

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