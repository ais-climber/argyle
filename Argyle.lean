import Mathlib.Tactic.LibrarySearch
import Lean.Parser.Tactic
import Graph.Graph

open Graph

-------------------------------------------------
-- Graphs
-------------------------------------------------
-- This is a graph with ℕ nodes
-- and Float edge weights.
def graph : Graph ℕ Float :=
  ⟨#[
    ⟨0, #[⟨1, 0.5⟩, ⟨2, 0.6⟩, ⟨3, 0.7⟩]⟩, 
    ⟨1, #[⟨2, 0.8⟩, ⟨3, 0.9⟩]⟩, 
    ⟨2, #[⟨3, 1.0⟩, ⟨3, 5.0⟩]⟩, 
    ⟨3, #[]⟩
  ]⟩

#check graph
#eval graph
#eval graph.edgeCount   -- evals to 7
#eval graph.order       -- evals to 4
#eval graph.toArray     -- evals to #[0, 1, 2, 3]

#eval graph.inDegree 1      -- evals to 1
#eval graph.outDegree 1     -- evals to 2
#eval graph.successors 1    -- evals to #[2, 3]
#eval graph.predecessors 1  -- evals to #[0]

#eval graph.inDegree 2      -- evals to 2
#eval graph.outDegree 2     -- evals to 2
#eval graph.successors 2    -- evals to #[3, 3]
#eval graph.predecessors 2  -- evals to #[0, 1]

-------------------------------------------------
-- My own graph functions and convenience
-- properties
-------------------------------------------------
namespace Graph
variable {α : Type} [Inhabited α] {β : Type}

def hasNode (g : Graph α β) (v : α) : Prop :=
  sorry

def hasEdge (g : Graph α β) (u : α) (v : α) : Prop :=
  sorry

end Graph

variable  (G : Graph ℕ Float)
          (is_refl : ∀ (x : ℕ), 
            G.hasNode x → G.hasEdge x x)
          (is_symm : ∀ (x y : ℕ),
            G.hasEdge x y → G.hasEdge y x)
          (is_trans : ∀ (x y z : ℕ),
            G.hasEdge x y → G.hasEdge y z → G.hasEdge x z)
          (is_acyclic : sorry)

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

-- Proof that binary_step is nondecreasing
-- This is also a 'hello world' to see if I can
-- reason about a branching program.
theorem binary_step_nondecr {x₁ x₂ : Float} (hyp : x₁ ≤ x₂) :
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

def net : Net :=
  ⟨graph, binary_step⟩

structure BFNN extends Net where 
  binary : ∀ (x : Float), 
    (activation x = 0.0) ∨ (activation x = 1.0)
  
  acyclic : sorry
  
  activ_nondecr : ∀ (x₁ x₂ : Float),
    x₁ ≤ x₂ → activation x₁ ≤ activation x₂

-- TODO: 
--   How to make Feedforward net and BFNN inherit from Net?
