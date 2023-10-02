import Argyle.Graph
import Argyle.Helpers
import Mathlib.Data.List.MinMax

open Graph

-------------------------------------------------
-- Our class of neural networks
-- We consider nets where:
--   - The activation function is binary
--   - The activation function is nondecreasing
--   - The activation function has a threshold
--   - The graph is nonempty
--   - The graph is acyclic
--   - The graph is fully connected
-------------------------------------------------
structure Net where
  graph : Graph ℕ ℚ
  activation : ℚ → ℚ
  rate : ℚ  -- learning rate
  rate_pos : rate > 0

  -- The activation function is binary
  binary : ∀ (x : ℚ), (activation x = 0) ∨ (activation x = 1)

  -- The activation function is nondecreasing
  activ_nondecr : ∀ (x₁ x₂ : ℚ), x₁ ≤ x₂ → activation x₁ ≤ activation x₂
  
  -- The activation function has a threshold
  threshold : ℚ
  activ_thres : activation (is_active) = 1

  -- The graph is nonempty, acyclic and fully connected
  nonempty : graph.vertices ≠ []
  acyclic : graph.is_acyclic
  connected : graph.is_connected

-- Because our activation function is bounded above by 1,
-- if act(x₁) = 1
-- then any act(x₂) greater than act(x₁) also = 1
--------------------------------------------------------------------
lemma activation_from_inequality (net : Net) (x₁ x₂ : ℚ) :
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


-- Just an abbreviation for the predecessors of n in 'net'
@[simp]
def preds (net : Net) (n : ℕ): List ℕ :=
  net.graph.predecessors n

--------------------------------------------------------------------
theorem edge_iff_preds (net : Net) (m n : ℕ) :
  m ∈ preds net n ↔ net.graph.hasEdge m n := by
--------------------------------------------------------------------
  simp only [preds, Graph.predecessors]
  apply Iff.intro

  case mp => 
    intro h₁
    have h₂ := List.of_mem_filter h₁
    exact h₂

  case mpr => 
    intro h₁
    have h₂ : ⟨m, n⟩ ∈ net.graph.edges := Graph.edge_of_hasEdge _ _ _ h₁
    have h₃ : m ∈ net.graph.get_vertices := by
      exact net.graph.edges_from_vertices_left h₂

    apply List.mem_filter_of_mem h₃
    exact h₁


def layer_acc (net : Net) (n : ℕ) (vertices : List ℕ) : ℕ :=
  match vertices with
  | [] => 0
  | vertices =>
    -- Call layer on each predecessor of n recursively,
    -- and then take maximum(pred_layers) + 1.
    let preds := net.graph.predecessors n
    let pred_layers := List.map (fun m => 
      layer_acc net m (vertices.erase n)) preds
    
    match pred_layers.maximum with
    | some max => max + 1
    | none => 0
termination_by layer_acc net n vertices => sizeOf vertices
decreasing_by
  simp_wf
  
  cases lt_or_eq_of_le (sizeOf_erase vertices n)
  case inl h₁ => exact h₁
  case inr h₁ => 
    sorry

def layer (net : Net) (n : ℕ) : ℕ :=
  layer_acc net n (net.graph.vertices)

-- The layer relation layer[m] ≤ layer[n] is well-founded
-- (i.e. it has a least element)
--------------------------------------------------------------------
lemma layer_wellfounded (net : Net) : 
  WellFounded (fun x y => layer net x ≤ layer net y) := by
--------------------------------------------------------------------
  apply WellFounded.wellFounded_iff_has_min.mpr 
  intro S hS
  
  -- Idea:
  -- By contradiction; for all m ∈ S there is some x ∈ S with a smaller layer.
  -- We can use this fact to create a cycle
  --   layer net x₁ < ... < layer net xₖ < layer net x₁
  -- and then by Lemma [layer_connected], we get edges
  --   x₁ ⟶ ... ⟶ xₖ ⟶ x₁
  -- which contradicts the fact that the net is acyclic!
  sorry

-- If m is a predecessor of n, then it must be in a previous layer.
-- Proof idea:
-- layer(m)  ≤  max({layer(v) | v ∈ preds(n)})  <  layer(n)
--------------------------------------------------------------------
lemma layer_preds (net : Net) (m n : ℕ) :
  m ∈ preds net n 
  → layer net m < layer net n := by
--------------------------------------------------------------------
  intro h₁
  sorry
  -- simp only [layer]

  -- generalize hls : (List.reverse (Graph.get_vertices net.graph)) = ls
  -- induction ls
  -- case nil =>
  --   -- This case is impossible;
  --   -- m ∈ preds(n) means that there is *something* in the graph.
  --   -- This contradicts the fact that the graph is empty!
  --   simp [preds, Graph.predecessors, Graph.get_vertices] at h₁
  --   simp [Graph.get_vertices] at hls
  --   rw [hls] at h₁
  --   rw [List.map_nil] at h₁
  --   rw [List.filter_nil] at h₁
  --   exact False.elim ((List.mem_nil_iff _).mp h₁)
    

  -- case cons v rest IH =>
  --   simp only [layer_acc]
  --   generalize hmax_m : (List.map (fun x => layer_acc net x rest) (preds net m)).maximum = max_m
  --   generalize hmax_n : (List.map (fun x => layer_acc net x rest) (preds net n)).maximum = max_n

  --   -- We branch out all of the possible cases
  --   -- (we have 4 branches from the 'if-then-else's, 
  --   -- and more for the 'match'es)
  --   by_cases v = m
  --   case pos => 
  --     rw [if_pos h]
  --     by_cases v = n
  --     case pos => 
  --       rw [if_pos h]
        
  --       match max_n with
  --       | none => -- This case is also impossible;
  --         -- m ∈ preds(n) means that there is *some* maximum in preds(n),
  --         -- which contradicts the fact that the max is empty.
  --         sorry

  --       | some L => 
  --         match max_m with
  --         | none => exact Nat.succ_pos L
  --         | some K => -- This is the tricky case!
  --           simp
  --           sorry

  --     case neg => 
  --       rw [if_neg h]
  --       match max_m with
  --       | none => 
  --         simp
  --         sorry
  --       | some K => sorry

  --   case neg =>
  --     rw [if_neg h]
  --     by_cases v = n
  --     case pos => 
  --       rw [if_pos h]
  --       match max_n with
  --       | none => sorry
  --       | some L => sorry

  --     case neg => 
  --       rw [if_neg h]
  --       exact IH sorry

--------------------------------------------------------------------
lemma layer_connected : ∀ (net : Net) (m n : ℕ), 
  layer net m < layer net n → net.graph.hasEdge m n := by
--------------------------------------------------------------------
  intro net m n h₁
  apply Classical.by_contradiction
  intro hcontr

  -- Since the net is connected, we have three cases:
  -- Either m ⟶ n, n ⟶ m, or m and n share the same successors
  -- and predecessors
  cases net.connected m n
  case inl h₂ => 
    -- Case 1: m ⟶ n.  But we assumed ¬ m ⟶ n.
    exact absurd h₂ hcontr
  case inr h₂ =>
    cases h₂
    case inl h₃ => 
      -- Case 2: n ⟶ m
      -- But then layer(n) < layer(m)
      apply not_lt_of_gt h₁ (layer_preds _ _ _ _)
      rw [edge_iff_preds]
      exact h₃

    case inr h₃ =>
      -- Case 3: n and m have the same successors and predecessors.
      -- But then layer(m) = layer(n.) 
      have h₄ : layer net m = layer net n := by
        simp only [layer]
        
        induction net.graph.vertices
        case nil => sorry
        case cons v vs IH => sorry

        -- rw [h₃.2]
        -- sorry
      
      apply ne_of_lt h₁ h₄


-- NOTE: Although 'do' notation might be more readable here,
--       I avoid it because it's hard to reason about.
noncomputable
def activ (net : Net) (prev_activ : List ℚ) (n : ℕ) : Prop :=
  let preds := preds net n
  let weights := List.map (fun i => 
      let m := preds.get! i
      net.graph.getEdgeWeight m n) 
    (List.range preds.length)
  let weight_sum := weighted_sum weights prev_activ
  let curr_activ := net.activation weight_sum
  curr_activ = 1
