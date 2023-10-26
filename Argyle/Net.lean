import Argyle.Graph
import Argyle.Helpers
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Lattice
import Std.Data.Fin.Lemmas

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
structure Net (Node : Type) where
  graph : Graph Node
  activation : ℚ → ℚ
  rate : ℚ  -- learning rate
  rate_pos : rate > 0

  -- The activation function is binary
  binary : ∀ (x : ℚ), (activation x = 0) ∨ (activation x = 1)

  -- The activation function is nondecreasing
  activ_nondecr : ∀ (x₁ x₂ : ℚ), x₁ ≤ x₂ → activation x₁ ≤ activation x₂

  -- The activation function has a threshold
  threshold : ℚ
  activ_thres : activation (threshold) = 1

  -- The graph is nonempty, acyclic and fully connected
  nonempty : Nonempty Node-- OR TRY: Finset.Nonempty graph.node_fintype.elems
  acyclic : graph.Acyclic
  connected : Connected graph.Edge

-- Because our activation function is bounded above by 1,
-- if act(x₁) = 1
-- then any act(x₂) greater than act(x₁) also = 1
--------------------------------------------------------------------
lemma activation_from_inequality (net : Net k) (x₁ x₂ : ℚ) :
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


-- This is not simply an abbreviation for the predecessors --
-- it also fixes an ordering of the predecessors, for each n!
-- (we return a list, rather than just a set)
@[simp]
noncomputable
def preds (net : Net Node) (n : Node) : List Node :=
  (net.graph.predecessors n).toList

--------------------------------------------------------------------
theorem edge_iff_preds (net : Net Node) (m n : Node) :
  m ∈ preds net n ↔ net.graph.Edge m n := by
--------------------------------------------------------------------
  simp only [preds, Graph.predecessors]
  apply Iff.intro

  case mp =>
    intro h₁

    rw [Finset.mem_toList] at h₁
    rw [Finset.mem_filter] at h₁
    exact h₁.2

  case mpr =>
    intro h₁

    rw [Finset.mem_toList]
    rw [Finset.mem_filter]
    exact ⟨net.graph.nodes.complete m, h₁⟩

-- def layer_acc (net : Net Node) (n : Node) (vertices : List (Fin k)) : Fin k :=
--   match vertices with
--   | [] => sorry
--   | vertices =>
--     -- Call layer on each predecessor of n recursively,
--     -- and then take maximum(pred_layers) + 1.
--     let preds := net.graph.predecessors n
--     let pred_layers := List.map (fun m =>
--       layer_acc net m (vertices.erase n)) preds

--     sorry
--     -- match pred_layers.maximum with
--     -- | some max => max + 1
--     -- | none => 0
-- termination_by layer_acc net n vertices => sizeOf vertices
-- decreasing_by
--   simp_wf

--   cases lt_or_eq_of_le (sizeOf_erase vertices n)
--   case inl h₁ => sorry -- exact h₁
--   case inr h₁ =>
--     sorry

-- The initial layer consists of all nodes that have no
-- predecessors (the order is fixed)
def initial_layer (net : Net Node) : Finset Node :=
  sorry
  -- Finset.filter (fun n => preds net n = []) net.graph.nodes.elems
  -- { n : Node | preds net n = ∅ }

-- TODO: Define layer as we do in the paper!
-- (much simpler, I don't think we have to worry about well-foundedness)
def layer (net : Net Node) (n : Node) : ℕ :=
  sorry
  -- MAX { distance(m, n) | m ∈ initial_layer }

  -- let nodes := net.graph.node_fintype.elems.toList
  -- match List.argmax (fun m => sorry) nodes with
  -- | some M => M
  -- | none => 0
  -- Finset.max' (_) _

  -- layer_acc net n (net.graph.vertices)

-- The layer relation layer[m] ≤ layer[n] is well-founded
-- (i.e. it has a least element)
--------------------------------------------------------------------
lemma layer_wellfounded (net : Net Node) :
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
lemma layer_preds (net : Net Node) (m n : Node) :
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
lemma layer_connected : ∀ (net : Net Node) (m n : Node),
  layer net m < layer net n → net.graph.Edge m n := by
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
      rw [← edge_iff_preds] at h₃
      have h₄ := layer_preds net n m h₃
      sorry
      -- exact not_lt_of_gt h₁ h₄
      -- apply not_lt_of_gt h₁ (layer_preds net n m h₃)
      -- apply not_lt_of_gt h₁ (layer_preds _ _ _ _)
      -- rw [edge_iff_preds]
      -- exact h₃

    case inr h₃ =>
      sorry
      -- -- Case 3: n and m have the same successors and predecessors.
      -- -- But then layer(m) = layer(n.)
      -- have h₄ : layer net m = layer net n := by
      --   simp only [layer]

      --   induction net.graph.vertices
      --   case nil => sorry
      --   case cons v vs IH => sorry

      --   -- rw [h₃.2]
      --   -- sorry

      -- sorry
      -- -- apply ne_of_lt h₁ h₄


-- NOTE: Although 'do' notation might be more readable here,
--       I avoid it because it's hard to reason about.
noncomputable
def activ (net : Net Node) (prev_activ : List ℚ) (n : Node) : Prop :=
  let preds := preds net n
  let weights := List.map (fun (i : Fin (preds.length)) =>
      let m := preds.get i
      net.graph.Weight m n)
    (List.finRange preds.length)
  let weight_sum := weighted_sum weights prev_activ
  let curr_activ := net.activation weight_sum
  curr_activ = 1
