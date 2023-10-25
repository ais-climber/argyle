import Argyle.Net
import Argyle.Operators.Reachable
import Argyle.Operators.Propagate

open Set
open Classical

variable (net : Net Node)

/-══════════════════════════════════════════════════════════════════
  Naive (Unstable) Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- For every m ⟶ n where m, n ∈ Prop(S), increase the weight
-- of that edge by η * act(m) * act(n).
noncomputable
def graph_update (net : Net Node) (g : Graph Node) (S : Set Node) : Graph Node :=
{ g with Weight := fun m n =>
    let activ_m := if m ∈ propagate net S then 1 else 0
    let activ_n := if n ∈ propagate net S then 1 else 0
    g.Weight m n + (net.rate * activ_m * activ_n)
}

-- This graph update does not affect the vertices of the graph.
--------------------------------------------------------------------
lemma graph_update_vertices (net : Net Node) (g : Graph Node) (S : Set Node) :
  (graph_update net g S).nodes = g.nodes := by
--------------------------------------------------------------------
  simp only [graph_update]

-- This graph update does not affect the *successor* structure
-- of the graph (it only affects weights!!!)
--------------------------------------------------------------------
lemma graph_update_successors (net : Net Node) (g : Graph Node) (S : Set Node) (n : Node) :
  (graph_update net g S).successors n = g.successors n := by
--------------------------------------------------------------------
  simp only [Graph.successors]
  congr 1

-- This graph update does not affect the *predecessor* structure
-- of the graph
--------------------------------------------------------------------
lemma graph_update_predecessors (net : Net Node) (g : Graph Node) (S : Set Node) (n : Node) :
  (graph_update net g S).predecessors n = g.predecessors n := by
--------------------------------------------------------------------
  simp only [Graph.predecessors]
  congr 1

-- This graph update does not affect the *edge* structure
-- of the graph
--------------------------------------------------------------------
lemma graph_update_edges (net : Net Node) (g : Graph Node) (S : Set Node) (m n : Node) :
  (graph_update net g S).Edge m n ↔ g.Edge m n := by
--------------------------------------------------------------------
  simp only [graph_update]

-- This graph update does not affect the *path* structure
-- of the graph
--------------------------------------------------------------------
lemma graph_update_path (net : Net Node) (g : Graph Node) (S : Set Node) (m n : Node) :
  Nonempty ((graph_update net g S).Path m n) ↔ Nonempty (g.Path m n) := by
--------------------------------------------------------------------
  -- By induction on the path in each case.
  apply Iff.intro
  case mp =>
    intro h₁
    have path := Classical.choice h₁

    induction path
    case trivial => sorry -- ⟨Graph.Path.trivial, sorry⟩
    case from_path x y _ edge_xy IH => sorry

    -- induction h₁
    -- case trivial => exact Graph.Path.trivial
    -- case from_path x y _ edge_xy IH =>
    --   rw [graph_update_edges] at edge_xy
    --   exact Graph.Path.from_path IH edge_xy

  case mpr =>
    intro h₁
    sorry
    -- induction h₁
    -- case trivial => exact Graph.Path.trivial
    -- case from_path x y _ edge_xy IH =>
    --   rw [← graph_update_edges] at edge_xy
    --   exact Graph.Path.from_path IH edge_xy

-- This graph update preserves whether the graph is connected.
--------------------------------------------------------------------
lemma graph_update_connected (net : Net Node) (g : Graph Node) (S : Set Node) :
  g.Connected → (graph_update net g S).Connected := by
--------------------------------------------------------------------
  simp only [Graph.Connected]
  intro h₁ u v

  rw [graph_update_edges]
  rw [graph_update_edges]
  rw [graph_update_successors]
  rw [graph_update_successors]
  rw [graph_update_predecessors]
  rw [graph_update_predecessors]

  exact h₁ u v

-- This graph update preserves whether the graph is acyclic.
--------------------------------------------------------------------
lemma graph_update_acyclic (net : Net Node) (g : Graph Node) (S : Set Node) :
  g.Acyclic → (graph_update net g S).Acyclic := by
--------------------------------------------------------------------
  simp only [Graph.Acyclic]
  intro g_acyclic
  intro x

  -- Suppose for contradiction that we *do* have a path from x to itself.
  apply Classical.by_contradiction
  intro h
  rw [not_isEmpty_iff] at h
  rw [graph_update_path] at h
  rw [← not_isEmpty_iff] at h
  exact absurd g_acyclic h

-- A single step of Hebbian update.
-- Propagate S through the net, and then increase the weights
-- of all the edges x₁ ⟶ x₂ involved in that propagation
-- by η * x₁ * x₂.
noncomputable
def hebb (net : Net Node) (S : Set Node) : Net Node :=
{ net with
  graph := graph_update net net.graph S

  -- We need to check that this new net is still acyclic and connected.
  acyclic := graph_update_acyclic _ _ _ net.acyclic
  connected := graph_update_connected _ _ _ net.connected
}


/-══════════════════════════════════════════════════════════════════
  Properties of Single-Iteration Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- A single round of Hebbian update does not affect the vertices
-- of the graph.
--------------------------------------------------------------------
theorem hebb_once_vertices (net : Net Node) (S : Set Node) :
  (hebb net S).graph.nodes = net.graph.nodes := by
--------------------------------------------------------------------
  simp only [hebb]
  rw [graph_update_vertices]

-- A single round of Hebbian update does not affect the predecessors
-- of any node.
--------------------------------------------------------------------
theorem hebb_once_preds (net : Net Node) (S : Set Node) (n : Node) :
  preds (hebb net S) n = preds net n := by
--------------------------------------------------------------------
  simp only [preds, hebb, Graph.predecessors]
  congr 1

-- A single round of Hebbian update hebb does not affect which
-- neurons are on which layer of the net.
--------------------------------------------------------------------
theorem hebb_once_layers (net : Net Node) (S : Set Node) :
  layer (hebb net S) n = layer net n := by
--------------------------------------------------------------------
  simp only [preds, hebb, layer]

-- A single round of Hebbian update hebb does not affect the
-- activation function.
--------------------------------------------------------------------
theorem hebb_once_activation (net : Net Node) (S : Set Node) :
  (hebb net S).activation = net.activation := by
--------------------------------------------------------------------
  exact rfl

-- A single round of Hebbian update hebb does not affect graph
-- reachability (It only affects the edge weights)
--------------------------------------------------------------------
theorem hebb_once_reach (net : Net Node) (B : Set Node) :
  reachable (hebb net A) B = reachable net B := by
--------------------------------------------------------------------
  apply ext
  intro (n : Node)

  apply Iff.intro
  case mp =>
    intro h₁

    -- There is some m with path from m to n in the *updated* net
    match h₁ with
    | ⟨m, path, hm⟩ =>
      induction path
      case trivial hma => exact reach_is_extens _ _ hm
      case from_path x y path_mx edge_xy IH =>
        -- First, apply our IH to get x ∈ Reach(B)
        have h₂ : x ∈ reachable (hebb net A) B := ⟨m, ⟨path_mx, hm⟩⟩
        have h₃ : x ∈ reachable net B := IH h₂

        -- So there is some u ∈ B with path from u to x (in the
        -- *original* net).  We extend this path with the edge
        -- from x to y.
        match h₃ with
        | ⟨u, path₂, hu⟩ =>
          -- We have an edge from x to y in the *updated* net,
          -- but we have to bring it down to the *original* net.
          have h₄ : net.graph.Edge x y := by
            rw [← edge_iff_preds]
            rw [← edge_iff_preds] at edge_xy
            convert edge_xy using 1

          exact ⟨u, ⟨Graph.Path.from_path path₂ h₄, hu⟩⟩ -- ⟨u, ⟨hu.1, (Graph.Path.from_path hu.2 h₄)⟩⟩

  -- This direction is very similar.
  case mpr =>
    intro h₁

    -- There is some m with path from m to n in the *original* net
    match h₁ with
    | ⟨m, path, hm⟩ =>
      induction path
      case trivial hma => exact reach_is_extens _ _ hm
      case from_path x y path_mx edge_xy IH =>
        -- First, apply our IH to get x ∈ Reach(B)
        have h₂ : x ∈ reachable net B := ⟨m, ⟨path_mx, hm⟩⟩
        have h₃ : x ∈ reachable (hebb net A) B := IH h₂

        -- So there is some u ∈ B with path from u to x (in the
        -- *original* net).  We extend this path with the edge
        -- from x to y.
        match h₃ with
        | ⟨u, path₂, hu⟩ =>
          -- We have an edge from x to y in the *updated* net,
          -- but we have to bring it down to the *original* net.
          have h₄ : (hebb net A).graph.Edge x y := by
            rw [← edge_iff_preds]
            rw [← edge_iff_preds] at edge_xy
            convert edge_xy using 1

          exact ⟨u, ⟨(Graph.Path.from_path path₂ h₄), hu⟩⟩

-- If m ∉ Prop(A) or n ∉ Prop(A), then the weight of m ⟶ n in
-- the *once* updated net is the same as in the original net.
--------------------------------------------------------------------
theorem hebb_once_weights_eq (net : Net Node) :
  (m ∉ propagate net A ∨ n ∉ propagate net A)
  → (hebb net A).graph.Weight m n =
    net.graph.Weight m n := by
--------------------------------------------------------------------
  intro h₁
  simp only [hebb, graph_update]

  -- From here we have two cases; either m ∉ Prop(A) or n ∉ Prop(A).
  -- In either case, the term that we're updating by reduces
  -- to weight + 0 = weight.
  cases h₁
  case inl h₂ =>
    conv => lhs; enter [2, 1, 2]; rw [if_neg h₂]
    simp

  case inr h₂ =>
    conv => lhs; enter [2, 2]; rw [if_neg h₂]
    simp

-- The weights of the new net are nondecreasing
-- (One round of Hebbian update can only increase the weights)
--------------------------------------------------------------------
theorem hebb_once_weights_le (net : Net Node) :
  net.graph.Weight m n ≤
  (hebb net A).graph.Weight m n := by
--------------------------------------------------------------------
  simp only [hebb, graph_update]

  -- Break up the m ∈ Prop(A) and n ∈ Prop(A) cases
  by_cases m ∈ propagate net A
  case neg =>
    rw [if_neg h]

    by_cases n ∈ propagate net A
    case neg => simp [if_neg h]
    case pos => simp [if_pos h]

  case pos =>
    rw [if_pos h]

    by_cases n ∈ propagate net A
    case neg => simp [if_neg h]
    case pos =>
      -- This is the important case, where we use the fact
      -- that net.rate ≥ 0. Knock it out with linarith!
      rw [if_pos h]
      linarith [net.rate_pos]

/-══════════════════════════════════════════════════════════════════
  "Iterated"/Fixed-Point Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- We score neurons by the total sum of *negative* weights coming
-- into them.  The neuron with the lowest score is the least likely
-- to activate (in the worst case where all of its negative signals
-- activate but none of its positive ones do).  If a neuron has
-- no negative incoming weights, we give it a score of 0.
noncomputable
def neg_weight_score (net : Net Node) (n : Node) : ℚ :=
  List.sum (List.map (fun m =>
    if net.graph.Weight m n < 0 then
      net.graph.Weight m n
    else 0)
    (preds net n))

-- NOTE: If there are no nodes to score, a value of 0 is fine.
noncomputable
def min_score (net : Net Node) : ℚ :=
  let scores := List.map (fun n => neg_weight_score net n) net.graph.nodes.elems.toList
  match scores.minimum with
  | some m => m
  | none => 0

-- -- For a *given* n, the neg_weight_score is smaller than
-- -- any possible weighted sum over activated predecessors of n.
-- -- (i.e. no matter what the activation list 'x' is.)
-- --------------------------------------------------------------------
-- lemma neg_weight_score_le (net : Net) (n : ℕ) (fx₁ : ℕ → Bool) :
--   let x : List ℚ := List.map (fun m => if fx₁ m then 1 else 0) (preds net n)
--   let w : List ℚ := List.map (fun m =>
--     Graph.getEdgeWeight net.graph m n) (preds net n)

--   (neg_weight_score net n) ≤ (weighted_sum w x) := by
-- --------------------------------------------------------------------
--   intro x w
--   simp only [neg_weight_score, weighted_sum]

--   -- First, we simplify the foldr and zipWith
--   rw [List.foldr_map]
--   rw [List.zipWith_map]
--   rw [List.zipWith_same]

--   -- By induction on the predecessor list
--   induction preds net n
--   case nil => simp only [List.filter, List.foldr]
--   case cons m ms IH =>
--     simp only [List.foldr]

--     -- We break up the if-statement.
--     by_cases (net.graph.getEdgeWeight m n < 0)

--     -- In this case, we need to show that
--     --     weight ≤ weight * (fx₁ m),
--     -- which is true because (fx₁ m) can only be 0 or 1,
--     -- and weight < 0.
--     case pos =>
--       rw [if_pos h]

--       by_cases (fx₁ m)
--       case pos =>
--         rw [if_pos h]
--         apply add_le_add _ IH
--         simp only [mul_one, le_refl]
--       case neg =>
--         rename_i neg_weight
--         rw [if_neg h]
--         apply add_le_add _ IH
--         rw [Rat.mul_zero]
--         exact le_of_lt neg_weight

--     -- In this case, we need to show that
--     --     0 ≤ weight * (fx₁ m),
--     -- which is true because (fx₁ m) can only be 0 or 1,
--     -- and weight ≥ 0!
--     case neg =>
--       rw [if_neg h]

--       by_cases (fx₁ m)
--       case pos =>
--         rename_i pos_weight
--         rw [if_pos h]
--         rw [Rat.mul_one]
--         apply add_le_add _ IH
--         exact le_of_not_lt pos_weight
--       case neg =>
--         rw [if_neg h]
--         rw [Rat.mul_zero]
--         exact add_le_add rfl IH

-- The *minimum* score is smaller than any individual weight
--------------------------------------------------------------------
lemma min_score_le (net : Net Node) (m n : Node) (hpred : m ∈ preds net n) :
  let weight := net.graph.Weight m n
  min_score net ≤ weight := by
--------------------------------------------------------------------
  intro weight
  simp only [min_score]

  -- These will be convenient for abbreviating later.
  generalize hLst : (List.eraseP (fun x => decide (Graph.Weight net.graph m n =
    if Graph.Weight net.graph x n < 0 then
      Graph.Weight net.graph x n
    else 0)) (preds net n)) = Lst
  generalize hf : (fun m =>
    if Graph.Weight net.graph m n < 0 then
      Graph.Weight net.graph m n
    else 0) = f

  -- Split on the match to ensure that there is a minimum at all.
  split
  case _ min hmin =>
    -------------------------
    -- The min is ≤ the sum of negative weights
    have h₁ : min ≤ List.sum (List.map f (preds net n)) := by
    -------------------------
      simp only [neg_weight_score] at hmin
      simp only [neg_weight_score] at hmin
      apply le_of_not_lt

      -- The minimum thing is a member of the whole list
      apply List.minimum_not_lt_of_mem _ hmin
      rw [← hf]
      apply List.mem_map_of_mem (fun n => List.sum (List.map (fun m =>
        if Graph.Weight net.graph m n < 0 then
          Graph.Weight net.graph m n
        else 0) (preds net n)))
      sorry
      -- simp only [Graph.get_vertices]

      -- Finally, we just need to show that n is a vertex in our graph.
      -- sorry
      -- apply net.graph.edges_from_vertices_right _
      -- exact m
      -- have h₂ : net.graph.hasEdge m n := (edge_iff_preds _ _ _).mp hpred
      -- simp only [Graph.hasEdge] at h₂

      -- -- Split the 'match' (this is tedious, we just have to work for it...)
      -- split at h₂
      -- case _ v h₃ =>
      --   have h₄ : v = n := by
      --     apply byContradiction
      --     intro hcontr
      --     rw [if_neg hcontr] at h₂
      --     exact absurd (symm h₂) (Bool.of_decide_false rfl)

      --   rw [← h₄]
      --   exact lookup_mem _ _ _ h₃
      -- case _ _ =>
      --   exact absurd (symm h₂) (Bool.of_decide_false rfl)

    -------------------------
    -- The sum of negative weights is ≤ any single weight
    have h₂ :
      List.sum (List.map f (preds net n))
      ≤ net.graph.getEdgeWeight m n := by
    -------------------------

      -- We show that the sum of the original list is negative.
      have h₃ : List.sum (List.map f (preds net n)) ≤ 0 := by
        apply sum_le_zero
        intro m _
        rw [← hf]
        simp
        by_cases (Graph.getEdgeWeight net.graph m n < 0)
        case pos =>
          rw [if_pos h]
          apply le_of_lt
          exact h
        case neg => rw [if_neg h]

      -- Next, we show that the sum of the list *without* Weight(m, n)
      -- is negative.
      have h₄ : List.sum (List.erase (List.map f (preds net n))
        (Graph.getEdgeWeight net.graph m n)) ≤ 0 := by
        -- Push in the 'erase'
        rw [List.erase_eq_eraseP]
        rw [List.eraseP_map]
        simp only [Function.comp]

        -- Rewrite Lst and f from earlier
        rw [← hf]
        rw [hLst]
        rw [hf]

        apply sum_le_zero
        intro m hm
        rw [← hLst] at hm
        rw [← hf]
        simp
        by_cases (Graph.getEdgeWeight net.graph m n < 0)
        case pos =>
          rw [if_pos h]
          apply le_of_lt
          exact h
        case neg => rw [if_neg h]

      -- If Weight(m, n) < 0, then this weight is in the list of weights.
      have h₅ : net.graph.getEdgeWeight m n < 0
        → net.graph.getEdgeWeight m n ∈ List.map f (preds net n) := by
        intro h₆
        rw [← hf]
        rw [← @if_pos _ (Rat.instDecidableLtRatInstLTRat _ _) h₆ _
          (Graph.getEdgeWeight net.graph m n) 0]

        exact List.mem_map_of_mem (fun m =>
          if Graph.getEdgeWeight net.graph m n < 0 then
            Graph.getEdgeWeight net.graph m n
          else 0) hpred

      -- We split into two cases;
      --   - Weight(m, n) < 0, and so it's a part of the sum,
      --       and we can pull it out of the sum
      --   - Weight(m, n) ≥ 0, and so it's positive, whereas
      --       the rest of the sum is negative.
      cases lt_or_ge (net.graph.getEdgeWeight m n) 0
      case inl h₆ =>
        rw [← List.sum_erase (h₅ h₆)]
        exact add_le_of_le_of_nonpos le_rfl h₄
      case inr h₆ => exact le_trans h₃ h₆

    exact le_trans h₁ h₂
  case _ hmin =>
    -- The case where there is no minimum is impossible, since
    -- net.graph is nonempty!
    simp [Graph.get_vertices] at hmin
    exact absurd hmin net.nonempty


-- This is the exact number of iterations of Hebbian learning
-- on 'net' and 'S' that we need to make the network unstable,
-- i.e. any activation involved within Prop(S) simply goes through.
noncomputable
def no_times (net : Net Node) : ℕ :=
  let N := ↑(net.graph.nodes.elems.card)
  let iter := Nat.ceil ((net.threshold - N * min_score net) / net.rate)

  -- Ensure that no_times is not 0.
  -- Int.toNat already ensures it is not negative.
  if iter > 0 then iter else 1

--------------------------------------------------------------------
lemma no_times_pos (net : Net Node) :
  0 < no_times net := by
--------------------------------------------------------------------
  simp only [no_times]
  let N := ↑(net.graph.nodes.elems.card)
  generalize hiter : Nat.ceil ((net.threshold - N * min_score net) / net.rate) = iter

  -- We have two cases: either iter > 0 or iter = 1.
  -- In either case, iter is positive.
  cases lt_or_ge 0 iter
  case inl h₁ =>
    rw [if_pos h₁]
    exact h₁
  case inr h₁ =>
    rw [if_neg (not_lt_of_le h₁)]
    decide

-- no_times may seem arbitrary, but we picked it to satisfy precisly
-- this inequality.
--------------------------------------------------------------------
lemma no_times_inequality (net : Net Node) :
  let N := ↑(net.graph.nodes.elems.card)
  net.threshold ≤ (N * min_score net) + (no_times net) * net.rate := by
--------------------------------------------------------------------
  simp only [no_times]
  generalize hiter : Nat.ceil ((net.threshold - ↑(net.graph.nodes.elems.card) * min_score net) / net.rate) = iter

  -- We split into cases based on iter > 0
  cases (lt_or_ge 0 iter)
  case inl h₅ =>
    rw [if_pos h₅]
    rw [← hiter]

    have h₆ :
      (net.threshold - ↑(net.graph.nodes.elems.card) * min_score net) / net.rate * net.rate
      ≤ Nat.ceil ((net.threshold - ↑(net.graph.nodes.elems.card) * min_score net) / net.rate) * net.rate := by
      rw [← hiter] at h₅
      apply mul_le_mul _ le_rfl (le_of_lt net.rate_pos) (le_of_lt _)
      rw [← Nat.ceil_le]
      rw [Nat.cast_pos]
      exact h₅

    have h₇ : net.rate ≠ 0 :=
      fun hcontr => absurd net.rate_pos (not_lt_of_le (le_of_eq hcontr))

    apply le_add_of_le_add_left _ h₆
    rw [div_mul_cancel _ h₇]
    linarith

  case inr h₅ =>
    rw [if_neg (not_lt_of_le h₅)]
    rw [← hiter] at h₅
    simp

    rw [ge_iff_le] at h₅
    simp at h₅
    rw [add_comm]
    rw [← sub_le_iff_le_add]

    have h₆ : ((net.threshold - ↑(net.graph.nodes.elems.card) *
      min_score net) / net.rate) * net.rate ≤ 0 * net.rate :=
      mul_le_mul h₅ le_rfl (le_of_lt net.rate_pos) le_rfl
    have h₇ : net.rate ≠ 0 :=
      fun hcontr => absurd net.rate_pos (not_lt_of_le (le_of_eq hcontr))

    rw [div_mul_cancel _ h₇] at h₆
    simp only [Rat.mul] at h₆
    rw [Rat.zero_mul] at h₆
    exact le_trans h₆ (le_of_lt net.rate_pos)

-- For every m ⟶ n where m, n ∈ Prop(S), increase the weight
-- of that edge by (no_times) * η * act(m) * act(n).
noncomputable
def graph_update_star (net : Net Node) (g : Graph Node) (S : Set Node) : Graph Node :=
{ g with Weight := fun m n =>
    let activ_m := if m ∈ propagate net S then 1 else 0
    let activ_n := if n ∈ propagate net S then 1 else 0
    g.Weight m n + (↑(no_times net) *net.rate * activ_m * activ_n)
}

-- We have exactly the same preservation properties that
-- we had for graph_update.
--------------------------------------------------------------------
lemma graph_update_star_vertices (net : Net Node) (g : Graph Node) (S : Set Node) :
  (graph_update_star net g S).nodes = g.nodes := by
--------------------------------------------------------------------
  simp only [graph_update_star]

--------------------------------------------------------------------
lemma graph_update_star_successors (net : Net Node) (g : Graph Node) (S : Set Node) (n : Node) :
  (graph_update_star net g S).successors n = g.successors n := by
--------------------------------------------------------------------
  simp only [Graph.successors]
  congr 1

--------------------------------------------------------------------
lemma graph_update_star_predecessors (net : Net Node) (g : Graph Node) (S : Set Node) (n : Node) :
  (graph_update_star net g S).predecessors n = g.predecessors n := by
--------------------------------------------------------------------
  simp only [Graph.predecessors]
  congr 1

--------------------------------------------------------------------
lemma graph_update_star_edges (net : Net Node) (g : Graph Node) (S : Set Node) (m n : Node) :
  (graph_update_star net g S).Edge m n ↔ g.Edge m n := by
--------------------------------------------------------------------
  simp only [graph_update_star]

--------------------------------------------------------------------
lemma graph_update_star_path (net : Net Node) (g : Graph Node) (S : Set Node) (m n : Node) :
  Nonempty ((graph_update_star net g S).Path m n) ↔ Nonempty (g.Path m n) := by
--------------------------------------------------------------------
  sorry
  -- By induction on the path in each case.
  -- apply Iff.intro
  -- case mp =>
  --   intro h₁
  --   induction h₁
  --   case trivial => exact Graph.Path.trivial
  --   case from_path x y _ edge_xy IH =>
  --     rw [graph_update_star_edges] at edge_xy
  --     exact Graph.Path.from_path IH edge_xy

  -- case mpr =>
  --   intro h₁
  --   induction h₁
  --   case trivial => exact Graph.Path.trivial
  --   case from_path x y _ edge_xy IH =>
  --     rw [← graph_update_star_edges] at edge_xy
  --     exact Graph.Path.from_path IH edge_xy

--------------------------------------------------------------------
lemma graph_update_star_connected (net : Net Node) (g : Graph Node) (S : Set Node) :
  g.Connected → (graph_update_star net g S).Connected := by
--------------------------------------------------------------------
  simp only [Graph.Connected]
  intro h₁ u v

  rw [graph_update_star_edges]
  rw [graph_update_star_edges]
  rw [graph_update_star_successors]
  rw [graph_update_star_successors]
  rw [graph_update_star_predecessors]
  rw [graph_update_star_predecessors]

  exact h₁ u v

--------------------------------------------------------------------
lemma graph_update_star_acyclic (net : Net Node) (g : Graph Node) (S : Set Node) :
  g.Acyclic → (graph_update_star net g S).Acyclic := by
--------------------------------------------------------------------
  simp only [Graph.Acyclic]
  intro g_acyclic
  intro x

  -- Suppose for contradiction that we *do* have a path from x to itself.
  apply Classical.by_contradiction
  intro h
  rw [not_isEmpty_iff] at h
  rw [graph_update_star_path] at h
  rw [← not_isEmpty_iff] at h
  exact absurd g_acyclic h

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
def hebb_star (net : Net Node) (S : Set Node) : Net Node :=
{ net with
  graph := graph_update_star net net.graph S

  -- We need to check that this new net is still acyclic and connected.
  acyclic := graph_update_star_acyclic _ _ _ net.acyclic
  connected := graph_update_star_connected _ _ _ net.connected
}


/-══════════════════════════════════════════════════════════════════
  Properties of "Iterated" Naive Hebbian Update
══════════════════════════════════════════════════════════════════-/

-- Hebbian update hebb_star does not affect the vertices of the graph.
--------------------------------------------------------------------
theorem hebb_vertices (net : Net Node) (S : Set Node) :
  (hebb_star net S).graph.nodes = net.graph.nodes := by
--------------------------------------------------------------------
  simp only [hebb_star]
  rw [graph_update_star_vertices]

-- Hebbian update hebb_star does not affect the predecessors
-- of any node.
--------------------------------------------------------------------
theorem hebb_preds (net : Net Node) (S : Set Node) :
  preds (hebb_star net S) n = preds net n := by
--------------------------------------------------------------------
  simp only [preds, hebb_star, Graph.predecessors]
  congr 1

-- Hebbian update hebb_star does not affect which neurons are
-- on which layer of the net.
--------------------------------------------------------------------
theorem hebb_layers (net : Net Node) (S : Set Node) :
  layer (hebb_star net S) n = layer net n := by
--------------------------------------------------------------------
  simp only [preds, hebb, layer]

-- Hebbian update hebb_star does not affect the activation function.
--------------------------------------------------------------------
theorem hebb_activation (net : Net Node) (S : Set Node) :
  (hebb_star net S).activation = net.activation := by
--------------------------------------------------------------------
  exact rfl

-- Hebbian update hebb_star does not affect graph reachability
-- (It only affects the edge weights)
--------------------------------------------------------------------
theorem hebb_reach (net : Net Node) (B : Set Node) :
  reachable (hebb_star net A) B =
    reachable net B := by
--------------------------------------------------------------------
  -- Same proof as [hebb_once_reach].
  apply ext
  intro (n : Node)

  apply Iff.intro
  case mp =>
    intro h₁

    -- There is some m with path from m to n in the *updated* net
    match h₁ with
    | ⟨m, path, hm⟩ =>
      induction path
      case trivial hma => exact reach_is_extens _ _ hm
      case from_path x y path_mx edge_xy IH =>
        -- First, apply our IH to get x ∈ Reach(B)
        have h₂ : x ∈ reachable (hebb_star net A) B := ⟨m, ⟨path_mx, hm⟩⟩
        have h₃ : x ∈ reachable net B := IH h₂

        -- So there is some u ∈ B with path from u to x (in the
        -- *original* net).  We extend this path with the edge
        -- from x to y.
        match h₃ with
        | ⟨u, path₂, hu⟩ =>
          -- We have an edge from x to y in the *updated* net,
          -- but we have to bring it down to the *original* net.
          have h₄ : net.graph.Edge x y := by
            rw [← edge_iff_preds]
            rw [← edge_iff_preds] at edge_xy
            convert edge_xy using 1

          exact ⟨u, ⟨(Graph.Path.from_path path₂ h₄), hu⟩⟩

  -- This direction is very similar.
  case mpr =>
    intro h₁

    -- There is some m with path from m to n in the *original* net
    match h₁ with
    | ⟨m, path, hm⟩ =>
      induction path
      case trivial hma => exact reach_is_extens _ _ hm
      case from_path x y path_mx edge_xy IH =>
        -- First, apply our IH to get x ∈ Reach(B)
        have h₂ : x ∈ reachable net B := ⟨m, ⟨path_mx, hm⟩⟩
        have h₃ : x ∈ reachable (hebb_star net A) B := IH h₂

        -- So there is some u ∈ B with path from u to x (in the
        -- *original* net).  We extend this path with the edge
        -- from x to y.
        match h₃ with
        | ⟨u, path₂, hu⟩ =>
          -- We have an edge from x to y in the *updated* net,
          -- but we have to bring it down to the *original* net.
          have h₄ : (hebb net A).graph.Edge x y := by
            rw [← edge_iff_preds]
            rw [← edge_iff_preds] at edge_xy
            convert edge_xy using 1

          exact ⟨u, ⟨(Graph.Path.from_path path₂ h₄), hu⟩⟩

-- If m ∉ Prop(A) or n ∉ Prop(A), then the edge m ⟶ n was not
-- increased by Hebbian update.  So its weight in the updated
-- net is the same as its weight in the original net.
--------------------------------------------------------------------
theorem hebb_weights_eq (net : Net Node) :
  (m ∉ propagate net A ∨ n ∉ propagate net A)
  → ((hebb_star net A).graph.Weight m n =
    net.graph.Weight m n) := by
--------------------------------------------------------------------
  -- Same proof as [hebb_once_weights_eq]
  intro h₁
  simp only [hebb_star, graph_update_star]

  -- From here we have two cases; either m ∉ Prop(A) or n ∉ Prop(A).
  -- In either case, the term that we're updating by reduces
  -- to weight + 0 = weight.
  cases h₁
  case inl h₂ =>
    conv => lhs; enter [2, 1, 2]; rw [if_neg h₂]
    simp

  case inr h₂ =>
    conv => lhs; enter [2, 2]; rw [if_neg h₂]
    simp

-- The weights of the new net are nondecreasing
-- (Hebbian update can only increase the weights)
-- Note that we *cannot* lift this property straightforwardly,
-- since it's an inequality.
--------------------------------------------------------------------
theorem hebb_weights_le (net : Net Node) :
  net.graph.Weight m n ≤
  (hebb_star net A).graph.Weight m n := by
--------------------------------------------------------------------
  simp only [hebb_star, graph_update_star]

  -- Break up the m ∈ Prop(A) and n ∈ Prop(A) cases
  by_cases m ∈ propagate net A
  case neg =>
    rw [if_neg h]

    by_cases n ∈ propagate net A
    case neg => simp [if_neg h]
    case pos => simp [if_pos h]

  case pos =>
    rw [if_pos h]

    by_cases n ∈ propagate net A
    case neg => simp [if_neg h]
    case pos =>
      -- This is the important case, where we use the fact
      -- that net.rate ≥ 0. Knock it out with linarith!
      rw [if_pos h]
      sorry
      -- linarith [net.rate_pos, no_times_pos]

-- A simplification lemma to get the full expression for
-- Weights(m, n) in (hebb_star net).
--------------------------------------------------------------------
theorem hebb_weights_simp (net : Net) (S : Set ℕ) (m n : ℕ) :
  let activ_m := if m ∈ propagate net S then (1 : ℚ) else (0 : ℚ)
  let activ_n := if n ∈ propagate net S then (1 : ℚ) else (0 : ℚ)
  (hebb_star net S).graph.getEdgeWeight m n
  = match List.lookup ⟨m, n⟩ net.graph.weights with
    | some weight => weight + (↑(no_times net) * net.rate * activ_m * activ_n)
    | none => 0 := by
    -- net.graph.getEdgeWeight m n + (↑(no_times net) * net.rate * activ_m * activ_n) := by
--------------------------------------------------------------------
  intro activ_m activ_n
  simp only [hebb_star, graph_update_star]
  simp only [Graph.getEdgeWeight]
  simp only [Prod.mk.eta]
  rw [lookup_map]

  -- Break up the innermost match statement
  induction List.lookup (m, n) net.graph.weights
  case some weight => simp only [some]
  case none => simp only [some]

/-══════════════════════════════════════════════════════════════════
  The more interesting/crucial properties
══════════════════════════════════════════════════════════════════-/

-- The lemma for 'activ' and 'hebb', essentially:
-- activ net prev_activ n  ⟶  activ (hebb_star net A) prev_activ n
--------------------------------------------------------------------
lemma hebb_activ_nondecreasing (net : Net) (A S : Set ℕ) (n : ℕ) :
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
    simp only [mul_zero, le_refl]
  case pos =>
    rw [if_pos h]
    simp only [mul_one, hebb_weights_le _]


-- If n ∉ Prop(A), then activ (hebb_star net A) _ n = activ net _ n.
--------------------------------------------------------------------
theorem hebb_activ_equal₁ (net : Net) (A : Set ℕ) (prev_activ : List ℚ) :
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
theorem hebb_activ_equal₂ (net : Net) (A S : Set ℕ) :
  (∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net S))

  → (activ (hebb_star net A) (List.map (fun i =>
      if propagate_acc net S ((Graph.predecessors net.graph n).get! i)
        (layer net ((Graph.predecessors net.graph n).get! i))
      then 1 else 0)
        (List.range (Graph.predecessors net.graph n).length)) n
  ↔ activ net (List.map (fun i =>
      if propagate_acc net S ((Graph.predecessors net.graph n).get! i)
        (layer net ((Graph.predecessors net.graph n).get! i))
      then 1 else 0)
        (List.range (Graph.predecessors net.graph n).length)) n) := by
--------------------------------------------------------------------
  intro h₁
  apply Eq.to_iff

  -- Do simplifications to get to the weighted sum
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]
  apply congr_arg (fun x => net.activation x = 1)

  -- The weighted sums are equal, ∑ w₁ x₁ = ∑ w₂ x₂,
  -- if all of their entries are equal, w₁ᵢ * x₁ᵢ = w₂ᵢ * x₂ᵢ
  apply weighted_sum_eq
  intro i
  generalize hm : List.get! (Graph.predecessors net.graph n) i = m

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
theorem hebb_activated_by (net : Net) (A B : Set ℕ) :
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
  intro preds prev_activ h₁ h₂ h₃
  simp only [activ]
  rw [hebb_activation net A]
  rw [hebb_preds net A]

  -- NOTE: This is one of the most crucial steps of the whole proof!
  -- We have some threshold 't' at which the activation = 1.
  -- Since the activation function is nondecreasing, we just have
  -- to show that the inner weighted sum ≥ t.
  apply activation_from_inequality _ (net.threshold) _ _ (net.activ_thres)
  apply net.activ_nondecr _ _

  let N := ↑(List.length net.graph.vertices)
  generalize hx : (if m ∈ propagate (hebb_star net A) B then (1 : ℚ) else (0 : ℚ)) = x

  have h₄ : N * min_score net + ↑(no_times net) * net.rate
    ≤ (N - 1) * min_score net + (hebb_star net A).graph.getEdgeWeight m n * x := by

    rw [← hx]
    rw [hebb_weights_simp net A m n]

    rw [if_pos h₃]
    rw [if_pos h₂.2]
    rw [if_pos h₁]
    rw [mul_one, mul_one, mul_one]

    -- Split up the match statement.  In the first case,
    -- we have some weight for m ⟶ n.
    split
    case _ weight h₅ =>
      have h₆ : net.graph.getEdgeWeight m n = weight := by
        simp only [Graph.getEdgeWeight]
        rw [h₅]

      rw [← h₆]
      rw [← add_assoc]
      apply add_le_add_right _ _
      apply le_add_of_le_add_left _ (min_score_le net m n h₂.1)
      apply le_of_eq

      -- From here we just need to show
      --     N * min_score = (N - 1) * min_score + min_score
      -- So we factor out the min_score, and let Lean simp do the rest.
      conv => rhs; enter [2]; rw [← one_mul (min_score net)]
      rw [← right_distrib]
      simp

    -- In this second case, there is no weight from m ⟶ n.
    -- But this is impossible, since it means there is no edge m ⟶ n
    -- whatsoever!
    case _ h₅ =>
      have h₆ : ⟨m, n⟩ ∈ net.graph.edges := by
        rw [edge_iff_preds] at h₂
        exact Graph.edge_of_hasEdge _ _ _ h₂.1
      have h₇ := lookup_none _ _ h₅

      apply absurd h₆
      intro hcontr
      sorry -- Need the connection between edges and weights here...

  exact le_trans (no_times_inequality net)
    (le_trans h₄ sorry)

-- If all predecessors of n (and all predecessors of those, etc.)
-- don't touch Prop(A) ∩ Prop(B), then n is activated in the
-- updated net iff it was in the original net.
--------------------------------------------------------------------
lemma hebb_before_intersection (net : Net) (A B : Set ℕ) (n : ℕ) :
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
  case hz => simp only [propagate_acc]

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
          exact h₁ _ (layer_preds _ _ _ hx)

        rw [simp_propagate_acc _ h] at h₂
        rw [simp_propagate_acc _ h]
        rw [hebb_preds] at h₂
        simp
        simp at h₂

        -- Get ready to apply IH
        -- We write down the usual lemmas for 'm', but we don't
        -- know what the index 'i' is we're grabbing yet.  So
        -- we write these for all i.
        generalize hm : List.get! (Graph.predecessors net.graph n) = m at h₂

        have h₄ : ∀ i, (m i) ∈ preds net n := by
          intro i
          rw [symm hm]
          simp [preds]
          exact get!_mem (net.graph.predecessors n) i

        have h₅ : ∀ i, (layer net (m i)) ≤ L := by
          intro i
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net (m i) n (h₄ i)

        have h₆ : ∀ (i x : ℕ), layer net x < layer net (m i)
          → ¬x ∈ propagate net A ∩ propagate net B := by
          intro i x hx
          exact h₁ _ (lt_trans hx (layer_preds _ _ _ (h₄ i)))

        -- Go into h₂ and apply our inductive hypothesis
        conv at h₂ =>
          enter [2, 1, i]
          rw [hebb_layers]
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
        intro _
        rw [← hL]
        exact propagate_acc_is_extens _ _ h
      case neg =>
        intro h₂

        -- Since *every* node with layer < n is not in Prop(A) ∩ Prop(B),
        -- in particular this holds for n's predecessors.
        have h₃ : ∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net B) := by
          intro x hx
          exact h₁ _ (layer_preds _ _ _ hx)

        rw [simp_propagate_acc _ h]
        rw [simp_propagate_acc _ h] at h₂
        rw [hebb_preds]
        simp
        simp at h₂

        -- Get ready to apply IH
        -- We write down the usual lemmas for 'm', but we don't
        -- know what the index 'i' is we're grabbing yet.  So
        -- we write these for all i.
        generalize hm : List.get! (Graph.predecessors net.graph n) = m


        have h₄ : ∀ i, (m i) ∈ preds net n := by
          intro i
          rw [symm hm]
          simp [preds]
          exact get!_mem (net.graph.predecessors n) i

        have h₅ : ∀ i, (layer net (m i)) ≤ L := by
          intro i
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net (m i) n (h₄ i)

        have h₆ : ∀ (i x : ℕ), layer net x < layer net (m i)
          → ¬x ∈ propagate net A ∩ propagate net B := by
          intro i x hx
          exact h₁ _ (lt_trans hx (layer_preds _ _ _ (h₄ i)))

        -- Go into the goal and apply our inductive hypothesis
        conv =>
          enter [2, 1, i]
          rw [hebb_layers]
          rw [IH (layer net (m i)) (h₅ i) (m i) (h₆ i) rfl]

        -- Unpack the (m i) term
        rw [← hm]

        -- Finally, apply hebb_activ_equal₂.
        exact (hebb_activ_equal₂ net A B h₃).mpr h₂


-- The updated propagation at least contains Prop(A) ∩ Prop(B).
--------------------------------------------------------------------
theorem hebb_extens (net : Net) (A B : Set ℕ) :
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
          rw [edge_iff_preds]
          exact layer_connected _ m n h₂

        -- We apply our IH to m
        rw [← hS] at hm
        have h₄ : layer net m ≤ L := by
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net m n h₃
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
theorem hebb_updated_path (net : Net) (A B : Set ℕ) :
  propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B))
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
    have h₂ : n ∈ (propagate net A) ∩ (propagate net B) :=
      reach_layer_zero _ _ _ hL h₁.2

    exact hebb_extens _ _ _ h₂

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH₁ =>
    -- We have a path from Prop(B) to n, going through Prop(A).
    match h₁.2 with
    | ⟨m, hm⟩ =>
      -- By induction on the length of this path
      induction hm.2

      case trivial => exact hebb_extens _ _ _ hm.1
      case from_path x y path_mx edge_xy _ =>
        -- Split by whether y ∈ B in order to simplify propagate_acc
        by_cases y ∈ (propagate net B)
        case pos => exact hebb_extens _ _ _ ⟨h₁.1, h⟩
        case neg =>
          have m_not_eq_y : m ≠ y := by
            intro hcontr
            rw [← hcontr] at h
            exact absurd hm.1.2 h
            -- exact absurd hm.1.2 sorry
          have y_not_in_B : y ∉ B := by
            intro hcontr
            exact absurd (propagate_is_extens _ _ hcontr) h

          -- Simplifications and rewriting
          simp only [propagate, Membership.mem, Set.Mem]
          rw [hebb_layers]
          rw [hL]
          rw [simp_propagate_acc (hebb_star net A) y_not_in_B]
          rw [hebb_preds]
          simp

          -- THIS IS A CRUCIAL STEP; it depends on the net being fully connected.
          -- Since we have a path from m ⟶ ... ⟶ y, and the net is
          -- fully connected, we actually have a single edge m ⟶ y.
          have edge_my : net.graph.hasEdge m y :=
            Path_edge _ (Graph.Path.from_path path_mx edge_xy) m_not_eq_y
          have hpreds : m ∈ preds net y :=
            (edge_iff_preds _ _ _).mpr edge_my
          have hpred_dec : layer net m ≤ L :=
            (Nat.lt_succ).mp (lt_of_lt_of_eq (layer_preds _ _ _ hpreds) hL)
          have hm_reachable : m ∈ propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) :=
            ⟨hm.1.1, ⟨m, ⟨hm.1, Graph.Path.trivial⟩⟩⟩
          have hm_propB : m ∈ propagate (hebb_star net A) B :=
            IH₁ (layer net m) hpred_dec hm_reachable rfl

          -- Apply simp_hebb_activ₃, which says:
          --  m, y ∈ Prop(A)
          --  There's an edge from m ⟶ y
          --  m ∈ Prop(B) in (hebb_star net)
          --  -------------------------------
          --  y is activ in hebb_star net
          exact hebb_activated_by net A B h₁.1 ⟨hpreds, hm_reachable.1⟩ hm_propB


-- Complementary to [hebb_updated_path]:
--     Prop(A) ∩ Reach(Prop(A) ∩ B) ⊆ Prop*(B)
-- we have
--     Prop(A) ∩ Prop*(B) ⊆ Prop(A) ∩ Reach(Prop(A) ∩ B).
-- This is the key lemma for the forward direction of the reduction;
-- it expresses a lower bound for Prop(A) ∩ Reach(Prop(A) ∩ B).
--------------------------------------------------------------------
theorem reach_of_hebb_prop (net : Net) (A B : Set ℕ) :
  propagate net A ∩ propagate (hebb_star net A) B
  ⊆ propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) := by
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

    exact ⟨propagate_is_extens _ _ h₁.1,
           reach_is_extens _ _
            ⟨propagate_is_extens _ _ h₁.1, propagate_is_extens _ _ h₁.2⟩⟩

  --------------------------------
  -- Inductive Step
  --------------------------------
  case hi L IH =>
    -- First, we case on n ∈ B to simplify propagate_acc.
    by_cases n ∈ B
    case pos => exact ⟨h₁.1, reach_is_extens _ _ ⟨h₁.1, propagate_is_extens _ _ h⟩⟩
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
          rw [edge_iff_preds]
          exact layer_connected _ m n h₂

        have hedge : Graph.hasEdge net.graph m n :=
              (edge_iff_preds _ _ _).mp h₃

        -- We apply our IH to m
        rw [← hS] at hm
        have h₄ : layer net m ≤ L := by
          apply Nat.lt_succ.mp
          rw [symm hL]
          exact layer_preds net m n h₃
        have h₅ : m ∈ propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) :=
          IH _ h₄ hm.1 rfl

        -- n is reachable from the same x ∈ Prop(A) ∩ B
        -- that m is reachable by.
        rw [← hS] at hn
        match h₅.2 with
        | ⟨x, hx⟩ =>
          exact ⟨hn.1, ⟨x, ⟨hx.1, Graph.Path.from_path hx.2 hedge⟩⟩⟩

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

        have h₄ : n ∈ propagate net B :=
          (hebb_before_intersection _ _ _ _ h₃).mp h₁.2

        exact ⟨h₁.1, reach_is_extens _ _ ⟨h₁.1, h₄⟩⟩


/-══════════════════════════════════════════════════════════════════
  Reduction for Unstable Hebbian Update
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
theorem hebb_reduction (net : Net) (A B : Set ℕ) :
  propagate (hebb_star net A) B =
  propagate net (B ∪ (propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)))) := by
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
    simp only [propagate_acc]
    simp only [Union.union, Set.union, Membership.mem, Set.Mem, setOf]
    simp only [Inter.inter, Set.inter, Membership.mem, Set.Mem, setOf]

    -- Forward direction is the easy part, so we do it first.
    -- Backwards direction relies on reach_layer_zero,
    -- a fact about paths when we know n is at layer 0.
    apply Iff.intro
    case mp => exact fun h₁ => Or.inl h₁
    case mpr =>
      intro h₁

      -- Either n ∈ B or n ∈ Prop(A) ∩ Reach(Prop(A) ∩ Prop(B)).
      -- At layer 0, this means n ∈ B, or n ∈ A ∩ B.
      cases h₁
      case inl h₂ => exact h₂
      case inr h₂ =>

        have h₃ : n ∈ (propagate net A) ∩ (propagate net B) :=
          reach_layer_zero _ _ _ hL h₂.2

        simp only [Inter.inter, Set.inter, Membership.mem, Set.Mem, setOf] at h₃
        simp only [Membership.mem, Set.Mem, propagate] at h₃
        rw [hL] at h₃
        simp only [propagate_acc] at h₃
        exact h₃.2

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
      by_cases n ∈ B ∪ (propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)))
      case pos =>
        -- In this case, just apply propagate_is_extens
        rw [← hL]
        simp only [propagate] at h
        exact propagate_acc_is_extens _ _ h

      case neg h₂ =>
        -- From here, we have two cases.  Either:
        --   - n ∈ Prop(A) and ∃ an active predecessor m⟶n in Prop(A)
        --   - or n ∉ Prop(A) *or* all predecessors m⟶n ∉ Prop(A) ∩ Prop(...)
        by_cases (n ∈ propagate net A) ∧
                  (∃ m, m ∈ preds net n ∧
                    m ∈ propagate net A ∩ propagate net (B ∪
                      (propagate net A ∩ reachable net
                        ((propagate net A) ∩ (propagate net B)))))

        ---------------------------------------
        -- Case 1: n ∈ Prop(A)
        -- and some m⟶n ∈ Prop(A) ∩ Prop(B ∪ ...)
        ---------------------------------------
        -- Since m ∈ Prop(B ∪ (Prop(A) ∩ Reach(Prop(A) ∩ Prop(B))))),
        --       m ∈ Prop(B) in the updated net. (by IH)
        -- But by [reach_of_hebb_prop], this means
        --       m ∈ Prop(A) ∩ Reach(Prop(A) ∩ Prop(B))
        -- Then, since m, n ∈ Prop(A) and m ⟶ n,
        --       n ∈ Prop(A) ∩ Reach(Prop(A) ∩ Prop(B))
        case pos =>
          match h.2 with
          | ⟨m, hm⟩ =>
            -- Simplifications to prepare for IH
            simp only [propagate, Membership.mem, Set.Mem] at hm
            simp only [propagate, Membership.mem, Set.Mem] at IH
            simp only [Inter.inter, Set.inter, setOf] at hm
            simp only [Inter.inter, Set.inter, setOf] at IH
            simp only [Membership.mem, Set.Mem] at hm
            simp only [Membership.mem, Set.Mem] at IH

            have hlayer : layer net m ≤ L := by
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact layer_preds net m n hm.1

            conv at hm =>
              enter [2, 2]
              rw [← IH (layer net m) hlayer m rfl]

            -- We can now apply [reach_of_hebb_prop]
            have h₂ : m ∈ propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) :=
              reach_of_hebb_prop _ _ _ hm.2
            have hedge : Graph.hasEdge net.graph m n :=
              (edge_iff_preds _ _ _).mp hm.1

            -- n is reachable from exactly that x ∈ Prop(A) ∩ B
            -- that m is reachable from.
            have h₃ : n ∈ propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) :=
              match h₂.2 with
              | ⟨x, hx⟩ => ⟨h.1, ⟨x, ⟨hx.1, Graph.Path.from_path hx.2 hedge⟩⟩⟩

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
              simp only [preds]
              exact get!_mem (net.graph.predecessors n) i
            have h₃ : Lm ≤ L := by
              rw [symm hLm]
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact layer_preds net m n h₂
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
            generalize hm : List.get! (Graph.predecessors net.graph n) = m at h₁
            have h₄ : ∀ i, (m i) ∈ preds net n := by
              intro i
              rw [symm hm]
              simp only [preds]
              exact get!_mem (net.graph.predecessors n) i

            have h₅ : ∀ i, (layer net (m i)) ≤ L := by
              intro i
              apply Nat.lt_succ.mp
              rw [symm hL]
              exact layer_preds net (m i) n (h₄ i)

            -- Go into h₁ and apply our inductive hypothesis
            conv at h₁ =>
              enter [2, 1, i]
              rw [hebb_layers]
              rw [IH (layer net (m i)) (h₅ i) (m i) rfl]

            -- Unpack the (m i) term
            rw [← hm] at h₁
            rw [← hm]

            -- Apply [hebb_activ_equal₂]
            let S := (B ∪ ((fun n =>
              propagate_acc net A n (layer net n)) ∩ reachable net ((fun n =>
                propagate_acc net A n (layer net n)) ∩
                  (fun n => propagate_acc net B n (layer net n)))))
            rw [hebb_activ_equal₂ _ _ S h₂] at h₁
            exact h₁

    ---------------------
    -- Backward Direction
    ---------------------
    -- We've already worked for this direction; most of the work
    -- is used to prove [hebb_updated_path], which is the crucial lemma here.
    case mpr =>
      intro h₁

      -- By cases; either n ∈ B ∪ (Prop(A) ∩ Reach(Prop(A) ∩ Prop(B))), or not.
      by_cases n ∈ B ∪ (propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)))
      case pos =>
        -- From here, we split again; either:
        --    1. n ∈ B, and by extens n ∈ Prop(B) in (hebb_star net)
        --    2. n ∈ Prop(A) ∩ Reach(B).  In this case, this path
        --       has been updated in the (hebb_star net), so of course
        --       n ∈ Prop(B) in (hebb_star_net) (by [hebb_updated_path])
        cases h
        case inl h₂ =>
          rw [← hL]
          exact propagate_acc_is_extens _ _ h₂
        case inr h₂ =>
          have h₃ : n ∈ propagate (hebb_star net A) B :=
            hebb_updated_path _ _ _ h₂
          simp only [propagate, Membership.mem, Set.Mem] at h₃
          rw [← hL]
          exact h₃

      case neg =>
        -- We get ready to simplify propagate_acc
        have n_not_in_B : n ∉ B :=
          fun n_in_B => absurd (Set.mem_union_left _ n_in_B) h

        -- Simplifications and rewriting, to prepare for IH
        -- We also rewrite the 'preds', 'layers', and 'activ'
        -- for (hebb_star net) in terms of the original 'net'.
        simp only [propagate] at h
        rw [simp_propagate_acc _ n_not_in_B]
        rw [simp_propagate_acc _ h] at h₁
        rw [hebb_preds net A] -- rewrite 'preds'

        -- The plan is to now apply our inductive hypothesis
        -- and use the 'activ_agree' lemmas.
        -- We write the two sets as S₁ and S₂ for convenience
        let S₁ := fun m => propagate_acc net (B ∪ ((fun n =>
          propagate_acc net A n (layer net n)) ∩
          reachable net ((fun n =>
            propagate_acc net A n (layer net n)) ∩ (fun n =>
              propagate_acc net B n (layer net n)) ))) m (layer net m)
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
            exact layer_preds net m n hm
          exact (symm (IH Lm h₃ m hLm).to_eq).to_iff

        -- Argument:
        -- By activ_agree, the predecessors m ∈ Prop(B) (over hebb_star)
        --   activate n *in the original net*
        -- But the weights in the updated net are either the same or
        --   increasing, so by [hebb_activ_nondecreasing], these same
        --   predecessors activate n *in the updated net*.
        simp only [preds]
        simp only [preds] at h₁
        exact hebb_activ_nondecreasing net A S₂ _
          (activ_agree _ S₁ S₂ _ h₂ h₁)

-- COROLLARY: If we plug in Prop(A) ∩ Prop(B) = ∅,
-- then the update has no effect on the propagation!
--------------------------------------------------------------------
theorem hebb_reduction_empty (net : Net) (A B : Set ℕ) :
  propagate net A ∩ propagate net B = ∅ →

  propagate (hebb_star net A) B = propagate net B := by
--------------------------------------------------------------------
  intro h₁
  apply ext
  intro (n : ℕ)

  -- We apply [reach_empty_of_inter_empty]
  -- to get Prop(A) ∩ Reach(Prop(A) ∩ Prop(B)) = ∅
  have h₂ : propagate net A ∩ reachable net ((propagate net A) ∩ (propagate net B)) = ∅ :=
    reach_empty_of_inter_empty _ _ _ h₁

  -- And now we just substitute ∅
  rw [hebb_reduction net A B]
  rw [h₂]
  rw [Set.union_empty B]



-- TODO: Move up!! Prove this!
--
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
-- theorem hebb_iteration_is_well_defined (net : Net) (S : Set ℕ) :
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


-- Save this for later!
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

-- def complete_and_max (net : Net) (A : Set ℕ) : Net :=
--   sorry

-- def fire_together (net : Net) (A : Set ℕ) : Net :=
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
