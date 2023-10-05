import Argyle.Net
open Set

/-══════════════════════════════════════════════════════════════════
  Graph Reachability
══════════════════════════════════════════════════════════════════-/

--------------------------------------------------------------------
theorem Path_of_preds {m n : ℕ} (net : Net) :
  m ∈ preds net n → net.graph.Path m n := by
--------------------------------------------------------------------
  intro h₁
  exact Graph.Path.from_path (Graph.Path.trivial) ((edge_iff_preds _ _ _).mp h₁)

-- Any nontrivial path can be shortcutted with an edge
-- (this is because the graph is connected.)
-- TODO: Fix this proof tomorrow,
--   and continue replacing reachable with reachable!
--------------------------------------------------------------------
theorem Path_edge {u v : ℕ} (net : Net) :
  net.graph.Path u v → u ≠ v → net.graph.hasEdge u v := by
--------------------------------------------------------------------
  intro h₁
  
  induction h₁
  case trivial => 
    -- This case is impossible (we assumed *nontrivial*)
    exact fun h₂ => absurd rfl h₂
  case from_path x y _ edge_xy IH =>
    intro _

    -- Either u = x or u ≠ x.
    by_cases u = x
    case pos =>
      rw [h]
      exact edge_xy
    case neg =>
      have h₄ : layer net u < layer net x := 
        layer_preds _ _ _ ((edge_iff_preds _ _ _).mpr (IH h))
      have h₅ : layer net x < layer net y := 
        layer_preds _ _ _ ((edge_iff_preds _ _ _).mpr edge_xy)
      
      exact layer_connected _ _ _ (lt_trans h₄ h₅)

-- Set of nodes reachable from S
def reachable (net : Net) (S : Set ℕ) : Set ℕ :=
  fun (n : ℕ) =>
    ∃ (m : ℕ), m ∈ S ∧ net.graph.Path m n

--------------------------------------------------------------------
lemma reach_layer_zero (net : Net) : ∀ (B : Set ℕ) (n : ℕ),
  layer net n = 0
  → n ∈ reachable net B
  → n ∈ B := by
--------------------------------------------------------------------
  intro B n h₁ h₂

  match h₂ with
  | ⟨m, hm⟩ => 
    -- By induction on the length of the path from B to n.
    --   path length = 0 => m ∈ B means n ∈ B
    --   path length ≥ 0 => this case should be impossible,
    --                      because at layer 0 n has *no predecessors*!
    induction hm.2
    case trivial => exact hm.1
    case from_path x y _ edge_xy _ => 
      -- Contradiction; y's layer is 0, but there is an edge from x to y!
      have h₃ : layer net x < layer net y :=
        layer_preds net x y ((edge_iff_preds _ _ _).mpr edge_xy)
      
      exact absurd h₁ (Nat.not_eq_zero_of_lt h₃)

--------------------------------------------------------------------
theorem reach_empty (net : Net) :
  reachable net ∅ = ∅ := by
--------------------------------------------------------------------
  apply ext
  intro n
  apply Iff.intro

  -- This direction is impossible
  case mp => 
    intro h₁
    match h₁ with
    | ⟨m, hm⟩ => 
      -- We have some m ∈ ∅, which is absurd!
      exact absurd hm.1 (Set.not_mem_empty m)

  -- This direction is trivial
  case mpr => 
    intro h₁
    exact ⟨n, ⟨h₁, Graph.Path.trivial⟩⟩
    

-- If A ∩ B is empty, then there are no nodes reachable
-- from B within A.
-- (This does *not* follow from [reach_is_extens]!)
--------------------------------------------------------------------
theorem reach_empty_of_inter_empty (net : Net) : ∀ (A B : Set ℕ),
  (A ∩ B) = ∅ → A ∩ reachable net (A ∩ B) = ∅ := by
--------------------------------------------------------------------
  intro A B
  rw [← Set.not_nonempty_iff_eq_empty]
  rw [← Set.not_nonempty_iff_eq_empty]
  
  -- Start a proof by contraposition, and simplify
  contrapose
  intro h₁
  rw [Classical.not_not]
  rw [Classical.not_not] at h₁

  -- Since A ∩ Reach(B) is nonempty, we have n ∈ A ∩ Reach(B).
  -- We argue that the m ∈ B that reaches n must be m ∈ A ∩ B.
  match h₁ with
  | ⟨n, hn⟩ => 
    match hn.2 with
    | ⟨m, hm⟩ => exact ⟨m, hm.1⟩

--------------------------------------------------------------------
theorem reach_is_extens (net : Net) : ∀ (B : Set ℕ),
  B ⊆ reachable net B := by
--------------------------------------------------------------------
  intro B n h₁
  exact ⟨n, ⟨h₁, Graph.Path.trivial⟩⟩
  

--------------------------------------------------------------------
theorem reach_is_idempotent (net : Net) : ∀ (B : Set ℕ),
  reachable net B = reachable net (reachable net B) := by
--------------------------------------------------------------------
  intro B
  apply ext
  intro n
  apply Iff.intro

  -- Forward direction
  -- (easy; just apply reach_is_extens)
  case mp => 
    intro h₁
    exact reach_is_extens _ _ h₁

  -- Backwards direction
  case mpr => 
    intro h₁
    match h₁ with
    | ⟨m, hm⟩ =>
      match hm.1 with
      | ⟨x, hx⟩ => exact ⟨x, ⟨hx.1, Graph.Path_trans _ hx.2 hm.2⟩⟩

--------------------------------------------------------------------
theorem reach_is_monotone (net : Net) : ∀ (A B : Set ℕ),
  A ⊆ B → reachable net A ⊆ reachable net B := by
--------------------------------------------------------------------
  intro A B h₁ n h₂

  exact match h₂ with
  | ⟨m, hm⟩ => ⟨m, ⟨(h₁ hm.1), hm.2⟩⟩

-- Reach is closed under union
-- (This is really a consequence of monotonicity)
--------------------------------------------------------------------
theorem reach_union (net : Net) : ∀ (A B : Set ℕ),
  reachable net (A ∪ B) = (reachable net A) ∪ (reachable net B) := by
--------------------------------------------------------------------
  intro A B
  apply ext
  intro n
  apply Iff.intro

  -- Backwards direction
  -- (easy; just monotonicity)
  case mpr =>
    intro h₁
    cases h₁
    case inl h₂ => exact reach_is_monotone _ _ _ (subset_union_left _ _) h₂
    case inr h₂ => exact reach_is_monotone _ _ _ (subset_union_right _ _) h₂

  -- Forward direction
  case mp =>
    intro h₁

    -- We have a path from m ∈ A ∪ B to n.
    -- In either case, the path from m ⟶ n gives us n ∈ Reach(_).
    match h₁ with
    | ⟨m, hm⟩ =>
      cases hm.1
      case inl h₂ => exact Or.inl ⟨m, ⟨h₂, hm.2⟩⟩
      case inr h₂ => exact Or.inr ⟨m, ⟨h₂, hm.2⟩⟩
