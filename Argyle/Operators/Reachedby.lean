import Argyle.Net
open Set

/-══════════════════════════════════════════════════════════════════
  Inverse Graph Reachability 'Reached by'
══════════════════════════════════════════════════════════════════-/

-- Set of nodes reachable from S
def reachedby (net : Net) (S : Set ℕ) : Set ℕ :=
  fun (m : ℕ) =>
    ∃ (n : ℕ), n ∈ S ∧ Graph.Path net.graph m n

--------------------------------------------------------------------
theorem reachedby_is_extens (net : Net) : ∀ (B : Set ℕ),
  B ⊆ reachedby net B := by
--------------------------------------------------------------------
  intro B m h₁
  exact ⟨m, ⟨h₁, Graph.Path.trivial⟩⟩

--------------------------------------------------------------------
theorem reachedby_is_idempotent (net : Net) : ∀ (B : Set ℕ),
  reachedby net B = reachedby net (reachedby net B) := by
--------------------------------------------------------------------
  intro B
  apply ext
  intro m
  apply Iff.intro

  -- Forward direction
  -- (easy; just apply reach_is_extens)
  case mp => 
    intro h₁
    exact reachedby_is_extens _ _ h₁
    
  -- Backwards direction
  case mpr => 
    intro h₁
    match h₁ with
    | ⟨n, hn⟩ =>
      match hn.1 with
      | ⟨y, hy⟩ => exact ⟨y, ⟨hy.1, Graph.Path_trans _ hn.2 hy.2⟩⟩

--------------------------------------------------------------------
theorem reachedby_is_monotone (net : Net) : ∀ (A B : Set ℕ),
  A ⊆ B → reachedby net A ⊆ reachedby net B := by
--------------------------------------------------------------------
  intro A B h₁ m h₂

  exact match h₂ with
  | ⟨n, hn⟩ => ⟨n, ⟨(h₁ hn.1), hn.2⟩⟩

--------------------------------------------------------------------
theorem reachedby_union (net : Net) : ∀ (A B : Set ℕ),
  reachedby net (A ∪ B) = (reachedby net A) ∪ (reachedby net B) := by
--------------------------------------------------------------------
  intro A B
  apply ext
  intro m
  apply Iff.intro

  -- Backwards direction
  -- (easy; just monotonicity)
  case mpr =>
    intro h₁
    cases h₁
    case inl h₂ => exact reachedby_is_monotone _ _ _ (subset_union_left _ _) h₂
    case inr h₂ => exact reachedby_is_monotone _ _ _ (subset_union_right _ _) h₂

  -- Forward direction
  case mp =>
    intro h₁

    -- We have a path from m ∈ A ∪ B to n.
    -- In either case, the path from m ⟶ n gives us n ∈ Reach(_).
    match h₁ with
    | ⟨n, hn⟩ =>
      cases hn.1
      case inl h₂ => exact Or.inl ⟨n, ⟨h₂, hn.2⟩⟩
      case inr h₂ => exact Or.inr ⟨n, ⟨h₂, hn.2⟩⟩