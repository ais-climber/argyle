import Argyle.Net
import Argyle.Operators.Propagate
import Argyle.Operators.Hebb

open Classical

-------------------------------------------------
-- FLAIRS Paper Results
-- 
-- I realized that some of the results from the
-- FLAIRS paper are incorrect, so I need to run
-- updated versions of the claims in Lean.
-------------------------------------------------

-- I'm choosing to skip [Definition-5] (subnet and net equivalence)
-- because the notation doesn't actually save much space.

-- Not in the original FLAIRS paper, but we will need this lemma.
-- If every *active* predecessor of n ∉ Prop(A), then
-- activ (hebb_star net A) _ n = activ net _ n.
-- Like activ_agree, we have to simplify the statement of this
-- lemma in order for Lean to be able to infer types efficiently.
--------------------------------------------------------------------
lemma flairs_activ_equal₂ (net : Net) (A S : Set ℕ) :
  (∀ x, x ∈ (preds net n) → x ∉ (propagate net A) ∩ (propagate net S))

  → (activ (hebb net A) (List.map (fun i => 
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
  rw [hebb_once_activation net A]
  rw [hebb_once_preds net A]
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
    simp [hebb_once_weights_eq _ (Or.inl h₃)]
    
  -- Otherwise, the RHS's reduce to 0, and so the
  -- weighted sums are trivially equal
  case neg => 
    simp only [propagate, Membership.mem, Set.Mem] at h
    rw [if_neg h]
    simp


-- Not in the original FLAIRS paper, but we will need this lemma.
--------------------------------------------------------------------
lemma flairs_before_intersection (net : Net) (A B : Set ℕ) (n : ℕ) :
  (∀ x, layer net x < layer net n → x ∉ propagate net A ∩ propagate net B) 
  → (n ∈ propagate (hebb net A) B ↔ n ∈ propagate net B) := by
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
        rw [hebb_once_preds] at h₂
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
          rw [hebb_once_layers]
          rw [IH (layer net (m i)) (h₅ i) (m i) (h₆ i) rfl]
        
        -- Unpack the (m i) term
        rw [← hm] at h₂
        rw [← hm]

        -- Finally, apply hebb_activ_equal₂.
        exact (flairs_activ_equal₂ net A B h₃).mp h₂


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
        rw [hebb_once_preds]
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
          rw [hebb_once_layers]
          rw [IH (layer net (m i)) (h₅ i) (m i) (h₆ i) rfl]

        -- Unpack the (m i) term
        rw [← hm]

        -- Finally, apply hebb_activ_equal₂.
        exact (flairs_activ_equal₂ net A B h₃).mpr h₂


-- [Theorem-3-Inclusion]
-- Same as hebb_extens, but for hebb rather than hebb_star
-- NOTE: The original 'inclusion' was Prop(B) ⊆ [A]Prop(B),
-- but this is false!  Instead we have Prop(A) ∩ Prop(B) ⊆ [A]Prop(B)
--------------------------------------------------------------------
theorem flairs_inclusion (net : Net) (A B : Set ℕ) :
  propagate net A ∩ propagate net B 
  ⊆ propagate (hebb net A) B := by
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
    rw [hebb_once_layers]
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
        have h₅ : m ∈ propagate (hebb net A) B :=
          IH _ h₄ hm.1 rfl
        
        -- Simplify and apply simp_hebb_activ₃.
        simp only [Membership.mem, Set.Mem, propagate]
        rw [hebb_once_layers]
        rw [hL]
        rw [simp_propagate_acc _ h]
        rw [hebb_once_preds]
        
        sorry
        -- exact hebb_activated_by net A B h₁.1 ⟨h₃, hm.1.1⟩ h₅
    
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
          exact absurd h₄ (not_lt_of_le (hm.2 _ hx))
        
        exact (flairs_before_intersection _ _ _ n h₃).mpr h₁.2