import Argyle.Logic.InterpretedNet
import Argyle.Logic.InhibitionNet
import Argyle.Logic.PrefModel
import Argyle.Logic.Classical.Base
import Argyle.Logic.Neural.Base
import Argyle.Activation

import Argyle.Operators.Reachable
import Argyle.Operators.Propagate
import Argyle.Helpers
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Logic.Relation
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Contrapose

import Argyle.Logic.Syntax
open Syntax

/-══════════════════════════════════════════════════════════════════
  Building InterpretedNets from PrefModels
══════════════════════════════════════════════════════════════════-/
-- In this section, I'm implementing Hannes Leitgeb's construction
-- for completeness, following his paper
--     "Nonmonotonic reasoning by inhibition nets" (2001)

def Rel.toList (R : Rel World World) : List (World × World) :=
  sorry

-- For any w ∈ M.worlds, we index its predecessors u ≼ w as a list
--     [u₁, u₂, ..., uₖ]
-- This ordering is arbitrary, but the important thing is that it
-- is *fixed* once and for all (so that we can reason about the indices).
def PrefModel.preds (M : PrefModel World) (w : World) : List World :=
  sorry

--------------------------------------------------------------------
theorem preds_index {M : PrefModel World} {u v : World} :
  M.Pref u v → ∃ i, u = ((M.preds v).get i) :=
--------------------------------------------------------------------
  sorry

-- This is the first part of the construction,
--    PrefModel --> Inhibition Net
-- See pages 186, 187 of the (2001) paper.
noncomputable
def PrefModel.toInhibitionNet (M : PrefModel World) : InhibitionNet World :=
  -- For the bias node, we just any arbitrary world that
  -- is less preferred than every other world (may not be unique).
  -- let bias := Classical.choose (Classical.exists_true_of_nonempty M.worlds_nonempty)
  let bias := Classical.choose M.lower_bound

  -- Edge is just the edges of the PrefModel, but with x, y swapped
  -- and all reflexive edges removed.
  -- Excit follows M.Pref, but we extend it so that bias ⟶ n for
  -- all nonminimal n.
{ Edge := fun u v =>
    if u = v then False
    else M.Edge.swap u v
  Excit := M.Pref
  Inhib := fun b ⟨u, v⟩ =>
    -- Note that we do the reverse of Leitgeb, and
    -- place inhibition edges as follows:
    --     preds[0] ⟶ ⟨preds[k-1], v⟩
    --     preds[i+1] ⟶ ⟨preds[i], v⟩
    -- (it's a bit easier to map things backwards in
    --  a functional programming language)
    let preds := (Finset.filter (fun u => M.Pref u v) M.worlds.elems).toList
    match preds.indexOf? b with
    | none => False
    | some Nat.zero => (preds.indexOf u) = (preds.length - 1)
    | some (Nat.succ i) => (preds.indexOf u) = i

  proposition_map := fun p => { w | M.proposition_eval p w }

  nodes := M.worlds
  bias := bias
  acyclic := by
    -- Follows from the fact that the PrefModel is reflexive, transitive,
    -- and antisymmetric, but we have to work a bit for it.
    simp only [Acyclic]
    apply by_contradiction
    intro h
    push_neg at h
    sorry
    -- conv at h => enter [1, x]; rw [not_isEmpty_iff]; rw [Rel.swap_path]

    -- match h with
    -- | ⟨w, hw⟩ => sorry
  connected := sorry -- Now much harder to prove!
    -- sorry -- Rel.swap_connected M.edges_connected

  -- If we have an excitation edge Excit m n,
  -- then we have an "ordinary" edge Edge m n.
  excit_edge := by
    intro m n h₁
    simp only [Rel.swap]
    have h₂ : m ≠ n := by
      intro hcontr
      rw [hcontr] at h₁
      exact absurd h₁ (M.pref_irrefl n)

    rw [if_neg h₂]
    exact M.pref_edges _ _ h₁

  inhib_excit := by
    intro b m n h₁
    conv at h₁ => simp
    generalize hpreds : (Finset.filter (fun u => M.Pref u n) M.worlds.elems).toList = preds
    rw [hpreds] at h₁

    -- We show that m is a predecessor of n, by cases on
    -- the index of m in preds(n)
    have h₂ : m ∈ preds := by
      sorry
      -- split at h₁
      -- case _ h₂ => exact h₁.elim
      -- case _ h₂ => exact indexOf?_some.mpr ⟨0, h₂⟩
      -- case _ i h₂ => exact indexOf?_some.mpr ⟨i + 1, h₂⟩

    -- We can now show that Pref m n by definition of filter
    rw [← hpreds] at h₂
    rw [Finset.mem_toList] at h₂
    rw [Finset.mem_filter] at h₂
    exact h₂.2
}

-- This is the second part of the construction,
--    Inhibition Net --> Interpreted ANN
-- See page 193 of the (2001) paper.
noncomputable
def InhibitionNet.toNet (N : InhibitionNet Node) : InterpretedNet Node := {
  net := {
    graph := {
      Edge := N.Edge
      Weight := sorry
      nodes := N.nodes
    }

    -- We just use a binary step activation function.
    -- The rate is somewhat arbitrary, since for the purposes
    -- of this construction we don't care about learning.
    -- So we just pick rate=1.
    activation := binary_step
    rate := 1
    rate_pos := by simp

    -- One possible threshold at which the activation function
    -- activates is T=1.
    binary := binary_step_is_binary
    activ_nondecr := binary_step_nondecr
    threshold := 1
    activ_thres := by simp

    bias := N.bias
    acyclic := N.acyclic
    connected := N.connected
  }

  proposition_map := N.proposition_map
}

-- We put the two parts of the construction together to get our Net!
noncomputable
def PrefModel.toNet (M : PrefModel World) : InterpretedNet World :=
  (M.toInhibitionNet).toNet

--------------------------------------------------------------------
lemma reachable_toNet {M : PrefModel World} {S : Set World} {w : World} :
  w ∈ reachable (M.toNet.net) S ↔ ∃ u, u ∈ S ∧ M.Edge w u  := by
--------------------------------------------------------------------
  apply Iff.intro
  case mp =>
    intro h₁
    match h₁ with
    | ⟨u, path, hu⟩ =>
      -- There's a path from u to w; so by induction on that path
      induction path
      case trivial => exact ⟨u, ⟨hu, M.edges_refl u⟩⟩
      case from_path x y path_ux edge_xy IH =>
        have h₂ : x ∈ reachable (PrefModel.toNet M).net S := by
          exact ⟨u, ⟨path_ux, hu⟩⟩
        have h₃ : M.Edge y x := by
          simp only [PrefModel.toNet, PrefModel.toInhibitionNet] at edge_xy
          simp only [InhibitionNet.toNet] at edge_xy
          simp only [Rel.swap] at edge_xy

          by_cases x = y
          case pos => rw [if_pos h] at edge_xy; exact edge_xy.elim
          case neg => rw [if_neg h] at edge_xy; exact edge_xy

        -- By IH there exists a v ∈ S with M.Edge
        match IH h₂ with
        | ⟨v, hv⟩ => exact ⟨v, ⟨hv.1, M.edges_trans h₃ hv.2⟩⟩

  case mpr =>
    intro h₁
    match h₁ with
    | ⟨u, hu⟩ =>
      by_cases u = w
      case pos =>
        rw [← h]
        exact reach_is_extens _ _ hu.1
      case neg =>
        have h₂ : Graph.Edge (PrefModel.toNet M).net.graph u w := by
          simp only [PrefModel.toNet, InhibitionNet.toNet]
          simp only [PrefModel.toInhibitionNet]
          rw [if_neg h]
          exact hu.2
        exact ⟨u, ⟨Rel.Path.from_path Rel.Path.trivial h₂, hu.1⟩⟩

--------------------------------------------------------------------
lemma propagate_toNet_helper₁ {M : PrefModel World} {S : Set World} :
  (M.toInhibitionNet).propagate S = (M.Pref.best (Sᶜ))ᶜ := by
--------------------------------------------------------------------
  apply Set.ext
  intro w
  simp only [InhibitionNet.propagate]
  simp only [Membership.mem, Set.Mem]

  -- By induction on the layer of 'w' in the *Inhibition Net*
  generalize hL : (PrefModel.toInhibitionNet M).layer w = L
  induction L using Nat.case_strong_induction_on generalizing w

  ---------------------
  -- Base Step
  ---------------------
  case hz =>
    simp only [InhibitionNet.propagate_acc]
    apply Iff.intro

    case mp =>
      intro h₁
      cases h₁

      -- CASE: w ∈ S.  So w ∉ Sᶜ, so by [best_inclusion], w ∉ (best(Sᶜ))ᶜ.
      case inl h₂ =>
        intro h
        simp at h
        have h₃ : w ∈ (Sᶜ) := best_inclusion h
        exact absurd h₂ h₃

      -- CASE: w is the 'bias' node
      case inr h₂ =>
        simp only [PrefModel.toInhibitionNet] at h₂
        rw [← @Set.mem_def _ _ (Rel.best M.Pref (Sᶜ)ᶜ)]
        rw [Set.mem_compl_iff]
        rw [not_best_iff]

        by_cases w ∈ Sᶜ
        case neg => exact Or.inl h
        case pos => exact Or.inr ⟨w, ⟨h, M.pref_irrefl w⟩⟩

    case mpr =>
      -- We apply [prop_layer_zero]
      intro h₁
      sorry
      -- simp only [PrefModel.toInhibitionNet]


      -- apply (PrefModel.toInhibitionNet M).prop_layer_zero S w hL
      -- apply (PrefModel.toInhibitionNet M).propagate_is_extens

      -- rw [← Set.not_mem_compl_iff]
      -- intro hcontr

  ---------------------
  -- Inductive Step
  ---------------------
  case hi L IH =>
    simp only [InhibitionNet.propagate_acc]
    apply Iff.intro

    ---------------------
    -- Forward Direction
    ---------------------
    case mp =>
      intro h₁
      cases h₁

      -- CASE : w ∈ S. Again, w ∉ Sᶜ, so by [best_inclusion], w ∉ (best(Sᶜ))ᶜ.
      case inl h₂ =>
        intro h
        simp at h
        have h₃ : w ∈ (Sᶜ) := best_inclusion h
        exact absurd h₂ h₃

      -- CASE: w is activated by some u, and there is no inhibitory
      --   edge that stops this.
      case inr h₂ =>
        match h₂ with
        | ⟨u, hu⟩ =>
          push_neg at hu

          -- First, we check whether u is the 'bias' node.
          -- If so, we immediately have our goal, w ∉ best(Sᶜ).
          have hedge : M.toInhibitionNet.Excit u w := hu.2.2.1
          simp only [PrefModel.toInhibitionNet] at hedge

          -- By our Inductive Hypothesis, u ∈ (best(Sᶜ))ᶜ,
          -- i.e. u ∉ best(Sᶜ).
          have h₃ : u ∉ M.Pref.best (Sᶜ) := by
            generalize hLu : M.toInhibitionNet.layer u = Lu
            rw [hLu] at hu
            rw [hL] at hu
            rw [IH Lu (Nat.le_of_lt_succ hu.1) u hLu] at hu
            exact hu.2.1

          -- This is where we apply the Smoothness condition!
          -- By smoothness, since u is not the best(Sᶜ), some
          -- other v ≺ u is the best(Sᶜ).
          cases M.pref_smooth (Sᶜ) u
          case inl h₄ => exact absurd h₄ h₃
          case inr h₄ =>
            match h₄ with
            | ⟨v, hv⟩ =>
              -- But since v is the best(Sᶜ), w is not the best(Sᶜ)!
              -- And this is exactly what we needed to show!
              rw [← @Set.mem_def _ _ (Rel.best M.Pref (Sᶜ)ᶜ)]
              rw [Set.mem_compl_iff]
              rw [not_best_iff]

              have h₅ : M.Pref v w := M.pref_trans hv.1 hedge
              have h₆ : v ∈ Sᶜ := best_inclusion hv.2
              exact Or.inr ⟨v, ⟨h₆, (PrefModel.not_pref_of_pref h₅)⟩⟩
          /-
          by_cases u = M.toInhibitionNet.bias
          case pos =>
            -- CASE: u is the 'bias' node.  We show that this leads
            -- to a contradiction (this case is impossible.)
            simp only [PrefModel.toInhibitionNet] at h
            rw [if_pos h] at hedge
            rw [not_best_iff] at hedge
            rw [← @Set.mem_def _ _ (Rel.best M.Pref (Sᶜ)ᶜ)]
            rw [Set.mem_compl_iff]
            rw [not_best_iff]

            cases hedge
            case inl h₃ => sorry
            case inr h₃ =>
              have h₄ := Classical.choose_spec M.lower_bound
              rw [← h] at h₄
              exact Or.inr ⟨u, ⟨sorry, PrefModel.not_pref_of_pref sorry⟩⟩

          case neg =>
            simp only [PrefModel.toInhibitionNet] at h
            rw [if_neg h] at hedge

            -- By our Inductive Hypothesis, u ∈ (best(Sᶜ))ᶜ,
            -- i.e. u ∉ best(Sᶜ).
            have h₃ : u ∉ M.Pref.best (Sᶜ) := by
              generalize hLu : M.toInhibitionNet.layer u = Lu
              rw [hLu] at hu
              rw [hL] at hu
              rw [IH Lu (Nat.le_of_lt_succ hu.1) u hLu] at hu
              exact hu.2.1

            -- This is where we apply the Smoothness condition!
            -- By smoothness, since u is not the best(Sᶜ), some
            -- other v ≺ u is the best(Sᶜ).
            cases M.pref_smooth (Sᶜ) u
            case inl h₄ => exact absurd h₄ h₃
            case inr h₄ =>
              match h₄ with
              | ⟨v, hv⟩ =>
                -- But since v is the best(Sᶜ), w is not the best(Sᶜ)!
                -- And this is exactly what we needed to show!
                rw [← @Set.mem_def _ _ (Rel.best M.Pref (Sᶜ)ᶜ)]
                rw [Set.mem_compl_iff]
                rw [not_best_iff]

                have h₅ : M.Pref v w := M.pref_trans hv.1 hedge
                have h₆ : v ∈ Sᶜ := best_inclusion hv.2
                exact Or.inr ⟨v, ⟨h₆, (PrefModel.not_pref_of_pref h₅)⟩⟩
            -/
    ---------------------
    -- Backward Direction
    ---------------------
    case mpr =>
      contrapose
      intro h₁
      push_neg at h₁
      rw [← @Set.mem_def _ _ (Rel.best M.Pref (Sᶜ)ᶜ)]
      rw [Set.mem_compl_iff]
      simp

      -- In fact, *every* predecessor of w will activate.
      -- Intuitively: These predecessors will each inhibit each
      -- other, which prevents w from firing!
      have h₂ : ∀ u, M.toInhibitionNet.layer u < M.toInhibitionNet.layer w →
        M.toInhibitionNet.Excit u w → u ∈ M.toInhibitionNet.propagate S := by

        -- Suppose not. Then we have *some* u ⟶ w that is inactive.
        -- By the Well-Ordering principle, we get the one with the *greatest*
        -- index (so all other uᵢ ⟶ w of smaller index are active).
        -- (Well-ordering applies in the reverse this way because lists are finite.)
        apply by_contradiction
        intro hcontr
        push_neg at hcontr

        generalize hpreds : (Finset.filter (fun u => M.Pref u w) M.worlds.elems).toList = preds
        let X : Set World := fun u =>
          M.toInhibitionNet.layer u < M.toInhibitionNet.layer w ∧
          M.toInhibitionNet.Excit u w ∧ u ∉ M.toInhibitionNet.propagate S
        have hwf : WellFounded (fun u v => preds.indexOf? u > preds.indexOf? v) := by
          sorry
        let u := WellFounded.min hwf X hcontr

        -- Note that u is a predecessor of v, by definition.
        have hu : u ∈ preds := sorry

        -- By cases on the index of u; either u is preds[0]
        -- or u is preds[i+1].
        generalize hindx : preds.indexOf? u = indx
        cases indx
        case a.none => exact absurd hu (indexOf?_none.mpr hindx)
        case a.some val =>
          cases val
          case zero =>
            -- In this case, *none* of the predecessors of w are
            -- active!  But this is absurd, since 'bias' is always
            -- a predecessor of every node, and bias ∈ Prop(S)!
            sorry

          case succ i =>
            -- We want to look at the "previous" node, i.e. if u is preds[i+1]
            -- we want to look at that u' at preds[i].
            generalize hu' : preds.get! i = u'

            /-
            ∀ (m : World),
            InhibitionNet.layer (PrefModel.toInhibitionNet M) m < InhibitionNet.layer (PrefModel.toInhibitionNet M) w →
            InhibitionNet.propagate_acc (PrefModel.toInhibitionNet M) S m
                (InhibitionNet.layer (PrefModel.toInhibitionNet M) m) →
              InhibitionNet.Excit (PrefModel.toInhibitionNet M) m w
            -/
            have h₃ : M.toInhibitionNet.layer u' < M.toInhibitionNet.layer u := by
              sorry

            have h₄ : u' ∈ M.toInhibitionNet.propagate S := by
              sorry

            have h₅ : M.toInhibitionNet.Excit u' w := by
              sorry

            -- We can finally apply our assumption to u':
            -- u' is an active predecessor of w, so it has some
            -- b ⟶ ⟨u', w⟩ inhibiting *it*.  But by matching on
            -- this b, we see that b = u.
            match h₁.2 u' h₃ h₄ h₅ with
            | ⟨b, hb⟩ =>
              have h₆ := hb.2.2
              simp only [PrefModel.toInhibitionNet] at h₆
              split at h₆
              case _ h₇ => exact h₆
              case _ h₇ =>
                rw [hpreds] at h₆
                rw [hpreds] at h₇
                sorry

              case _ i h₇ =>
                rw [hpreds] at h₆
                rw [hpreds] at h₇
                sorry




        -- let u' : World :=
        --   match indx with
        --   | none => absurd hu (indexOf?_none.mpr hindx)
        --   | some Nat.zero => preds.get! (preds.length - 1)
        --   | some (Nat.succ i) => preds.get! i



        -- match (generalizing := true) preds.indexOf? u with
        -- | none => sorry
        -- | some Nat.zero => sorry
        -- | some (Nat.succ i) => sorry

        -- cases preds.indexOf? u
        -- case a.none => sorry
        -- case a.some val =>
        --   cases val
        --   case zero => sorry
        --   case succ i => sorry

        -- match indx with
        -- | none =>
        --   have h₃ : u ∈ preds := by
        --     sorry
        --   rw [← indexOf?_none] at hindx
        --   exact absurd h₃ hindx

        -- | some Nat.zero =>
        --   sorry

        -- | some (Nat.succ i) =>
        --   let u' := preds.get! (i + 1)
        --   sorry

        -- We now consider the node immediately after 'u' in the preds,
        -- i.e. if u is preds[i], this u' is preds[i+1]
        -- let u' := preds.get! (preds.indexOf? u + 1)

        -- This u is both in the set, and is the smallest such u.
        -- have hu : u ∈ X ∧ ∀ v, v ∈ X →
        --   (preds.indexOf? u < preds.indexOf? v) ∨ preds.indexOf? u = preds.indexOf? v :=
        --   sorry
          -- ⟨WellFounded.min_mem _ _ _,
          --   fun v hv => WellFounded.not_lt_min hwf _ _ hv⟩

        -- cases (hu.2 _ _)
        -- case inl h₂ => sorry
        -- case inr h₂ => sorry

        -- By the Well-Ordering principle, this u ⟶ w is the *least*
        -- such one that is inactive.


        -- match hcontr with
        -- | ⟨u, hu⟩ =>


          /-
          -- Using Well-Ordering principle:
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
          -/

          /-
          -- Breaking apart Inhibition edge:
          intro b m n h₁
          conv at h₁ => simp
          generalize hpreds : (Finset.filter (fun u => M.Pref u n) M.worlds.elems).toList = preds
          rw [hpreds] at h₁

          -- We show that m is a predecessor of n, by cases on
          -- the index of m in preds(n)
          have h₂ : m ∈ preds := by
            split at h₁
            case _ h₂ => exact h₁.elim
            case _ h₂ => exact indexOf?_some.mpr ⟨0, h₂⟩
            case _ i h₂ => exact indexOf?_some.mpr ⟨i + 1, h₂⟩
          -/


      -- Applying our Inductive Hypothesis, this says that every
      -- u ≺ w is NOT a best(Sᶜ)-world!
      have h₃ : ∀ u, M.Pref u w → u ∉ M.Pref.best (Sᶜ) := by
        sorry

      -- But by Smoothness, this means we must have w ∈ best(Sᶜ)!
      -- (We prove by cases, but just rule out the negative case.)
      cases M.pref_smooth (Sᶜ) w
      case inl h₄ => exact h₄
      case inr h₄ =>
        apply absurd h₄
        push_neg
        exact h₃



--------------------------------------------------------------------
lemma propagate_toNet_helper₂ {N : InhibitionNet Node} {S : Set Node} :
  propagate (N.toNet.net) S = N.propagate S := by
--------------------------------------------------------------------
  sorry
  /-
  apply Set.ext
  intro n
  simp only [InhibitionNet.propagate, Membership.mem, Set.Mem]
  simp only [propagate]

  -- By induction on the layer of the net containing n
  -- (to split up the ANN propagation)
  generalize hL : layer N.toNet.net n = L
  induction L

  ---------------------
  -- Base Step
  ---------------------
  case zero =>
    -- Most of these cases are trivial (either n ∈ S or n = bias),
    -- except for the last case which we show is impossible.
    simp only [propagate_acc]
    apply Iff.intro

    case mp =>
      intro h₁
      simp only [InhibitionNet.toNet] at h₁
      cases h₁
      case inl h₂ => exact Or.inl h₂
      case inr h₂ => exact Or.inr (Or.inl h₂)

    case mpr =>
      intro h₁
      simp only [InhibitionNet.toNet]
      cases h₁
      case inl h₂ => exact Or.inl h₂
      case inr h₂ =>
        cases h₂
        case inl h₃ => exact Or.inr h₃
        case inr h₃ =>
          -- This is the case that we will show is impossible.
          -- (n can't be at layer 0 *and* have some m ⟶ n)
          -- Right now the hypothesis gives us an m with Excit m n,
          -- so we'll match on that m.
          match h₃ with
          | ⟨m, hm⟩ =>
            have h₄ : (InhibitionNet.toNet N).net.graph.Edge m n := by
              simp only [InhibitionNet.toNet]
              exact N.excit_edge _ _ hm.1

            have h₅ : layer (InhibitionNet.toNet N).net m < 0 := by
              simp at hL
              rw [← hL]
              apply layer_preds
              rw [edge_iff_preds]
              exact h₄

            exact absurd h₅ (Nat.not_lt_zero (layer _ m))

  ---------------------
  -- Inductive Step
  ---------------------
  case succ L IH =>
    apply Iff.intro

    -- Forward direction
    case mp =>
      intro h₁
      simp only [propagate_acc] at h₁
      cases h₁

      case inl h₂ => exact Or.inl h₂
      case inr h₂ =>
        apply Or.inr
        apply Or.inr
        sorry

    -- Backward direction
    -- We have three cases; either
    --    - n ∈ S
    --    - n = bias
    --    - We have Excit m n for some m, and no inhibitory synapse
    --        stops this activation.
    case mpr =>
      simp only [propagate_acc]
      intro h₁
      cases h₁

      case inl h₂ => exact Or.inl h₂
      case inr h₂ =>
        cases h₂
        case inl h₃ =>
          -- TODO: Prove that this case is impossible!
          -- (n = bias can only be on layer 0!!)
          sorry
        case inr h₃ =>
          -- This is the important case (Excit m n, and no inhibitory
          -- synapses stop this)
          sorry
  -/

--------------------------------------------------------------------
lemma propagate_toNet {M : PrefModel World} {S : Set World} :
  propagate (M.toNet.net) S = (M.Pref.best (Sᶜ))ᶜ := by
--------------------------------------------------------------------
  simp only [PrefModel.toNet]
  rw [propagate_toNet_helper₂]
  rw [propagate_toNet_helper₁]

-- This is the big theorem, which says that
-- PrefModel.toNet is a homomorphism.
-- This corresponds to the *COMPLETENESS* of the neural semantics
-- (in other words, this is the hard part!)
--------------------------------------------------------------------
theorem toNet_homomorphism {M : PrefModel World} {ϕ : Formula} {w : World} :
  (M.toNet; w ⊩ ϕ) ↔ (M; w ⊩ ϕ) := by
--------------------------------------------------------------------
  induction ϕ generalizing w

  case proposition p =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp [PrefModel.toNet, PrefModel.toInhibitionNet, InhibitionNet.toNet]

  case top =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    simp [InterpretedNet.top]
    exact trivial

  case _ ϕ IH =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    rw [Set.mem_compl_iff]
    rw [not_iff_not]
    exact IH

  case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂

  case Know ϕ IH =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    conv => lhs; simp
    simp only [Neural.Base.satisfies, Neural.Base.interpret] at IH
    rw [not_iff_comm]
    rw [reachable_toNet]
    push_neg

    -- Rephrase our Inductive Hypothesis
    have IH : (⟦ϕ⟧_PrefModel.toNet M)ᶜ = {u | (M; u ⊩ ϕ)}ᶜ := by
      apply Set.ext
      intro w; simp
      rw [not_iff_not]
      exact IH

    -- Go in and apply IH to the right-hand side.  Then just swap the ∧!
    conv => rhs; enter [1, u, 1]; rw [IH]; simp
    conv => rhs; enter [1, u]; rw [and_comm]

  case Typ ϕ IH =>
    simp only [Classical.Base.satisfies]
    simp only [Neural.Base.satisfies, Neural.Base.interpret]
    rw [propagate_toNet]
    simp

    -- Go in and apply IH to the right-hand side
    conv => rhs; enter [2, w, 2, u, 1, u]; rw [← IH]

--------------------------------------------------------------------
theorem toNet_models {M : PrefModel World} {ϕ : Formula} :
  Neural.Base.models (M.toNet) ϕ ↔ Classical.Base.models M ϕ := by
--------------------------------------------------------------------
  simp only [Classical.Base.models, Neural.Base.models]
  apply Iff.intro
  case mp => exact fun h₁ n => toNet_homomorphism.mp (h₁ n)
  case mpr => exact fun h₁ w => toNet_homomorphism.mpr (h₁ w)

/-══════════════════════════════════════════════════════════════════
  Completeness for Classical Base Logic
══════════════════════════════════════════════════════════════════-/



/-══════════════════════════════════════════════════════════════════
  Completeness for Neural Base Logic
══════════════════════════════════════════════════════════════════-/
-- Since we already have model building & completeness for the
-- base logic, and we can build an InterpretedNet from a PrefModel,
-- we get model building & completeness for free!



/-══════════════════════════════════════════════════════════════════
  Completeness for Neural Hebb Logic
══════════════════════════════════════════════════════════════════-/




/-══════════════════════════════════════════════════════════════════
  OLD: Soundness constructions that I decided I don't need
  right now.  They do not help with proving completeness
  for the neural semantics (and we've already shown soundness
  anyway, they're a bit redundant).
══════════════════════════════════════════════════════════════════-/
-- First, a couple of lemmas which establish soundness
-- for each of our frame properties (it's cleaner to separate
-- them from the main definition)
-- --------------------------------------------------------------------
-- lemma connected_toPrefModel {Net : InterpretedNet} :
--   Connected (Relation.ReflTransGen (Graph.hasEdge_Rel Net.net.graph)) := by
-- --------------------------------------------------------------------
--   intro x y
--   -- The model is connected because *Net* is connected!
--   cases (Net.net.connected x y)
--   case inl h₁ =>
--     apply Or.inl
--     apply Relation.ReflTransGen.single
--     exact Net.net.graph.hasEdgeRel_of_hasEdge x y h₁
--   case inr h₂ =>
--     cases h₂
--     case inl h₂₁ =>
--       apply Or.inr
--       apply Or.inl
--       apply Relation.ReflTransGen.single
--       exact Net.net.graph.hasEdgeRel_of_hasEdge y x h₂₁
--     case inr h₂₂ =>
--       apply Or.inr
--       apply Or.inr
--       sorry


-- def InterpretedNet.toPrefModel (Net : InterpretedNet) : PrefModel := {
--   -- worlds - just neurons in the neural net
--   -- edges  - the reflexive-transitive closure of edges in the neural net
--   worlds := Net.net.graph.get_vertices -- Net.net.graph.vertices  (make it a Set!)
--   edges := Relation.ReflTransGen Net.net.graph.hasEdge_Rel
--   pref := sorry
--   proposition_eval := fun p w => w ∈ Net.proposition_map p

--   -- "Soundness" direction for each of the frame properties
--   edges_refl := IsRefl.reflexive
--   edges_trans := Relation.transitive_reflTransGen
--   edges_connected := connected_toPrefModel

--   pref_refl := sorry
--   pref_trans := sorry
-- }

-- -- The following lemmas relate the Propagation in the
-- -- InterpretedNet to the 'Best' function in the PrefModel.
-- -- These were first shown by Hannes Leitgeb (2001).
-- --------------------------------------------------------------------
-- lemma best_eq_propagate {Net : InterpretedNet} {A : Set ℕ} :
--   (Net.toPrefModel).best A = (propagate Net.net (Aᶜ))ᶜ :=
-- --------------------------------------------------------------------
--   sorry

-- -- This is the first big theorem, which says that
-- -- InterpretedNet.toPrefModel is a homomorphism,
-- -- i.e. preserves the satisfaction relation (and truth as well).
-- -- This corresponds to the *SOUNDNESS* of the neural semantics.
-- --------------------------------------------------------------------
-- lemma toPrefModel_homomorphism {Net : InterpretedNet} {ϕ : Formula} {n : ℕ} :
--   (Net.toPrefModel; n ⊩ ϕ) ↔ (Net; n ⊩ ϕ) := by
-- --------------------------------------------------------------------
--   induction ϕ
--   case proposition p =>
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     simp only [InterpretedNet.toPrefModel]

--   case top =>
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [InterpretedNet.top]
--     simp [Classical.Base.satisfies]
--     exact trivial

--   case _ ϕ IH =>
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     rw [Set.mem_compl_iff]
--     rw [not_iff_not]
--     exact IH

--   case _ ϕ ψ IH₁ IH₂ => exact and_congr IH₁ IH₂

--   case Know ϕ IH =>
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     sorry


--   case Typ ϕ IH =>
--     simp only [Neural.Base.satisfies, Neural.Base.interpret]
--     simp only [Classical.Base.satisfies]
--     rw [best_eq_propagate]
--     sorry

-- --------------------------------------------------------------------
-- theorem toPrefModel_models {Net : InterpretedNet} {ϕ : Formula} :
--   Classical.Base.models (Net.toPrefModel) ϕ ↔ Neural.Base.models Net ϕ := by
-- --------------------------------------------------------------------
--   simp only [Classical.Base.models, Neural.Base.models]
--   apply Iff.intro
--   case mp => exact fun h₁ n => toPrefModel_homomorphism.mp (h₁ n)
--   case mpr => exact fun h₁ w => toPrefModel_homomorphism.mpr (h₁ w)
