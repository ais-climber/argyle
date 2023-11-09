import Mathlib.Data.List.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rel
set_option checkBinderAnnotations false

-------------------------------------------------
-- Helper functions and lemmas
-------------------------------------------------

inductive Rel.Path (R : Rel α α) : α → α → Type where
  | trivial {u : α} :
      Path R u u
  | from_path {u v w : α} :
      Path R u v → R v w → Path R u w

--------------------------------------------------------------------
theorem Path_trans {u v w : α} (R : Rel α α) :
  R.Path u v → R.Path v w → R.Path u w := by
--------------------------------------------------------------------
  intro (h₁ : R.Path u v)
  intro (h₂ : R.Path v w)

  induction h₂
  case trivial => exact h₁
  case from_path x y _ edge_xy path_ux =>
    exact Rel.Path.from_path path_ux edge_xy

-- TODO: Fill these out!!!
/-
def Path_length {u v : Node} (g : Graph Node) : g.Path u v → ℕ :=
  sorry

noncomputable
def distance (g : Graph Node) (u v : Node) : ℕ :=
  sorry
-/

-- Note that we don't allow reflexive edges at all.
-- We do this by simply saying "the type of paths from x to x
-- is empty."
def Acyclic (R : Rel α α) : Prop :=
  ∀ {x : α}, IsEmpty (Rel.Path R x x)

-- ∀ {x y : α}, IsEmpty (∃ (_ : R.Path x y), ∃ (_ : R.Path x y), ⊤)


-- Strangely not in the standard library
-- A relation is fully connected iff all elements x y
-- are either related, or have exactly the same image
-- and preimage over R.
def Connected (R : Rel α α) : Prop := ∀ (x y : α),
  (R x y) ∨ (R y x)
  ∨ (R.image {x} = R.image {y}
      ∧ R.preimage {x} = R.preimage {y})

def Rel.swap (R : Rel α α) : Rel α α :=
  fun u v => R v u

-- If we swap a connected relation we get a connected relation.
-- (We should be able to generalize this to *any* property on R...)
--------------------------------------------------------------------
theorem Rel.swap_connected {R : Rel α α} :
  Connected R → Connected R.swap := by
--------------------------------------------------------------------
  simp only [Connected, swap]
  intro h₁ x y
  cases h₁ x y

  -- The first two cases are easy (either R x y or R y x,
  -- and we just swap whichever is true.)
  case inl h₂ => exact Or.inr (Or.inl h₂)
  case inr h₂ =>
    cases h₂
    case inl h₃ => exact Or.inl h₃
    case inr h₃ =>
      -- In this case, the image of the swapped is the preimage of the
      -- original, and vice-versa!
      sorry

-- If we have a path from u to v over R, then we also
-- have a path from v to u over R.swap
--------------------------------------------------------------------
theorem Rel.swap_path {R : Rel α α} {u v : α} :
  Nonempty (R.swap.Path v u) ↔ Nonempty (R.Path u v) := by
--------------------------------------------------------------------
  simp only [swap]
  apply Iff.intro
  case mp =>
    intro h₁
    match Classical.exists_true_of_nonempty h₁ with
    | ⟨x, hx⟩ =>
      sorry
      -- exact nonempty_of_exists ⟨_, _⟩

  case mpr => sorry

-- This isn't in the standard library, but essentially it says:
-- If we treat xs like an association list, and we *don't*
-- change the indices, lookup after mapping f to the outputs
-- is the same as applying f to the original lookup.
--------------------------------------------------------------------
theorem lookup_map (xs : List ((ℕ × ℕ) × ℚ)) (a : ℕ × ℕ) (f : ((ℕ × ℕ) × ℚ) → ℚ) :
  List.lookup a (List.map (fun x => (x.1, f x)) xs) =
    match List.lookup a xs with
    | some v => f (a, v)
    | none => none := by
--------------------------------------------------------------------
  induction xs
  case nil => simp
  case cons x xs IH =>
    simp only [List.map, List.lookup]

    -- Break up the inner match statements, and apply our IH!
    by_cases (a = x.fst)
    case pos => simp [h]
    case neg =>
      have h₁ : (a == x.fst) = false := by
        apply Classical.byContradiction
        intro hcontr
        exact absurd (eq_of_beq (eq_true_of_ne_false hcontr)) h

      simp [h₁]
      exact IH

-- This should *also* be in the standard library, but isn't!
--------------------------------------------------------------------
theorem lookup_mem (xs : List (ℕ × ℕ)) (a b : ℕ) :
  (List.lookup a xs = some b) → (a, b) ∈ xs := by
--------------------------------------------------------------------
  intro h₁

  induction xs
  case nil => simp at h₁
  case cons x xs IH =>
    simp only [List.lookup] at h₁

    -- Split up the match!
    split at h₁
    case _ h₂ =>
      have h₃ : x = (a, b) := by
        rw [Prod.eq_iff_fst_eq_snd_eq]
        simp
        simp at h₁
        simp at h₂
        exact ⟨symm h₂, h₁⟩

      rw [h₃]
      exact List.mem_cons_self _ _
    case _ _ => exact List.mem_cons_of_mem _ (IH h₁)

/-
List.lookup (m, n) net.graph.weights = none
-/

-- This should *also* be in the standard library, but isn't!
--------------------------------------------------------------------
theorem lookup_none (xs : List ((ℕ × ℕ) × ℚ)) (a : ℕ × ℕ) :
  (List.lookup a xs = none) → ∀ (b : ℚ), (a, b) ∉ xs := by
--------------------------------------------------------------------
  intro h₁ b

  induction xs
  case nil => simp
  case cons x xs IH =>
    simp only [List.lookup] at h₁

    -- Split up the match!
    split at h₁
    case _ h₂ =>
      intro hcontr
      sorry
      -- have h₃ : x = (a, b) := by
      --   rw [Prod.eq_iff_fst_eq_snd_eq]
      --   simp
      --   simp at h₁
      --   simp at h₂
      --   exact ⟨symm h₂, h₁⟩

      -- rw [h₃]
      -- exact List.mem_cons_self _ _
    case _ h₂ =>
      intro hcontr
      rw [List.mem_cons] at hcontr

      -- We split; either (a, b) = x or (a, b) ∈ xs
      cases hcontr
      case inl h₃ =>
        simp at h₂
        have h₄ : b = x.2 := by
          apply symm
          apply Prod.snd_eq_iff.mpr
          apply symm
          sorry

        apply h₂
        apply symm
        apply Prod.fst_eq_iff.mpr
        apply symm
        rw [← h₄]
        exact h₃
        -- exact h₂ (symm (Prod.fst_eq_iff.mpr (symm _)))
        -- conv at h₂ =>
        --   simp; enter [1]
        --   rw [Prod.fst_eq_iff]
        -- simp at h₂

        -- -- rw [symm _ _] at h₂
        -- rw [Prod.fst_eq_iff] at h₂
        -- exact h₂ _
      case inr h₃ => exact IH h₁ h₃
      -- sorry -- exact List.mem_cons_of_mem _ (IH h₁)

-- I think this should be in the standard library, but it isn't.
-- It says: If every member of a sum is ≤ 0, then the whole sum is ≤ 0.
--------------------------------------------------------------------
theorem sum_le_zero {lst : List ℕ} {f : ℕ → ℚ} :
  (∀ (a : ℕ), a ∈ lst → f a ≤ 0)
  → List.sum (List.map f lst) ≤ 0 := by
--------------------------------------------------------------------
  intro h₁
  induction lst
  case nil => rw [List.map_nil, List.sum_nil]
  case cons x xs IH =>
    simp only [List.map]
    rw [List.sum_cons]

    -- f(x) ≤ 0 and Sum(Map(xs)) ≤ 0,
    -- so their sum ≤ 0.
    have h₂ : f x ≤ 0 := by simp [h₁]
    have h₃ : ∀ (a : ℕ), a ∈ xs → f a ≤ 0 := by
      intro a ha
      simp [h₁, ha]

    exact add_nonpos h₂ (IH h₃)

--------------------------------------------------------------------
theorem sizeOf_erase (xs : List ℕ) (a : ℕ) :
  sizeOf (List.erase xs a) ≤ sizeOf xs := by
--------------------------------------------------------------------
  induction xs
  case nil => simp [List.erase]
  case cons x xs IH =>
    simp only [List.erase]

    -- Split the match
    split
    case _ _ _ => simp
    case _ _ _ => simp [IH]

-- List.erase_of_not_mem is in the standard library,
-- but the other direction is not!
--------------------------------------------------------------------
theorem not_mem_of_erase {xs : List ℕ} {a : ℕ} :
  (List.erase xs a) = xs → a ∉ xs := by
--------------------------------------------------------------------
  induction xs
  case nil => simp
  case cons x xs IH =>
    intro h₁
    simp only [List.erase] at h₁

    -- Split the match
    split at h₁
    case _ _ _ =>
      -- This case is impossible, since xs = x :: xs!
      exact absurd (symm h₁) (List.cons_ne_self x xs)
    case _ _ h₂ =>
      simp at h₁
      simp at h₂
      intro hcontr

      -- Either a = x or a ∈ xs. Either way we get a contradiction.
      cases (List.mem_cons).mp hcontr
      case inl h₃ => exact absurd (symm h₃) h₂
      case inr h₃ => exact absurd h₃ (IH h₁)

/-══════════════════════════════════════════════════════════════════
  Forward propagation in a net
══════════════════════════════════════════════════════════════════-/

-- I would like to write
--     List.sum [w * x | for w in weights, for x in lst],
-- but list comprehensions are harder to reason about.
def weighted_sum (weights : List ℚ) (lst : List ℚ) : ℚ :=
  List.sum (List.zipWith (· * ·) weights lst)


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

  apply List.sum_le_sum
  intro m _
  exact h₁ m

--------------------------------------------------------------------
theorem indexOf?_some [BEq α] {ls : List α} {x : α} :
  x ∈ ls ↔ (∃ (i : ℕ), List.indexOf? x ls = some i) := by
--------------------------------------------------------------------
  induction ls
  case nil => simp [List.indexOf?, List.findIdx?]
  case cons l ls IH =>
    simp [List.indexOf?, List.findIdx?]
    apply Iff.intro

    case mp =>
      -- Inductively, either x = l or x ∈ ls.
      intro h₁
      cases h₁
      case inl h₂ => sorry
      case inr h₂ => sorry

    case mpr =>
      -- We have some i such that ls.index(x) = some i
      intro h₁
      match h₁ with
      | ⟨i, hi⟩ => sorry

--------------------------------------------------------------------
theorem indexOf?_none [BEq α] {ls : List α} {x : α} :
  x ∉ ls ↔ List.indexOf? x ls = none := by
--------------------------------------------------------------------
  sorry

-- List.indexOf? m (Finset.toList (Finset.filter (fun u => Pref M u n) Fintype.elems)) = some (Nat.succ i)

-- WARNING:
-- This is actually FALSE!  For infinite sets, l[i] is not provably
-- in l (as far as I can figure.)
-- TODO: In the future, when making all this computable, I will
-- be using finite sets, and then I can use get instead of get!,
-- and get_mem in the standard library.
axiom get!_mem {α : Type} [Inhabited α] :
  ∀ (l : List α) i, (l.get! i) ∈ l
