import Mathlib

-- Minimum working example for a question about convert

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


variable (coll : List ℕ)

example (Pred : List ℕ → Prop) (cond : ℕ → Bool) : 
  Pred [if cond a then 1 else 0 | for a in coll]
  → Pred [if cond b then 1 else 0 | for b in coll] := by
  
  intro h
  convert h
  done
  -- intro h
  -- convert h
  -- done
  -- intro h
  -- convert h
  -- done
  
