------------------------------------------------------------------------
-- Functions.Base
-- 
-- Basic activation functions and other helper functions
-- for doing machine learning.
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _+_; _*_; _≤ᵇ_; _<ᵇ_)
open import Data.Vec using (Vec; foldr; zipWith; []; _∷_)
open import Data.List using (List; length; unzip)
open import Data.Product using (proj₁; proj₂)

open import Data.Fin using (Fin; toℕ)
open import Data.Graph.Acyclic using (Graph; preds)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

------------------------------------------------------------------------
-- Helper functions
-- 
-- TODO: Double-check whether some of these can be found in the standard
-- library!

-- A function to give the indegree of a node in a graph.
-- All of the arguments are implicit so that we can conveniently
-- just say 'indegree' to indicate the current indegree in context.
indegree : {n : ℕ} → Fin n → Graph ℕ Float n → ℕ
indegree {n} node graph = length (preds graph node)

-- Function that gets the predecessors of 'node',
-- i.e. those 'mᵢ' immediately preceding 'node'.
preceding-nodes : {n : ℕ} {graph : Graph ℕ Float n} → 
    (node : Fin n) → List (Fin (toℕ node))
preceding-nodes {n} {graph} node = proj₁ (unzip (preds graph node))

-- Function that gets the weights of the predecessors of 'node'
preceding-weights : {n : ℕ} {graph : Graph ℕ Float n} → 
    (node : Fin n) → List Float
preceding-weights {n} {graph} node = proj₂ (unzip (preds graph node))


-- A function to give a Vec of n zeros
zeros : (n : ℕ) → Vec Float n
zeros zero = []
zeros (suc n) = 0.0 ∷ zeros n

-- A function to help coerce a Vec A into a Vec B
coerce : {n : ℕ} {A B : Set} → (A → B) → Vec A n → Vec B n
coerce {.zero} A→B [] = []
coerce {.(suc _)} A→B (a ∷ vector) = A→B a ∷ (coerce A→B vector)


-- Pointwise less than for Vectors of Floats.
infix 4 _≤ⱽ_
_≤ⱽ_ : ∀ {n : ℕ} → Vec Float n → Vec Float n → Bool
_≤ⱽ_ {zero} [] [] = true
_≤ⱽ_ {suc n} (x1 ∷ v1) (x2 ∷ v2) = 
    (x1 ≤ᵇ x2) ∧ (v1 ≤ⱽ v2)

-- Function to convert Bools to Floats
fromBool : Bool → Float
fromBool true = 1.0
fromBool false = 0.0

------------------------------------------------------------------------
-- Activation and Output function wrappers
-- 
-- These are just convenience functions that wrap neural network 
-- activation and output functions so that they have the correct type 
-- when we pass them into the net.
-- 
-- In wrapping, we do two things:
--   1. Prepend the argument 'Fin n', where 'n' is the indegree
--      of the current node being considered
--   2. Type-cast the inputs and outputs correctly

-- TODO: 
--   make-activation's f should accept Vec's of any type whatsoever
--     e.g. Bool, Int, Float, String
--     and should coerce these into Float before applying f
--   
--   Similarly, make-output's f should return any type whatsoever
--     and should coerce the Float activation into this.
--   
--   Type casting is the real work these functions need to be doing.

make-activation : {n : ℕ} {i : ℕ} (f : Vec Float i → Vec Float i → Float) 
    → Fin n → Vec Float i → Vec Float i → Float
make-activation f = λ n prev-outputs weights → f prev-outputs weights

make-output : {n : ℕ} → (f : Float → Bool) 
    → Fin n → Float → Bool
make-output f = λ n activation → f activation

------------------------------------------------------------------------
-- Various activation functions

weighted-sum : {n : ℕ} → Vec Float n → Vec Float n → Float
weighted-sum v1 v2 = foldr _ _+_ 0.0 (zipWith _*_ v1 v2)

------------------------------------------------------------------------
-- Various output functions

-- Note that the threshold has to be 0.0 in order to guarantee
-- that this function is Zero at Zero.
binary-step : Float → Bool
binary-step activ = 0.0 <ᵇ activ


------------------------------------------------------------------------
-- Example usage for make-activation and make-output
example-act : {n : ℕ} {i : ℕ} → Fin n → Vec Float i → Vec Float i → Float
example-act = make-activation weighted-sum

example-out : {n : ℕ} → Fin n → Float → Bool
example-out = make-output binary-step
