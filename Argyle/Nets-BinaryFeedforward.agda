------------------------------------------------------------------------
-- Nets.BinaryFeedforward
-- 
-- A binary, feed-forward neural network (BFNN)
------------------------------------------------------------------------
-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

open import Data.Bool using (Bool; true; false; T)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.Float using (Float)
open import Data.Vec using (Vec; allFin; take; lookup; fromList; map; []; [_]; _∷_; _++_)
open import Data.List using (List; unzip; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Data.Fin.Subset using (Subset; _⊆_) renaming (_∈_ to memberOf)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Fin using (Fin; _ℕ-ℕ_; toℕ; fromℕ; fromℕ<)
open import Data.Graph.Acyclic using (Graph; ∅; _&_; preds; sucs)

open import Functions-Base using (indegree; preceding-nodes; preceding-weights; fromBool; coerce)
open import Functions-Properties using (Zero-at-Zero; Nondecreasing; same-arity)

-- Decidable
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming (map to dec-map)
open import Relation.Binary.Core

open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- Definition of a BFNN
-- A BFNN consists of:
--   graph - a (float)-weighted, directed acyclic graph 
--           with ℕ node labels
--   activation - the activation function for each node
--   output - the output function for each node
record BFNN {n : ℕ} : Set where
    field 
        graph : Graph ℕ Float n

        activation : {i : ℕ}
            → Fin n → Vec Float i → Vec Float i → Float
        
        output : {i : ℕ}
            → Fin n → Float → Bool

        -- Properties of a BFNN
        -- Note that the graph is binary and acyclic by construction. 
        zero-at-zero : ∀ (node : Fin n)
            → let i = indegree node graph
              in  Zero-at-Zero {n} {graph} {node} activation (output {i})
            
        nondecreasing : ∀ (node : Fin n)
            → let i = indegree node graph
              in  Nondecreasing {n} {graph} {node} activation (output {i})


-- -- Function to make a BFNN from an ordinary neural network
-- -- TODO: From, e.g., Pytorch.
-- make-net : {!   !} → BFNN
-- make-net pytorchModel = record { 
--     graph = {!   !} ; 
--     activation = {!   !} ; 
--     output = {!   !} ; 
--     zeroAtZero = {!   !} ; 
--     monotIncreasing = {!   !}}

-- Function to take the first 'k' indices of a Subset,
-- i.e. to reduce a 'Subset n' to be a 'Subset k'
subset-take : {n : ℕ} (k : ℕ) → Subset n → Subset k
subset-take k set = take {{!   !}} k {!   !}

net-take : {n : ℕ} (k : ℕ)  → BFNN {n} → BFNN {k}
net-take {n} k Net = record { 
    graph = {!   !} ; 
    activation = λ fin-k → (BFNN.activation Net) (fromℕ< {k} {!   !}) ;
    output = {!   !} ; 
    zero-at-zero = {!   !} ; 
    nondecreasing = {!   !} }

{-
Just write propagate by induction on the graph,
and then clean it up using StateMachine and States later.

Get it working first, then improve it.
-}


-- Prove that GraphReach and Propagate are decidable!
-- TODO: Just a placeholder until I can figure out how Decidables actually work...
Drop : Set → Bool
Drop = {!   !}

data GraphReach {n : ℕ} (Net : BFNN {n}) (signal : Subset n) (node : Fin n) : Set where

    in-signal : 
        memberOf node signal
        -----------------------------
        → GraphReach Net signal node

    reached-by : ∀ (m : Fin (toℕ node)) →
        let -- Take the signal and Net up until 'node'
            -- for recursive calls.
            recsignal = subset-take (toℕ node) signal
            recNet = net-take (toℕ node) Net

            -- The neural network's graph
            graph = BFNN.graph Net
        in  
            -- If some 'm' is reached by the signal, and m -> node,
            -- then 'node' is reached by the signal.
              m ∈ preceding-nodes {n} {graph} node
            → GraphReach recNet recsignal m
            -----------------------------
            → GraphReach Net signal node


data Propagate {n : ℕ} (Net : BFNN {n}) (signal : Subset n) (node : Fin n) : Set where

    in-signal : memberOf node signal
        → Propagate Net signal node

    activated-by :
        let -- Take the signal and Net up until 'node'
            -- for recursive calls.
            recsignal = subset-take (toℕ node) signal
            recNet = net-take (toℕ node) Net
        
            -- Define graph, activation, and output
            graph = BFNN.graph Net
            act = BFNN.activation Net
            out = BFNN.output Net

            -- Get activations and weights for mᵢs in previous layer
            -- TODO: The relevant RECURSIVE CALL should look like:
            --       Propagate {toℕ node} recNet recsignal mᵢ
            -- Actually, I think there's an error here --
            -- mᵢs will look like [_, _, _, _],
            -- and won't be a full list of the indices,
            -- and so it will get mapped badly...
            weights = fromList (preceding-weights {n} {graph} node)
            mᵢs = subst (λ e → Vec (Fin (toℕ node)) e) (same-arity node) 
                        (fromList (preceding-nodes {n} {graph} node))
            mᵢ-activations = map (λ mᵢ → fromBool (Drop (Propagate {toℕ node} recNet recsignal mᵢ))) mᵢs
                -- map (λ mᵢ → fromBool 
                -- ⌊ {! DecidePropagate ?  !} ⌋) mᵢs
        in  
            -- Let m₁...mₖ be those mᵢ preceding 'node'.
            -- If the weighted activation of these mᵢs is strong enough,
            -- then 'node' is activated (i.e. propagated by the signal).
            T (out {n} node (act node mᵢ-activations weights))
            --------------------
            → Propagate Net signal node

-- With these, we can state properties such as:
-- Inclusion : {n : ℕ} (Net : BFNN {n})
--     → ∀ S → ∀ node → memberOf node S → GraphReach Net S node

-- Inclusion Net S node = λ node∈S → in-signal node∈S

-- WORKING BACKWARDS:

graph-reach : {n : ℕ} (Net : BFNN {n}) → Subset n → Subset n
graph-reach Net signal = {!   !}

propagate : {n : ℕ} (Net : BFNN {n}) → Subset n → Subset n
propagate Net signal = {!   !}

infix 4 _≡ˢ_

_≡ˢ_ : {n : ℕ} → Subset n → Subset n → Set
A ≡ˢ B = A ⊆ B × B ⊆ A

Reach-Inclusion : {n : ℕ} (Net : BFNN {n}) (S : Subset n) 
    → S ⊆ graph-reach Net S

Reach-Inclusion = {!   !}


Reach-Idempotence : {n : ℕ} (Net : BFNN {n}) (S : Subset n)
    → graph-reach Net S ≡ˢ graph-reach Net (graph-reach Net S)

Reach-Idempotence = {!   !}


Reach-Monotonicity : {n : ℕ} (Net : BFNN {n}) (S1 S2 : Subset n)
    → S1 ⊆ S2 → graph-reach Net S1 ⊆ graph-reach Net S2

Reach-Monotonicity = {!   !}



Prop-Inclusion : {n : ℕ} (Net : BFNN {n}) (S : Subset n) 
    → S ⊆ propagate Net S

Prop-Inclusion = {!   !}


Prop-Idempotence : {n : ℕ} (Net : BFNN {n}) (S : Subset n)
    → propagate Net S ≡ˢ propagate Net (propagate Net S)

Prop-Idempotence = {!   !}


nPreds : {n : ℕ} → Vec Set n → Set
nPreds {zero} [] = ⊤
nPreds {suc n} (Pred ∷ vec) = Pred × nPreds {n} vec

Prop-Loop : {n : ℕ} {k : ℕ} (Net : BFNN {n}) (signals : Vec (Subset n) (suc k))
    → nPreds (map (λ i → 
          lookup signals (Data.Fin.suc i) ⊆ lookup signals (fromℕ< {toℕ i} {!   !})) 
      (allFin k))
    → lookup signals (fromℕ< {0} {! 0  !}) ⊆ lookup signals (fromℕ k)
      ---------------------------
    → {!   !}

Prop-Loop = {!   !}

{-
Prop-Loop : {n : ℕ} (Net : BFNN {n}) (S0 ... Sk : Subset n)
    → S1 ⊆ propagate Net S0
      ...
    → Sk ⊆ propagate Net Sk-1
    → S0 ⊆ propagate Net Sk
    -----------------------
    → Si ≡ˢ Sj for all i, j
-}

-- It would be nice if I could state it cleanly in set notation,
-- e.g.
-- ∀ S → S ⊆ GraphReach Net S

{- ISSUE: Given the current state of affairs, we can't actually
          nest GraphReach!!!
          
          So I probably should define the function from
          Subset n → Subset n,
          and think hard about what I'm doing induction on...!

Idempotence : {n : ℕ} (Net : BFNN {n})
    → ∀ S → ∀ node → {! GraphReach Net S node → GraphReach ()  !}

Idempotence = {!   !}
-}