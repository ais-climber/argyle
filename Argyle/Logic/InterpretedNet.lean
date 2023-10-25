import Argyle.Net

-- Interpreted nets are just neural networks,
-- along with a mapping from propositions to sets of neurons.
-- Adding this extra mapping is what allows us to use
-- neural networks as logic models.
structure InterpretedNet (Node : Type) where
  net : Net Node
  proposition_map : String → Set Node

-- We abbreviate the 'top' state of the net (the set of
-- all neurons)
-- TODO: Update when I make sets finite.  This should really
-- be Finset.univ (or something like that to make the proofs go through)
def InterpretedNet.top (_ : InterpretedNet Node) : Set Node :=
  Set.univ
