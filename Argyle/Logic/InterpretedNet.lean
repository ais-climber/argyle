import Argyle.Net

-- Interpreted nets are just neural networks,
-- along with a mapping from propositions to sets of neurons.
-- Adding this extra mapping is what allows us to use
-- neural networks as logic models.
structure InterpretedNet where
  net : Net
  proposition_map : String → Set ℕ

-- We abbreviate the 'top' state of the net (the set of
-- all neurons)
-- TODO: Update when I make sets finite.  This should really
-- be Finset.univ (or something like that to make the proofs go through)
def InterpretedNet.top (Net : InterpretedNet) : Set ℕ :=
  Set.univ
  -- Net.net.graph.vertices.toFinset

