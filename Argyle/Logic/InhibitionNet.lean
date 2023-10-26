import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rel
import Argyle.Helpers

-- Inhibition Nets, an implementation of Hannes' construction
-- following his paper:
--    "Nonmonotonic reasoning by inhibition nets" (2001)
--
-- An Inhibition Net is a special net that has no weights,
-- but inhibitory synapses control the flow of activation).
-- It turns out that binary ANNs are equivalent to
-- Inhibition Nets (the inhibitory synapses simulate
-- negative weights).
--
-- An inhibitory edge connects a node to an excitatory edge, e.g.:
--
--         a --------> b
--               |
--               |
--         c ----⧸
--
-- Additionally, there are no weights or activation functions.
-- Excitatory edges always go through, unless some inhibitory
-- edge is currently preventing it from going through.
-- There are three types of edges:
--   - Edge: Do nothing, act as a "skeleton" for excitatory edges.
--   - Excit: Excitatory edges that always go through, unless inhibited
--   - Inhib: Inhibitory edges that prevent excitatory edges from going through

-- NOTE: As with InterpretedNets, we add a proposition mapping
-- as well.  We also have a 'bias' node, which occurs in *every*
-- activation.
structure InhibitionNet (Node : Type) where
  Edge : Rel Node Node -- NOTE: Skeleton edges do nothing; they just specify
                           -- where the excitatory edges can be
  Excit : Rel Node Node
  Inhib : Rel Node (Node × Node) -- need to be connected to excitatory_edges!!!
  proposition_map : String → Set Node

  -- There are finitely many nodes, and there is some node 'bias' ∈ Node.
  -- (bias is a node which shows up in the propagation of every signal.)
  nodes : Fintype Node
  bias : Node

  -- The graph is nonempty, acyclic and fully connected.
  acyclic : Acyclic Edge
  connected : Connected Edge

  -- The relationships between each of the edge types
  excit_edge : ∀ (m n : Node), Excit m n → Edge m n
  inhib_excit : ∀ (b m n : Node), Inhib b ⟨m, n⟩ → Excit m n

-- Propagation in an Inhibition Net
-- Essentially, n is active iff some node m excites n
-- and there is no inhibitory node b that stops this activation.
-- Note that the 'bias' node always activates.
def InhibitionNet.propagate (net : InhibitionNet Node) (S : Set Node) : Set Node :=
  fun n => n ∈ S ∨ (n = net.bias) ∨
    ∃ m, net.Excit m n ∧ ¬∃ b, net.Inhib b ⟨m, n⟩
