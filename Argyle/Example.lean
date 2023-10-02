-- Notice that this graph is acyclic, since each predecessor
-- list only refers to nodes above the current node.
/-
def graphA : Graph ℕ ℚ :=
{ vertices := [0, 1, 2, 3]
  edges := 
    [ ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, 
      ⟨1, 2⟩, ⟨1, 3⟩,
      ⟨2, 3⟩
    ]
  weights :=
    [ ⟨⟨0, 1⟩, 0.5⟩,
      ⟨⟨0, 2⟩, 0.6⟩,
      ⟨⟨0, 3⟩, 0.7⟩,
      ⟨⟨1, 2⟩, 0.8⟩,
      ⟨⟨1, 3⟩, 0.9⟩,
      ⟨⟨2, 3⟩, 1.0⟩,
      ⟨⟨2, 3⟩, 3.0⟩
    ]
  edges_from_vertices_left := sorry
  edges_from_vertices_right := sorry
}
-/

-- TODO: Make graph a Repr!
-- #check graphA
-- #eval graphA

-- Some sanity checks
-- #eval get_vertices graphA
-- #eval successors graphA 0
-- #eval successors graphA 1
-- #eval successors graphA 2
-- #eval successors graphA 3
-- #eval predecessors graphA 0
-- #eval predecessors graphA 1
-- #eval predecessors graphA 2
-- #eval predecessors graphA 3
-- #eval hasEdge graphA 1 2
-- #eval hasEdge graphA 1 3
-- #eval hasEdge graphA 3 2
-- #eval getEdgeWeight graphA 1 2
-- #eval getEdgeWeight graphA 1 3
-- #eval getEdgeWeight graphA 3 2

-- Put in examples file!  (We don't need to figure it out
-- right now!)
-- def myNet : Net :=
--   {
--     graph := graphA
--     activation := binary_step
--     rate := 1

--     binary := binary_step_is_binary
--     -- sort := (topSortUnsafe graphA).toList.reverse
--     acyclic := sorry -- graphA_is_acyclic
--     activ_nondecr := binary_step_nondecr
--     activ_pos := sorry
--   }

/-
-- Put in example file!
-- 0 jumps to 2, 1 jumps to 3, short connection from 1 to 2
def layer_test_graph : Graph ℕ ℚ :=
  ⟨[⟨0, [⟨2, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨1, [⟨2, 0.5⟩, ⟨3, 0.5⟩]⟩, -- ⟨4, 0.5⟩
    ⟨2, []⟩, -- ⟨4, 0.5⟩
    ⟨3, [⟨4, 0.5⟩]⟩, -- remove ⟨4, 0.5⟩
    
    -- Add a new edge, and toggle which previous edge jumps to it.
    ⟨4, []⟩]⟩

def layer_test_net : Net :=
  { graph := layer_test_graph, activation := binary_step, rate := 1,
    binary := binary_step_is_binary,
    activ_nondecr := binary_step_nondecr, activ_pos := sorry
  }

#eval layer layer_test_net 0
#eval layer layer_test_net 1
#eval layer layer_test_net 2
#eval layer layer_test_net 3
#eval layer layer_test_net 4
-/

-- #check propagate myNet {n : ℕ | n ≤ 4}
-- #eval propagate myNet {n : ℕ | n ≤ 4}
-- need to make sets finite in order to evaluate???
-- 
-- It's important for everything to be evaluatable, since:
-- 1) I will want to verify that a *specific*
--    neural network has certain properties
-- 2) #eval helps me debug errors

-------------------------------------------------
-- Example:  Our graphA is acyclic
-- (We should just be able to call 'Topological Sort'
-- on the graph and check if that is successful.)
-------------------------------------------------
-- Put in examples file! (and figure it out later, we don't need
-- it right now)
-- 
-- theorem graphA_is_acyclic : graphA.is_acyclic := by
--   intro (u : ℕ) (v : ℕ)
--         (path_uv : Path graphA u v)
--         (path_vu : Path graphA v u)

--   sorry