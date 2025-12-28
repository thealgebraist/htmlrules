module CSS.FSM where

open import Data.String
open import Data.List hiding (_++_)
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

{-# FOREIGN GHC import qualified Data.Text.IO as Text
#-}{-# FOREIGN GHC import qualified Data.Text as T
#-}

postulate
  putStrLn : String → IO ⊤

{-# COMPILE GHC putStrLn = Text.putStrLn #-}

-- ------------------------------------------------------------------------
-- FSM DEFINITION
-- Modeling the lifecycle of the HTML/CSS Rendering Engine
-- ------------------------------------------------------------------------

data State : Set where
  Start            : State
  -- Layout Phase
  ComputeStyle     : State
  ResolveWidth     : State
  LayoutChildren   : State
  AccumulateHeight : State
  ResolveHeight    : State
  BoxConstruction  : State
  -- Paint Phase
  StartPaint       : State
  GenerateCmds     : State
  PaintChildren    : State
  End              : State

showState : State → String
showState Start            = "Start"
showState ComputeStyle     = "ComputeStyle"
showState ResolveWidth     = "ResolveWidth"
showState LayoutChildren   = "LayoutChildren"
showState AccumulateHeight = "AccumulateHeight"
showState ResolveHeight    = "ResolveHeight"
showState BoxConstruction  = "BoxConstruction"
showState StartPaint       = "StartPaint"
showState GenerateCmds     = "GenerateCmds"
showState PaintChildren    = "PaintChildren"
showState End              = "End"

-- Transitions with labels describing the logic
record Transition : Set where
  constructor tr
  field
    from  : State
    to    : State
    label : String

fsmTransitions : List Transition
fsmTransitions = 
  -- Initialization
  tr Start ComputeStyle "Receive Viewport, DOM, CSS" ∷
  
  -- Layout Phase (Per Node)
  tr ComputeStyle ResolveWidth "Match Selectors & Cascade" ∷
  tr ResolveWidth LayoutChildren "Calculate Actual Width" ∷
  
  -- Recursion Logic
  tr LayoutChildren ComputeStyle "Recurse: Child Node (Push)" ∷
  tr BoxConstruction AccumulateHeight "Return: Child Done (Pop)" ∷
  tr AccumulateHeight LayoutChildren "Next Sibling (Update Y)" ∷
  
  -- Finalizing Node Layout
  tr LayoutChildren ResolveHeight "No More Children" ∷
  tr ResolveHeight BoxConstruction "Calculate Actual Height" ∷
  
  -- Transition to Painting (After Root Layout)
  tr BoxConstruction StartPaint "Layout Tree Complete" ∷
  
  -- Painting Phase
  tr StartPaint GenerateCmds "Traverse Layout Tree" ∷
  tr GenerateCmds PaintChildren "Emit Draw Command" ∷
  tr PaintChildren GenerateCmds "Recurse: Paint Kids" ∷
  tr GenerateCmds End "Traversal Complete" ∷
  []

-- ------------------------------------------------------------------------
-- DOT GENERATION
-- ------------------------------------------------------------------------

toDot : List Transition → String
toDot [] = ""
toDot (tr f t l ∷ ts) = 
  "  " ++ showState f ++ " -> " ++ showState t ++ " [label=\"" ++ l ++ "\"];\n" ++ toDot ts

generateDot : String
generateDot = 
  "digraph RenderingFSM {\n" ++
  "  rankdir=LR;\n" ++
  "  node [shape=box, style=rounded];\n" ++
  "  Start [shape=circle, style=filled, fillcolor=black, fontcolor=white];\n" ++
  "  End [shape=doublecircle, style=filled, fillcolor=black, fontcolor=white];\n" ++
  "  LayoutChildren [style=filled, fillcolor=lightyellow];\n" ++
  "  ComputeStyle [style=filled, fillcolor=lightblue];\n" ++
  "  GenerateCmds [style=filled, fillcolor=lightgreen];\n\n" ++
  toDot fsmTransitions ++
  "}"

main : IO ⊤
main = putStrLn generateDot
