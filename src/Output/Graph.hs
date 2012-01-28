module Output.Graph ( dotControlGraph, annotateddotControlGraph, sourceAnnotatedEmbellished ) where
  
import Data.Map ( Map )
import Data.List.Utils ( replace )
import qualified Data.Map as Map ( map, mapWithKey , toList )
import qualified Data.Set as Set ( toList, Set )
import Data.List                 ( intersperse )

import Analysis.Monotone
import IPython.Typing (Environment, Var, Type, Context)
import IPython.AST 

import Language.Python.Common.AST (Module)
import IPython.Pretty ( prettyText )
import IPython.Conversion ( from )

dotControlGraph :: Label -> ControlFlow -> String
dotControlGraph startLabel flow = 
        unlines  ["digraph controlgraph {"
                 ,"  \"" ++ show startLabel ++ "\" [color=\"#FF0000\"]"
                 ,"  size=\"6,6\";"
                 ,"  node [color=lightblue2, style=filled];"
                 ]
        ++       unlines (map (nodeToGraph "") flow)
        ++       "}"
        
annotateddotControlGraph :: Label -> ControlFlow -> Map Int Environment -> String
annotateddotControlGraph startLabel flow env = 
        unlines  ["digraph controlgraph {"
                 ,"  \"" ++ show startLabel ++ "\" [color=\"#FF0000\"]"
                 ,"  size=\"6,6\";"
                 ,"  node [color=lightblue2, style=filled];"
                 ]
        ++       unlines (map annotationToGraph (Map.toList env))
        ++       unlines (map (nodeToGraph "") flow)
        ++       "}"
  where annotationToGraph (label , env)  = "  "   ++ show label ++ "[label=\"" ++ show label ++ "\\n" ++ unlinesLit (map printEnvEntry (Map.toList env)) ++ "\"]"


{-
 - Create a graph representation including all contexts in every node. Prints both two graphs, one with the incoming situation, one with the outgoing.
 -}
sourceAnnotatedEmbellished :: (ELattice Environment, ELattice Environment) -> IModule -> ControlFlow -> String
sourceAnnotatedEmbellished (pr, po) code cfg =
     unlines ["digraph controlgraph {"
             ,"  size=\"15,15\";"
             ,"  node [color=lightblue2,shape=record];"
             ]
  ++ unlines ["  code [label=\"" ++ (printCode code) ++ "\"]"]
  ++ unlines (map (printLabel "pre") (filter (\(l, _) -> l /= defaultStartLabel) $ Map.toList pr))
  ++ unlines (map (printLabel "post") (filter (\(l, _) -> l /= defaultStartLabel) $ Map.toList po))
  ++ unlines (map (nodeToGraph "pre") cfg)
  ++ unlines (map (nodeToGraph "post") cfg)
  ++ "}"
  
  where
    printCode = (concatMap (++ "\\l").map (escape.f.show).lines.prettyText.(from :: IModule -> Module LabelAnnot))
    escape = replace "<" "\\<" . replace ">" "\\>" . replace "&" "\\&"
    f = tail . init 
    printLabel :: String -> (Label, Map Context Environment) -> String
    printLabel str (label, ctx) = "  "++str++show label++" [label=\""++show label++" | " ++ ((concat . intersperse "|" . map printCtx . Map.toList) ctx) ++ " \"]"
    printCtx :: (Context, Environment) -> String
    printCtx (ctx, val)   = "{" ++ show ctx ++ "|"++ ((unlinesLit . map printEnvEntry . Map.toList) val)  ++ "}"

-- Helpers
unlinesLit = concatMap (++ "\\n")
printEnvEntry (variable , types) = variable ++ " :: " ++ (show . Set.toList ) types
nodeToGraph str (InterFlow (f , t))  = "  \"" ++ str ++ show f ++ "\" -> \"" ++ str ++ show t ++ "\"[color=\"#ff0000\"]" 
nodeToGraph str (IntraFlow (f , t))  = "  \"" ++ str ++ show f ++ "\" -> \"" ++ str ++ show t ++ "\"[color=\"#00ff00\"]"