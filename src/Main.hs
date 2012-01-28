{-# LANGUAGE DeriveDataTypeable #-}
-------------------------------------------------------------------------------
-- Module    :  Main
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade 
-- Main module that contains wrapers for command line usage
-- and the run function that produces the actual analysis  
module Main where
	
import Language.Python.Version2.Parser
import Language.Python.Version2.Lexer
import System.Console.CmdArgs

import Language.Python.Common.PrettyAST

import Language.Python.Common.AST ( Module )

import Data.Map

import IPython.AST
import IPython.Conversion
import IPython.Typing

import Analysis.Monotone
import Analysis.Lattice
import Analysis.Python

import IPython.Pretty ( prettyText )
import Output.Graph

-- Options 
data OutputOption = AnnGraph | Graph | Plain | Debug
  deriving (Show, Data, Typeable)

instance Default OutputOption where
  def = AnnGraph

data ProgramOptions = SoftType {
    output :: String
  , input  :: FilePath
  , callStringLen :: Int
  , typeoutput :: OutputOption
    
  }
  deriving (Show, Data, Typeable)


standard = cmdArgsMode $ SoftType 
           { 
             output        = (def &= help "Output file") &= typFile
           , input         = (def &= args )
           , callStringLen = (def &= help "max Length of the call string (not used atm)")
           , typeoutput    = (def &= help "AnnGraph|Graph|Plain|Debug" &= typ "AnnGraph")
           } &= summary usage


main = do args <- cmdArgsRun standard
          runAg args

-- Given a module it produces the actual result
run :: Syn_IModule -> (ELattice Environment, ELattice Environment)
run modul = (pre, post)
  where flow = controlFlow_Syn_IModule modul
        interflow = interFlow_Syn_IModule modul
        labels = labels_Syn_IModule modul
        transferFunctions = insert defaultStartLabel (Unary id) (transFunctions_Syn_IModule modul)
        initLabel = startLabel_Syn_IModule modul
        (pre, post) = case initLabel of
	                        Nothing -> error "There is no start label"
	                        Just iLabel -> mfp defaultSettings iLabel flow interflow labels [iLabel] empty transferFunctions

-- Wraper for command line usage                        
runAg :: ProgramOptions -> IO ()		
runAg options = do  let filename = input options 
                    str <- readFile filename 
                    case parseModule str filename of
                      (Right (modulspan , _)) -> let imodul = convert modulspan
                                                     w      = wrap_IModule (sem_IModule (imodul)) (Inh_IModule undefined undefined undefined undefined undefined undefined undefined)
                                                     pS f label   = do putStrLn (label ++ ":")
                                                                       (putStrLn . show . f) w
                                                 in case (startLabel_Syn_IModule w , typeoutput options) of
                                                   (Nothing,           Graph)     -> error "No startlabel defined, we cannot draw the call graph now."
                                                   (Nothing,           AnnGraph)  -> error "No startlabel defined, we cannot draw the call graph now."
                                                   (Just startLabel,   Graph)     -> do putStr $ dotControlGraph startLabel (controlFlow_Syn_IModule w)
                                                   (_,   AnnGraph)  -> do putStr $ sourceAnnotatedEmbellished (run w)
                                                                                                              (self_Syn_IModule w)                                                 
                                                                                                              (controlFlow_Syn_IModule w)
                                                   (_          ,       Debug)     -> do putStrLn ("The AST:")
                                                                                        mapM putStrLn ((lines.prettyText.(from :: IModule -> Module LabelAnnot) . self_Syn_IModule) w) 
                                                                                        pS controlFlow_Syn_IModule    "The control flow"
                                                                                        pS interFlow_Syn_IModule      "The inter flow"
                                                                                        pS labels_Syn_IModule      "All used labels"
                                                                                        pS startLabel_Syn_IModule  "Start Label"
                                                                                        pS run                     "Softtyped result"                                                                                        
                                                   (_          ,       Plain)     -> do pS self_Syn_IModule        "The AST"
                                                                                        pS (printResult.snd.run)       "Softtyped result"
                      (Left error)             -> putStrLn $ show error
                 where printResult = Prelude.map (\(x, y) -> (x, toList y)) . toList

usage :: String
usage = unlines ["The soft-typing team"]