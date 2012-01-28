-------------------------------------------------------------------------------
-- Module    :  Analysis.Monotone
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade   
module Analysis.Monotone where

import qualified Data.Set as S
import Prelude 
import Data.List 
import qualified Data.Map as Map 
import Data.Maybe (fromJust)

import IPython.AST (Label, defaultStartLabel)
import IPython.Typing (Type, fromJustWError, Context)
import Analysis.Lattice
  
-- We need the different flow types here to be able to make the distinction on
-- which info to retain on function call and so on (scoping)
-- Maybe that in the end it plays out that due to the python rules with side-
-- effect it isn't that big a deal.
data Flow  =  InterFlow ( Label , Label ) -- Between functions
           |  IntraFlow ( Label , Label ) -- Inside normal
  deriving (Eq, Show)
  
type IntraFlow   = [ Flow ]

-- | The list of allowed interflows through the program:
--      call-site , enter , exit , return
type InterFlow   = [ ( Label , Label , Label , Label )]

type ControlFlow = [ Flow ]

-- Our transfer functions that respect the type : (delta -> lattice) -> delta -> lattice
-- Unary represents the function that only needs one context and one lattice
-- Binary represents the function to combine lattices of different contexts
data TransferFunction c e =  Unary  ((c, e) -> (c, e))
                          |  Binary ((c, e) -> ((c, e) -> (c, e)))

-- Settings for the Monotone Framework
data MonotoneSettings = MonotoneSettings { callStringLength :: Int }

-- We set maximum call string of 5
defaultSettings = MonotoneSettings { callStringLength = 5 }

-- Represents our Embelished Monotone Framework (Assume Lattice s =>)
type ELattice s = Map.Map Label (Map.Map Context s)

-- Work List represents valid execution paths 
type WorkList = [((Label, Context), (Label, Context))]

{- Generic Algorithm that computes the minimal fix point
   Starts by initializing the complete lattice
   Calculates the initial workflow based on the initial label 
   Iterates until reach a fix point
   Apply the transfer function to obtain the effect
-}
mfp :: (Lattice s, Show s) => MonotoneSettings -> Label -> ControlFlow -> InterFlow -> [Label] -> [Label] -> s -> Map.Map Label (TransferFunction Context s) -> (ELattice s, ELattice s)
mfp settings startLabel controlFlow interFlow allLabels eLabels eValue transFunc =
	  let initContext = []
	      initMap = iMap allLabels eLabels eValue initContext
	      initWL  = successors settings startLabel initContext controlFlow interFlow
	      (wList, preMap) = mfp_iteration settings allLabels eLabels eValue initWL controlFlow interFlow initMap transFunc
	      wList' = foldr (getContexts $ callStringLength settings) Map.empty wList 
	  in (preMap, effect interFlow transFunc wList' preMap)
	
-- The final step in the mfp algorithm: apply all the transfer functions once more (but use the right context)
effect :: (Lattice s, Show s) => InterFlow -> Map.Map Label (TransferFunction Context s) -> Map.Map Label [Context] -> ELattice s -> ELattice s
effect iFlow trans wLF lat = Map.mapWithKey (\l mc -> applyTF l iFlow lat (fromJustWError "end" $ Map.lookup l trans) mc (maybe [] id (Map.lookup l wLF))) lat

{-
 - settings: monotone framework settings
 - allLabels: all program points
 - eLabels: the extremal labels
 - eValue: the extremal value
 - wList: the queue of 'edges' (equations) still needing to be checked
 - cFlow: the control flow
 - iFlow: the interflow
 - eLat: the complete lattice
 - transFunc: maps labels to transfer functions
 -}
mfp_iteration :: (Lattice s, Show s) => MonotoneSettings -> [Label] -> [Label] -> s -> WorkList -> ControlFlow -> InterFlow -> ELattice s -> Map.Map Label (TransferFunction Context s) -> (WorkList, ELattice s)
mfp_iteration settings allLabels eLabels eValue wList cFlow iFlow eLat transFunc =
								if null wList
                                then (wList, eLat)
								else let ((l,c), (l',c')) = head wList
								         tf = fromJustWError ("mfp_iteration: Transfer function for not found for " ++ show l) $ Map.lookup l transFunc
								         eLat' = updateELattice allLabels eLabels eValue eLat c' -- if it's a call add new column to matrix
								         lat   = fromJustWError "1" $ Map.lookup c  (fromJustWError "11" $ Map.lookup l  eLat')             
								         lat'  = fromJustWError "2" $ Map.lookup c' (fromJustWError ("22 " ++ show l' ++ " " ++ show eLat') $ Map.lookup l' eLat')
								         (nc, nlat) = case tf of
									                        (Unary f)  -> f (c, lat)
									                        (Binary f) -> let pc = findEntryPoint l iFlow
									                                          pLat = fromJustWError "3" $ Map.lookup c (fromJustWError "33" $ Map.lookup pc eLat') 
									                                      in f (c, pLat) (c, lat)									
									  in if nlat ⊑ lat'
									      then let (wList', fLat) = mfp_iteration settings allLabels eLabels eValue (tail wList) cFlow iFlow eLat' transFunc
									           in (nub (wList ++ wList'), fLat) 
									      else let nwList = successors settings l' c' cFlow iFlow
									               (wList', fLat) = mfp_iteration settings allLabels eLabels eValue (tail wList ++ nwList) cFlow iFlow (Map.update (\m -> Just $ Map.insert c' (lat' ⊔ nlat) m) l' eLat') transFunc
										        in (nub (wList ++ wList'), fLat) 

-- Applies the transfer function
applyTF :: (Lattice s, Show s) => Label -> InterFlow -> ELattice s -> TransferFunction Context s -> Map.Map Context s -> [Context] -> Map.Map Context s
applyTF l iFlow eLat f m [] = m
applyTF l iFlow eLat tf@(Binary f) m (c1:t) = let pc = findEntryPoint l iFlow
                                                  pLat = fromJustWError "3" $ Map.lookup c1 (fromJustWError "33" $ Map.lookup pc eLat) 
                                              in applyTF l iFlow eLat tf (Map.update (\lat -> Just $ snd $ f (c1,pLat) (c1,lat)) c1 m) t
applyTF l iFlow eLat tf@(Unary f)  m (c1:t) = applyTF l iFlow eLat tf (Map.update (\lat -> Just $ snd $ f (c1,lat)) c1 m) t


-- Find all the context that were created
getContexts :: Int -> ((Label, Context), (Label, Context)) -> Map.Map Label [Context] -> Map.Map Label [Context]
getContexts i ((l,c),(l',c')) r = let left = case Map.lookup l r of
										                	Nothing -> Map.insert l [c] r
										                	Just k  -> if length k > i then r else Map.insert l (nub (c:k)) r
                                      right = case Map.lookup l' r of
															    Nothing -> Map.insert l' [c'] r
															    Just k  -> if length k > i then r else Map.insert l' (nub (c':k)) r
										  in Map.unionWith (\x y -> take i $ nub (x ++ y)) left right

-- Because of the ag system we could automatically say that the entry point is l-1
findEntryPoint :: Label -> InterFlow -> Label
findEntryPoint l [] = error "Couldn't find entry point"
findEntryPoint l ((x,_,_,l'):t) = if l == l'
	                               then x
	                               else findEntryPoint l t	 	

-- Generates a new lattice initialized to the extremal value for a new context and inserts that on the previous "matrix"	
updateELattice :: (Lattice s, Show s) => [Label] -> [Label] -> s -> ELattice s -> Context -> ELattice s
updateELattice allLabels eLabels eValue imap c = case Map.lookup (head allLabels) imap of
																			 Nothing -> error "Error updating Lattice"
																			 Just m -> case Map.lookup c m of
																								 Nothing -> Map.unionWith (Map.union) imap $ iMap allLabels eLabels eValue c																								            
																								 Just x  -> imap

-- Finds the valid successors
successors :: MonotoneSettings -> Label -> Context -> ControlFlow -> InterFlow -> WorkList
successors settings b c []                     _     = []
successors settings b c ((InterFlow (l,l')):r) iFlow = if b == l
	                                                    then if isCall (l,l') iFlow
		                                                      then if (length c < callStringLength settings) 
			                                                        then ((l,c),(l',c++[l])):(successors settings b c r iFlow)
			                                                        else ((l,c),(l',c)):(successors settings b c r iFlow)
		                                                      else if isReturn (l,l') iFlow
			                                                        then let il = last c
			                                                             in if (il+1) == l'
				                                                             then ((l,c),(l',init c)):(successors settings b c r iFlow)
				                                                             else successors settings b c r iFlow 				      
			                                                        else error "Has to return something"
	                                                    else successors settings b c r iFlow
successors settings b c ((IntraFlow (l,l')):r) iFlow = if b == l
	                                                    then ((l,c),(l',c)):(successors settings b c r iFlow)
	                                                    else successors settings b c r iFlow

-- Check if a flow is a call flow
isCall :: (Label, Label) -> InterFlow -> Bool
isCall (l,l') []  = False
isCall (l,l') ((l1,l1',_,_):t) = (l1 == l1 && l' == l1') || isCall (l,l') t

-- Check if a flow is a return flow
isReturn :: (Label, Label) -> InterFlow -> Bool
isReturn (l,l') []  = False
isReturn (l,l') ((_,_,l1,l1'):t) = (l1 == l1 && l' == l1') || isReturn (l,l') t

-- Creates a initialized eLattice 
iMap :: (Lattice s, Show s) => [Label] -> [Label] -> s -> Context -> ELattice s
iMap allLabels eLabels eValue c = Map.fromList $ zip eLabels (repeat (Map.singleton c eValue)) ++ zip (allLabels \\ eLabels) (repeat (Map.singleton c bottom))
