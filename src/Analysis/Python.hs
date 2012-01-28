

{-# LANGUAGE TypeSynonymInstances #-}

{-# LANGUAGE DeriveDataTypeable #-}
-- UUAGC 0.9.38.6 (src/Analysis/Python.ag)
module Analysis.Python where

{-# LINE 13 "src/Analysis/Python.ag" #-}

import Data.Map as Map hiding (map)
import Data.Set as Set hiding (map)
import Data.List (nub)
import Data.Maybe (fromJust, fromMaybe) 

import Analysis.Monotone
import IPython.Typing
import Debug.Trace
import IPython.AST
{-# LINE 21 "src/Analysis/Python.hs" #-}
{-# LINE 1 "src/Analysis/Python.ag" #-}

-------------------------------------------------------------------------------
-- Module    :  Analysis.Python
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade   
{-# LINE 27 "src/Analysis/Python.hs" #-}

{-# LINE 29 "src/Analysis/Python.ag" #-}

nextUnique n = (n+1,n)
{-# LINE 32 "src/Analysis/Python.hs" #-}

{-# LINE 287 "src/Analysis/Python.ag" #-}

-- Utility functions
removeRet :: IExpr -> Environment -> Environment
removeRet (ICall (IVar x) _ _ _) env = Map.delete ("r"++x) env
removeRet _                      env = env

filterOut :: Environment -> Environment -> String -> Environment
filterOut fEnv pEnv rfunName = Map.insert rfunName (fromJustWError "filterOut" $ Map.lookup rfunName pEnv) fEnv

getVarParams :: IParams -> [Var]
getVarParams = map getVarParam

getVarParam :: IParameter -> Var
getVarParam (IParam      name _ _) = name
getVarParam (IVarArgsPos name _)   = name
getVarParam IParamNotSupported     = "Not Supported"

getArgsTy :: IArgs -> Environment -> [Set.Set Type]
getArgsTy args env = map (\arg -> getArgTy arg env) args

getArgTy :: IArgument -> Environment -> Set.Set Type
getArgTy (IArgExpr       expr _) env = typesOf env expr
getArgTy (IArgVarArgsPos expr)   env = typesOf env expr
getArgTy IArgNotSupported        env = Set.empty

prevTypesOf' :: Environment -> String -> Set.Set Type
prevTypesOf' env var = fromMaybe (Set.singleton None) $ Map.lookup var env

prevTypesOf :: Environment -> String -> Set.Set Type
prevTypesOf env var = fromMaybe Set.empty $ Map.lookup var env

createFlow :: ((Label, Label) -> Flow) -> [Label] -> [Label] -> ControlFlow
createFlow f ls rs = [f (l , r) | l <- ls, r <- rs, l /= defaultStartLabel]

createInterFlow :: Label -> Label -> [Label] -> Label -> InterFlow
createInterFlow call enter exits return = map (\exit -> (call, enter, exit, return)) exits
 
fname :: IExpr -> String
fname (IVar x) = x
fname _        = error "fname: Not supported ICall"

varOf :: IExprs -> String
varOf ((IVar x) : _) = x
varOf x              = error $ "Unsupported: " ++ show x

varOf_ :: IExpr -> String
varOf_ (IVar x) = x
{-# LINE 82 "src/Analysis/Python.hs" #-}

{-# LINE 3 "src/Analysis/../IPython/AST.ag" #-}

-------------------------------------------------------------------------------
-- Module    :  IPython.AST
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade 
-- This AG module contains the AST that we convert the parser result from
-- The analyzed fields are annotated with Label.  
{-# LINE 91 "src/Analysis/Python.hs" #-}
-- IArgs -------------------------------------------------------
-- cata
sem_IArgs :: IArgs  ->
             T_IArgs 
sem_IArgs list  =
    (Prelude.foldr sem_IArgs_Cons sem_IArgs_Nil (Prelude.map sem_IArgument list) )
-- semantic domain
type T_IArgs  = (Map String [(Label, Label)]) ->
                Label ->
                ([Label]) ->
                ([Label]) ->
                (Map String Label) ->
                String ->
                (Map String [Var]) ->
                (Map String [Label]) ->
                ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IArgs ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IArgs  = Inh_IArgs {callLabels_Inh_IArgs :: (Map String [(Label, Label)]),counter_Inh_IArgs :: Label,downGLabel_Inh_IArgs :: ([Label]),downLabel_Inh_IArgs :: ([Label]),funLabels_Inh_IArgs :: (Map String Label),funName_Inh_IArgs :: String,funParams_Inh_IArgs :: (Map String [Var]),retLabels_Inh_IArgs :: (Map String [Label])}
data Syn_IArgs  = Syn_IArgs {callLabels_Syn_IArgs :: (Map String [(Label, Label)]),controlFlow_Syn_IArgs :: ControlFlow,counter_Syn_IArgs :: Label,funLabels_Syn_IArgs :: (Map String Label),funName_Syn_IArgs :: String,funParams_Syn_IArgs :: (Map String [Var]),interFlow_Syn_IArgs :: InterFlow,labels_Syn_IArgs :: ([Label]),retLabels_Syn_IArgs :: (Map String [Label]),self_Syn_IArgs :: IArgs ,startLabel_Syn_IArgs :: ( Maybe Label ),transFunctions_Syn_IArgs :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IArgs :: ([Label]),upLabel_Syn_IArgs :: ([Label])}
wrap_IArgs :: T_IArgs  ->
              Inh_IArgs  ->
              Syn_IArgs 
wrap_IArgs sem (Inh_IArgs _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IArgs _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IArgs_Cons :: T_IArgument  ->
                  T_IArgs  ->
                  T_IArgs 
sem_IArgs_Cons hd_ tl_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _hdOdownLabel :: ([Label])
              _hdOdownGLabel :: ([Label])
              _tlOdownLabel :: ([Label])
              _tlOdownGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IArgs 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _hdOcallLabels :: (Map String [(Label, Label)])
              _hdOcounter :: Label
              _hdOfunLabels :: (Map String Label)
              _hdOfunName :: String
              _hdOfunParams :: (Map String [Var])
              _hdOretLabels :: (Map String [Label])
              _tlOcallLabels :: (Map String [(Label, Label)])
              _tlOcounter :: Label
              _tlOfunLabels :: (Map String Label)
              _tlOfunName :: String
              _tlOfunParams :: (Map String [Var])
              _tlOretLabels :: (Map String [Label])
              _hdIcallLabels :: (Map String [(Label, Label)])
              _hdIcontrolFlow :: ControlFlow
              _hdIcounter :: Label
              _hdIfunLabels :: (Map String Label)
              _hdIfunName :: String
              _hdIfunParams :: (Map String [Var])
              _hdIinterFlow :: InterFlow
              _hdIlabels :: ([Label])
              _hdIretLabels :: (Map String [Label])
              _hdIself :: IArgument 
              _hdIstartLabel :: ( Maybe Label )
              _hdItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _hdIupGLabel :: ([Label])
              _hdIupLabel :: ([Label])
              _tlIcallLabels :: (Map String [(Label, Label)])
              _tlIcontrolFlow :: ControlFlow
              _tlIcounter :: Label
              _tlIfunLabels :: (Map String Label)
              _tlIfunName :: String
              _tlIfunParams :: (Map String [Var])
              _tlIinterFlow :: InterFlow
              _tlIlabels :: ([Label])
              _tlIretLabels :: (Map String [Label])
              _tlIself :: IArgs 
              _tlIstartLabel :: ( Maybe Label )
              _tlItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _tlIupGLabel :: ([Label])
              _tlIupLabel :: ([Label])
              _hdOdownLabel =
                  ({-# LINE 119 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 189 "src/Analysis/Python.hs" #-}
                   )
              _hdOdownGLabel =
                  ({-# LINE 120 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 194 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownLabel =
                  ({-# LINE 121 "src/Analysis/Python.ag" #-}
                   _hdIupLabel
                   {-# LINE 199 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownGLabel =
                  ({-# LINE 122 "src/Analysis/Python.ag" #-}
                   _hdIupGLabel
                   {-# LINE 204 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 123 "src/Analysis/Python.ag" #-}
                   maybe _tlIstartLabel (\_ -> _hdIstartLabel) _hdIstartLabel
                   {-# LINE 209 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _hdIcontrolFlow ++ _tlIcontrolFlow
                   {-# LINE 214 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _hdIinterFlow ++ _tlIinterFlow
                   {-# LINE 219 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 224 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _hdItransFunctions `Map.union` _tlItransFunctions
                   {-# LINE 229 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _tlIcallLabels
                   {-# LINE 238 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 243 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _tlIfunLabels
                   {-# LINE 248 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _tlIfunName
                   {-# LINE 253 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _tlIfunParams
                   {-# LINE 258 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _tlIretLabels
                   {-# LINE 263 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _tlIupGLabel
                   {-# LINE 268 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _tlIupLabel
                   {-# LINE 273 "src/Analysis/Python.hs" #-}
                   )
              _hdOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 278 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 283 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 288 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 293 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 298 "src/Analysis/Python.hs" #-}
                   )
              _hdOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 303 "src/Analysis/Python.hs" #-}
                   )
              _tlOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _hdIcallLabels
                   {-# LINE 308 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 313 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _hdIfunLabels
                   {-# LINE 318 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _hdIfunName
                   {-# LINE 323 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _hdIfunParams
                   {-# LINE 328 "src/Analysis/Python.hs" #-}
                   )
              _tlOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _hdIretLabels
                   {-# LINE 333 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcallLabels,_hdIcontrolFlow,_hdIcounter,_hdIfunLabels,_hdIfunName,_hdIfunParams,_hdIinterFlow,_hdIlabels,_hdIretLabels,_hdIself,_hdIstartLabel,_hdItransFunctions,_hdIupGLabel,_hdIupLabel) =
                  hd_ _hdOcallLabels _hdOcounter _hdOdownGLabel _hdOdownLabel _hdOfunLabels _hdOfunName _hdOfunParams _hdOretLabels 
              ( _tlIcallLabels,_tlIcontrolFlow,_tlIcounter,_tlIfunLabels,_tlIfunName,_tlIfunParams,_tlIinterFlow,_tlIlabels,_tlIretLabels,_tlIself,_tlIstartLabel,_tlItransFunctions,_tlIupGLabel,_tlIupLabel) =
                  tl_ _tlOcallLabels _tlOcounter _tlOdownGLabel _tlOdownLabel _tlOfunLabels _tlOfunName _tlOfunParams _tlOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IArgs_Nil :: T_IArgs 
sem_IArgs_Nil  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOupLabel :: ([Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IArgs 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupLabel =
                  ({-# LINE 124 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 367 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 125 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 372 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 126 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 377 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 382 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 387 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 392 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 397 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 406 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 411 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 416 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 421 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 426 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 431 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IArgument ---------------------------------------------------
-- cata
sem_IArgument :: IArgument  ->
                 T_IArgument 
sem_IArgument (IArgExpr _expr _label )  =
    (sem_IArgument_IArgExpr (sem_IExpr _expr ) (sem_Label _label ) )
sem_IArgument (IArgNotSupported )  =
    (sem_IArgument_IArgNotSupported )
sem_IArgument (IArgVarArgsPos _expr )  =
    (sem_IArgument_IArgVarArgsPos (sem_IExpr _expr ) )
-- semantic domain
type T_IArgument  = (Map String [(Label, Label)]) ->
                    Label ->
                    ([Label]) ->
                    ([Label]) ->
                    (Map String Label) ->
                    String ->
                    (Map String [Var]) ->
                    (Map String [Label]) ->
                    ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IArgument ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IArgument  = Inh_IArgument {callLabels_Inh_IArgument :: (Map String [(Label, Label)]),counter_Inh_IArgument :: Label,downGLabel_Inh_IArgument :: ([Label]),downLabel_Inh_IArgument :: ([Label]),funLabels_Inh_IArgument :: (Map String Label),funName_Inh_IArgument :: String,funParams_Inh_IArgument :: (Map String [Var]),retLabels_Inh_IArgument :: (Map String [Label])}
data Syn_IArgument  = Syn_IArgument {callLabels_Syn_IArgument :: (Map String [(Label, Label)]),controlFlow_Syn_IArgument :: ControlFlow,counter_Syn_IArgument :: Label,funLabels_Syn_IArgument :: (Map String Label),funName_Syn_IArgument :: String,funParams_Syn_IArgument :: (Map String [Var]),interFlow_Syn_IArgument :: InterFlow,labels_Syn_IArgument :: ([Label]),retLabels_Syn_IArgument :: (Map String [Label]),self_Syn_IArgument :: IArgument ,startLabel_Syn_IArgument :: ( Maybe Label ),transFunctions_Syn_IArgument :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IArgument :: ([Label]),upLabel_Syn_IArgument :: ([Label])}
wrap_IArgument :: T_IArgument  ->
                  Inh_IArgument  ->
                  Syn_IArgument 
wrap_IArgument sem (Inh_IArgument _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IArgument _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IArgument_IArgExpr :: T_IExpr  ->
                          T_Label  ->
                          T_IArgument 
sem_IArgument_IArgExpr expr_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOself :: IArgument 
              _lhsOlabels :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup1 :: ((Label,Label))
              _exprOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOdownGLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOself =
                  ({-# LINE 78 "src/Analysis/Python.ag" #-}
                   IArgExpr _exprIself _label
                   {-# LINE 516 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 79 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 521 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 222 "src/Analysis/Python.ag" #-}
                   createFlow IntraFlow _lhsIdownLabel [_label    ]
                   {-# LINE 526 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 223 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 531 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 224 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 536 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 284 "src/Analysis/Python.ag" #-}
                   Map.singleton _label     $ Unary id
                   {-# LINE 541 "src/Analysis/Python.hs" #-}
                   )
              __tup1 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_exprOcounter,_) =
                  ({-# LINE 80 "src/Analysis/Python.ag" #-}
                   __tup1
                   {-# LINE 548 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 80 "src/Analysis/Python.ag" #-}
                   __tup1
                   {-# LINE 553 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprIinterFlow
                   {-# LINE 558 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IArgExpr _exprIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 565 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 570 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 575 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 580 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 585 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 590 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 595 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 600 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 605 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 610 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 615 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 620 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 625 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 630 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IArgument_IArgNotSupported :: T_IArgument 
sem_IArgument_IArgNotSupported  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IArgument 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 664 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 669 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 674 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 679 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IArgNotSupported
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 688 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 693 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 698 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 703 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 708 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 713 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IArgument.IArgNotSupported.lhs.startLabel"
                   {-# LINE 718 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IArgument.IArgNotSupported.lhs.upGLabel"
                   {-# LINE 723 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   error "missing rule: IArgument.IArgNotSupported.lhs.upLabel"
                   {-# LINE 728 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IArgument_IArgVarArgsPos :: T_IExpr  ->
                                T_IArgument 
sem_IArgument_IArgVarArgsPos expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IArgument 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOcounter :: Label
              _exprOdownGLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _exprIcontrolFlow
                   {-# LINE 781 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprIinterFlow
                   {-# LINE 786 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _exprIlabels
                   {-# LINE 791 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _exprItransFunctions
                   {-# LINE 796 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IArgVarArgsPos _exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 805 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 810 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 815 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 820 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 825 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 830 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _exprIstartLabel
                   {-# LINE 835 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 840 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _exprIupLabel
                   {-# LINE 845 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 850 "src/Analysis/Python.hs" #-}
                   )
              _exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 855 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 860 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 865 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 870 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 875 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 880 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 885 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IAssignOp ---------------------------------------------------
-- cata
sem_IAssignOp :: IAssignOp  ->
                 T_IAssignOp 
sem_IAssignOp (IBinAndAssign )  =
    (sem_IAssignOp_IBinAndAssign )
sem_IAssignOp (IBinOrAssign )  =
    (sem_IAssignOp_IBinOrAssign )
sem_IAssignOp (IBinXorAssign )  =
    (sem_IAssignOp_IBinXorAssign )
sem_IAssignOp (IDivAssign )  =
    (sem_IAssignOp_IDivAssign )
sem_IAssignOp (IFloorDivAssign )  =
    (sem_IAssignOp_IFloorDivAssign )
sem_IAssignOp (ILeftShiftAssign )  =
    (sem_IAssignOp_ILeftShiftAssign )
sem_IAssignOp (IMinusAssign )  =
    (sem_IAssignOp_IMinusAssign )
sem_IAssignOp (IModAssign )  =
    (sem_IAssignOp_IModAssign )
sem_IAssignOp (IMultAssign )  =
    (sem_IAssignOp_IMultAssign )
sem_IAssignOp (IPlusAssign )  =
    (sem_IAssignOp_IPlusAssign )
sem_IAssignOp (IPowAssign )  =
    (sem_IAssignOp_IPowAssign )
sem_IAssignOp (IRightShiftAssign )  =
    (sem_IAssignOp_IRightShiftAssign )
-- semantic domain
type T_IAssignOp  = ( IAssignOp )
data Inh_IAssignOp  = Inh_IAssignOp {}
data Syn_IAssignOp  = Syn_IAssignOp {self_Syn_IAssignOp :: IAssignOp }
wrap_IAssignOp :: T_IAssignOp  ->
                  Inh_IAssignOp  ->
                  Syn_IAssignOp 
wrap_IAssignOp sem (Inh_IAssignOp )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IAssignOp _lhsOself ))
sem_IAssignOp_IBinAndAssign :: T_IAssignOp 
sem_IAssignOp_IBinAndAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IBinAndAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IBinOrAssign :: T_IAssignOp 
sem_IAssignOp_IBinOrAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IBinOrAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IBinXorAssign :: T_IAssignOp 
sem_IAssignOp_IBinXorAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IBinXorAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IDivAssign :: T_IAssignOp 
sem_IAssignOp_IDivAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IDivAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IFloorDivAssign :: T_IAssignOp 
sem_IAssignOp_IFloorDivAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IFloorDivAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_ILeftShiftAssign :: T_IAssignOp 
sem_IAssignOp_ILeftShiftAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             ILeftShiftAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IMinusAssign :: T_IAssignOp 
sem_IAssignOp_IMinusAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IMinusAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IModAssign :: T_IAssignOp 
sem_IAssignOp_IModAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IModAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IMultAssign :: T_IAssignOp 
sem_IAssignOp_IMultAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IMultAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IPlusAssign :: T_IAssignOp 
sem_IAssignOp_IPlusAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IPlusAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IPowAssign :: T_IAssignOp 
sem_IAssignOp_IPowAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IPowAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IAssignOp_IRightShiftAssign :: T_IAssignOp 
sem_IAssignOp_IRightShiftAssign  =
    (let _lhsOself :: IAssignOp 
         _self =
             IRightShiftAssign
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IContext ----------------------------------------------------
-- cata
sem_IContext :: IContext  ->
                T_IContext 
sem_IContext list  =
    (Prelude.foldr sem_IContext_Cons sem_IContext_Nil (Prelude.map sem_PairExprMybExpr list) )
-- semantic domain
type T_IContext  = Label ->
                   ( Label,([Label]),IContext ,( Maybe Label ))
data Inh_IContext  = Inh_IContext {counter_Inh_IContext :: Label}
data Syn_IContext  = Syn_IContext {counter_Syn_IContext :: Label,labels_Syn_IContext :: ([Label]),self_Syn_IContext :: IContext ,startLabel_Syn_IContext :: ( Maybe Label )}
wrap_IContext :: T_IContext  ->
                 Inh_IContext  ->
                 Syn_IContext 
wrap_IContext sem (Inh_IContext _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IContext _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IContext_Cons :: T_PairExprMybExpr  ->
                     T_IContext  ->
                     T_IContext 
sem_IContext_Cons hd_ tl_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IContext 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _hdOcounter :: Label
              _tlOcounter :: Label
              _hdIcounter :: Label
              _hdIlabels :: ([Label])
              _hdIself :: PairExprMybExpr 
              _hdIstartLabel :: ( Maybe Label )
              _tlIcounter :: Label
              _tlIlabels :: ([Label])
              _tlIself :: IContext 
              _tlIstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 1063 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 1072 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _tlIstartLabel
                   {-# LINE 1077 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1082 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 1087 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcounter,_hdIlabels,_hdIself,_hdIstartLabel) =
                  hd_ _hdOcounter 
              ( _tlIcounter,_tlIlabels,_tlIself,_tlIstartLabel) =
                  tl_ _tlOcounter 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IContext_Nil :: T_IContext 
sem_IContext_Nil  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IContext 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 1104 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1113 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IContext.Nil.lhs.startLabel"
                   {-# LINE 1118 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IDecorator --------------------------------------------------
-- cata
sem_IDecorator :: IDecorator  ->
                  T_IDecorator 
sem_IDecorator (IDecorator _name _args )  =
    (sem_IDecorator_IDecorator (sem_IDottedName _name ) (sem_IArgs _args ) )
-- semantic domain
type T_IDecorator  = Label ->
                     ( Label,([Label]),IDecorator ,( Maybe Label ))
data Inh_IDecorator  = Inh_IDecorator {counter_Inh_IDecorator :: Label}
data Syn_IDecorator  = Syn_IDecorator {counter_Syn_IDecorator :: Label,labels_Syn_IDecorator :: ([Label]),self_Syn_IDecorator :: IDecorator ,startLabel_Syn_IDecorator :: ( Maybe Label )}
wrap_IDecorator :: T_IDecorator  ->
                   Inh_IDecorator  ->
                   Syn_IDecorator 
wrap_IDecorator sem (Inh_IDecorator _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IDecorator _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IDecorator_IDecorator :: T_IDottedName  ->
                             T_IArgs  ->
                             T_IDecorator 
sem_IDecorator_IDecorator name_ args_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IDecorator 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _argsOcallLabels :: (Map String [(Label, Label)])
              _argsOcounter :: Label
              _argsOdownGLabel :: ([Label])
              _argsOdownLabel :: ([Label])
              _argsOfunLabels :: (Map String Label)
              _argsOfunName :: String
              _argsOfunParams :: (Map String [Var])
              _argsOretLabels :: (Map String [Label])
              _nameIself :: IDottedName 
              _argsIcallLabels :: (Map String [(Label, Label)])
              _argsIcontrolFlow :: ControlFlow
              _argsIcounter :: Label
              _argsIfunLabels :: (Map String Label)
              _argsIfunName :: String
              _argsIfunParams :: (Map String [Var])
              _argsIinterFlow :: InterFlow
              _argsIlabels :: ([Label])
              _argsIretLabels :: (Map String [Label])
              _argsIself :: IArgs 
              _argsIstartLabel :: ( Maybe Label )
              _argsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _argsIupGLabel :: ([Label])
              _argsIupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _argsIlabels
                   {-# LINE 1173 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IDecorator _nameIself _argsIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _argsIcounter
                   {-# LINE 1182 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _argsIstartLabel
                   {-# LINE 1187 "src/Analysis/Python.hs" #-}
                   )
              _argsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.callLabels"
                   {-# LINE 1192 "src/Analysis/Python.hs" #-}
                   )
              _argsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1197 "src/Analysis/Python.hs" #-}
                   )
              _argsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.downGLabel"
                   {-# LINE 1202 "src/Analysis/Python.hs" #-}
                   )
              _argsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.downLabel"
                   {-# LINE 1207 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.funLabels"
                   {-# LINE 1212 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.funName"
                   {-# LINE 1217 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.funParams"
                   {-# LINE 1222 "src/Analysis/Python.hs" #-}
                   )
              _argsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorator.IDecorator.args.retLabels"
                   {-# LINE 1227 "src/Analysis/Python.hs" #-}
                   )
              ( _nameIself) =
                  name_ 
              ( _argsIcallLabels,_argsIcontrolFlow,_argsIcounter,_argsIfunLabels,_argsIfunName,_argsIfunParams,_argsIinterFlow,_argsIlabels,_argsIretLabels,_argsIself,_argsIstartLabel,_argsItransFunctions,_argsIupGLabel,_argsIupLabel) =
                  args_ _argsOcallLabels _argsOcounter _argsOdownGLabel _argsOdownLabel _argsOfunLabels _argsOfunName _argsOfunParams _argsOretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IDecorators -------------------------------------------------
-- cata
sem_IDecorators :: IDecorators  ->
                   T_IDecorators 
sem_IDecorators list  =
    (Prelude.foldr sem_IDecorators_Cons sem_IDecorators_Nil (Prelude.map sem_IDecorator list) )
-- semantic domain
type T_IDecorators  = Label ->
                      ( Label,([Label]),IDecorators ,( Maybe Label ))
data Inh_IDecorators  = Inh_IDecorators {counter_Inh_IDecorators :: Label}
data Syn_IDecorators  = Syn_IDecorators {counter_Syn_IDecorators :: Label,labels_Syn_IDecorators :: ([Label]),self_Syn_IDecorators :: IDecorators ,startLabel_Syn_IDecorators :: ( Maybe Label )}
wrap_IDecorators :: T_IDecorators  ->
                    Inh_IDecorators  ->
                    Syn_IDecorators 
wrap_IDecorators sem (Inh_IDecorators _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IDecorators _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IDecorators_Cons :: T_IDecorator  ->
                        T_IDecorators  ->
                        T_IDecorators 
sem_IDecorators_Cons hd_ tl_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IDecorators 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _hdOcounter :: Label
              _tlOcounter :: Label
              _hdIcounter :: Label
              _hdIlabels :: ([Label])
              _hdIself :: IDecorator 
              _hdIstartLabel :: ( Maybe Label )
              _tlIcounter :: Label
              _tlIlabels :: ([Label])
              _tlIself :: IDecorators 
              _tlIstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 1273 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 1282 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _tlIstartLabel
                   {-# LINE 1287 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1292 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 1297 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcounter,_hdIlabels,_hdIself,_hdIstartLabel) =
                  hd_ _hdOcounter 
              ( _tlIcounter,_tlIlabels,_tlIself,_tlIstartLabel) =
                  tl_ _tlOcounter 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IDecorators_Nil :: T_IDecorators 
sem_IDecorators_Nil  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IDecorators 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 1314 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1323 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IDecorators.Nil.lhs.startLabel"
                   {-# LINE 1328 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IDottedName -------------------------------------------------
-- cata
sem_IDottedName :: IDottedName  ->
                   T_IDottedName 
sem_IDottedName list  =
    (Prelude.foldr sem_IDottedName_Cons sem_IDottedName_Nil list )
-- semantic domain
type T_IDottedName  = ( IDottedName )
data Inh_IDottedName  = Inh_IDottedName {}
data Syn_IDottedName  = Syn_IDottedName {self_Syn_IDottedName :: IDottedName }
wrap_IDottedName :: T_IDottedName  ->
                    Inh_IDottedName  ->
                    Syn_IDottedName 
wrap_IDottedName sem (Inh_IDottedName )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IDottedName _lhsOself ))
sem_IDottedName_Cons :: String ->
                        T_IDottedName  ->
                        T_IDottedName 
sem_IDottedName_Cons hd_ tl_  =
    (let _lhsOself :: IDottedName 
         _tlIself :: IDottedName 
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_ 
     in  ( _lhsOself))
sem_IDottedName_Nil :: T_IDottedName 
sem_IDottedName_Nil  =
    (let _lhsOself :: IDottedName 
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IExceptClause -----------------------------------------------
-- cata
sem_IExceptClause :: IExceptClause  ->
                     T_IExceptClause 
sem_IExceptClause (IExceptClause _clause )  =
    (sem_IExceptClause_IExceptClause _clause )
-- semantic domain
type T_IExceptClause  = ( IExceptClause )
data Inh_IExceptClause  = Inh_IExceptClause {}
data Syn_IExceptClause  = Syn_IExceptClause {self_Syn_IExceptClause :: IExceptClause }
wrap_IExceptClause :: T_IExceptClause  ->
                      Inh_IExceptClause  ->
                      Syn_IExceptClause 
wrap_IExceptClause sem (Inh_IExceptClause )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IExceptClause _lhsOself ))
sem_IExceptClause_IExceptClause :: (Maybe IExceptClauseType) ->
                                   T_IExceptClause 
sem_IExceptClause_IExceptClause clause_  =
    (let _lhsOself :: IExceptClause 
         _self =
             IExceptClause clause_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IExceptClauseType -------------------------------------------
-- cata
sem_IExceptClauseType :: IExceptClauseType  ->
                         T_IExceptClauseType 
sem_IExceptClauseType ( x1,x2)  =
    (sem_IExceptClauseType_Tuple (sem_IExpr x1 ) x2 )
-- semantic domain
type T_IExceptClauseType  = Label ->
                            ( Label,([Label]),IExceptClauseType ,( Maybe Label ))
data Inh_IExceptClauseType  = Inh_IExceptClauseType {counter_Inh_IExceptClauseType :: Label}
data Syn_IExceptClauseType  = Syn_IExceptClauseType {counter_Syn_IExceptClauseType :: Label,labels_Syn_IExceptClauseType :: ([Label]),self_Syn_IExceptClauseType :: IExceptClauseType ,startLabel_Syn_IExceptClauseType :: ( Maybe Label )}
wrap_IExceptClauseType :: T_IExceptClauseType  ->
                          Inh_IExceptClauseType  ->
                          Syn_IExceptClauseType 
wrap_IExceptClauseType sem (Inh_IExceptClauseType _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IExceptClauseType _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IExceptClauseType_Tuple :: T_IExpr  ->
                               (Maybe IExpr) ->
                               T_IExceptClauseType 
sem_IExceptClauseType_Tuple x1_ x2_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IExceptClauseType 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _x1OcallLabels :: (Map String [(Label, Label)])
              _x1Ocounter :: Label
              _x1OdownGLabel :: ([Label])
              _x1OdownLabel :: ([Label])
              _x1OfunLabels :: (Map String Label)
              _x1OfunName :: String
              _x1OfunParams :: (Map String [Var])
              _x1OretLabels :: (Map String [Label])
              _x1IcallLabels :: (Map String [(Label, Label)])
              _x1IcontrolFlow :: ControlFlow
              _x1Icounter :: Label
              _x1IfunLabels :: (Map String Label)
              _x1IfunName :: String
              _x1IfunParams :: (Map String [Var])
              _x1IinterFlow :: InterFlow
              _x1Ilabels :: ([Label])
              _x1IretLabels :: (Map String [Label])
              _x1Iself :: IExpr 
              _x1IstartLabel :: ( Maybe Label )
              _x1ItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _x1IupGLabel :: ([Label])
              _x1IupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _x1Ilabels
                   {-# LINE 1444 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (_x1Iself,x2_)
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _x1Icounter
                   {-# LINE 1453 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _x1IstartLabel
                   {-# LINE 1458 "src/Analysis/Python.hs" #-}
                   )
              _x1OcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.callLabels"
                   {-# LINE 1463 "src/Analysis/Python.hs" #-}
                   )
              _x1Ocounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1468 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.downGLabel"
                   {-# LINE 1473 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.downLabel"
                   {-# LINE 1478 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.funLabels"
                   {-# LINE 1483 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.funName"
                   {-# LINE 1488 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.funParams"
                   {-# LINE 1493 "src/Analysis/Python.hs" #-}
                   )
              _x1OretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType.Tuple.x1.retLabels"
                   {-# LINE 1498 "src/Analysis/Python.hs" #-}
                   )
              ( _x1IcallLabels,_x1IcontrolFlow,_x1Icounter,_x1IfunLabels,_x1IfunName,_x1IfunParams,_x1IinterFlow,_x1Ilabels,_x1IretLabels,_x1Iself,_x1IstartLabel,_x1ItransFunctions,_x1IupGLabel,_x1IupLabel) =
                  x1_ _x1OcallLabels _x1Ocounter _x1OdownGLabel _x1OdownLabel _x1OfunLabels _x1OfunName _x1OfunParams _x1OretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IExceptClauseType2 ------------------------------------------
-- cata
sem_IExceptClauseType2 :: IExceptClauseType2  ->
                          T_IExceptClauseType2 
sem_IExceptClauseType2 ( x1,x2)  =
    (sem_IExceptClauseType2_Tuple (sem_IExpr x1 ) x2 )
-- semantic domain
type T_IExceptClauseType2  = Label ->
                             ( Label,([Label]),IExceptClauseType2 ,( Maybe Label ))
data Inh_IExceptClauseType2  = Inh_IExceptClauseType2 {counter_Inh_IExceptClauseType2 :: Label}
data Syn_IExceptClauseType2  = Syn_IExceptClauseType2 {counter_Syn_IExceptClauseType2 :: Label,labels_Syn_IExceptClauseType2 :: ([Label]),self_Syn_IExceptClauseType2 :: IExceptClauseType2 ,startLabel_Syn_IExceptClauseType2 :: ( Maybe Label )}
wrap_IExceptClauseType2 :: T_IExceptClauseType2  ->
                           Inh_IExceptClauseType2  ->
                           Syn_IExceptClauseType2 
wrap_IExceptClauseType2 sem (Inh_IExceptClauseType2 _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IExceptClauseType2 _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IExceptClauseType2_Tuple :: T_IExpr  ->
                                (Maybe IExceptClauseType) ->
                                T_IExceptClauseType2 
sem_IExceptClauseType2_Tuple x1_ x2_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IExceptClauseType2 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _x1OcallLabels :: (Map String [(Label, Label)])
              _x1Ocounter :: Label
              _x1OdownGLabel :: ([Label])
              _x1OdownLabel :: ([Label])
              _x1OfunLabels :: (Map String Label)
              _x1OfunName :: String
              _x1OfunParams :: (Map String [Var])
              _x1OretLabels :: (Map String [Label])
              _x1IcallLabels :: (Map String [(Label, Label)])
              _x1IcontrolFlow :: ControlFlow
              _x1Icounter :: Label
              _x1IfunLabels :: (Map String Label)
              _x1IfunName :: String
              _x1IfunParams :: (Map String [Var])
              _x1IinterFlow :: InterFlow
              _x1Ilabels :: ([Label])
              _x1IretLabels :: (Map String [Label])
              _x1Iself :: IExpr 
              _x1IstartLabel :: ( Maybe Label )
              _x1ItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _x1IupGLabel :: ([Label])
              _x1IupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _x1Ilabels
                   {-# LINE 1554 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (_x1Iself,x2_)
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _x1Icounter
                   {-# LINE 1563 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _x1IstartLabel
                   {-# LINE 1568 "src/Analysis/Python.hs" #-}
                   )
              _x1OcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.callLabels"
                   {-# LINE 1573 "src/Analysis/Python.hs" #-}
                   )
              _x1Ocounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1578 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.downGLabel"
                   {-# LINE 1583 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.downLabel"
                   {-# LINE 1588 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.funLabels"
                   {-# LINE 1593 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.funName"
                   {-# LINE 1598 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.funParams"
                   {-# LINE 1603 "src/Analysis/Python.hs" #-}
                   )
              _x1OretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExceptClauseType2.Tuple.x1.retLabels"
                   {-# LINE 1608 "src/Analysis/Python.hs" #-}
                   )
              ( _x1IcallLabels,_x1IcontrolFlow,_x1Icounter,_x1IfunLabels,_x1IfunName,_x1IfunParams,_x1IinterFlow,_x1Ilabels,_x1IretLabels,_x1Iself,_x1IstartLabel,_x1ItransFunctions,_x1IupGLabel,_x1IupLabel) =
                  x1_ _x1OcallLabels _x1Ocounter _x1OdownGLabel _x1OdownLabel _x1OfunLabels _x1OfunName _x1OfunParams _x1OretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IExpr -------------------------------------------------------
-- cata
sem_IExpr :: IExpr  ->
             T_IExpr 
sem_IExpr (IBinaryOp _operator _left_op_arg _right_op_arg )  =
    (sem_IExpr_IBinaryOp (sem_IOp _operator ) (sem_IExpr _left_op_arg ) (sem_IExpr _right_op_arg ) )
sem_IExpr (IBool _bool_value )  =
    (sem_IExpr_IBool _bool_value )
sem_IExpr (ICall _call_fun _call_args _call_callLabel _call_returnLabel )  =
    (sem_IExpr_ICall (sem_IExpr _call_fun ) (sem_IArgs _call_args ) (sem_Label _call_callLabel ) (sem_Label _call_returnLabel ) )
sem_IExpr (ICondExpr _ce_true_branch _ce_condition _ce_false_branch )  =
    (sem_IExpr_ICondExpr (sem_IExpr _ce_true_branch ) (sem_IExpr _ce_condition ) (sem_IExpr _ce_false_branch ) )
sem_IExpr (IExprNotSupported )  =
    (sem_IExpr_IExprNotSupported )
sem_IExpr (IFloat _float_value _expr_literal )  =
    (sem_IExpr_IFloat _float_value _expr_literal )
sem_IExpr (IImaginary _imaginary_value _expr_literal )  =
    (sem_IExpr_IImaginary _imaginary_value _expr_literal )
sem_IExpr (IInt _int_value _expr_literal )  =
    (sem_IExpr_IInt _int_value _expr_literal )
sem_IExpr (ILambda _lambda_args _lambda_body )  =
    (sem_IExpr_ILambda (sem_IParams _lambda_args ) (sem_IExpr _lambda_body ) )
sem_IExpr (IList _list_exprs )  =
    (sem_IExpr_IList (sem_IExprs _list_exprs ) )
sem_IExpr (ILongInt _int_value _expr_literal )  =
    (sem_IExpr_ILongInt _int_value _expr_literal )
sem_IExpr (INone )  =
    (sem_IExpr_INone )
sem_IExpr (IParen _paren_expr )  =
    (sem_IExpr_IParen (sem_IExpr _paren_expr ) )
sem_IExpr (ISet _set_exprs )  =
    (sem_IExpr_ISet (sem_IExprs _set_exprs ) )
sem_IExpr (IString _expr_literal )  =
    (sem_IExpr_IString (sem_Strings _expr_literal ) )
sem_IExpr (IStringConversion _backquoted_expr )  =
    (sem_IExpr_IStringConversion (sem_IExpr _backquoted_expr ) )
sem_IExpr (ISubscript _subscriptee _subscript_expr )  =
    (sem_IExpr_ISubscript (sem_IExpr _subscriptee ) (sem_IExpr _subscript_expr ) )
sem_IExpr (ITuple _tuple_exprs )  =
    (sem_IExpr_ITuple (sem_IExprs _tuple_exprs ) )
sem_IExpr (IUnaryOp _operator _op_arg )  =
    (sem_IExpr_IUnaryOp (sem_IOp _operator ) (sem_IExpr _op_arg ) )
sem_IExpr (IVar _var_ident )  =
    (sem_IExpr_IVar _var_ident )
-- semantic domain
type T_IExpr  = (Map String [(Label, Label)]) ->
                Label ->
                ([Label]) ->
                ([Label]) ->
                (Map String Label) ->
                String ->
                (Map String [Var]) ->
                (Map String [Label]) ->
                ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IExpr ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IExpr  = Inh_IExpr {callLabels_Inh_IExpr :: (Map String [(Label, Label)]),counter_Inh_IExpr :: Label,downGLabel_Inh_IExpr :: ([Label]),downLabel_Inh_IExpr :: ([Label]),funLabels_Inh_IExpr :: (Map String Label),funName_Inh_IExpr :: String,funParams_Inh_IExpr :: (Map String [Var]),retLabels_Inh_IExpr :: (Map String [Label])}
data Syn_IExpr  = Syn_IExpr {callLabels_Syn_IExpr :: (Map String [(Label, Label)]),controlFlow_Syn_IExpr :: ControlFlow,counter_Syn_IExpr :: Label,funLabels_Syn_IExpr :: (Map String Label),funName_Syn_IExpr :: String,funParams_Syn_IExpr :: (Map String [Var]),interFlow_Syn_IExpr :: InterFlow,labels_Syn_IExpr :: ([Label]),retLabels_Syn_IExpr :: (Map String [Label]),self_Syn_IExpr :: IExpr ,startLabel_Syn_IExpr :: ( Maybe Label ),transFunctions_Syn_IExpr :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IExpr :: ([Label]),upLabel_Syn_IExpr :: ([Label])}
wrap_IExpr :: T_IExpr  ->
              Inh_IExpr  ->
              Syn_IExpr 
wrap_IExpr sem (Inh_IExpr _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IExpr _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IExpr_IBinaryOp :: T_IOp  ->
                       T_IExpr  ->
                       T_IExpr  ->
                       T_IExpr 
sem_IExpr_IBinaryOp operator_ left_op_arg_ right_op_arg_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _left_op_argOcallLabels :: (Map String [(Label, Label)])
              _left_op_argOcounter :: Label
              _left_op_argOdownGLabel :: ([Label])
              _left_op_argOdownLabel :: ([Label])
              _left_op_argOfunLabels :: (Map String Label)
              _left_op_argOfunName :: String
              _left_op_argOfunParams :: (Map String [Var])
              _left_op_argOretLabels :: (Map String [Label])
              _right_op_argOcallLabels :: (Map String [(Label, Label)])
              _right_op_argOcounter :: Label
              _right_op_argOdownGLabel :: ([Label])
              _right_op_argOdownLabel :: ([Label])
              _right_op_argOfunLabels :: (Map String Label)
              _right_op_argOfunName :: String
              _right_op_argOfunParams :: (Map String [Var])
              _right_op_argOretLabels :: (Map String [Label])
              _operatorIself :: IOp 
              _left_op_argIcallLabels :: (Map String [(Label, Label)])
              _left_op_argIcontrolFlow :: ControlFlow
              _left_op_argIcounter :: Label
              _left_op_argIfunLabels :: (Map String Label)
              _left_op_argIfunName :: String
              _left_op_argIfunParams :: (Map String [Var])
              _left_op_argIinterFlow :: InterFlow
              _left_op_argIlabels :: ([Label])
              _left_op_argIretLabels :: (Map String [Label])
              _left_op_argIself :: IExpr 
              _left_op_argIstartLabel :: ( Maybe Label )
              _left_op_argItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _left_op_argIupGLabel :: ([Label])
              _left_op_argIupLabel :: ([Label])
              _right_op_argIcallLabels :: (Map String [(Label, Label)])
              _right_op_argIcontrolFlow :: ControlFlow
              _right_op_argIcounter :: Label
              _right_op_argIfunLabels :: (Map String Label)
              _right_op_argIfunName :: String
              _right_op_argIfunParams :: (Map String [Var])
              _right_op_argIinterFlow :: InterFlow
              _right_op_argIlabels :: ([Label])
              _right_op_argIretLabels :: (Map String [Label])
              _right_op_argIself :: IExpr 
              _right_op_argIstartLabel :: ( Maybe Label )
              _right_op_argItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _right_op_argIupGLabel :: ([Label])
              _right_op_argIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 1750 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 1755 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _left_op_argIcontrolFlow ++ _right_op_argIcontrolFlow
                   {-# LINE 1760 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _left_op_argIinterFlow ++ _right_op_argIinterFlow
                   {-# LINE 1765 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _left_op_argIlabels ++ _right_op_argIlabels
                   {-# LINE 1770 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _left_op_argItransFunctions `Map.union` _right_op_argItransFunctions
                   {-# LINE 1775 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IBinaryOp _operatorIself _left_op_argIself _right_op_argIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _right_op_argIcallLabels
                   {-# LINE 1784 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _right_op_argIcounter
                   {-# LINE 1789 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _right_op_argIfunLabels
                   {-# LINE 1794 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _right_op_argIfunName
                   {-# LINE 1799 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _right_op_argIfunParams
                   {-# LINE 1804 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _right_op_argIretLabels
                   {-# LINE 1809 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _right_op_argIupGLabel
                   {-# LINE 1814 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 1819 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1824 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 1829 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 1834 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 1839 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 1844 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 1849 "src/Analysis/Python.hs" #-}
                   )
              _left_op_argOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 1854 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _left_op_argIcallLabels
                   {-# LINE 1859 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _left_op_argIcounter
                   {-# LINE 1864 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 1869 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 1874 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _left_op_argIfunLabels
                   {-# LINE 1879 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _left_op_argIfunName
                   {-# LINE 1884 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _left_op_argIfunParams
                   {-# LINE 1889 "src/Analysis/Python.hs" #-}
                   )
              _right_op_argOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _left_op_argIretLabels
                   {-# LINE 1894 "src/Analysis/Python.hs" #-}
                   )
              ( _operatorIself) =
                  operator_ 
              ( _left_op_argIcallLabels,_left_op_argIcontrolFlow,_left_op_argIcounter,_left_op_argIfunLabels,_left_op_argIfunName,_left_op_argIfunParams,_left_op_argIinterFlow,_left_op_argIlabels,_left_op_argIretLabels,_left_op_argIself,_left_op_argIstartLabel,_left_op_argItransFunctions,_left_op_argIupGLabel,_left_op_argIupLabel) =
                  left_op_arg_ _left_op_argOcallLabels _left_op_argOcounter _left_op_argOdownGLabel _left_op_argOdownLabel _left_op_argOfunLabels _left_op_argOfunName _left_op_argOfunParams _left_op_argOretLabels 
              ( _right_op_argIcallLabels,_right_op_argIcontrolFlow,_right_op_argIcounter,_right_op_argIfunLabels,_right_op_argIfunName,_right_op_argIfunParams,_right_op_argIinterFlow,_right_op_argIlabels,_right_op_argIretLabels,_right_op_argIself,_right_op_argIstartLabel,_right_op_argItransFunctions,_right_op_argIupGLabel,_right_op_argIupLabel) =
                  right_op_arg_ _right_op_argOcallLabels _right_op_argOcounter _right_op_argOdownGLabel _right_op_argOdownLabel _right_op_argOfunLabels _right_op_argOfunName _right_op_argOfunParams _right_op_argOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IBool :: Bool ->
                   T_IExpr 
sem_IExpr_IBool bool_value_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 1931 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 1936 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 1941 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 1946 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 1951 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 1956 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IBool bool_value_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 1965 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 1970 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 1975 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 1980 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 1985 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 1990 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IBool.lhs.upGLabel"
                   {-# LINE 1995 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ICall :: T_IExpr  ->
                   T_IArgs  ->
                   T_Label  ->
                   T_Label  ->
                   T_IExpr 
sem_IExpr_ICall call_fun_ call_args_ call_callLabel_ call_returnLabel_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOself :: IExpr 
              _lhsOlabels :: ([Label])
              _call_argsOdownLabel :: ([Label])
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOupLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup2 :: ((Label,Label,Label))
              _call_funOcounter :: Label
              _label :: Label
              _return :: Label
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _call_funOcallLabels :: (Map String [(Label, Label)])
              _call_funOdownGLabel :: ([Label])
              _call_funOdownLabel :: ([Label])
              _call_funOfunLabels :: (Map String Label)
              _call_funOfunName :: String
              _call_funOfunParams :: (Map String [Var])
              _call_funOretLabels :: (Map String [Label])
              _call_argsOcallLabels :: (Map String [(Label, Label)])
              _call_argsOcounter :: Label
              _call_argsOdownGLabel :: ([Label])
              _call_argsOfunLabels :: (Map String Label)
              _call_argsOfunName :: String
              _call_argsOfunParams :: (Map String [Var])
              _call_argsOretLabels :: (Map String [Label])
              _call_funIcallLabels :: (Map String [(Label, Label)])
              _call_funIcontrolFlow :: ControlFlow
              _call_funIcounter :: Label
              _call_funIfunLabels :: (Map String Label)
              _call_funIfunName :: String
              _call_funIfunParams :: (Map String [Var])
              _call_funIinterFlow :: InterFlow
              _call_funIlabels :: ([Label])
              _call_funIretLabels :: (Map String [Label])
              _call_funIself :: IExpr 
              _call_funIstartLabel :: ( Maybe Label )
              _call_funItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _call_funIupGLabel :: ([Label])
              _call_funIupLabel :: ([Label])
              _call_argsIcallLabels :: (Map String [(Label, Label)])
              _call_argsIcontrolFlow :: ControlFlow
              _call_argsIcounter :: Label
              _call_argsIfunLabels :: (Map String Label)
              _call_argsIfunName :: String
              _call_argsIfunParams :: (Map String [Var])
              _call_argsIinterFlow :: InterFlow
              _call_argsIlabels :: ([Label])
              _call_argsIretLabels :: (Map String [Label])
              _call_argsIself :: IArgs 
              _call_argsIstartLabel :: ( Maybe Label )
              _call_argsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _call_argsIupGLabel :: ([Label])
              _call_argsIupLabel :: ([Label])
              _call_callLabelIself :: Label 
              _call_returnLabelIself :: Label 
              _lhsOself =
                  ({-# LINE 88 "src/Analysis/Python.ag" #-}
                   ICall _call_funIself _call_argsIself _label     _return
                   {-# LINE 2078 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 89 "src/Analysis/Python.ag" #-}
                   _label    :(_return    :(_call_argsIlabels))
                   {-# LINE 2083 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOdownLabel =
                  ({-# LINE 203 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2088 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcallLabels =
                  ({-# LINE 204 "src/Analysis/Python.ag" #-}
                   Map.insertWith (++) (fname _call_funIself) [(_label    , _return    )] _lhsIcallLabels
                   {-# LINE 2093 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 205 "src/Analysis/Python.ag" #-}
                   let funame = fname _call_funIself
                                           in case Map.lookup funame _lhsIfunLabels of
                                                        Nothing -> error "Function not defined"
                                                        Just l  -> let funame = fname _call_funIself
                                                                       in if (funame == _lhsIfunName)
                                                                          then (InterFlow (_label    , l)):(createFlow IntraFlow _call_argsIupLabel [_label    ] ++ _call_funIcontrolFlow ++ _call_argsIcontrolFlow)
                                                                      else case Map.lookup funame _lhsIretLabels of
                                                                                                        Nothing -> error $ "Can't find retLabels for " ++ show funame ++ show _lhsIretLabels
                                                                                                        Just r  -> (InterFlow (_label    , l)):(createFlow IntraFlow _call_argsIupLabel [_label    ] ++ createFlow InterFlow r [_return    ] ++ _call_funIcontrolFlow ++ _call_argsIcontrolFlow)
                   {-# LINE 2106 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 214 "src/Analysis/Python.ag" #-}
                   [_return    ]
                   {-# LINE 2111 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 215 "src/Analysis/Python.ag" #-}
                   case _call_argsIstartLabel of
                        Nothing -> Just _label
                        Just x  -> Just x
                   {-# LINE 2118 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 240 "src/Analysis/Python.ag" #-}
                   let funame = fname _call_funIself
                                           in if (funame == _lhsIfunName) then []
                                              else case Map.lookup funame _lhsIfunLabels of
                                                            Nothing -> error "Function not defined"
                                                            Just l  -> case Map.lookup funame _lhsIretLabels of
                                                                                  Nothing -> error "Shouldn't happen bla"
                                                                                  Just r  -> createInterFlow _label     l r _return
                   {-# LINE 2129 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 273 "src/Analysis/Python.ag" #-}
                   let funame = fname _call_funIself
                       funargs  = fromJustWError ("Function not defined " ++ show funame) $ Map.lookup funame _lhsIfunParams
                       ltyargs = \env -> getArgsTy _call_argsIself env
                       margsty = \env -> Map.fromList $ zip funargs (ltyargs env)
                       ctf = Unary $ \(c, env) -> (c ++ [_label    ], Map.union (margsty env) env)
                                               in Map.insert _label     ctf $ Map.insert _return     (Binary $ \(c, env) (cf, envf) -> (cf, filterOut env envf ("r"++funame))) $ _call_argsItransFunctions
                   {-# LINE 2139 "src/Analysis/Python.hs" #-}
                   )
              __tup2 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> case nextUnique __cont of { (__cont, return) -> (__cont, label,return)}} )
              (_call_funOcounter,_,_) =
                  ({-# LINE 90 "src/Analysis/Python.ag" #-}
                   __tup2
                   {-# LINE 2146 "src/Analysis/Python.hs" #-}
                   )
              (_,_label,_) =
                  ({-# LINE 90 "src/Analysis/Python.ag" #-}
                   __tup2
                   {-# LINE 2151 "src/Analysis/Python.hs" #-}
                   )
              (_,_,_return) =
                  ({-# LINE 91 "src/Analysis/Python.ag" #-}
                   __tup2
                   {-# LINE 2156 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ICall _call_funIself _call_argsIself _call_callLabelIself _call_returnLabelIself
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _call_argsIcounter
                   {-# LINE 2163 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _call_argsIfunLabels
                   {-# LINE 2168 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _call_argsIfunName
                   {-# LINE 2173 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _call_argsIfunParams
                   {-# LINE 2178 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _call_argsIretLabels
                   {-# LINE 2183 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _call_argsIupGLabel
                   {-# LINE 2188 "src/Analysis/Python.hs" #-}
                   )
              _call_funOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2193 "src/Analysis/Python.hs" #-}
                   )
              _call_funOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 2198 "src/Analysis/Python.hs" #-}
                   )
              _call_funOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2203 "src/Analysis/Python.hs" #-}
                   )
              _call_funOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2208 "src/Analysis/Python.hs" #-}
                   )
              _call_funOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2213 "src/Analysis/Python.hs" #-}
                   )
              _call_funOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2218 "src/Analysis/Python.hs" #-}
                   )
              _call_funOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2223 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _call_funIcallLabels
                   {-# LINE 2228 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _call_funIcounter
                   {-# LINE 2233 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 2238 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _call_funIfunLabels
                   {-# LINE 2243 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _call_funIfunName
                   {-# LINE 2248 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _call_funIfunParams
                   {-# LINE 2253 "src/Analysis/Python.hs" #-}
                   )
              _call_argsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _call_funIretLabels
                   {-# LINE 2258 "src/Analysis/Python.hs" #-}
                   )
              ( _call_funIcallLabels,_call_funIcontrolFlow,_call_funIcounter,_call_funIfunLabels,_call_funIfunName,_call_funIfunParams,_call_funIinterFlow,_call_funIlabels,_call_funIretLabels,_call_funIself,_call_funIstartLabel,_call_funItransFunctions,_call_funIupGLabel,_call_funIupLabel) =
                  call_fun_ _call_funOcallLabels _call_funOcounter _call_funOdownGLabel _call_funOdownLabel _call_funOfunLabels _call_funOfunName _call_funOfunParams _call_funOretLabels 
              ( _call_argsIcallLabels,_call_argsIcontrolFlow,_call_argsIcounter,_call_argsIfunLabels,_call_argsIfunName,_call_argsIfunParams,_call_argsIinterFlow,_call_argsIlabels,_call_argsIretLabels,_call_argsIself,_call_argsIstartLabel,_call_argsItransFunctions,_call_argsIupGLabel,_call_argsIupLabel) =
                  call_args_ _call_argsOcallLabels _call_argsOcounter _call_argsOdownGLabel _call_argsOdownLabel _call_argsOfunLabels _call_argsOfunName _call_argsOfunParams _call_argsOretLabels 
              ( _call_callLabelIself) =
                  call_callLabel_ 
              ( _call_returnLabelIself) =
                  call_returnLabel_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ICondExpr :: T_IExpr  ->
                       T_IExpr  ->
                       T_IExpr  ->
                       T_IExpr 
sem_IExpr_ICondExpr ce_true_branch_ ce_condition_ ce_false_branch_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _ce_true_branchOcallLabels :: (Map String [(Label, Label)])
              _ce_true_branchOcounter :: Label
              _ce_true_branchOdownGLabel :: ([Label])
              _ce_true_branchOdownLabel :: ([Label])
              _ce_true_branchOfunLabels :: (Map String Label)
              _ce_true_branchOfunName :: String
              _ce_true_branchOfunParams :: (Map String [Var])
              _ce_true_branchOretLabels :: (Map String [Label])
              _ce_conditionOcallLabels :: (Map String [(Label, Label)])
              _ce_conditionOcounter :: Label
              _ce_conditionOdownGLabel :: ([Label])
              _ce_conditionOdownLabel :: ([Label])
              _ce_conditionOfunLabels :: (Map String Label)
              _ce_conditionOfunName :: String
              _ce_conditionOfunParams :: (Map String [Var])
              _ce_conditionOretLabels :: (Map String [Label])
              _ce_false_branchOcallLabels :: (Map String [(Label, Label)])
              _ce_false_branchOcounter :: Label
              _ce_false_branchOdownGLabel :: ([Label])
              _ce_false_branchOdownLabel :: ([Label])
              _ce_false_branchOfunLabels :: (Map String Label)
              _ce_false_branchOfunName :: String
              _ce_false_branchOfunParams :: (Map String [Var])
              _ce_false_branchOretLabels :: (Map String [Label])
              _ce_true_branchIcallLabels :: (Map String [(Label, Label)])
              _ce_true_branchIcontrolFlow :: ControlFlow
              _ce_true_branchIcounter :: Label
              _ce_true_branchIfunLabels :: (Map String Label)
              _ce_true_branchIfunName :: String
              _ce_true_branchIfunParams :: (Map String [Var])
              _ce_true_branchIinterFlow :: InterFlow
              _ce_true_branchIlabels :: ([Label])
              _ce_true_branchIretLabels :: (Map String [Label])
              _ce_true_branchIself :: IExpr 
              _ce_true_branchIstartLabel :: ( Maybe Label )
              _ce_true_branchItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _ce_true_branchIupGLabel :: ([Label])
              _ce_true_branchIupLabel :: ([Label])
              _ce_conditionIcallLabels :: (Map String [(Label, Label)])
              _ce_conditionIcontrolFlow :: ControlFlow
              _ce_conditionIcounter :: Label
              _ce_conditionIfunLabels :: (Map String Label)
              _ce_conditionIfunName :: String
              _ce_conditionIfunParams :: (Map String [Var])
              _ce_conditionIinterFlow :: InterFlow
              _ce_conditionIlabels :: ([Label])
              _ce_conditionIretLabels :: (Map String [Label])
              _ce_conditionIself :: IExpr 
              _ce_conditionIstartLabel :: ( Maybe Label )
              _ce_conditionItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _ce_conditionIupGLabel :: ([Label])
              _ce_conditionIupLabel :: ([Label])
              _ce_false_branchIcallLabels :: (Map String [(Label, Label)])
              _ce_false_branchIcontrolFlow :: ControlFlow
              _ce_false_branchIcounter :: Label
              _ce_false_branchIfunLabels :: (Map String Label)
              _ce_false_branchIfunName :: String
              _ce_false_branchIfunParams :: (Map String [Var])
              _ce_false_branchIinterFlow :: InterFlow
              _ce_false_branchIlabels :: ([Label])
              _ce_false_branchIretLabels :: (Map String [Label])
              _ce_false_branchIself :: IExpr 
              _ce_false_branchIstartLabel :: ( Maybe Label )
              _ce_false_branchItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _ce_false_branchIupGLabel :: ([Label])
              _ce_false_branchIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2365 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2370 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIcontrolFlow ++ _ce_conditionIcontrolFlow ++ _ce_false_branchIcontrolFlow
                   {-# LINE 2375 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIinterFlow ++ _ce_conditionIinterFlow ++ _ce_false_branchIinterFlow
                   {-# LINE 2380 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIlabels ++ _ce_conditionIlabels ++ _ce_false_branchIlabels
                   {-# LINE 2385 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _ce_true_branchItransFunctions `Map.union` _ce_conditionItransFunctions `Map.union` _ce_false_branchItransFunctions
                   {-# LINE 2390 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ICondExpr _ce_true_branchIself _ce_conditionIself _ce_false_branchIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIcallLabels
                   {-# LINE 2399 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIcounter
                   {-# LINE 2404 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIfunLabels
                   {-# LINE 2409 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIfunName
                   {-# LINE 2414 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIfunParams
                   {-# LINE 2419 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIretLabels
                   {-# LINE 2424 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _ce_false_branchIupGLabel
                   {-# LINE 2429 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2434 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 2439 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 2444 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2449 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2454 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2459 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2464 "src/Analysis/Python.hs" #-}
                   )
              _ce_true_branchOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2469 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIcallLabels
                   {-# LINE 2474 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIcounter
                   {-# LINE 2479 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 2484 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2489 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIfunLabels
                   {-# LINE 2494 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIfunName
                   {-# LINE 2499 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIfunParams
                   {-# LINE 2504 "src/Analysis/Python.hs" #-}
                   )
              _ce_conditionOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _ce_true_branchIretLabels
                   {-# LINE 2509 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _ce_conditionIcallLabels
                   {-# LINE 2514 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _ce_conditionIcounter
                   {-# LINE 2519 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 2524 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2529 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _ce_conditionIfunLabels
                   {-# LINE 2534 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _ce_conditionIfunName
                   {-# LINE 2539 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _ce_conditionIfunParams
                   {-# LINE 2544 "src/Analysis/Python.hs" #-}
                   )
              _ce_false_branchOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _ce_conditionIretLabels
                   {-# LINE 2549 "src/Analysis/Python.hs" #-}
                   )
              ( _ce_true_branchIcallLabels,_ce_true_branchIcontrolFlow,_ce_true_branchIcounter,_ce_true_branchIfunLabels,_ce_true_branchIfunName,_ce_true_branchIfunParams,_ce_true_branchIinterFlow,_ce_true_branchIlabels,_ce_true_branchIretLabels,_ce_true_branchIself,_ce_true_branchIstartLabel,_ce_true_branchItransFunctions,_ce_true_branchIupGLabel,_ce_true_branchIupLabel) =
                  ce_true_branch_ _ce_true_branchOcallLabels _ce_true_branchOcounter _ce_true_branchOdownGLabel _ce_true_branchOdownLabel _ce_true_branchOfunLabels _ce_true_branchOfunName _ce_true_branchOfunParams _ce_true_branchOretLabels 
              ( _ce_conditionIcallLabels,_ce_conditionIcontrolFlow,_ce_conditionIcounter,_ce_conditionIfunLabels,_ce_conditionIfunName,_ce_conditionIfunParams,_ce_conditionIinterFlow,_ce_conditionIlabels,_ce_conditionIretLabels,_ce_conditionIself,_ce_conditionIstartLabel,_ce_conditionItransFunctions,_ce_conditionIupGLabel,_ce_conditionIupLabel) =
                  ce_condition_ _ce_conditionOcallLabels _ce_conditionOcounter _ce_conditionOdownGLabel _ce_conditionOdownLabel _ce_conditionOfunLabels _ce_conditionOfunName _ce_conditionOfunParams _ce_conditionOretLabels 
              ( _ce_false_branchIcallLabels,_ce_false_branchIcontrolFlow,_ce_false_branchIcounter,_ce_false_branchIfunLabels,_ce_false_branchIfunName,_ce_false_branchIfunParams,_ce_false_branchIinterFlow,_ce_false_branchIlabels,_ce_false_branchIretLabels,_ce_false_branchIself,_ce_false_branchIstartLabel,_ce_false_branchItransFunctions,_ce_false_branchIupGLabel,_ce_false_branchIupLabel) =
                  ce_false_branch_ _ce_false_branchOcallLabels _ce_false_branchOcounter _ce_false_branchOdownGLabel _ce_false_branchOdownLabel _ce_false_branchOfunLabels _ce_false_branchOfunName _ce_false_branchOfunParams _ce_false_branchOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IExprNotSupported :: T_IExpr 
sem_IExpr_IExprNotSupported  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2585 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2590 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2595 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2600 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2605 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 2610 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IExprNotSupported
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2619 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 2624 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2629 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2634 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2639 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2644 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IExprNotSupported.lhs.upGLabel"
                   {-# LINE 2649 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IFloat :: Double ->
                    String ->
                    T_IExpr 
sem_IExpr_IFloat float_value_ expr_literal_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2681 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2686 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2691 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2696 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2701 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 2706 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IFloat float_value_ expr_literal_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2715 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 2720 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2725 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2730 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2735 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2740 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IFloat.lhs.upGLabel"
                   {-# LINE 2745 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IImaginary :: Double ->
                        String ->
                        T_IExpr 
sem_IExpr_IImaginary imaginary_value_ expr_literal_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2777 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2782 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2787 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2792 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2797 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 2802 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IImaginary imaginary_value_ expr_literal_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2811 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 2816 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2821 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2826 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2831 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2836 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IImaginary.lhs.upGLabel"
                   {-# LINE 2841 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IInt :: Integer ->
                  String ->
                  T_IExpr 
sem_IExpr_IInt int_value_ expr_literal_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2873 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 2878 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2883 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2888 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 2893 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 2898 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IInt int_value_ expr_literal_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 2907 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 2912 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 2917 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 2922 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 2927 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 2932 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IInt.lhs.upGLabel"
                   {-# LINE 2937 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ILambda :: T_IParams  ->
                     T_IExpr  ->
                     T_IExpr 
sem_IExpr_ILambda lambda_args_ lambda_body_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lambda_argsOcounter :: Label
              _lambda_bodyOcallLabels :: (Map String [(Label, Label)])
              _lambda_bodyOcounter :: Label
              _lambda_bodyOdownGLabel :: ([Label])
              _lambda_bodyOdownLabel :: ([Label])
              _lambda_bodyOfunLabels :: (Map String Label)
              _lambda_bodyOfunName :: String
              _lambda_bodyOfunParams :: (Map String [Var])
              _lambda_bodyOretLabels :: (Map String [Label])
              _lambda_argsIcounter :: Label
              _lambda_argsIlabels :: ([Label])
              _lambda_argsIself :: IParams 
              _lambda_argsIstartLabel :: ( Maybe Label )
              _lambda_bodyIcallLabels :: (Map String [(Label, Label)])
              _lambda_bodyIcontrolFlow :: ControlFlow
              _lambda_bodyIcounter :: Label
              _lambda_bodyIfunLabels :: (Map String Label)
              _lambda_bodyIfunName :: String
              _lambda_bodyIfunParams :: (Map String [Var])
              _lambda_bodyIinterFlow :: InterFlow
              _lambda_bodyIlabels :: ([Label])
              _lambda_bodyIretLabels :: (Map String [Label])
              _lambda_bodyIself :: IExpr 
              _lambda_bodyIstartLabel :: ( Maybe Label )
              _lambda_bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lambda_bodyIupGLabel :: ([Label])
              _lambda_bodyIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 2996 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3001 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIcontrolFlow
                   {-# LINE 3006 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIinterFlow
                   {-# LINE 3011 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _lambda_argsIlabels ++ _lambda_bodyIlabels
                   {-# LINE 3016 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _lambda_bodyItransFunctions
                   {-# LINE 3021 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ILambda _lambda_argsIself _lambda_bodyIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIcallLabels
                   {-# LINE 3030 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIcounter
                   {-# LINE 3035 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIfunLabels
                   {-# LINE 3040 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIfunName
                   {-# LINE 3045 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIfunParams
                   {-# LINE 3050 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIretLabels
                   {-# LINE 3055 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _lambda_bodyIupGLabel
                   {-# LINE 3060 "src/Analysis/Python.hs" #-}
                   )
              _lambda_argsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3065 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3070 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lambda_argsIcounter
                   {-# LINE 3075 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 3080 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3085 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3090 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3095 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3100 "src/Analysis/Python.hs" #-}
                   )
              _lambda_bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3105 "src/Analysis/Python.hs" #-}
                   )
              ( _lambda_argsIcounter,_lambda_argsIlabels,_lambda_argsIself,_lambda_argsIstartLabel) =
                  lambda_args_ _lambda_argsOcounter 
              ( _lambda_bodyIcallLabels,_lambda_bodyIcontrolFlow,_lambda_bodyIcounter,_lambda_bodyIfunLabels,_lambda_bodyIfunName,_lambda_bodyIfunParams,_lambda_bodyIinterFlow,_lambda_bodyIlabels,_lambda_bodyIretLabels,_lambda_bodyIself,_lambda_bodyIstartLabel,_lambda_bodyItransFunctions,_lambda_bodyIupGLabel,_lambda_bodyIupLabel) =
                  lambda_body_ _lambda_bodyOcallLabels _lambda_bodyOcounter _lambda_bodyOdownGLabel _lambda_bodyOdownLabel _lambda_bodyOfunLabels _lambda_bodyOfunName _lambda_bodyOfunParams _lambda_bodyOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IList :: T_IExprs  ->
                   T_IExpr 
sem_IExpr_IList list_exprs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _list_exprsOcallLabels :: (Map String [(Label, Label)])
              _list_exprsOcounter :: Label
              _list_exprsOdownGLabel :: ([Label])
              _list_exprsOdownLabel :: ([Label])
              _list_exprsOfunLabels :: (Map String Label)
              _list_exprsOfunName :: String
              _list_exprsOfunParams :: (Map String [Var])
              _list_exprsOretLabels :: (Map String [Label])
              _list_exprsIcallLabels :: (Map String [(Label, Label)])
              _list_exprsIcontrolFlow :: ControlFlow
              _list_exprsIcounter :: Label
              _list_exprsIfunLabels :: (Map String Label)
              _list_exprsIfunName :: String
              _list_exprsIfunParams :: (Map String [Var])
              _list_exprsIinterFlow :: InterFlow
              _list_exprsIlabels :: ([Label])
              _list_exprsIretLabels :: (Map String [Label])
              _list_exprsIself :: IExprs 
              _list_exprsIstartLabel :: ( Maybe Label )
              _list_exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _list_exprsIupGLabel :: ([Label])
              _list_exprsIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3162 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3167 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _list_exprsIcontrolFlow
                   {-# LINE 3172 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _list_exprsIinterFlow
                   {-# LINE 3177 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _list_exprsIlabels
                   {-# LINE 3182 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _list_exprsItransFunctions
                   {-# LINE 3187 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IList _list_exprsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _list_exprsIcallLabels
                   {-# LINE 3196 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _list_exprsIcounter
                   {-# LINE 3201 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _list_exprsIfunLabels
                   {-# LINE 3206 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _list_exprsIfunName
                   {-# LINE 3211 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _list_exprsIfunParams
                   {-# LINE 3216 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _list_exprsIretLabels
                   {-# LINE 3221 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _list_exprsIupGLabel
                   {-# LINE 3226 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3231 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3236 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 3241 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3246 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3251 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3256 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3261 "src/Analysis/Python.hs" #-}
                   )
              _list_exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3266 "src/Analysis/Python.hs" #-}
                   )
              ( _list_exprsIcallLabels,_list_exprsIcontrolFlow,_list_exprsIcounter,_list_exprsIfunLabels,_list_exprsIfunName,_list_exprsIfunParams,_list_exprsIinterFlow,_list_exprsIlabels,_list_exprsIretLabels,_list_exprsIself,_list_exprsIstartLabel,_list_exprsItransFunctions,_list_exprsIupGLabel,_list_exprsIupLabel) =
                  list_exprs_ _list_exprsOcallLabels _list_exprsOcounter _list_exprsOdownGLabel _list_exprsOdownLabel _list_exprsOfunLabels _list_exprsOfunName _list_exprsOfunParams _list_exprsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ILongInt :: Integer ->
                      String ->
                      T_IExpr 
sem_IExpr_ILongInt int_value_ expr_literal_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3300 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3305 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3310 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3315 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3320 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 3325 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ILongInt int_value_ expr_literal_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3334 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3339 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3344 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3349 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3354 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3359 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.ILongInt.lhs.upGLabel"
                   {-# LINE 3364 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_INone :: T_IExpr 
sem_IExpr_INone  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3394 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3399 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3404 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3409 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3414 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 3419 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  INone
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3428 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3433 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3438 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3443 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3448 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3453 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.INone.lhs.upGLabel"
                   {-# LINE 3458 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IParen :: T_IExpr  ->
                    T_IExpr 
sem_IExpr_IParen paren_expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _paren_exprOcallLabels :: (Map String [(Label, Label)])
              _paren_exprOcounter :: Label
              _paren_exprOdownGLabel :: ([Label])
              _paren_exprOdownLabel :: ([Label])
              _paren_exprOfunLabels :: (Map String Label)
              _paren_exprOfunName :: String
              _paren_exprOfunParams :: (Map String [Var])
              _paren_exprOretLabels :: (Map String [Label])
              _paren_exprIcallLabels :: (Map String [(Label, Label)])
              _paren_exprIcontrolFlow :: ControlFlow
              _paren_exprIcounter :: Label
              _paren_exprIfunLabels :: (Map String Label)
              _paren_exprIfunName :: String
              _paren_exprIfunParams :: (Map String [Var])
              _paren_exprIinterFlow :: InterFlow
              _paren_exprIlabels :: ([Label])
              _paren_exprIretLabels :: (Map String [Label])
              _paren_exprIself :: IExpr 
              _paren_exprIstartLabel :: ( Maybe Label )
              _paren_exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _paren_exprIupGLabel :: ([Label])
              _paren_exprIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3511 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3516 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _paren_exprIcontrolFlow
                   {-# LINE 3521 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _paren_exprIinterFlow
                   {-# LINE 3526 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _paren_exprIlabels
                   {-# LINE 3531 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _paren_exprItransFunctions
                   {-# LINE 3536 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IParen _paren_exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _paren_exprIcallLabels
                   {-# LINE 3545 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _paren_exprIcounter
                   {-# LINE 3550 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _paren_exprIfunLabels
                   {-# LINE 3555 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _paren_exprIfunName
                   {-# LINE 3560 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _paren_exprIfunParams
                   {-# LINE 3565 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _paren_exprIretLabels
                   {-# LINE 3570 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _paren_exprIupGLabel
                   {-# LINE 3575 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3580 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3585 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 3590 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3595 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3600 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3605 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3610 "src/Analysis/Python.hs" #-}
                   )
              _paren_exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3615 "src/Analysis/Python.hs" #-}
                   )
              ( _paren_exprIcallLabels,_paren_exprIcontrolFlow,_paren_exprIcounter,_paren_exprIfunLabels,_paren_exprIfunName,_paren_exprIfunParams,_paren_exprIinterFlow,_paren_exprIlabels,_paren_exprIretLabels,_paren_exprIself,_paren_exprIstartLabel,_paren_exprItransFunctions,_paren_exprIupGLabel,_paren_exprIupLabel) =
                  paren_expr_ _paren_exprOcallLabels _paren_exprOcounter _paren_exprOdownGLabel _paren_exprOdownLabel _paren_exprOfunLabels _paren_exprOfunName _paren_exprOfunParams _paren_exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ISet :: T_IExprs  ->
                  T_IExpr 
sem_IExpr_ISet set_exprs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _set_exprsOcallLabels :: (Map String [(Label, Label)])
              _set_exprsOcounter :: Label
              _set_exprsOdownGLabel :: ([Label])
              _set_exprsOdownLabel :: ([Label])
              _set_exprsOfunLabels :: (Map String Label)
              _set_exprsOfunName :: String
              _set_exprsOfunParams :: (Map String [Var])
              _set_exprsOretLabels :: (Map String [Label])
              _set_exprsIcallLabels :: (Map String [(Label, Label)])
              _set_exprsIcontrolFlow :: ControlFlow
              _set_exprsIcounter :: Label
              _set_exprsIfunLabels :: (Map String Label)
              _set_exprsIfunName :: String
              _set_exprsIfunParams :: (Map String [Var])
              _set_exprsIinterFlow :: InterFlow
              _set_exprsIlabels :: ([Label])
              _set_exprsIretLabels :: (Map String [Label])
              _set_exprsIself :: IExprs 
              _set_exprsIstartLabel :: ( Maybe Label )
              _set_exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _set_exprsIupGLabel :: ([Label])
              _set_exprsIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3670 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3675 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _set_exprsIcontrolFlow
                   {-# LINE 3680 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _set_exprsIinterFlow
                   {-# LINE 3685 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _set_exprsIlabels
                   {-# LINE 3690 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _set_exprsItransFunctions
                   {-# LINE 3695 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ISet _set_exprsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _set_exprsIcallLabels
                   {-# LINE 3704 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _set_exprsIcounter
                   {-# LINE 3709 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _set_exprsIfunLabels
                   {-# LINE 3714 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _set_exprsIfunName
                   {-# LINE 3719 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _set_exprsIfunParams
                   {-# LINE 3724 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _set_exprsIretLabels
                   {-# LINE 3729 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _set_exprsIupGLabel
                   {-# LINE 3734 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3739 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3744 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 3749 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3754 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3759 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3764 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3769 "src/Analysis/Python.hs" #-}
                   )
              _set_exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3774 "src/Analysis/Python.hs" #-}
                   )
              ( _set_exprsIcallLabels,_set_exprsIcontrolFlow,_set_exprsIcounter,_set_exprsIfunLabels,_set_exprsIfunName,_set_exprsIfunParams,_set_exprsIinterFlow,_set_exprsIlabels,_set_exprsIretLabels,_set_exprsIself,_set_exprsIstartLabel,_set_exprsItransFunctions,_set_exprsIupGLabel,_set_exprsIupLabel) =
                  set_exprs_ _set_exprsOcallLabels _set_exprsOcounter _set_exprsOdownGLabel _set_exprsOdownLabel _set_exprsOfunLabels _set_exprsOfunName _set_exprsOfunParams _set_exprsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IString :: T_Strings  ->
                     T_IExpr 
sem_IExpr_IString expr_literal_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _expr_literalIself :: Strings 
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3808 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3813 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3818 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3823 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 3828 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 3833 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IString _expr_literalIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3842 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 3847 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 3852 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 3857 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 3862 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 3867 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IString.lhs.upGLabel"
                   {-# LINE 3872 "src/Analysis/Python.hs" #-}
                   )
              ( _expr_literalIself) =
                  expr_literal_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IStringConversion :: T_IExpr  ->
                               T_IExpr 
sem_IExpr_IStringConversion backquoted_expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _backquoted_exprOcallLabels :: (Map String [(Label, Label)])
              _backquoted_exprOcounter :: Label
              _backquoted_exprOdownGLabel :: ([Label])
              _backquoted_exprOdownLabel :: ([Label])
              _backquoted_exprOfunLabels :: (Map String Label)
              _backquoted_exprOfunName :: String
              _backquoted_exprOfunParams :: (Map String [Var])
              _backquoted_exprOretLabels :: (Map String [Label])
              _backquoted_exprIcallLabels :: (Map String [(Label, Label)])
              _backquoted_exprIcontrolFlow :: ControlFlow
              _backquoted_exprIcounter :: Label
              _backquoted_exprIfunLabels :: (Map String Label)
              _backquoted_exprIfunName :: String
              _backquoted_exprIfunParams :: (Map String [Var])
              _backquoted_exprIinterFlow :: InterFlow
              _backquoted_exprIlabels :: ([Label])
              _backquoted_exprIretLabels :: (Map String [Label])
              _backquoted_exprIself :: IExpr 
              _backquoted_exprIstartLabel :: ( Maybe Label )
              _backquoted_exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _backquoted_exprIupGLabel :: ([Label])
              _backquoted_exprIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 3927 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 3932 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIcontrolFlow
                   {-# LINE 3937 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIinterFlow
                   {-# LINE 3942 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIlabels
                   {-# LINE 3947 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _backquoted_exprItransFunctions
                   {-# LINE 3952 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IStringConversion _backquoted_exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIcallLabels
                   {-# LINE 3961 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIcounter
                   {-# LINE 3966 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIfunLabels
                   {-# LINE 3971 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIfunName
                   {-# LINE 3976 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIfunParams
                   {-# LINE 3981 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIretLabels
                   {-# LINE 3986 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _backquoted_exprIupGLabel
                   {-# LINE 3991 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 3996 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4001 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4006 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4011 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4016 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4021 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4026 "src/Analysis/Python.hs" #-}
                   )
              _backquoted_exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4031 "src/Analysis/Python.hs" #-}
                   )
              ( _backquoted_exprIcallLabels,_backquoted_exprIcontrolFlow,_backquoted_exprIcounter,_backquoted_exprIfunLabels,_backquoted_exprIfunName,_backquoted_exprIfunParams,_backquoted_exprIinterFlow,_backquoted_exprIlabels,_backquoted_exprIretLabels,_backquoted_exprIself,_backquoted_exprIstartLabel,_backquoted_exprItransFunctions,_backquoted_exprIupGLabel,_backquoted_exprIupLabel) =
                  backquoted_expr_ _backquoted_exprOcallLabels _backquoted_exprOcounter _backquoted_exprOdownGLabel _backquoted_exprOdownLabel _backquoted_exprOfunLabels _backquoted_exprOfunName _backquoted_exprOfunParams _backquoted_exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ISubscript :: T_IExpr  ->
                        T_IExpr  ->
                        T_IExpr 
sem_IExpr_ISubscript subscriptee_ subscript_expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _subscripteeOcallLabels :: (Map String [(Label, Label)])
              _subscripteeOcounter :: Label
              _subscripteeOdownGLabel :: ([Label])
              _subscripteeOdownLabel :: ([Label])
              _subscripteeOfunLabels :: (Map String Label)
              _subscripteeOfunName :: String
              _subscripteeOfunParams :: (Map String [Var])
              _subscripteeOretLabels :: (Map String [Label])
              _subscript_exprOcallLabels :: (Map String [(Label, Label)])
              _subscript_exprOcounter :: Label
              _subscript_exprOdownGLabel :: ([Label])
              _subscript_exprOdownLabel :: ([Label])
              _subscript_exprOfunLabels :: (Map String Label)
              _subscript_exprOfunName :: String
              _subscript_exprOfunParams :: (Map String [Var])
              _subscript_exprOretLabels :: (Map String [Label])
              _subscripteeIcallLabels :: (Map String [(Label, Label)])
              _subscripteeIcontrolFlow :: ControlFlow
              _subscripteeIcounter :: Label
              _subscripteeIfunLabels :: (Map String Label)
              _subscripteeIfunName :: String
              _subscripteeIfunParams :: (Map String [Var])
              _subscripteeIinterFlow :: InterFlow
              _subscripteeIlabels :: ([Label])
              _subscripteeIretLabels :: (Map String [Label])
              _subscripteeIself :: IExpr 
              _subscripteeIstartLabel :: ( Maybe Label )
              _subscripteeItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _subscripteeIupGLabel :: ([Label])
              _subscripteeIupLabel :: ([Label])
              _subscript_exprIcallLabels :: (Map String [(Label, Label)])
              _subscript_exprIcontrolFlow :: ControlFlow
              _subscript_exprIcounter :: Label
              _subscript_exprIfunLabels :: (Map String Label)
              _subscript_exprIfunName :: String
              _subscript_exprIfunParams :: (Map String [Var])
              _subscript_exprIinterFlow :: InterFlow
              _subscript_exprIlabels :: ([Label])
              _subscript_exprIretLabels :: (Map String [Label])
              _subscript_exprIself :: IExpr 
              _subscript_exprIstartLabel :: ( Maybe Label )
              _subscript_exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _subscript_exprIupGLabel :: ([Label])
              _subscript_exprIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 4109 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4114 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _subscripteeIcontrolFlow ++ _subscript_exprIcontrolFlow
                   {-# LINE 4119 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _subscripteeIinterFlow ++ _subscript_exprIinterFlow
                   {-# LINE 4124 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _subscripteeIlabels ++ _subscript_exprIlabels
                   {-# LINE 4129 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _subscripteeItransFunctions `Map.union` _subscript_exprItransFunctions
                   {-# LINE 4134 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ISubscript _subscripteeIself _subscript_exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _subscript_exprIcallLabels
                   {-# LINE 4143 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _subscript_exprIcounter
                   {-# LINE 4148 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _subscript_exprIfunLabels
                   {-# LINE 4153 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _subscript_exprIfunName
                   {-# LINE 4158 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _subscript_exprIfunParams
                   {-# LINE 4163 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _subscript_exprIretLabels
                   {-# LINE 4168 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _subscript_exprIupGLabel
                   {-# LINE 4173 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4178 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4183 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4188 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4193 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4198 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4203 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4208 "src/Analysis/Python.hs" #-}
                   )
              _subscripteeOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4213 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _subscripteeIcallLabels
                   {-# LINE 4218 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _subscripteeIcounter
                   {-# LINE 4223 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4228 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4233 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _subscripteeIfunLabels
                   {-# LINE 4238 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _subscripteeIfunName
                   {-# LINE 4243 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _subscripteeIfunParams
                   {-# LINE 4248 "src/Analysis/Python.hs" #-}
                   )
              _subscript_exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _subscripteeIretLabels
                   {-# LINE 4253 "src/Analysis/Python.hs" #-}
                   )
              ( _subscripteeIcallLabels,_subscripteeIcontrolFlow,_subscripteeIcounter,_subscripteeIfunLabels,_subscripteeIfunName,_subscripteeIfunParams,_subscripteeIinterFlow,_subscripteeIlabels,_subscripteeIretLabels,_subscripteeIself,_subscripteeIstartLabel,_subscripteeItransFunctions,_subscripteeIupGLabel,_subscripteeIupLabel) =
                  subscriptee_ _subscripteeOcallLabels _subscripteeOcounter _subscripteeOdownGLabel _subscripteeOdownLabel _subscripteeOfunLabels _subscripteeOfunName _subscripteeOfunParams _subscripteeOretLabels 
              ( _subscript_exprIcallLabels,_subscript_exprIcontrolFlow,_subscript_exprIcounter,_subscript_exprIfunLabels,_subscript_exprIfunName,_subscript_exprIfunParams,_subscript_exprIinterFlow,_subscript_exprIlabels,_subscript_exprIretLabels,_subscript_exprIself,_subscript_exprIstartLabel,_subscript_exprItransFunctions,_subscript_exprIupGLabel,_subscript_exprIupLabel) =
                  subscript_expr_ _subscript_exprOcallLabels _subscript_exprOcounter _subscript_exprOdownGLabel _subscript_exprOdownLabel _subscript_exprOfunLabels _subscript_exprOfunName _subscript_exprOfunParams _subscript_exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_ITuple :: T_IExprs  ->
                    T_IExpr 
sem_IExpr_ITuple tuple_exprs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _tuple_exprsOcallLabels :: (Map String [(Label, Label)])
              _tuple_exprsOcounter :: Label
              _tuple_exprsOdownGLabel :: ([Label])
              _tuple_exprsOdownLabel :: ([Label])
              _tuple_exprsOfunLabels :: (Map String Label)
              _tuple_exprsOfunName :: String
              _tuple_exprsOfunParams :: (Map String [Var])
              _tuple_exprsOretLabels :: (Map String [Label])
              _tuple_exprsIcallLabels :: (Map String [(Label, Label)])
              _tuple_exprsIcontrolFlow :: ControlFlow
              _tuple_exprsIcounter :: Label
              _tuple_exprsIfunLabels :: (Map String Label)
              _tuple_exprsIfunName :: String
              _tuple_exprsIfunParams :: (Map String [Var])
              _tuple_exprsIinterFlow :: InterFlow
              _tuple_exprsIlabels :: ([Label])
              _tuple_exprsIretLabels :: (Map String [Label])
              _tuple_exprsIself :: IExprs 
              _tuple_exprsIstartLabel :: ( Maybe Label )
              _tuple_exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _tuple_exprsIupGLabel :: ([Label])
              _tuple_exprsIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 4310 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4315 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIcontrolFlow
                   {-# LINE 4320 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIinterFlow
                   {-# LINE 4325 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIlabels
                   {-# LINE 4330 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _tuple_exprsItransFunctions
                   {-# LINE 4335 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ITuple _tuple_exprsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIcallLabels
                   {-# LINE 4344 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIcounter
                   {-# LINE 4349 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIfunLabels
                   {-# LINE 4354 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIfunName
                   {-# LINE 4359 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIfunParams
                   {-# LINE 4364 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIretLabels
                   {-# LINE 4369 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _tuple_exprsIupGLabel
                   {-# LINE 4374 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4379 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4384 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4389 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4394 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4399 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4404 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4409 "src/Analysis/Python.hs" #-}
                   )
              _tuple_exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4414 "src/Analysis/Python.hs" #-}
                   )
              ( _tuple_exprsIcallLabels,_tuple_exprsIcontrolFlow,_tuple_exprsIcounter,_tuple_exprsIfunLabels,_tuple_exprsIfunName,_tuple_exprsIfunParams,_tuple_exprsIinterFlow,_tuple_exprsIlabels,_tuple_exprsIretLabels,_tuple_exprsIself,_tuple_exprsIstartLabel,_tuple_exprsItransFunctions,_tuple_exprsIupGLabel,_tuple_exprsIupLabel) =
                  tuple_exprs_ _tuple_exprsOcallLabels _tuple_exprsOcounter _tuple_exprsOdownGLabel _tuple_exprsOdownLabel _tuple_exprsOfunLabels _tuple_exprsOfunName _tuple_exprsOfunParams _tuple_exprsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IUnaryOp :: T_IOp  ->
                      T_IExpr  ->
                      T_IExpr 
sem_IExpr_IUnaryOp operator_ op_arg_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _op_argOcallLabels :: (Map String [(Label, Label)])
              _op_argOcounter :: Label
              _op_argOdownGLabel :: ([Label])
              _op_argOdownLabel :: ([Label])
              _op_argOfunLabels :: (Map String Label)
              _op_argOfunName :: String
              _op_argOfunParams :: (Map String [Var])
              _op_argOretLabels :: (Map String [Label])
              _operatorIself :: IOp 
              _op_argIcallLabels :: (Map String [(Label, Label)])
              _op_argIcontrolFlow :: ControlFlow
              _op_argIcounter :: Label
              _op_argIfunLabels :: (Map String Label)
              _op_argIfunName :: String
              _op_argIfunParams :: (Map String [Var])
              _op_argIinterFlow :: InterFlow
              _op_argIlabels :: ([Label])
              _op_argIretLabels :: (Map String [Label])
              _op_argIself :: IExpr 
              _op_argIstartLabel :: ( Maybe Label )
              _op_argItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _op_argIupGLabel :: ([Label])
              _op_argIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 4471 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4476 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _op_argIcontrolFlow
                   {-# LINE 4481 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _op_argIinterFlow
                   {-# LINE 4486 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _op_argIlabels
                   {-# LINE 4491 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _op_argItransFunctions
                   {-# LINE 4496 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IUnaryOp _operatorIself _op_argIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _op_argIcallLabels
                   {-# LINE 4505 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _op_argIcounter
                   {-# LINE 4510 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _op_argIfunLabels
                   {-# LINE 4515 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _op_argIfunName
                   {-# LINE 4520 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _op_argIfunParams
                   {-# LINE 4525 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _op_argIretLabels
                   {-# LINE 4530 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _op_argIupGLabel
                   {-# LINE 4535 "src/Analysis/Python.hs" #-}
                   )
              _op_argOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4540 "src/Analysis/Python.hs" #-}
                   )
              _op_argOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4545 "src/Analysis/Python.hs" #-}
                   )
              _op_argOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4550 "src/Analysis/Python.hs" #-}
                   )
              _op_argOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4555 "src/Analysis/Python.hs" #-}
                   )
              _op_argOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4560 "src/Analysis/Python.hs" #-}
                   )
              _op_argOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4565 "src/Analysis/Python.hs" #-}
                   )
              _op_argOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4570 "src/Analysis/Python.hs" #-}
                   )
              _op_argOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4575 "src/Analysis/Python.hs" #-}
                   )
              ( _operatorIself) =
                  operator_ 
              ( _op_argIcallLabels,_op_argIcontrolFlow,_op_argIcounter,_op_argIfunLabels,_op_argIfunName,_op_argIfunParams,_op_argIinterFlow,_op_argIlabels,_op_argIretLabels,_op_argIself,_op_argIstartLabel,_op_argItransFunctions,_op_argIupGLabel,_op_argIupLabel) =
                  op_arg_ _op_argOcallLabels _op_argOcounter _op_argOdownGLabel _op_argOdownLabel _op_argOfunLabels _op_argOfunName _op_argOfunParams _op_argOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExpr_IVar :: String ->
                  T_IExpr 
sem_IExpr_IVar var_ident_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 218 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 4610 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 219 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4615 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4620 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4625 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4630 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 4635 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IVar var_ident_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4644 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4649 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4654 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4659 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4664 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4669 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IExpr.IVar.lhs.upGLabel"
                   {-# LINE 4674 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IExprs ------------------------------------------------------
-- cata
sem_IExprs :: IExprs  ->
              T_IExprs 
sem_IExprs list  =
    (Prelude.foldr sem_IExprs_Cons sem_IExprs_Nil (Prelude.map sem_IExpr list) )
-- semantic domain
type T_IExprs  = (Map String [(Label, Label)]) ->
                 Label ->
                 ([Label]) ->
                 ([Label]) ->
                 (Map String Label) ->
                 String ->
                 (Map String [Var]) ->
                 (Map String [Label]) ->
                 ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IExprs ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IExprs  = Inh_IExprs {callLabels_Inh_IExprs :: (Map String [(Label, Label)]),counter_Inh_IExprs :: Label,downGLabel_Inh_IExprs :: ([Label]),downLabel_Inh_IExprs :: ([Label]),funLabels_Inh_IExprs :: (Map String Label),funName_Inh_IExprs :: String,funParams_Inh_IExprs :: (Map String [Var]),retLabels_Inh_IExprs :: (Map String [Label])}
data Syn_IExprs  = Syn_IExprs {callLabels_Syn_IExprs :: (Map String [(Label, Label)]),controlFlow_Syn_IExprs :: ControlFlow,counter_Syn_IExprs :: Label,funLabels_Syn_IExprs :: (Map String Label),funName_Syn_IExprs :: String,funParams_Syn_IExprs :: (Map String [Var]),interFlow_Syn_IExprs :: InterFlow,labels_Syn_IExprs :: ([Label]),retLabels_Syn_IExprs :: (Map String [Label]),self_Syn_IExprs :: IExprs ,startLabel_Syn_IExprs :: ( Maybe Label ),transFunctions_Syn_IExprs :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IExprs :: ([Label]),upLabel_Syn_IExprs :: ([Label])}
wrap_IExprs :: T_IExprs  ->
               Inh_IExprs  ->
               Syn_IExprs 
wrap_IExprs sem (Inh_IExprs _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IExprs _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IExprs_Cons :: T_IExpr  ->
                   T_IExprs  ->
                   T_IExprs 
sem_IExprs_Cons hd_ tl_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _hdOdownLabel :: ([Label])
              _hdOdownGLabel :: ([Label])
              _tlOdownLabel :: ([Label])
              _tlOdownGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExprs 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _hdOcallLabels :: (Map String [(Label, Label)])
              _hdOcounter :: Label
              _hdOfunLabels :: (Map String Label)
              _hdOfunName :: String
              _hdOfunParams :: (Map String [Var])
              _hdOretLabels :: (Map String [Label])
              _tlOcallLabels :: (Map String [(Label, Label)])
              _tlOcounter :: Label
              _tlOfunLabels :: (Map String Label)
              _tlOfunName :: String
              _tlOfunParams :: (Map String [Var])
              _tlOretLabels :: (Map String [Label])
              _hdIcallLabels :: (Map String [(Label, Label)])
              _hdIcontrolFlow :: ControlFlow
              _hdIcounter :: Label
              _hdIfunLabels :: (Map String Label)
              _hdIfunName :: String
              _hdIfunParams :: (Map String [Var])
              _hdIinterFlow :: InterFlow
              _hdIlabels :: ([Label])
              _hdIretLabels :: (Map String [Label])
              _hdIself :: IExpr 
              _hdIstartLabel :: ( Maybe Label )
              _hdItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _hdIupGLabel :: ([Label])
              _hdIupLabel :: ([Label])
              _tlIcallLabels :: (Map String [(Label, Label)])
              _tlIcontrolFlow :: ControlFlow
              _tlIcounter :: Label
              _tlIfunLabels :: (Map String Label)
              _tlIfunName :: String
              _tlIfunParams :: (Map String [Var])
              _tlIinterFlow :: InterFlow
              _tlIlabels :: ([Label])
              _tlIretLabels :: (Map String [Label])
              _tlIself :: IExprs 
              _tlIstartLabel :: ( Maybe Label )
              _tlItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _tlIupGLabel :: ([Label])
              _tlIupLabel :: ([Label])
              _hdOdownLabel =
                  ({-# LINE 119 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4774 "src/Analysis/Python.hs" #-}
                   )
              _hdOdownGLabel =
                  ({-# LINE 120 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4779 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownLabel =
                  ({-# LINE 121 "src/Analysis/Python.ag" #-}
                   _hdIupLabel
                   {-# LINE 4784 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownGLabel =
                  ({-# LINE 122 "src/Analysis/Python.ag" #-}
                   _hdIupGLabel
                   {-# LINE 4789 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 123 "src/Analysis/Python.ag" #-}
                   maybe _tlIstartLabel (\_ -> _hdIstartLabel) _hdIstartLabel
                   {-# LINE 4794 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _hdIcontrolFlow ++ _tlIcontrolFlow
                   {-# LINE 4799 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _hdIinterFlow ++ _tlIinterFlow
                   {-# LINE 4804 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 4809 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _hdItransFunctions `Map.union` _tlItransFunctions
                   {-# LINE 4814 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _tlIcallLabels
                   {-# LINE 4823 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 4828 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _tlIfunLabels
                   {-# LINE 4833 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _tlIfunName
                   {-# LINE 4838 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _tlIfunParams
                   {-# LINE 4843 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _tlIretLabels
                   {-# LINE 4848 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _tlIupGLabel
                   {-# LINE 4853 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _tlIupLabel
                   {-# LINE 4858 "src/Analysis/Python.hs" #-}
                   )
              _hdOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4863 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4868 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 4873 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 4878 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 4883 "src/Analysis/Python.hs" #-}
                   )
              _hdOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 4888 "src/Analysis/Python.hs" #-}
                   )
              _tlOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _hdIcallLabels
                   {-# LINE 4893 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 4898 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _hdIfunLabels
                   {-# LINE 4903 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _hdIfunName
                   {-# LINE 4908 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _hdIfunParams
                   {-# LINE 4913 "src/Analysis/Python.hs" #-}
                   )
              _tlOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _hdIretLabels
                   {-# LINE 4918 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcallLabels,_hdIcontrolFlow,_hdIcounter,_hdIfunLabels,_hdIfunName,_hdIfunParams,_hdIinterFlow,_hdIlabels,_hdIretLabels,_hdIself,_hdIstartLabel,_hdItransFunctions,_hdIupGLabel,_hdIupLabel) =
                  hd_ _hdOcallLabels _hdOcounter _hdOdownGLabel _hdOdownLabel _hdOfunLabels _hdOfunName _hdOfunParams _hdOretLabels 
              ( _tlIcallLabels,_tlIcontrolFlow,_tlIcounter,_tlIfunLabels,_tlIfunName,_tlIfunParams,_tlIinterFlow,_tlIlabels,_tlIretLabels,_tlIself,_tlIstartLabel,_tlItransFunctions,_tlIupGLabel,_tlIupLabel) =
                  tl_ _tlOcallLabels _tlOcounter _tlOdownGLabel _tlOdownLabel _tlOfunLabels _tlOfunName _tlOfunParams _tlOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IExprs_Nil :: T_IExprs 
sem_IExprs_Nil  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOupLabel :: ([Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IExprs 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupLabel =
                  ({-# LINE 124 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 4952 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 125 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 4957 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 126 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 4962 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4967 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4972 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 4977 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 4982 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 4991 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 4996 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 5001 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 5006 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 5011 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 5016 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IFromItem ---------------------------------------------------
-- cata
sem_IFromItem :: IFromItem  ->
                 T_IFromItem 
sem_IFromItem (IFromItem _name _asname )  =
    (sem_IFromItem_IFromItem _name _asname )
-- semantic domain
type T_IFromItem  = ( IFromItem )
data Inh_IFromItem  = Inh_IFromItem {}
data Syn_IFromItem  = Syn_IFromItem {self_Syn_IFromItem :: IFromItem }
wrap_IFromItem :: T_IFromItem  ->
                  Inh_IFromItem  ->
                  Syn_IFromItem 
wrap_IFromItem sem (Inh_IFromItem )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IFromItem _lhsOself ))
sem_IFromItem_IFromItem :: String ->
                           (Maybe String) ->
                           T_IFromItem 
sem_IFromItem_IFromItem name_ asname_  =
    (let _lhsOself :: IFromItem 
         _self =
             IFromItem name_ asname_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IFromItems --------------------------------------------------
-- cata
sem_IFromItems :: IFromItems  ->
                  T_IFromItems 
sem_IFromItems (IFromItems _items )  =
    (sem_IFromItems_IFromItems (sem_ILFromItem _items ) )
sem_IFromItems (IImportEverything )  =
    (sem_IFromItems_IImportEverything )
-- semantic domain
type T_IFromItems  = ( IFromItems )
data Inh_IFromItems  = Inh_IFromItems {}
data Syn_IFromItems  = Syn_IFromItems {self_Syn_IFromItems :: IFromItems }
wrap_IFromItems :: T_IFromItems  ->
                   Inh_IFromItems  ->
                   Syn_IFromItems 
wrap_IFromItems sem (Inh_IFromItems )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IFromItems _lhsOself ))
sem_IFromItems_IFromItems :: T_ILFromItem  ->
                             T_IFromItems 
sem_IFromItems_IFromItems items_  =
    (let _lhsOself :: IFromItems 
         _itemsIself :: ILFromItem 
         _self =
             IFromItems _itemsIself
         _lhsOself =
             _self
         ( _itemsIself) =
             items_ 
     in  ( _lhsOself))
sem_IFromItems_IImportEverything :: T_IFromItems 
sem_IFromItems_IImportEverything  =
    (let _lhsOself :: IFromItems 
         _self =
             IImportEverything
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IGuard ------------------------------------------------------
-- cata
sem_IGuard :: IGuard  ->
              T_IGuard 
sem_IGuard (IGuard _cond _body _label )  =
    (sem_IGuard_IGuard (sem_IExpr _cond ) (sem_ISuite _body ) (sem_Label _label ) )
-- semantic domain
type T_IGuard  = (Map String [(Label, Label)]) ->
                 Label ->
                 ([Label]) ->
                 ([Label]) ->
                 (Map String Label) ->
                 String ->
                 (Map String [Var]) ->
                 (Map String [Label]) ->
                 ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IGuard ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IGuard  = Inh_IGuard {callLabels_Inh_IGuard :: (Map String [(Label, Label)]),counter_Inh_IGuard :: Label,downGLabel_Inh_IGuard :: ([Label]),downLabel_Inh_IGuard :: ([Label]),funLabels_Inh_IGuard :: (Map String Label),funName_Inh_IGuard :: String,funParams_Inh_IGuard :: (Map String [Var]),retLabels_Inh_IGuard :: (Map String [Label])}
data Syn_IGuard  = Syn_IGuard {callLabels_Syn_IGuard :: (Map String [(Label, Label)]),controlFlow_Syn_IGuard :: ControlFlow,counter_Syn_IGuard :: Label,funLabels_Syn_IGuard :: (Map String Label),funName_Syn_IGuard :: String,funParams_Syn_IGuard :: (Map String [Var]),interFlow_Syn_IGuard :: InterFlow,labels_Syn_IGuard :: ([Label]),retLabels_Syn_IGuard :: (Map String [Label]),self_Syn_IGuard :: IGuard ,startLabel_Syn_IGuard :: ( Maybe Label ),transFunctions_Syn_IGuard :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IGuard :: ([Label]),upLabel_Syn_IGuard :: ([Label])}
wrap_IGuard :: T_IGuard  ->
               Inh_IGuard  ->
               Syn_IGuard 
wrap_IGuard sem (Inh_IGuard _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IGuard _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IGuard_IGuard :: T_IExpr  ->
                     T_ISuite  ->
                     T_Label  ->
                     T_IGuard 
sem_IGuard_IGuard cond_ body_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOself :: IGuard 
              _lhsOlabels :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOupGLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup3 :: ((Label,Label))
              _condOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _condOcallLabels :: (Map String [(Label, Label)])
              _condOdownGLabel :: ([Label])
              _condOdownLabel :: ([Label])
              _condOfunLabels :: (Map String Label)
              _condOfunName :: String
              _condOfunParams :: (Map String [Var])
              _condOretLabels :: (Map String [Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _condIcallLabels :: (Map String [(Label, Label)])
              _condIcontrolFlow :: ControlFlow
              _condIcounter :: Label
              _condIfunLabels :: (Map String Label)
              _condIfunName :: String
              _condIfunParams :: (Map String [Var])
              _condIinterFlow :: InterFlow
              _condIlabels :: ([Label])
              _condIretLabels :: (Map String [Label])
              _condIself :: IExpr 
              _condIstartLabel :: ( Maybe Label )
              _condItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _condIupGLabel :: ([Label])
              _condIupLabel :: ([Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOself =
                  ({-# LINE 83 "src/Analysis/Python.ag" #-}
                   IGuard _condIself _bodyIself _label
                   {-# LINE 5184 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 84 "src/Analysis/Python.ag" #-}
                   _label    :(_bodyIlabels)
                   {-# LINE 5189 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 137 "src/Analysis/Python.ag" #-}
                   case _lhsIdownGLabel of
                       [] -> createFlow IntraFlow _lhsIdownLabel [_label    ] ++ _bodyIcontrolFlow
                       g  -> createFlow IntraFlow g              [_label    ] ++ _bodyIcontrolFlow
                   {-# LINE 5196 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 140 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 5201 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 141 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 5206 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 142 "src/Analysis/Python.ag" #-}
                   case _lhsIdownGLabel of
                        [] -> _bodyIupLabel
                        g  -> _bodyIupLabel ++ _lhsIdownLabel
                   {-# LINE 5213 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 281 "src/Analysis/Python.ag" #-}
                   Map.insert _label     (Unary id) _bodyItransFunctions
                   {-# LINE 5218 "src/Analysis/Python.hs" #-}
                   )
              __tup3 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_condOcounter,_) =
                  ({-# LINE 85 "src/Analysis/Python.ag" #-}
                   __tup3
                   {-# LINE 5225 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 85 "src/Analysis/Python.ag" #-}
                   __tup3
                   {-# LINE 5230 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _condIinterFlow ++ _bodyIinterFlow
                   {-# LINE 5235 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IGuard _condIself _bodyIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 5242 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 5247 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 5252 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 5257 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 5262 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 5267 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _bodyIstartLabel
                   {-# LINE 5272 "src/Analysis/Python.hs" #-}
                   )
              _condOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 5277 "src/Analysis/Python.hs" #-}
                   )
              _condOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 5282 "src/Analysis/Python.hs" #-}
                   )
              _condOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 5287 "src/Analysis/Python.hs" #-}
                   )
              _condOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 5292 "src/Analysis/Python.hs" #-}
                   )
              _condOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 5297 "src/Analysis/Python.hs" #-}
                   )
              _condOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 5302 "src/Analysis/Python.hs" #-}
                   )
              _condOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 5307 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _condIcallLabels
                   {-# LINE 5312 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _condIcounter
                   {-# LINE 5317 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 5322 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _condIfunLabels
                   {-# LINE 5327 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _condIfunName
                   {-# LINE 5332 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _condIfunParams
                   {-# LINE 5337 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _condIretLabels
                   {-# LINE 5342 "src/Analysis/Python.hs" #-}
                   )
              ( _condIcallLabels,_condIcontrolFlow,_condIcounter,_condIfunLabels,_condIfunName,_condIfunParams,_condIinterFlow,_condIlabels,_condIretLabels,_condIself,_condIstartLabel,_condItransFunctions,_condIupGLabel,_condIupLabel) =
                  cond_ _condOcallLabels _condOcounter _condOdownGLabel _condOdownLabel _condOfunLabels _condOfunName _condOfunParams _condOretLabels 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IGuards -----------------------------------------------------
-- cata
sem_IGuards :: IGuards  ->
               T_IGuards 
sem_IGuards list  =
    (Prelude.foldr sem_IGuards_Cons sem_IGuards_Nil (Prelude.map sem_IGuard list) )
-- semantic domain
type T_IGuards  = (Map String [(Label, Label)]) ->
                  Label ->
                  ([Label]) ->
                  ([Label]) ->
                  (Map String Label) ->
                  String ->
                  (Map String [Var]) ->
                  (Map String [Label]) ->
                  ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IGuards ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IGuards  = Inh_IGuards {callLabels_Inh_IGuards :: (Map String [(Label, Label)]),counter_Inh_IGuards :: Label,downGLabel_Inh_IGuards :: ([Label]),downLabel_Inh_IGuards :: ([Label]),funLabels_Inh_IGuards :: (Map String Label),funName_Inh_IGuards :: String,funParams_Inh_IGuards :: (Map String [Var]),retLabels_Inh_IGuards :: (Map String [Label])}
data Syn_IGuards  = Syn_IGuards {callLabels_Syn_IGuards :: (Map String [(Label, Label)]),controlFlow_Syn_IGuards :: ControlFlow,counter_Syn_IGuards :: Label,funLabels_Syn_IGuards :: (Map String Label),funName_Syn_IGuards :: String,funParams_Syn_IGuards :: (Map String [Var]),interFlow_Syn_IGuards :: InterFlow,labels_Syn_IGuards :: ([Label]),retLabels_Syn_IGuards :: (Map String [Label]),self_Syn_IGuards :: IGuards ,startLabel_Syn_IGuards :: ( Maybe Label ),transFunctions_Syn_IGuards :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IGuards :: ([Label]),upLabel_Syn_IGuards :: ([Label])}
wrap_IGuards :: T_IGuards  ->
                Inh_IGuards  ->
                Syn_IGuards 
wrap_IGuards sem (Inh_IGuards _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IGuards _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IGuards_Cons :: T_IGuard  ->
                    T_IGuards  ->
                    T_IGuards 
sem_IGuards_Cons hd_ tl_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _hdOdownLabel :: ([Label])
              _hdOdownGLabel :: ([Label])
              _tlOdownLabel :: ([Label])
              _tlOdownGLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IGuards 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _hdOcallLabels :: (Map String [(Label, Label)])
              _hdOcounter :: Label
              _hdOfunLabels :: (Map String Label)
              _hdOfunName :: String
              _hdOfunParams :: (Map String [Var])
              _hdOretLabels :: (Map String [Label])
              _tlOcallLabels :: (Map String [(Label, Label)])
              _tlOcounter :: Label
              _tlOfunLabels :: (Map String Label)
              _tlOfunName :: String
              _tlOfunParams :: (Map String [Var])
              _tlOretLabels :: (Map String [Label])
              _hdIcallLabels :: (Map String [(Label, Label)])
              _hdIcontrolFlow :: ControlFlow
              _hdIcounter :: Label
              _hdIfunLabels :: (Map String Label)
              _hdIfunName :: String
              _hdIfunParams :: (Map String [Var])
              _hdIinterFlow :: InterFlow
              _hdIlabels :: ([Label])
              _hdIretLabels :: (Map String [Label])
              _hdIself :: IGuard 
              _hdIstartLabel :: ( Maybe Label )
              _hdItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _hdIupGLabel :: ([Label])
              _hdIupLabel :: ([Label])
              _tlIcallLabels :: (Map String [(Label, Label)])
              _tlIcontrolFlow :: ControlFlow
              _tlIcounter :: Label
              _tlIfunLabels :: (Map String Label)
              _tlIfunName :: String
              _tlIfunParams :: (Map String [Var])
              _tlIinterFlow :: InterFlow
              _tlIlabels :: ([Label])
              _tlIretLabels :: (Map String [Label])
              _tlIself :: IGuards 
              _tlIstartLabel :: ( Maybe Label )
              _tlItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _tlIupGLabel :: ([Label])
              _tlIupLabel :: ([Label])
              _hdOdownLabel =
                  ({-# LINE 129 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 5448 "src/Analysis/Python.hs" #-}
                   )
              _hdOdownGLabel =
                  ({-# LINE 130 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 5453 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownLabel =
                  ({-# LINE 131 "src/Analysis/Python.ag" #-}
                   _hdIupLabel
                   {-# LINE 5458 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownGLabel =
                  ({-# LINE 132 "src/Analysis/Python.ag" #-}
                   _hdIupGLabel
                   {-# LINE 5463 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _hdIcontrolFlow ++ _tlIcontrolFlow
                   {-# LINE 5468 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _hdIinterFlow ++ _tlIinterFlow
                   {-# LINE 5473 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 5478 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _hdItransFunctions `Map.union` _tlItransFunctions
                   {-# LINE 5483 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _tlIcallLabels
                   {-# LINE 5492 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 5497 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _tlIfunLabels
                   {-# LINE 5502 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _tlIfunName
                   {-# LINE 5507 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _tlIfunParams
                   {-# LINE 5512 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _tlIretLabels
                   {-# LINE 5517 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _tlIstartLabel
                   {-# LINE 5522 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _tlIupGLabel
                   {-# LINE 5527 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _tlIupLabel
                   {-# LINE 5532 "src/Analysis/Python.hs" #-}
                   )
              _hdOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 5537 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 5542 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 5547 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 5552 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 5557 "src/Analysis/Python.hs" #-}
                   )
              _hdOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 5562 "src/Analysis/Python.hs" #-}
                   )
              _tlOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _hdIcallLabels
                   {-# LINE 5567 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 5572 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _hdIfunLabels
                   {-# LINE 5577 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _hdIfunName
                   {-# LINE 5582 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _hdIfunParams
                   {-# LINE 5587 "src/Analysis/Python.hs" #-}
                   )
              _tlOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _hdIretLabels
                   {-# LINE 5592 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcallLabels,_hdIcontrolFlow,_hdIcounter,_hdIfunLabels,_hdIfunName,_hdIfunParams,_hdIinterFlow,_hdIlabels,_hdIretLabels,_hdIself,_hdIstartLabel,_hdItransFunctions,_hdIupGLabel,_hdIupLabel) =
                  hd_ _hdOcallLabels _hdOcounter _hdOdownGLabel _hdOdownLabel _hdOfunLabels _hdOfunName _hdOfunParams _hdOretLabels 
              ( _tlIcallLabels,_tlIcontrolFlow,_tlIcounter,_tlIfunLabels,_tlIfunName,_tlIfunParams,_tlIinterFlow,_tlIlabels,_tlIretLabels,_tlIself,_tlIstartLabel,_tlItransFunctions,_tlIupGLabel,_tlIupLabel) =
                  tl_ _tlOcallLabels _tlOcounter _tlOdownGLabel _tlOdownLabel _tlOfunLabels _tlOfunName _tlOfunParams _tlOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IGuards_Nil :: T_IGuards 
sem_IGuards_Nil  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOupLabel :: ([Label])
              _lhsOupGLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IGuards 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupLabel =
                  ({-# LINE 133 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 5626 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 134 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 5631 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 5636 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 5641 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 5646 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 5651 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 5660 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 5665 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 5670 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 5675 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 5680 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 5685 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IGuards.Nil.lhs.startLabel"
                   {-# LINE 5690 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IHandler ----------------------------------------------------
-- cata
sem_IHandler :: IHandler  ->
                T_IHandler 
sem_IHandler (IHandler _clause _suite )  =
    (sem_IHandler_IHandler (sem_IExceptClause _clause ) (sem_ISuite _suite ) )
-- semantic domain
type T_IHandler  = Label ->
                   ( Label,([Label]),IHandler ,( Maybe Label ))
data Inh_IHandler  = Inh_IHandler {counter_Inh_IHandler :: Label}
data Syn_IHandler  = Syn_IHandler {counter_Syn_IHandler :: Label,labels_Syn_IHandler :: ([Label]),self_Syn_IHandler :: IHandler ,startLabel_Syn_IHandler :: ( Maybe Label )}
wrap_IHandler :: T_IHandler  ->
                 Inh_IHandler  ->
                 Syn_IHandler 
wrap_IHandler sem (Inh_IHandler _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IHandler _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IHandler_IHandler :: T_IExceptClause  ->
                         T_ISuite  ->
                         T_IHandler 
sem_IHandler_IHandler clause_ suite_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IHandler 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _suiteOcallLabels :: (Map String [(Label, Label)])
              _suiteOcounter :: Label
              _suiteOdownGLabel :: ([Label])
              _suiteOdownLabel :: ([Label])
              _suiteOfunLabels :: (Map String Label)
              _suiteOfunName :: String
              _suiteOfunParams :: (Map String [Var])
              _suiteOretLabels :: (Map String [Label])
              _clauseIself :: IExceptClause 
              _suiteIcallLabels :: (Map String [(Label, Label)])
              _suiteIcontrolFlow :: ControlFlow
              _suiteIcounter :: Label
              _suiteIfunLabels :: (Map String Label)
              _suiteIfunName :: String
              _suiteIfunParams :: (Map String [Var])
              _suiteIinterFlow :: InterFlow
              _suiteIlabels :: ([Label])
              _suiteIretLabels :: (Map String [Label])
              _suiteIself :: ISuite 
              _suiteIstartLabel :: ( Maybe Label )
              _suiteItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _suiteIupGLabel :: ([Label])
              _suiteIupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _suiteIlabels
                   {-# LINE 5745 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IHandler _clauseIself _suiteIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _suiteIcounter
                   {-# LINE 5754 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _suiteIstartLabel
                   {-# LINE 5759 "src/Analysis/Python.hs" #-}
                   )
              _suiteOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.callLabels"
                   {-# LINE 5764 "src/Analysis/Python.hs" #-}
                   )
              _suiteOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 5769 "src/Analysis/Python.hs" #-}
                   )
              _suiteOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.downGLabel"
                   {-# LINE 5774 "src/Analysis/Python.hs" #-}
                   )
              _suiteOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.downLabel"
                   {-# LINE 5779 "src/Analysis/Python.hs" #-}
                   )
              _suiteOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.funLabels"
                   {-# LINE 5784 "src/Analysis/Python.hs" #-}
                   )
              _suiteOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.funName"
                   {-# LINE 5789 "src/Analysis/Python.hs" #-}
                   )
              _suiteOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.funParams"
                   {-# LINE 5794 "src/Analysis/Python.hs" #-}
                   )
              _suiteOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandler.IHandler.suite.retLabels"
                   {-# LINE 5799 "src/Analysis/Python.hs" #-}
                   )
              ( _clauseIself) =
                  clause_ 
              ( _suiteIcallLabels,_suiteIcontrolFlow,_suiteIcounter,_suiteIfunLabels,_suiteIfunName,_suiteIfunParams,_suiteIinterFlow,_suiteIlabels,_suiteIretLabels,_suiteIself,_suiteIstartLabel,_suiteItransFunctions,_suiteIupGLabel,_suiteIupLabel) =
                  suite_ _suiteOcallLabels _suiteOcounter _suiteOdownGLabel _suiteOdownLabel _suiteOfunLabels _suiteOfunName _suiteOfunParams _suiteOretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IHandlers ---------------------------------------------------
-- cata
sem_IHandlers :: IHandlers  ->
                 T_IHandlers 
sem_IHandlers list  =
    (Prelude.foldr sem_IHandlers_Cons sem_IHandlers_Nil (Prelude.map sem_IHandler list) )
-- semantic domain
type T_IHandlers  = Label ->
                    ( Label,([Label]),IHandlers ,( Maybe Label ))
data Inh_IHandlers  = Inh_IHandlers {counter_Inh_IHandlers :: Label}
data Syn_IHandlers  = Syn_IHandlers {counter_Syn_IHandlers :: Label,labels_Syn_IHandlers :: ([Label]),self_Syn_IHandlers :: IHandlers ,startLabel_Syn_IHandlers :: ( Maybe Label )}
wrap_IHandlers :: T_IHandlers  ->
                  Inh_IHandlers  ->
                  Syn_IHandlers 
wrap_IHandlers sem (Inh_IHandlers _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IHandlers _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IHandlers_Cons :: T_IHandler  ->
                      T_IHandlers  ->
                      T_IHandlers 
sem_IHandlers_Cons hd_ tl_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IHandlers 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _hdOcounter :: Label
              _tlOcounter :: Label
              _hdIcounter :: Label
              _hdIlabels :: ([Label])
              _hdIself :: IHandler 
              _hdIstartLabel :: ( Maybe Label )
              _tlIcounter :: Label
              _tlIlabels :: ([Label])
              _tlIself :: IHandlers 
              _tlIstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 5845 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 5854 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _tlIstartLabel
                   {-# LINE 5859 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 5864 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 5869 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcounter,_hdIlabels,_hdIself,_hdIstartLabel) =
                  hd_ _hdOcounter 
              ( _tlIcounter,_tlIlabels,_tlIself,_tlIstartLabel) =
                  tl_ _tlOcounter 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IHandlers_Nil :: T_IHandlers 
sem_IHandlers_Nil  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IHandlers 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 5886 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 5895 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IHandlers.Nil.lhs.startLabel"
                   {-# LINE 5900 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IIdent ------------------------------------------------------
-- cata
sem_IIdent :: IIdent  ->
              T_IIdent 
sem_IIdent ( x1)  =
    (sem_IIdent_Tuple x1 )
-- semantic domain
type T_IIdent  = ( IIdent )
data Inh_IIdent  = Inh_IIdent {}
data Syn_IIdent  = Syn_IIdent {self_Syn_IIdent :: IIdent }
wrap_IIdent :: T_IIdent  ->
               Inh_IIdent  ->
               Syn_IIdent 
wrap_IIdent sem (Inh_IIdent )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IIdent _lhsOself ))
sem_IIdent_Tuple :: String ->
                    T_IIdent 
sem_IIdent_Tuple x1_  =
    (let _lhsOself :: IIdent 
         _self =
             (x1_)
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IIdents -----------------------------------------------------
-- cata
sem_IIdents :: IIdents  ->
               T_IIdents 
sem_IIdents list  =
    (Prelude.foldr sem_IIdents_Cons sem_IIdents_Nil list )
-- semantic domain
type T_IIdents  = ( IIdents )
data Inh_IIdents  = Inh_IIdents {}
data Syn_IIdents  = Syn_IIdents {self_Syn_IIdents :: IIdents }
wrap_IIdents :: T_IIdents  ->
                Inh_IIdents  ->
                Syn_IIdents 
wrap_IIdents sem (Inh_IIdents )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IIdents _lhsOself ))
sem_IIdents_Cons :: String ->
                    T_IIdents  ->
                    T_IIdents 
sem_IIdents_Cons hd_ tl_  =
    (let _lhsOself :: IIdents 
         _tlIself :: IIdents 
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_ 
     in  ( _lhsOself))
sem_IIdents_Nil :: T_IIdents 
sem_IIdents_Nil  =
    (let _lhsOself :: IIdents 
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IImportItem -------------------------------------------------
-- cata
sem_IImportItem :: IImportItem  ->
                   T_IImportItem 
sem_IImportItem (IImportItem _name _asname )  =
    (sem_IImportItem_IImportItem (sem_IDottedName _name ) _asname )
-- semantic domain
type T_IImportItem  = ( IImportItem )
data Inh_IImportItem  = Inh_IImportItem {}
data Syn_IImportItem  = Syn_IImportItem {self_Syn_IImportItem :: IImportItem }
wrap_IImportItem :: T_IImportItem  ->
                    Inh_IImportItem  ->
                    Syn_IImportItem 
wrap_IImportItem sem (Inh_IImportItem )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IImportItem _lhsOself ))
sem_IImportItem_IImportItem :: T_IDottedName  ->
                               (Maybe String) ->
                               T_IImportItem 
sem_IImportItem_IImportItem name_ asname_  =
    (let _lhsOself :: IImportItem 
         _nameIself :: IDottedName 
         _self =
             IImportItem _nameIself asname_
         _lhsOself =
             _self
         ( _nameIself) =
             name_ 
     in  ( _lhsOself))
-- IImportItems ------------------------------------------------
-- cata
sem_IImportItems :: IImportItems  ->
                    T_IImportItems 
sem_IImportItems list  =
    (Prelude.foldr sem_IImportItems_Cons sem_IImportItems_Nil (Prelude.map sem_IImportItem list) )
-- semantic domain
type T_IImportItems  = ( IImportItems )
data Inh_IImportItems  = Inh_IImportItems {}
data Syn_IImportItems  = Syn_IImportItems {self_Syn_IImportItems :: IImportItems }
wrap_IImportItems :: T_IImportItems  ->
                     Inh_IImportItems  ->
                     Syn_IImportItems 
wrap_IImportItems sem (Inh_IImportItems )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IImportItems _lhsOself ))
sem_IImportItems_Cons :: T_IImportItem  ->
                         T_IImportItems  ->
                         T_IImportItems 
sem_IImportItems_Cons hd_ tl_  =
    (let _lhsOself :: IImportItems 
         _hdIself :: IImportItem 
         _tlIself :: IImportItems 
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_ 
         ( _tlIself) =
             tl_ 
     in  ( _lhsOself))
sem_IImportItems_Nil :: T_IImportItems 
sem_IImportItems_Nil  =
    (let _lhsOself :: IImportItems 
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IImportRelative ---------------------------------------------
-- cata
sem_IImportRelative :: IImportRelative  ->
                       T_IImportRelative 
sem_IImportRelative (IImportRelative _dots _modul )  =
    (sem_IImportRelative_IImportRelative _dots _modul )
-- semantic domain
type T_IImportRelative  = ( IImportRelative )
data Inh_IImportRelative  = Inh_IImportRelative {}
data Syn_IImportRelative  = Syn_IImportRelative {self_Syn_IImportRelative :: IImportRelative }
wrap_IImportRelative :: T_IImportRelative  ->
                        Inh_IImportRelative  ->
                        Syn_IImportRelative 
wrap_IImportRelative sem (Inh_IImportRelative )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IImportRelative _lhsOself ))
sem_IImportRelative_IImportRelative :: Int ->
                                       (Maybe IDottedName) ->
                                       T_IImportRelative 
sem_IImportRelative_IImportRelative dots_ modul_  =
    (let _lhsOself :: IImportRelative 
         _self =
             IImportRelative dots_ modul_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ILFromItem --------------------------------------------------
-- cata
sem_ILFromItem :: ILFromItem  ->
                  T_ILFromItem 
sem_ILFromItem list  =
    (Prelude.foldr sem_ILFromItem_Cons sem_ILFromItem_Nil (Prelude.map sem_IFromItem list) )
-- semantic domain
type T_ILFromItem  = ( ILFromItem )
data Inh_ILFromItem  = Inh_ILFromItem {}
data Syn_ILFromItem  = Syn_ILFromItem {self_Syn_ILFromItem :: ILFromItem }
wrap_ILFromItem :: T_ILFromItem  ->
                   Inh_ILFromItem  ->
                   Syn_ILFromItem 
wrap_ILFromItem sem (Inh_ILFromItem )  =
    (let ( _lhsOself) = sem 
     in  (Syn_ILFromItem _lhsOself ))
sem_ILFromItem_Cons :: T_IFromItem  ->
                       T_ILFromItem  ->
                       T_ILFromItem 
sem_ILFromItem_Cons hd_ tl_  =
    (let _lhsOself :: ILFromItem 
         _hdIself :: IFromItem 
         _tlIself :: ILFromItem 
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_ 
         ( _tlIself) =
             tl_ 
     in  ( _lhsOself))
sem_ILFromItem_Nil :: T_ILFromItem 
sem_ILFromItem_Nil  =
    (let _lhsOself :: ILFromItem 
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IModule -----------------------------------------------------
-- cata
sem_IModule :: IModule  ->
               T_IModule 
sem_IModule (IModule _stats )  =
    (sem_IModule_IModule (sem_ISuite _stats ) )
-- semantic domain
type T_IModule  = (Map String [(Label, Label)]) ->
                  ([Label]) ->
                  ([Label]) ->
                  (Map String Label) ->
                  String ->
                  (Map String [Var]) ->
                  (Map String [Label]) ->
                  ( (Map String [(Label, Label)]),ControlFlow,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IModule ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IModule  = Inh_IModule {callLabels_Inh_IModule :: (Map String [(Label, Label)]),downGLabel_Inh_IModule :: ([Label]),downLabel_Inh_IModule :: ([Label]),funLabels_Inh_IModule :: (Map String Label),funName_Inh_IModule :: String,funParams_Inh_IModule :: (Map String [Var]),retLabels_Inh_IModule :: (Map String [Label])}
data Syn_IModule  = Syn_IModule {callLabels_Syn_IModule :: (Map String [(Label, Label)]),controlFlow_Syn_IModule :: ControlFlow,funLabels_Syn_IModule :: (Map String Label),funName_Syn_IModule :: String,funParams_Syn_IModule :: (Map String [Var]),interFlow_Syn_IModule :: InterFlow,labels_Syn_IModule :: ([Label]),retLabels_Syn_IModule :: (Map String [Label]),self_Syn_IModule :: IModule ,startLabel_Syn_IModule :: ( Maybe Label ),transFunctions_Syn_IModule :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IModule :: ([Label]),upLabel_Syn_IModule :: ([Label])}
wrap_IModule :: T_IModule  ->
                Inh_IModule  ->
                Syn_IModule 
wrap_IModule sem (Inh_IModule _lhsIcallLabels _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IModule _lhsOcallLabels _lhsOcontrolFlow _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IModule_IModule :: T_ISuite  ->
                       T_IModule 
sem_IModule_IModule stats_  =
    (\ _lhsIcallLabels
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _statsOcounter :: Label
              _statsOdownLabel :: ([Label])
              _statsOfunName :: String
              _statsOretLabels :: (Map String [Label])
              _statsOfunLabels :: (Map String Label)
              _statsOfunParams :: (Map String [Var])
              _statsOcallLabels :: (Map String [(Label, Label)])
              _statsOdownGLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IModule 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _statsIcallLabels :: (Map String [(Label, Label)])
              _statsIcontrolFlow :: ControlFlow
              _statsIcounter :: Label
              _statsIfunLabels :: (Map String Label)
              _statsIfunName :: String
              _statsIfunParams :: (Map String [Var])
              _statsIinterFlow :: InterFlow
              _statsIlabels :: ([Label])
              _statsIretLabels :: (Map String [Label])
              _statsIself :: ISuite 
              _statsIstartLabel :: ( Maybe Label )
              _statsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _statsIupGLabel :: ([Label])
              _statsIupLabel :: ([Label])
              _statsOcounter =
                  ({-# LINE 47 "src/Analysis/Python.ag" #-}
                   defaultStartLabel+1
                   {-# LINE 6171 "src/Analysis/Python.hs" #-}
                   )
              _statsOdownLabel =
                  ({-# LINE 110 "src/Analysis/Python.ag" #-}
                   [defaultStartLabel]
                   {-# LINE 6176 "src/Analysis/Python.hs" #-}
                   )
              _statsOfunName =
                  ({-# LINE 111 "src/Analysis/Python.ag" #-}
                   "Global"
                   {-# LINE 6181 "src/Analysis/Python.hs" #-}
                   )
              _statsOretLabels =
                  ({-# LINE 112 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 6186 "src/Analysis/Python.hs" #-}
                   )
              _statsOfunLabels =
                  ({-# LINE 113 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 6191 "src/Analysis/Python.hs" #-}
                   )
              _statsOfunParams =
                  ({-# LINE 114 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 6196 "src/Analysis/Python.hs" #-}
                   )
              _statsOcallLabels =
                  ({-# LINE 115 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 6201 "src/Analysis/Python.hs" #-}
                   )
              _statsOdownGLabel =
                  ({-# LINE 116 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 6206 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _statsIcontrolFlow
                   {-# LINE 6211 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _statsIinterFlow
                   {-# LINE 6216 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _statsIlabels
                   {-# LINE 6221 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _statsItransFunctions
                   {-# LINE 6226 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IModule _statsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _statsIcallLabels
                   {-# LINE 6235 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _statsIfunLabels
                   {-# LINE 6240 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _statsIfunName
                   {-# LINE 6245 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _statsIfunParams
                   {-# LINE 6250 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _statsIretLabels
                   {-# LINE 6255 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _statsIstartLabel
                   {-# LINE 6260 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _statsIupGLabel
                   {-# LINE 6265 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _statsIupLabel
                   {-# LINE 6270 "src/Analysis/Python.hs" #-}
                   )
              ( _statsIcallLabels,_statsIcontrolFlow,_statsIcounter,_statsIfunLabels,_statsIfunName,_statsIfunParams,_statsIinterFlow,_statsIlabels,_statsIretLabels,_statsIself,_statsIstartLabel,_statsItransFunctions,_statsIupGLabel,_statsIupLabel) =
                  stats_ _statsOcallLabels _statsOcounter _statsOdownGLabel _statsOdownLabel _statsOfunLabels _statsOfunName _statsOfunParams _statsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- IOp ---------------------------------------------------------
-- cata
sem_IOp :: IOp  ->
           T_IOp 
sem_IOp (IAnd )  =
    (sem_IOp_IAnd )
sem_IOp (IBinaryAnd )  =
    (sem_IOp_IBinaryAnd )
sem_IOp (IBinaryOr )  =
    (sem_IOp_IBinaryOr )
sem_IOp (IDivide )  =
    (sem_IOp_IDivide )
sem_IOp (IDot )  =
    (sem_IOp_IDot )
sem_IOp (IEquality )  =
    (sem_IOp_IEquality )
sem_IOp (IExponent )  =
    (sem_IOp_IExponent )
sem_IOp (IFloorDivide )  =
    (sem_IOp_IFloorDivide )
sem_IOp (IGreaterThan )  =
    (sem_IOp_IGreaterThan )
sem_IOp (IGreaterThanEquals )  =
    (sem_IOp_IGreaterThanEquals )
sem_IOp (IIn )  =
    (sem_IOp_IIn )
sem_IOp (IInvert )  =
    (sem_IOp_IInvert )
sem_IOp (IIs )  =
    (sem_IOp_IIs )
sem_IOp (IIsNot )  =
    (sem_IOp_IIsNot )
sem_IOp (ILessThan )  =
    (sem_IOp_ILessThan )
sem_IOp (ILessThanEquals )  =
    (sem_IOp_ILessThanEquals )
sem_IOp (IMinus )  =
    (sem_IOp_IMinus )
sem_IOp (IModulo )  =
    (sem_IOp_IModulo )
sem_IOp (IMultiply )  =
    (sem_IOp_IMultiply )
sem_IOp (INot )  =
    (sem_IOp_INot )
sem_IOp (INotEquals )  =
    (sem_IOp_INotEquals )
sem_IOp (INotEqualsV2 )  =
    (sem_IOp_INotEqualsV2 )
sem_IOp (INotIn )  =
    (sem_IOp_INotIn )
sem_IOp (IOr )  =
    (sem_IOp_IOr )
sem_IOp (IPlus )  =
    (sem_IOp_IPlus )
sem_IOp (IShiftLeft )  =
    (sem_IOp_IShiftLeft )
sem_IOp (IShiftRight )  =
    (sem_IOp_IShiftRight )
sem_IOp (IXor )  =
    (sem_IOp_IXor )
-- semantic domain
type T_IOp  = ( IOp )
data Inh_IOp  = Inh_IOp {}
data Syn_IOp  = Syn_IOp {self_Syn_IOp :: IOp }
wrap_IOp :: T_IOp  ->
            Inh_IOp  ->
            Syn_IOp 
wrap_IOp sem (Inh_IOp )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IOp _lhsOself ))
sem_IOp_IAnd :: T_IOp 
sem_IOp_IAnd  =
    (let _lhsOself :: IOp 
         _self =
             IAnd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IBinaryAnd :: T_IOp 
sem_IOp_IBinaryAnd  =
    (let _lhsOself :: IOp 
         _self =
             IBinaryAnd
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IBinaryOr :: T_IOp 
sem_IOp_IBinaryOr  =
    (let _lhsOself :: IOp 
         _self =
             IBinaryOr
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IDivide :: T_IOp 
sem_IOp_IDivide  =
    (let _lhsOself :: IOp 
         _self =
             IDivide
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IDot :: T_IOp 
sem_IOp_IDot  =
    (let _lhsOself :: IOp 
         _self =
             IDot
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IEquality :: T_IOp 
sem_IOp_IEquality  =
    (let _lhsOself :: IOp 
         _self =
             IEquality
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IExponent :: T_IOp 
sem_IOp_IExponent  =
    (let _lhsOself :: IOp 
         _self =
             IExponent
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IFloorDivide :: T_IOp 
sem_IOp_IFloorDivide  =
    (let _lhsOself :: IOp 
         _self =
             IFloorDivide
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IGreaterThan :: T_IOp 
sem_IOp_IGreaterThan  =
    (let _lhsOself :: IOp 
         _self =
             IGreaterThan
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IGreaterThanEquals :: T_IOp 
sem_IOp_IGreaterThanEquals  =
    (let _lhsOself :: IOp 
         _self =
             IGreaterThanEquals
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IIn :: T_IOp 
sem_IOp_IIn  =
    (let _lhsOself :: IOp 
         _self =
             IIn
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IInvert :: T_IOp 
sem_IOp_IInvert  =
    (let _lhsOself :: IOp 
         _self =
             IInvert
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IIs :: T_IOp 
sem_IOp_IIs  =
    (let _lhsOself :: IOp 
         _self =
             IIs
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IIsNot :: T_IOp 
sem_IOp_IIsNot  =
    (let _lhsOself :: IOp 
         _self =
             IIsNot
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_ILessThan :: T_IOp 
sem_IOp_ILessThan  =
    (let _lhsOself :: IOp 
         _self =
             ILessThan
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_ILessThanEquals :: T_IOp 
sem_IOp_ILessThanEquals  =
    (let _lhsOself :: IOp 
         _self =
             ILessThanEquals
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IMinus :: T_IOp 
sem_IOp_IMinus  =
    (let _lhsOself :: IOp 
         _self =
             IMinus
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IModulo :: T_IOp 
sem_IOp_IModulo  =
    (let _lhsOself :: IOp 
         _self =
             IModulo
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IMultiply :: T_IOp 
sem_IOp_IMultiply  =
    (let _lhsOself :: IOp 
         _self =
             IMultiply
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_INot :: T_IOp 
sem_IOp_INot  =
    (let _lhsOself :: IOp 
         _self =
             INot
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_INotEquals :: T_IOp 
sem_IOp_INotEquals  =
    (let _lhsOself :: IOp 
         _self =
             INotEquals
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_INotEqualsV2 :: T_IOp 
sem_IOp_INotEqualsV2  =
    (let _lhsOself :: IOp 
         _self =
             INotEqualsV2
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_INotIn :: T_IOp 
sem_IOp_INotIn  =
    (let _lhsOself :: IOp 
         _self =
             INotIn
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IOr :: T_IOp 
sem_IOp_IOr  =
    (let _lhsOself :: IOp 
         _self =
             IOr
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IPlus :: T_IOp 
sem_IOp_IPlus  =
    (let _lhsOself :: IOp 
         _self =
             IPlus
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IShiftLeft :: T_IOp 
sem_IOp_IShiftLeft  =
    (let _lhsOself :: IOp 
         _self =
             IShiftLeft
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IShiftRight :: T_IOp 
sem_IOp_IShiftRight  =
    (let _lhsOself :: IOp 
         _self =
             IShiftRight
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IOp_IXor :: T_IOp 
sem_IOp_IXor  =
    (let _lhsOself :: IOp 
         _self =
             IXor
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IParameter --------------------------------------------------
-- cata
sem_IParameter :: IParameter  ->
                  T_IParameter 
sem_IParameter (IParam _name _py_annot _default )  =
    (sem_IParameter_IParam _name (sem_MybExpr _py_annot ) (sem_MybExpr _default ) )
sem_IParameter (IParamNotSupported )  =
    (sem_IParameter_IParamNotSupported )
sem_IParameter (IVarArgsPos _name _py_annot )  =
    (sem_IParameter_IVarArgsPos _name (sem_MybExpr _py_annot ) )
-- semantic domain
type T_IParameter  = Label ->
                     ( Label,([Label]),IParameter ,( Maybe Label ))
data Inh_IParameter  = Inh_IParameter {counter_Inh_IParameter :: Label}
data Syn_IParameter  = Syn_IParameter {counter_Syn_IParameter :: Label,labels_Syn_IParameter :: ([Label]),self_Syn_IParameter :: IParameter ,startLabel_Syn_IParameter :: ( Maybe Label )}
wrap_IParameter :: T_IParameter  ->
                   Inh_IParameter  ->
                   Syn_IParameter 
wrap_IParameter sem (Inh_IParameter _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IParameter _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IParameter_IParam :: String ->
                         T_MybExpr  ->
                         T_MybExpr  ->
                         T_IParameter 
sem_IParameter_IParam name_ py_annot_ default_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IParameter 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _py_annotOcallLabels :: (Map String [(Label, Label)])
              _py_annotOcounter :: Label
              _py_annotOdownGLabel :: ([Label])
              _py_annotOdownLabel :: ([Label])
              _py_annotOfunLabels :: (Map String Label)
              _py_annotOfunName :: String
              _py_annotOfunParams :: (Map String [Var])
              _py_annotOretLabels :: (Map String [Label])
              _defaultOcallLabels :: (Map String [(Label, Label)])
              _defaultOcounter :: Label
              _defaultOdownGLabel :: ([Label])
              _defaultOdownLabel :: ([Label])
              _defaultOfunLabels :: (Map String Label)
              _defaultOfunName :: String
              _defaultOfunParams :: (Map String [Var])
              _defaultOretLabels :: (Map String [Label])
              _py_annotIcallLabels :: (Map String [(Label, Label)])
              _py_annotIcontrolFlow :: ControlFlow
              _py_annotIcounter :: Label
              _py_annotIfunLabels :: (Map String Label)
              _py_annotIfunName :: String
              _py_annotIfunParams :: (Map String [Var])
              _py_annotIinterFlow :: InterFlow
              _py_annotIlabels :: ([Label])
              _py_annotIretLabels :: (Map String [Label])
              _py_annotIself :: MybExpr 
              _py_annotIstartLabel :: ( Maybe Label )
              _py_annotItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _py_annotIupGLabel :: ([Label])
              _py_annotIupLabel :: ([Label])
              _defaultIcallLabels :: (Map String [(Label, Label)])
              _defaultIcontrolFlow :: ControlFlow
              _defaultIcounter :: Label
              _defaultIfunLabels :: (Map String Label)
              _defaultIfunName :: String
              _defaultIfunParams :: (Map String [Var])
              _defaultIinterFlow :: InterFlow
              _defaultIlabels :: ([Label])
              _defaultIretLabels :: (Map String [Label])
              _defaultIself :: MybExpr 
              _defaultIstartLabel :: ( Maybe Label )
              _defaultItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _defaultIupGLabel :: ([Label])
              _defaultIupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _py_annotIlabels ++ _defaultIlabels
                   {-# LINE 6647 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IParam name_ _py_annotIself _defaultIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _defaultIcounter
                   {-# LINE 6656 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _defaultIstartLabel
                   {-# LINE 6661 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.callLabels"
                   {-# LINE 6666 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 6671 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.downGLabel"
                   {-# LINE 6676 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.downLabel"
                   {-# LINE 6681 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.funLabels"
                   {-# LINE 6686 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.funName"
                   {-# LINE 6691 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.funParams"
                   {-# LINE 6696 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.py_annot.retLabels"
                   {-# LINE 6701 "src/Analysis/Python.hs" #-}
                   )
              _defaultOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _py_annotIcallLabels
                   {-# LINE 6706 "src/Analysis/Python.hs" #-}
                   )
              _defaultOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _py_annotIcounter
                   {-# LINE 6711 "src/Analysis/Python.hs" #-}
                   )
              _defaultOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.default.downGLabel"
                   {-# LINE 6716 "src/Analysis/Python.hs" #-}
                   )
              _defaultOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParam.default.downLabel"
                   {-# LINE 6721 "src/Analysis/Python.hs" #-}
                   )
              _defaultOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _py_annotIfunLabels
                   {-# LINE 6726 "src/Analysis/Python.hs" #-}
                   )
              _defaultOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _py_annotIfunName
                   {-# LINE 6731 "src/Analysis/Python.hs" #-}
                   )
              _defaultOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _py_annotIfunParams
                   {-# LINE 6736 "src/Analysis/Python.hs" #-}
                   )
              _defaultOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _py_annotIretLabels
                   {-# LINE 6741 "src/Analysis/Python.hs" #-}
                   )
              ( _py_annotIcallLabels,_py_annotIcontrolFlow,_py_annotIcounter,_py_annotIfunLabels,_py_annotIfunName,_py_annotIfunParams,_py_annotIinterFlow,_py_annotIlabels,_py_annotIretLabels,_py_annotIself,_py_annotIstartLabel,_py_annotItransFunctions,_py_annotIupGLabel,_py_annotIupLabel) =
                  py_annot_ _py_annotOcallLabels _py_annotOcounter _py_annotOdownGLabel _py_annotOdownLabel _py_annotOfunLabels _py_annotOfunName _py_annotOfunParams _py_annotOretLabels 
              ( _defaultIcallLabels,_defaultIcontrolFlow,_defaultIcounter,_defaultIfunLabels,_defaultIfunName,_defaultIfunParams,_defaultIinterFlow,_defaultIlabels,_defaultIretLabels,_defaultIself,_defaultIstartLabel,_defaultItransFunctions,_defaultIupGLabel,_defaultIupLabel) =
                  default_ _defaultOcallLabels _defaultOcounter _defaultOdownGLabel _defaultOdownLabel _defaultOfunLabels _defaultOfunName _defaultOfunParams _defaultOretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IParameter_IParamNotSupported :: T_IParameter 
sem_IParameter_IParamNotSupported  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IParameter 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 6758 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IParamNotSupported
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 6767 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IParamNotSupported.lhs.startLabel"
                   {-# LINE 6772 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IParameter_IVarArgsPos :: String ->
                              T_MybExpr  ->
                              T_IParameter 
sem_IParameter_IVarArgsPos name_ py_annot_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IParameter 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _py_annotOcallLabels :: (Map String [(Label, Label)])
              _py_annotOcounter :: Label
              _py_annotOdownGLabel :: ([Label])
              _py_annotOdownLabel :: ([Label])
              _py_annotOfunLabels :: (Map String Label)
              _py_annotOfunName :: String
              _py_annotOfunParams :: (Map String [Var])
              _py_annotOretLabels :: (Map String [Label])
              _py_annotIcallLabels :: (Map String [(Label, Label)])
              _py_annotIcontrolFlow :: ControlFlow
              _py_annotIcounter :: Label
              _py_annotIfunLabels :: (Map String Label)
              _py_annotIfunName :: String
              _py_annotIfunParams :: (Map String [Var])
              _py_annotIinterFlow :: InterFlow
              _py_annotIlabels :: ([Label])
              _py_annotIretLabels :: (Map String [Label])
              _py_annotIself :: MybExpr 
              _py_annotIstartLabel :: ( Maybe Label )
              _py_annotItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _py_annotIupGLabel :: ([Label])
              _py_annotIupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _py_annotIlabels
                   {-# LINE 6809 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IVarArgsPos name_ _py_annotIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _py_annotIcounter
                   {-# LINE 6818 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _py_annotIstartLabel
                   {-# LINE 6823 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.callLabels"
                   {-# LINE 6828 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 6833 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.downGLabel"
                   {-# LINE 6838 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.downLabel"
                   {-# LINE 6843 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.funLabels"
                   {-# LINE 6848 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.funName"
                   {-# LINE 6853 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.funParams"
                   {-# LINE 6858 "src/Analysis/Python.hs" #-}
                   )
              _py_annotOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParameter.IVarArgsPos.py_annot.retLabels"
                   {-# LINE 6863 "src/Analysis/Python.hs" #-}
                   )
              ( _py_annotIcallLabels,_py_annotIcontrolFlow,_py_annotIcounter,_py_annotIfunLabels,_py_annotIfunName,_py_annotIfunParams,_py_annotIinterFlow,_py_annotIlabels,_py_annotIretLabels,_py_annotIself,_py_annotIstartLabel,_py_annotItransFunctions,_py_annotIupGLabel,_py_annotIupLabel) =
                  py_annot_ _py_annotOcallLabels _py_annotOcounter _py_annotOdownGLabel _py_annotOdownLabel _py_annotOfunLabels _py_annotOfunName _py_annotOfunParams _py_annotOretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IParams -----------------------------------------------------
-- cata
sem_IParams :: IParams  ->
               T_IParams 
sem_IParams list  =
    (Prelude.foldr sem_IParams_Cons sem_IParams_Nil (Prelude.map sem_IParameter list) )
-- semantic domain
type T_IParams  = Label ->
                  ( Label,([Label]),IParams ,( Maybe Label ))
data Inh_IParams  = Inh_IParams {counter_Inh_IParams :: Label}
data Syn_IParams  = Syn_IParams {counter_Syn_IParams :: Label,labels_Syn_IParams :: ([Label]),self_Syn_IParams :: IParams ,startLabel_Syn_IParams :: ( Maybe Label )}
wrap_IParams :: T_IParams  ->
                Inh_IParams  ->
                Syn_IParams 
wrap_IParams sem (Inh_IParams _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_IParams _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_IParams_Cons :: T_IParameter  ->
                    T_IParams  ->
                    T_IParams 
sem_IParams_Cons hd_ tl_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IParams 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _hdOcounter :: Label
              _tlOcounter :: Label
              _hdIcounter :: Label
              _hdIlabels :: ([Label])
              _hdIself :: IParameter 
              _hdIstartLabel :: ( Maybe Label )
              _tlIcounter :: Label
              _tlIlabels :: ([Label])
              _tlIself :: IParams 
              _tlIstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 6907 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 6916 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _tlIstartLabel
                   {-# LINE 6921 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 6926 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 6931 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcounter,_hdIlabels,_hdIself,_hdIstartLabel) =
                  hd_ _hdOcounter 
              ( _tlIcounter,_tlIlabels,_tlIself,_tlIstartLabel) =
                  tl_ _tlOcounter 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
sem_IParams_Nil :: T_IParams 
sem_IParams_Nil  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IParams 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 6948 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 6957 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IParams.Nil.lhs.startLabel"
                   {-# LINE 6962 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- IRaiseExpr --------------------------------------------------
-- cata
sem_IRaiseExpr :: IRaiseExpr  ->
                  T_IRaiseExpr 
sem_IRaiseExpr (IRaiseV2 _raisev2 )  =
    (sem_IRaiseExpr_IRaiseV2 _raisev2 )
sem_IRaiseExpr (IRaiseV3 _raisev3 )  =
    (sem_IRaiseExpr_IRaiseV3 _raisev3 )
-- semantic domain
type T_IRaiseExpr  = ( IRaiseExpr )
data Inh_IRaiseExpr  = Inh_IRaiseExpr {}
data Syn_IRaiseExpr  = Syn_IRaiseExpr {self_Syn_IRaiseExpr :: IRaiseExpr }
wrap_IRaiseExpr :: T_IRaiseExpr  ->
                   Inh_IRaiseExpr  ->
                   Syn_IRaiseExpr 
wrap_IRaiseExpr sem (Inh_IRaiseExpr )  =
    (let ( _lhsOself) = sem 
     in  (Syn_IRaiseExpr _lhsOself ))
sem_IRaiseExpr_IRaiseV2 :: (Maybe IExceptClauseType2) ->
                           T_IRaiseExpr 
sem_IRaiseExpr_IRaiseV2 raisev2_  =
    (let _lhsOself :: IRaiseExpr 
         _self =
             IRaiseV2 raisev2_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_IRaiseExpr_IRaiseV3 :: (Maybe IExceptClauseType) ->
                           T_IRaiseExpr 
sem_IRaiseExpr_IRaiseV3 raisev3_  =
    (let _lhsOself :: IRaiseExpr 
         _self =
             IRaiseV3 raisev3_
         _lhsOself =
             _self
     in  ( _lhsOself))
-- IStatement --------------------------------------------------
-- cata
sem_IStatement :: IStatement  ->
                  T_IStatement 
sem_IStatement (IAssert _exprs )  =
    (sem_IStatement_IAssert (sem_IExprs _exprs ) )
sem_IStatement (IAssign _to _expr _label )  =
    (sem_IStatement_IAssign (sem_IExprs _to ) (sem_IExpr _expr ) (sem_Label _label ) )
sem_IStatement (IAugmentedAssign _to _op _expr _label )  =
    (sem_IStatement_IAugmentedAssign (sem_IExpr _to ) (sem_IAssignOp _op ) (sem_IExpr _expr ) (sem_Label _label ) )
sem_IStatement (IBreak _label )  =
    (sem_IStatement_IBreak (sem_Label _label ) )
sem_IStatement (IClass _name _args _body )  =
    (sem_IStatement_IClass _name (sem_IArgs _args ) (sem_ISuite _body ) )
sem_IStatement (IConditional _guards _else )  =
    (sem_IStatement_IConditional (sem_IGuards _guards ) (sem_ISuite _else ) )
sem_IStatement (IContinue _label )  =
    (sem_IStatement_IContinue (sem_Label _label ) )
sem_IStatement (IDecorated _decorators _stat )  =
    (sem_IStatement_IDecorated (sem_IDecorators _decorators ) (sem_IStatement _stat ) )
sem_IStatement (IDelete _exprs )  =
    (sem_IStatement_IDelete (sem_IExprs _exprs ) )
sem_IStatement (IExec _expr _globlocs )  =
    (sem_IStatement_IExec (sem_IExpr _expr ) _globlocs )
sem_IStatement (IFor _targets _generator _body _else )  =
    (sem_IStatement_IFor (sem_IExprs _targets ) (sem_IExpr _generator ) (sem_ISuite _body ) (sem_ISuite _else ) )
sem_IStatement (IFromImport _modul _items _label )  =
    (sem_IStatement_IFromImport (sem_IImportRelative _modul ) (sem_IFromItems _items ) (sem_Label _label ) )
sem_IStatement (IFun _name _args _result _body _entry )  =
    (sem_IStatement_IFun _name (sem_IParams _args ) (sem_MybExpr _result ) (sem_ISuite _body ) (sem_Label _entry ) )
sem_IStatement (IGlobal _vars _label )  =
    (sem_IStatement_IGlobal (sem_IIdents _vars ) (sem_Label _label ) )
sem_IStatement (IImport _items _label )  =
    (sem_IStatement_IImport (sem_IImportItems _items ) (sem_Label _label ) )
sem_IStatement (INonLocal _vars _label )  =
    (sem_IStatement_INonLocal (sem_IIdents _vars ) (sem_Label _label ) )
sem_IStatement (IPass _label )  =
    (sem_IStatement_IPass (sem_Label _label ) )
sem_IStatement (IPrint _chevron _exprs _trailcomma _label )  =
    (sem_IStatement_IPrint _chevron (sem_IExprs _exprs ) _trailcomma (sem_Label _label ) )
sem_IStatement (IRaise _expr )  =
    (sem_IStatement_IRaise (sem_IRaiseExpr _expr ) )
sem_IStatement (IReturn _expr _label )  =
    (sem_IStatement_IReturn (sem_MybExpr _expr ) (sem_Label _label ) )
sem_IStatement (IStmtExpr _expr )  =
    (sem_IStatement_IStmtExpr (sem_IExpr _expr ) )
sem_IStatement (ITry _body _excepts _else _finally )  =
    (sem_IStatement_ITry (sem_ISuite _body ) (sem_IHandlers _excepts ) (sem_ISuite _else ) (sem_ISuite _finally ) )
sem_IStatement (IWhile _cond _body _else _label )  =
    (sem_IStatement_IWhile (sem_IExpr _cond ) (sem_ISuite _body ) (sem_ISuite _else ) (sem_Label _label ) )
sem_IStatement (IWith _context _body )  =
    (sem_IStatement_IWith (sem_IContext _context ) (sem_ISuite _body ) )
-- semantic domain
type T_IStatement  = (Map String [(Label, Label)]) ->
                     Label ->
                     ([Label]) ->
                     ([Label]) ->
                     (Map String Label) ->
                     String ->
                     (Map String [Var]) ->
                     (Map String [Label]) ->
                     ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),IStatement ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_IStatement  = Inh_IStatement {callLabels_Inh_IStatement :: (Map String [(Label, Label)]),counter_Inh_IStatement :: Label,downGLabel_Inh_IStatement :: ([Label]),downLabel_Inh_IStatement :: ([Label]),funLabels_Inh_IStatement :: (Map String Label),funName_Inh_IStatement :: String,funParams_Inh_IStatement :: (Map String [Var]),retLabels_Inh_IStatement :: (Map String [Label])}
data Syn_IStatement  = Syn_IStatement {callLabels_Syn_IStatement :: (Map String [(Label, Label)]),controlFlow_Syn_IStatement :: ControlFlow,counter_Syn_IStatement :: Label,funLabels_Syn_IStatement :: (Map String Label),funName_Syn_IStatement :: String,funParams_Syn_IStatement :: (Map String [Var]),interFlow_Syn_IStatement :: InterFlow,labels_Syn_IStatement :: ([Label]),retLabels_Syn_IStatement :: (Map String [Label]),self_Syn_IStatement :: IStatement ,startLabel_Syn_IStatement :: ( Maybe Label ),transFunctions_Syn_IStatement :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_IStatement :: ([Label]),upLabel_Syn_IStatement :: ([Label])}
wrap_IStatement :: T_IStatement  ->
                   Inh_IStatement  ->
                   Syn_IStatement 
wrap_IStatement sem (Inh_IStatement _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_IStatement _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_IStatement_IAssert :: T_IExprs  ->
                          T_IStatement 
sem_IStatement_IAssert exprs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprsOcallLabels :: (Map String [(Label, Label)])
              _exprsOcounter :: Label
              _exprsOdownGLabel :: ([Label])
              _exprsOdownLabel :: ([Label])
              _exprsOfunLabels :: (Map String Label)
              _exprsOfunName :: String
              _exprsOfunParams :: (Map String [Var])
              _exprsOretLabels :: (Map String [Label])
              _exprsIcallLabels :: (Map String [(Label, Label)])
              _exprsIcontrolFlow :: ControlFlow
              _exprsIcounter :: Label
              _exprsIfunLabels :: (Map String Label)
              _exprsIfunName :: String
              _exprsIfunParams :: (Map String [Var])
              _exprsIinterFlow :: InterFlow
              _exprsIlabels :: ([Label])
              _exprsIretLabels :: (Map String [Label])
              _exprsIself :: IExprs 
              _exprsIstartLabel :: ( Maybe Label )
              _exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprsIupGLabel :: ([Label])
              _exprsIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _exprsIcontrolFlow
                   {-# LINE 7121 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprsIinterFlow
                   {-# LINE 7126 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _exprsIlabels
                   {-# LINE 7131 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _exprsItransFunctions
                   {-# LINE 7136 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IAssert _exprsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprsIcallLabels
                   {-# LINE 7145 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprsIcounter
                   {-# LINE 7150 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprsIfunLabels
                   {-# LINE 7155 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprsIfunName
                   {-# LINE 7160 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprsIfunParams
                   {-# LINE 7165 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprsIretLabels
                   {-# LINE 7170 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _exprsIstartLabel
                   {-# LINE 7175 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprsIupGLabel
                   {-# LINE 7180 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _exprsIupLabel
                   {-# LINE 7185 "src/Analysis/Python.hs" #-}
                   )
              _exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 7190 "src/Analysis/Python.hs" #-}
                   )
              _exprsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 7195 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 7200 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 7205 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 7210 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 7215 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 7220 "src/Analysis/Python.hs" #-}
                   )
              _exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 7225 "src/Analysis/Python.hs" #-}
                   )
              ( _exprsIcallLabels,_exprsIcontrolFlow,_exprsIcounter,_exprsIfunLabels,_exprsIfunName,_exprsIfunParams,_exprsIinterFlow,_exprsIlabels,_exprsIretLabels,_exprsIself,_exprsIstartLabel,_exprsItransFunctions,_exprsIupGLabel,_exprsIupLabel) =
                  exprs_ _exprsOcallLabels _exprsOcounter _exprsOdownGLabel _exprsOdownLabel _exprsOfunLabels _exprsOfunName _exprsOfunParams _exprsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IAssign :: T_IExprs  ->
                          T_IExpr  ->
                          T_Label  ->
                          T_IStatement 
sem_IStatement_IAssign to_ expr_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOcontrolFlow :: ControlFlow
              _lhsOstartLabel :: ( Maybe Label )
              _exprOdownLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup4 :: ((Label,Label))
              _toOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _toOcallLabels :: (Map String [(Label, Label)])
              _toOdownGLabel :: ([Label])
              _toOdownLabel :: ([Label])
              _toOfunLabels :: (Map String Label)
              _toOfunName :: String
              _toOfunParams :: (Map String [Var])
              _toOretLabels :: (Map String [Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOcounter :: Label
              _exprOdownGLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _toIcallLabels :: (Map String [(Label, Label)])
              _toIcontrolFlow :: ControlFlow
              _toIcounter :: Label
              _toIfunLabels :: (Map String Label)
              _toIfunName :: String
              _toIfunParams :: (Map String [Var])
              _toIinterFlow :: InterFlow
              _toIlabels :: ([Label])
              _toIretLabels :: (Map String [Label])
              _toIself :: IExprs 
              _toIstartLabel :: ( Maybe Label )
              _toItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _toIupGLabel :: ([Label])
              _toIupLabel :: ([Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 58 "src/Analysis/Python.ag" #-}
                   _label    :(_exprIlabels)
                   {-# LINE 7307 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 66 "src/Analysis/Python.ag" #-}
                   IAssign _toIself _exprIself _label
                   {-# LINE 7312 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 148 "src/Analysis/Python.ag" #-}
                   createFlow IntraFlow _exprIupLabel [_label    ] ++ _exprIcontrolFlow
                   {-# LINE 7317 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 149 "src/Analysis/Python.ag" #-}
                   case _exprIstartLabel of
                        Nothing -> Just _label
                        Just x  -> Just x
                   {-# LINE 7324 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 152 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 7329 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 7334 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 7339 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 258 "src/Analysis/Python.ag" #-}
                   let tf = Unary $ \(c, env) -> (c, Map.insert _varName     (typesOf env _exprIself) (removeRet _exprIself env))
                                               in  Map.insert _label     tf _exprItransFunctions
                   {-# LINE 7345 "src/Analysis/Python.hs" #-}
                   )
              _varName =
                  ({-# LINE 260 "src/Analysis/Python.ag" #-}
                   varOf _toIself
                   {-# LINE 7350 "src/Analysis/Python.hs" #-}
                   )
              __tup4 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_toOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup4
                   {-# LINE 7357 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup4
                   {-# LINE 7362 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _toIinterFlow ++ _exprIinterFlow
                   {-# LINE 7367 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IAssign _toIself _exprIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 7374 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 7379 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 7384 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 7389 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 7394 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 7399 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 7404 "src/Analysis/Python.hs" #-}
                   )
              _toOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 7409 "src/Analysis/Python.hs" #-}
                   )
              _toOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 7414 "src/Analysis/Python.hs" #-}
                   )
              _toOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 7419 "src/Analysis/Python.hs" #-}
                   )
              _toOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 7424 "src/Analysis/Python.hs" #-}
                   )
              _toOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 7429 "src/Analysis/Python.hs" #-}
                   )
              _toOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 7434 "src/Analysis/Python.hs" #-}
                   )
              _toOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 7439 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _toIcallLabels
                   {-# LINE 7444 "src/Analysis/Python.hs" #-}
                   )
              _exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _toIcounter
                   {-# LINE 7449 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 7454 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _toIfunLabels
                   {-# LINE 7459 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _toIfunName
                   {-# LINE 7464 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _toIfunParams
                   {-# LINE 7469 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _toIretLabels
                   {-# LINE 7474 "src/Analysis/Python.hs" #-}
                   )
              ( _toIcallLabels,_toIcontrolFlow,_toIcounter,_toIfunLabels,_toIfunName,_toIfunParams,_toIinterFlow,_toIlabels,_toIretLabels,_toIself,_toIstartLabel,_toItransFunctions,_toIupGLabel,_toIupLabel) =
                  to_ _toOcallLabels _toOcounter _toOdownGLabel _toOdownLabel _toOfunLabels _toOfunName _toOfunParams _toOretLabels 
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IAugmentedAssign :: T_IExpr  ->
                                   T_IAssignOp  ->
                                   T_IExpr  ->
                                   T_Label  ->
                                   T_IStatement 
sem_IStatement_IAugmentedAssign to_ op_ expr_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup5 :: ((Label,Label))
              _toOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _toOcallLabels :: (Map String [(Label, Label)])
              _toOdownGLabel :: ([Label])
              _toOdownLabel :: ([Label])
              _toOfunLabels :: (Map String Label)
              _toOfunName :: String
              _toOfunParams :: (Map String [Var])
              _toOretLabels :: (Map String [Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOcounter :: Label
              _exprOdownGLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _toIcallLabels :: (Map String [(Label, Label)])
              _toIcontrolFlow :: ControlFlow
              _toIcounter :: Label
              _toIfunLabels :: (Map String Label)
              _toIfunName :: String
              _toIfunParams :: (Map String [Var])
              _toIinterFlow :: InterFlow
              _toIlabels :: ([Label])
              _toIretLabels :: (Map String [Label])
              _toIself :: IExpr 
              _toIstartLabel :: ( Maybe Label )
              _toItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _toIupGLabel :: ([Label])
              _toIupLabel :: ([Label])
              _opIself :: IAssignOp 
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 7562 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 67 "src/Analysis/Python.ag" #-}
                   IAugmentedAssign _toIself _opIself _exprIself _label
                   {-# LINE 7567 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 7572 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 7577 "src/Analysis/Python.hs" #-}
                   )
              __tup5 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_toOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup5
                   {-# LINE 7584 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup5
                   {-# LINE 7589 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _toIcontrolFlow ++ _exprIcontrolFlow
                   {-# LINE 7594 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _toIinterFlow ++ _exprIinterFlow
                   {-# LINE 7599 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _toItransFunctions `Map.union` _exprItransFunctions
                   {-# LINE 7604 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IAugmentedAssign _toIself _opIself _exprIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 7611 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 7616 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 7621 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 7626 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 7631 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 7636 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 7641 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 7646 "src/Analysis/Python.hs" #-}
                   )
              _toOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 7651 "src/Analysis/Python.hs" #-}
                   )
              _toOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 7656 "src/Analysis/Python.hs" #-}
                   )
              _toOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 7661 "src/Analysis/Python.hs" #-}
                   )
              _toOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 7666 "src/Analysis/Python.hs" #-}
                   )
              _toOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 7671 "src/Analysis/Python.hs" #-}
                   )
              _toOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 7676 "src/Analysis/Python.hs" #-}
                   )
              _toOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 7681 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _toIcallLabels
                   {-# LINE 7686 "src/Analysis/Python.hs" #-}
                   )
              _exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _toIcounter
                   {-# LINE 7691 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 7696 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 7701 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _toIfunLabels
                   {-# LINE 7706 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _toIfunName
                   {-# LINE 7711 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _toIfunParams
                   {-# LINE 7716 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _toIretLabels
                   {-# LINE 7721 "src/Analysis/Python.hs" #-}
                   )
              ( _toIcallLabels,_toIcontrolFlow,_toIcounter,_toIfunLabels,_toIfunName,_toIfunParams,_toIinterFlow,_toIlabels,_toIretLabels,_toIself,_toIstartLabel,_toItransFunctions,_toIupGLabel,_toIupLabel) =
                  to_ _toOcallLabels _toOcounter _toOdownGLabel _toOdownLabel _toOfunLabels _toOfunName _toOfunParams _toOretLabels 
              ( _opIself) =
                  op_ 
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IBreak :: T_Label  ->
                         T_IStatement 
sem_IStatement_IBreak label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup6 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 7763 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 70 "src/Analysis/Python.ag" #-}
                   IBreak _label
                   {-# LINE 7768 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 7773 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 7778 "src/Analysis/Python.hs" #-}
                   )
              __tup6 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup6
                   {-# LINE 7785 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup6
                   {-# LINE 7790 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 7795 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 7800 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 7805 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IBreak _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 7812 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 7817 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 7822 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 7827 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 7832 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 7837 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IBreak.lhs.upGLabel"
                   {-# LINE 7842 "src/Analysis/Python.hs" #-}
                   )
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IClass :: String ->
                         T_IArgs  ->
                         T_ISuite  ->
                         T_IStatement 
sem_IStatement_IClass name_ args_ body_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _argsOcallLabels :: (Map String [(Label, Label)])
              _argsOcounter :: Label
              _argsOdownGLabel :: ([Label])
              _argsOdownLabel :: ([Label])
              _argsOfunLabels :: (Map String Label)
              _argsOfunName :: String
              _argsOfunParams :: (Map String [Var])
              _argsOretLabels :: (Map String [Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _argsIcallLabels :: (Map String [(Label, Label)])
              _argsIcontrolFlow :: ControlFlow
              _argsIcounter :: Label
              _argsIfunLabels :: (Map String Label)
              _argsIfunName :: String
              _argsIfunParams :: (Map String [Var])
              _argsIinterFlow :: InterFlow
              _argsIlabels :: ([Label])
              _argsIretLabels :: (Map String [Label])
              _argsIself :: IArgs 
              _argsIstartLabel :: ( Maybe Label )
              _argsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _argsIupGLabel :: ([Label])
              _argsIupLabel :: ([Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _argsIcontrolFlow ++ _bodyIcontrolFlow
                   {-# LINE 7921 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _argsIinterFlow ++ _bodyIinterFlow
                   {-# LINE 7926 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _argsIlabels ++ _bodyIlabels
                   {-# LINE 7931 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _argsItransFunctions `Map.union` _bodyItransFunctions
                   {-# LINE 7936 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IClass name_ _argsIself _bodyIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 7945 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 7950 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 7955 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 7960 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 7965 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 7970 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _bodyIstartLabel
                   {-# LINE 7975 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _bodyIupGLabel
                   {-# LINE 7980 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _bodyIupLabel
                   {-# LINE 7985 "src/Analysis/Python.hs" #-}
                   )
              _argsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 7990 "src/Analysis/Python.hs" #-}
                   )
              _argsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 7995 "src/Analysis/Python.hs" #-}
                   )
              _argsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8000 "src/Analysis/Python.hs" #-}
                   )
              _argsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8005 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8010 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8015 "src/Analysis/Python.hs" #-}
                   )
              _argsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8020 "src/Analysis/Python.hs" #-}
                   )
              _argsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8025 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _argsIcallLabels
                   {-# LINE 8030 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _argsIcounter
                   {-# LINE 8035 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8040 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8045 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _argsIfunLabels
                   {-# LINE 8050 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _argsIfunName
                   {-# LINE 8055 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _argsIfunParams
                   {-# LINE 8060 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _argsIretLabels
                   {-# LINE 8065 "src/Analysis/Python.hs" #-}
                   )
              ( _argsIcallLabels,_argsIcontrolFlow,_argsIcounter,_argsIfunLabels,_argsIfunName,_argsIfunParams,_argsIinterFlow,_argsIlabels,_argsIretLabels,_argsIself,_argsIstartLabel,_argsItransFunctions,_argsIupGLabel,_argsIupLabel) =
                  args_ _argsOcallLabels _argsOcounter _argsOdownGLabel _argsOdownLabel _argsOfunLabels _argsOfunName _argsOfunParams _argsOretLabels 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IConditional :: T_IGuards  ->
                               T_ISuite  ->
                               T_IStatement 
sem_IStatement_IConditional guards_ else_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _guardsOdownLabel :: ([Label])
              _guardsOdownGLabel :: ([Label])
              _elseOdownLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _guardsOcallLabels :: (Map String [(Label, Label)])
              _guardsOcounter :: Label
              _guardsOfunLabels :: (Map String Label)
              _guardsOfunName :: String
              _guardsOfunParams :: (Map String [Var])
              _guardsOretLabels :: (Map String [Label])
              _elseOcallLabels :: (Map String [(Label, Label)])
              _elseOcounter :: Label
              _elseOdownGLabel :: ([Label])
              _elseOfunLabels :: (Map String Label)
              _elseOfunName :: String
              _elseOfunParams :: (Map String [Var])
              _elseOretLabels :: (Map String [Label])
              _guardsIcallLabels :: (Map String [(Label, Label)])
              _guardsIcontrolFlow :: ControlFlow
              _guardsIcounter :: Label
              _guardsIfunLabels :: (Map String Label)
              _guardsIfunName :: String
              _guardsIfunParams :: (Map String [Var])
              _guardsIinterFlow :: InterFlow
              _guardsIlabels :: ([Label])
              _guardsIretLabels :: (Map String [Label])
              _guardsIself :: IGuards 
              _guardsIstartLabel :: ( Maybe Label )
              _guardsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _guardsIupGLabel :: ([Label])
              _guardsIupLabel :: ([Label])
              _elseIcallLabels :: (Map String [(Label, Label)])
              _elseIcontrolFlow :: ControlFlow
              _elseIcounter :: Label
              _elseIfunLabels :: (Map String Label)
              _elseIfunName :: String
              _elseIfunParams :: (Map String [Var])
              _elseIinterFlow :: InterFlow
              _elseIlabels :: ([Label])
              _elseIretLabels :: (Map String [Label])
              _elseIself :: ISuite 
              _elseIstartLabel :: ( Maybe Label )
              _elseItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _elseIupGLabel :: ([Label])
              _elseIupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 54 "src/Analysis/Python.ag" #-}
                   _guardsIlabels ++ _elseIlabels
                   {-# LINE 8145 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 155 "src/Analysis/Python.ag" #-}
                   _guardsIcontrolFlow ++ _elseIcontrolFlow
                   {-# LINE 8150 "src/Analysis/Python.hs" #-}
                   )
              _guardsOdownLabel =
                  ({-# LINE 156 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8155 "src/Analysis/Python.hs" #-}
                   )
              _guardsOdownGLabel =
                  ({-# LINE 157 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 8160 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownLabel =
                  ({-# LINE 158 "src/Analysis/Python.ag" #-}
                   _guardsIupGLabel
                   {-# LINE 8165 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 159 "src/Analysis/Python.ag" #-}
                   _guardsIupLabel ++ _elseIupLabel
                   {-# LINE 8170 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _guardsIinterFlow ++ _elseIinterFlow
                   {-# LINE 8175 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _guardsItransFunctions `Map.union` _elseItransFunctions
                   {-# LINE 8180 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IConditional _guardsIself _elseIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _elseIcallLabels
                   {-# LINE 8189 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _elseIcounter
                   {-# LINE 8194 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _elseIfunLabels
                   {-# LINE 8199 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _elseIfunName
                   {-# LINE 8204 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _elseIfunParams
                   {-# LINE 8209 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _elseIretLabels
                   {-# LINE 8214 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _elseIstartLabel
                   {-# LINE 8219 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _elseIupGLabel
                   {-# LINE 8224 "src/Analysis/Python.hs" #-}
                   )
              _guardsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 8229 "src/Analysis/Python.hs" #-}
                   )
              _guardsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 8234 "src/Analysis/Python.hs" #-}
                   )
              _guardsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8239 "src/Analysis/Python.hs" #-}
                   )
              _guardsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8244 "src/Analysis/Python.hs" #-}
                   )
              _guardsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8249 "src/Analysis/Python.hs" #-}
                   )
              _guardsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8254 "src/Analysis/Python.hs" #-}
                   )
              _elseOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _guardsIcallLabels
                   {-# LINE 8259 "src/Analysis/Python.hs" #-}
                   )
              _elseOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _guardsIcounter
                   {-# LINE 8264 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8269 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _guardsIfunLabels
                   {-# LINE 8274 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _guardsIfunName
                   {-# LINE 8279 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _guardsIfunParams
                   {-# LINE 8284 "src/Analysis/Python.hs" #-}
                   )
              _elseOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _guardsIretLabels
                   {-# LINE 8289 "src/Analysis/Python.hs" #-}
                   )
              ( _guardsIcallLabels,_guardsIcontrolFlow,_guardsIcounter,_guardsIfunLabels,_guardsIfunName,_guardsIfunParams,_guardsIinterFlow,_guardsIlabels,_guardsIretLabels,_guardsIself,_guardsIstartLabel,_guardsItransFunctions,_guardsIupGLabel,_guardsIupLabel) =
                  guards_ _guardsOcallLabels _guardsOcounter _guardsOdownGLabel _guardsOdownLabel _guardsOfunLabels _guardsOfunName _guardsOfunParams _guardsOretLabels 
              ( _elseIcallLabels,_elseIcontrolFlow,_elseIcounter,_elseIfunLabels,_elseIfunName,_elseIfunParams,_elseIinterFlow,_elseIlabels,_elseIretLabels,_elseIself,_elseIstartLabel,_elseItransFunctions,_elseIupGLabel,_elseIupLabel) =
                  else_ _elseOcallLabels _elseOcounter _elseOdownGLabel _elseOdownLabel _elseOfunLabels _elseOfunName _elseOfunParams _elseOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IContinue :: T_Label  ->
                            T_IStatement 
sem_IStatement_IContinue label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup7 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 8327 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 71 "src/Analysis/Python.ag" #-}
                   IContinue _label
                   {-# LINE 8332 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 8337 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 8342 "src/Analysis/Python.hs" #-}
                   )
              __tup7 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup7
                   {-# LINE 8349 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup7
                   {-# LINE 8354 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 8359 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 8364 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 8369 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IContinue _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 8376 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8381 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8386 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8391 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8396 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 8401 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IContinue.lhs.upGLabel"
                   {-# LINE 8406 "src/Analysis/Python.hs" #-}
                   )
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IDecorated :: T_IDecorators  ->
                             T_IStatement  ->
                             T_IStatement 
sem_IStatement_IDecorated decorators_ stat_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _decoratorsOcounter :: Label
              _statOcallLabels :: (Map String [(Label, Label)])
              _statOcounter :: Label
              _statOdownGLabel :: ([Label])
              _statOdownLabel :: ([Label])
              _statOfunLabels :: (Map String Label)
              _statOfunName :: String
              _statOfunParams :: (Map String [Var])
              _statOretLabels :: (Map String [Label])
              _decoratorsIcounter :: Label
              _decoratorsIlabels :: ([Label])
              _decoratorsIself :: IDecorators 
              _decoratorsIstartLabel :: ( Maybe Label )
              _statIcallLabels :: (Map String [(Label, Label)])
              _statIcontrolFlow :: ControlFlow
              _statIcounter :: Label
              _statIfunLabels :: (Map String Label)
              _statIfunName :: String
              _statIfunParams :: (Map String [Var])
              _statIinterFlow :: InterFlow
              _statIlabels :: ([Label])
              _statIretLabels :: (Map String [Label])
              _statIself :: IStatement 
              _statIstartLabel :: ( Maybe Label )
              _statItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _statIupGLabel :: ([Label])
              _statIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _statIcontrolFlow
                   {-# LINE 8467 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _statIinterFlow
                   {-# LINE 8472 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _decoratorsIlabels ++ _statIlabels
                   {-# LINE 8477 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _statItransFunctions
                   {-# LINE 8482 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IDecorated _decoratorsIself _statIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _statIcallLabels
                   {-# LINE 8491 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _statIcounter
                   {-# LINE 8496 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _statIfunLabels
                   {-# LINE 8501 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _statIfunName
                   {-# LINE 8506 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _statIfunParams
                   {-# LINE 8511 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _statIretLabels
                   {-# LINE 8516 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _statIstartLabel
                   {-# LINE 8521 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _statIupGLabel
                   {-# LINE 8526 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _statIupLabel
                   {-# LINE 8531 "src/Analysis/Python.hs" #-}
                   )
              _decoratorsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 8536 "src/Analysis/Python.hs" #-}
                   )
              _statOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 8541 "src/Analysis/Python.hs" #-}
                   )
              _statOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _decoratorsIcounter
                   {-# LINE 8546 "src/Analysis/Python.hs" #-}
                   )
              _statOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8551 "src/Analysis/Python.hs" #-}
                   )
              _statOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8556 "src/Analysis/Python.hs" #-}
                   )
              _statOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8561 "src/Analysis/Python.hs" #-}
                   )
              _statOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8566 "src/Analysis/Python.hs" #-}
                   )
              _statOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8571 "src/Analysis/Python.hs" #-}
                   )
              _statOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8576 "src/Analysis/Python.hs" #-}
                   )
              ( _decoratorsIcounter,_decoratorsIlabels,_decoratorsIself,_decoratorsIstartLabel) =
                  decorators_ _decoratorsOcounter 
              ( _statIcallLabels,_statIcontrolFlow,_statIcounter,_statIfunLabels,_statIfunName,_statIfunParams,_statIinterFlow,_statIlabels,_statIretLabels,_statIself,_statIstartLabel,_statItransFunctions,_statIupGLabel,_statIupLabel) =
                  stat_ _statOcallLabels _statOcounter _statOdownGLabel _statOdownLabel _statOfunLabels _statOfunName _statOfunParams _statOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IDelete :: T_IExprs  ->
                          T_IStatement 
sem_IStatement_IDelete exprs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprsOcallLabels :: (Map String [(Label, Label)])
              _exprsOcounter :: Label
              _exprsOdownGLabel :: ([Label])
              _exprsOdownLabel :: ([Label])
              _exprsOfunLabels :: (Map String Label)
              _exprsOfunName :: String
              _exprsOfunParams :: (Map String [Var])
              _exprsOretLabels :: (Map String [Label])
              _exprsIcallLabels :: (Map String [(Label, Label)])
              _exprsIcontrolFlow :: ControlFlow
              _exprsIcounter :: Label
              _exprsIfunLabels :: (Map String Label)
              _exprsIfunName :: String
              _exprsIfunParams :: (Map String [Var])
              _exprsIinterFlow :: InterFlow
              _exprsIlabels :: ([Label])
              _exprsIretLabels :: (Map String [Label])
              _exprsIself :: IExprs 
              _exprsIstartLabel :: ( Maybe Label )
              _exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprsIupGLabel :: ([Label])
              _exprsIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _exprsIcontrolFlow
                   {-# LINE 8633 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprsIinterFlow
                   {-# LINE 8638 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _exprsIlabels
                   {-# LINE 8643 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _exprsItransFunctions
                   {-# LINE 8648 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IDelete _exprsIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprsIcallLabels
                   {-# LINE 8657 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprsIcounter
                   {-# LINE 8662 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprsIfunLabels
                   {-# LINE 8667 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprsIfunName
                   {-# LINE 8672 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprsIfunParams
                   {-# LINE 8677 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprsIretLabels
                   {-# LINE 8682 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _exprsIstartLabel
                   {-# LINE 8687 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprsIupGLabel
                   {-# LINE 8692 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _exprsIupLabel
                   {-# LINE 8697 "src/Analysis/Python.hs" #-}
                   )
              _exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 8702 "src/Analysis/Python.hs" #-}
                   )
              _exprsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 8707 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8712 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8717 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8722 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8727 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8732 "src/Analysis/Python.hs" #-}
                   )
              _exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8737 "src/Analysis/Python.hs" #-}
                   )
              ( _exprsIcallLabels,_exprsIcontrolFlow,_exprsIcounter,_exprsIfunLabels,_exprsIfunName,_exprsIfunParams,_exprsIinterFlow,_exprsIlabels,_exprsIretLabels,_exprsIself,_exprsIstartLabel,_exprsItransFunctions,_exprsIupGLabel,_exprsIupLabel) =
                  exprs_ _exprsOcallLabels _exprsOcounter _exprsOdownGLabel _exprsOdownLabel _exprsOfunLabels _exprsOfunName _exprsOfunParams _exprsOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IExec :: T_IExpr  ->
                        (Maybe PairExprMybExpr) ->
                        T_IStatement 
sem_IStatement_IExec expr_ globlocs_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOcounter :: Label
              _exprOdownGLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _exprIcontrolFlow
                   {-# LINE 8793 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprIinterFlow
                   {-# LINE 8798 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _exprIlabels
                   {-# LINE 8803 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _exprItransFunctions
                   {-# LINE 8808 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IExec _exprIself globlocs_
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 8817 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 8822 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 8827 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 8832 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 8837 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 8842 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _exprIstartLabel
                   {-# LINE 8847 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 8852 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _exprIupLabel
                   {-# LINE 8857 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 8862 "src/Analysis/Python.hs" #-}
                   )
              _exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 8867 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 8872 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 8877 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 8882 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 8887 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 8892 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 8897 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IFor :: T_IExprs  ->
                       T_IExpr  ->
                       T_ISuite  ->
                       T_ISuite  ->
                       T_IStatement 
sem_IStatement_IFor targets_ generator_ body_ else_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _targetsOcallLabels :: (Map String [(Label, Label)])
              _targetsOcounter :: Label
              _targetsOdownGLabel :: ([Label])
              _targetsOdownLabel :: ([Label])
              _targetsOfunLabels :: (Map String Label)
              _targetsOfunName :: String
              _targetsOfunParams :: (Map String [Var])
              _targetsOretLabels :: (Map String [Label])
              _generatorOcallLabels :: (Map String [(Label, Label)])
              _generatorOcounter :: Label
              _generatorOdownGLabel :: ([Label])
              _generatorOdownLabel :: ([Label])
              _generatorOfunLabels :: (Map String Label)
              _generatorOfunName :: String
              _generatorOfunParams :: (Map String [Var])
              _generatorOretLabels :: (Map String [Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _elseOcallLabels :: (Map String [(Label, Label)])
              _elseOcounter :: Label
              _elseOdownGLabel :: ([Label])
              _elseOdownLabel :: ([Label])
              _elseOfunLabels :: (Map String Label)
              _elseOfunName :: String
              _elseOfunParams :: (Map String [Var])
              _elseOretLabels :: (Map String [Label])
              _targetsIcallLabels :: (Map String [(Label, Label)])
              _targetsIcontrolFlow :: ControlFlow
              _targetsIcounter :: Label
              _targetsIfunLabels :: (Map String Label)
              _targetsIfunName :: String
              _targetsIfunParams :: (Map String [Var])
              _targetsIinterFlow :: InterFlow
              _targetsIlabels :: ([Label])
              _targetsIretLabels :: (Map String [Label])
              _targetsIself :: IExprs 
              _targetsIstartLabel :: ( Maybe Label )
              _targetsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _targetsIupGLabel :: ([Label])
              _targetsIupLabel :: ([Label])
              _generatorIcallLabels :: (Map String [(Label, Label)])
              _generatorIcontrolFlow :: ControlFlow
              _generatorIcounter :: Label
              _generatorIfunLabels :: (Map String Label)
              _generatorIfunName :: String
              _generatorIfunParams :: (Map String [Var])
              _generatorIinterFlow :: InterFlow
              _generatorIlabels :: ([Label])
              _generatorIretLabels :: (Map String [Label])
              _generatorIself :: IExpr 
              _generatorIstartLabel :: ( Maybe Label )
              _generatorItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _generatorIupGLabel :: ([Label])
              _generatorIupLabel :: ([Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _elseIcallLabels :: (Map String [(Label, Label)])
              _elseIcontrolFlow :: ControlFlow
              _elseIcounter :: Label
              _elseIfunLabels :: (Map String Label)
              _elseIfunName :: String
              _elseIfunParams :: (Map String [Var])
              _elseIinterFlow :: InterFlow
              _elseIlabels :: ([Label])
              _elseIretLabels :: (Map String [Label])
              _elseIself :: ISuite 
              _elseIstartLabel :: ( Maybe Label )
              _elseItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _elseIupGLabel :: ([Label])
              _elseIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _targetsIcontrolFlow ++ _generatorIcontrolFlow ++ _bodyIcontrolFlow ++ _elseIcontrolFlow
                   {-# LINE 9021 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _targetsIinterFlow ++ _generatorIinterFlow ++ _bodyIinterFlow ++ _elseIinterFlow
                   {-# LINE 9026 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _targetsIlabels ++ _generatorIlabels ++ _bodyIlabels ++ _elseIlabels
                   {-# LINE 9031 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _targetsItransFunctions `Map.union` _generatorItransFunctions `Map.union` _bodyItransFunctions `Map.union` _elseItransFunctions
                   {-# LINE 9036 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IFor _targetsIself _generatorIself _bodyIself _elseIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _elseIcallLabels
                   {-# LINE 9045 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _elseIcounter
                   {-# LINE 9050 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _elseIfunLabels
                   {-# LINE 9055 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _elseIfunName
                   {-# LINE 9060 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _elseIfunParams
                   {-# LINE 9065 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _elseIretLabels
                   {-# LINE 9070 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _elseIstartLabel
                   {-# LINE 9075 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _elseIupGLabel
                   {-# LINE 9080 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _elseIupLabel
                   {-# LINE 9085 "src/Analysis/Python.hs" #-}
                   )
              _targetsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9090 "src/Analysis/Python.hs" #-}
                   )
              _targetsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 9095 "src/Analysis/Python.hs" #-}
                   )
              _targetsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9100 "src/Analysis/Python.hs" #-}
                   )
              _targetsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9105 "src/Analysis/Python.hs" #-}
                   )
              _targetsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9110 "src/Analysis/Python.hs" #-}
                   )
              _targetsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9115 "src/Analysis/Python.hs" #-}
                   )
              _targetsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9120 "src/Analysis/Python.hs" #-}
                   )
              _targetsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9125 "src/Analysis/Python.hs" #-}
                   )
              _generatorOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _targetsIcallLabels
                   {-# LINE 9130 "src/Analysis/Python.hs" #-}
                   )
              _generatorOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _targetsIcounter
                   {-# LINE 9135 "src/Analysis/Python.hs" #-}
                   )
              _generatorOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9140 "src/Analysis/Python.hs" #-}
                   )
              _generatorOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9145 "src/Analysis/Python.hs" #-}
                   )
              _generatorOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _targetsIfunLabels
                   {-# LINE 9150 "src/Analysis/Python.hs" #-}
                   )
              _generatorOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _targetsIfunName
                   {-# LINE 9155 "src/Analysis/Python.hs" #-}
                   )
              _generatorOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _targetsIfunParams
                   {-# LINE 9160 "src/Analysis/Python.hs" #-}
                   )
              _generatorOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _targetsIretLabels
                   {-# LINE 9165 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _generatorIcallLabels
                   {-# LINE 9170 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _generatorIcounter
                   {-# LINE 9175 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9180 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9185 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _generatorIfunLabels
                   {-# LINE 9190 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _generatorIfunName
                   {-# LINE 9195 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _generatorIfunParams
                   {-# LINE 9200 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _generatorIretLabels
                   {-# LINE 9205 "src/Analysis/Python.hs" #-}
                   )
              _elseOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 9210 "src/Analysis/Python.hs" #-}
                   )
              _elseOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 9215 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9220 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9225 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 9230 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 9235 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 9240 "src/Analysis/Python.hs" #-}
                   )
              _elseOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 9245 "src/Analysis/Python.hs" #-}
                   )
              ( _targetsIcallLabels,_targetsIcontrolFlow,_targetsIcounter,_targetsIfunLabels,_targetsIfunName,_targetsIfunParams,_targetsIinterFlow,_targetsIlabels,_targetsIretLabels,_targetsIself,_targetsIstartLabel,_targetsItransFunctions,_targetsIupGLabel,_targetsIupLabel) =
                  targets_ _targetsOcallLabels _targetsOcounter _targetsOdownGLabel _targetsOdownLabel _targetsOfunLabels _targetsOfunName _targetsOfunParams _targetsOretLabels 
              ( _generatorIcallLabels,_generatorIcontrolFlow,_generatorIcounter,_generatorIfunLabels,_generatorIfunName,_generatorIfunParams,_generatorIinterFlow,_generatorIlabels,_generatorIretLabels,_generatorIself,_generatorIstartLabel,_generatorItransFunctions,_generatorIupGLabel,_generatorIupLabel) =
                  generator_ _generatorOcallLabels _generatorOcounter _generatorOdownGLabel _generatorOdownLabel _generatorOfunLabels _generatorOfunName _generatorOfunParams _generatorOretLabels 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
              ( _elseIcallLabels,_elseIcontrolFlow,_elseIcounter,_elseIfunLabels,_elseIfunName,_elseIfunParams,_elseIinterFlow,_elseIlabels,_elseIretLabels,_elseIself,_elseIstartLabel,_elseItransFunctions,_elseIupGLabel,_elseIupLabel) =
                  else_ _elseOcallLabels _elseOcounter _elseOdownGLabel _elseOdownLabel _elseOfunLabels _elseOfunName _elseOfunParams _elseOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IFromImport :: T_IImportRelative  ->
                              T_IFromItems  ->
                              T_Label  ->
                              T_IStatement 
sem_IStatement_IFromImport modul_ items_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup8 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _modulIself :: IImportRelative 
              _itemsIself :: IFromItems 
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9291 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 64 "src/Analysis/Python.ag" #-}
                   IFromImport _modulIself _itemsIself _label
                   {-# LINE 9296 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9301 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 9306 "src/Analysis/Python.hs" #-}
                   )
              __tup8 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup8
                   {-# LINE 9313 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup8
                   {-# LINE 9318 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9323 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9328 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 9333 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IFromImport _modulIself _itemsIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9340 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9345 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9350 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9355 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9360 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 9365 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IFromImport.lhs.upGLabel"
                   {-# LINE 9370 "src/Analysis/Python.hs" #-}
                   )
              ( _modulIself) =
                  modul_ 
              ( _itemsIself) =
                  items_ 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IFun :: String ->
                       T_IParams  ->
                       T_MybExpr  ->
                       T_ISuite  ->
                       T_Label  ->
                       T_IStatement 
sem_IStatement_IFun name_ args_ result_ body_ entry_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOcontrolFlow :: ControlFlow
              _lhsOupLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _bodyOfunName :: String
              _lhsOfunName :: String
              _bodyOfunLabels :: (Map String Label)
              _lhsOfunLabels :: (Map String Label)
              _bodyOfunParams :: (Map String [Var])
              _lhsOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup9 :: ((Label,Label))
              _argsOcounter :: Label
              _label :: Label
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOupGLabel :: ([Label])
              _resultOcallLabels :: (Map String [(Label, Label)])
              _resultOcounter :: Label
              _resultOdownGLabel :: ([Label])
              _resultOdownLabel :: ([Label])
              _resultOfunLabels :: (Map String Label)
              _resultOfunName :: String
              _resultOfunParams :: (Map String [Var])
              _resultOretLabels :: (Map String [Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _argsIcounter :: Label
              _argsIlabels :: ([Label])
              _argsIself :: IParams 
              _argsIstartLabel :: ( Maybe Label )
              _resultIcallLabels :: (Map String [(Label, Label)])
              _resultIcontrolFlow :: ControlFlow
              _resultIcounter :: Label
              _resultIfunLabels :: (Map String Label)
              _resultIfunName :: String
              _resultIfunParams :: (Map String [Var])
              _resultIinterFlow :: InterFlow
              _resultIlabels :: ([Label])
              _resultIretLabels :: (Map String [Label])
              _resultIself :: MybExpr 
              _resultIstartLabel :: ( Maybe Label )
              _resultItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _resultIupGLabel :: ([Label])
              _resultIupLabel :: ([Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _entryIself :: Label 
              _lhsOlabels =
                  ({-# LINE 56 "src/Analysis/Python.ag" #-}
                   _label    :(_bodyIlabels)
                   {-# LINE 9463 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 65 "src/Analysis/Python.ag" #-}
                   IFun name_ _argsIself _resultIself _bodyIself _label
                   {-# LINE 9468 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 168 "src/Analysis/Python.ag" #-}
                   let call = snd $ unzip $ maybe [] id (Map.lookup name_ _bodyIcallLabels)
                       ret = maybe [] id (Map.lookup name_ _bodyIretLabels)
                   in nub $ createFlow InterFlow ret call ++ _bodyIcontrolFlow
                   {-# LINE 9475 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 171 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9480 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 172 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9485 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 173 "src/Analysis/Python.ag" #-}
                   name_
                   {-# LINE 9490 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 174 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9495 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 175 "src/Analysis/Python.ag" #-}
                   Map.insert name_ _label     _lhsIfunLabels
                   {-# LINE 9500 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 176 "src/Analysis/Python.ag" #-}
                   Map.insert name_ _label     _lhsIfunLabels
                   {-# LINE 9505 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 177 "src/Analysis/Python.ag" #-}
                   Map.insert name_ (getVarParams _argsIself) _lhsIfunParams
                   {-# LINE 9510 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 178 "src/Analysis/Python.ag" #-}
                   Map.insert name_ (getVarParams _argsIself) _lhsIfunParams
                   {-# LINE 9515 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 179 "src/Analysis/Python.ag" #-}
                   case Map.lookup name_ _lhsIretLabels of
                        Nothing -> _lhsIretLabels
                        Just x  -> Map.delete name_ _lhsIretLabels
                   {-# LINE 9522 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 182 "src/Analysis/Python.ag" #-}
                   case Map.lookup name_ _bodyIretLabels of
                                          Nothing -> case _bodyIupLabel of
                                                                                  [] -> Map.insert name_ [_label    ] _lhsIretLabels
                                                                                  l  -> Map.insert name_ l                        _lhsIretLabels
                                          Just rl  -> case _bodyIupLabel of
                                                                                  [] -> Map.insert name_ rl _lhsIretLabels
                                                                                  l  -> Map.insert name_ (nub (l ++ rl)) _lhsIretLabels
                   {-# LINE 9533 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 189 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 9538 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 235 "src/Analysis/Python.ag" #-}
                   let l = maybe [] id (Map.lookup name_ _bodyIcallLabels)
                       ret = maybe [] id (Map.lookup name_ _bodyIretLabels)
                   in nub $ (foldr (++) [] (map (\(c,ce) -> createInterFlow c _label     ret ce) l)) ++ _bodyIinterFlow
                   {-# LINE 9545 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 263 "src/Analysis/Python.ag" #-}
                   Map.insert _label     (Unary id) _bodyItransFunctions
                   {-# LINE 9550 "src/Analysis/Python.hs" #-}
                   )
              __tup9 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_argsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup9
                   {-# LINE 9557 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup9
                   {-# LINE 9562 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IFun name_ _argsIself _resultIself _bodyIself _entryIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 9569 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 9574 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _bodyIupGLabel
                   {-# LINE 9579 "src/Analysis/Python.hs" #-}
                   )
              _resultOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9584 "src/Analysis/Python.hs" #-}
                   )
              _resultOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _argsIcounter
                   {-# LINE 9589 "src/Analysis/Python.hs" #-}
                   )
              _resultOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9594 "src/Analysis/Python.hs" #-}
                   )
              _resultOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 9599 "src/Analysis/Python.hs" #-}
                   )
              _resultOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9604 "src/Analysis/Python.hs" #-}
                   )
              _resultOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9609 "src/Analysis/Python.hs" #-}
                   )
              _resultOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9614 "src/Analysis/Python.hs" #-}
                   )
              _resultOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9619 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _resultIcallLabels
                   {-# LINE 9624 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _resultIcounter
                   {-# LINE 9629 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 9634 "src/Analysis/Python.hs" #-}
                   )
              ( _argsIcounter,_argsIlabels,_argsIself,_argsIstartLabel) =
                  args_ _argsOcounter 
              ( _resultIcallLabels,_resultIcontrolFlow,_resultIcounter,_resultIfunLabels,_resultIfunName,_resultIfunParams,_resultIinterFlow,_resultIlabels,_resultIretLabels,_resultIself,_resultIstartLabel,_resultItransFunctions,_resultIupGLabel,_resultIupLabel) =
                  result_ _resultOcallLabels _resultOcounter _resultOdownGLabel _resultOdownLabel _resultOfunLabels _resultOfunName _resultOfunParams _resultOretLabels 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
              ( _entryIself) =
                  entry_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IGlobal :: T_IIdents  ->
                          T_Label  ->
                          T_IStatement 
sem_IStatement_IGlobal vars_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup10 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _varsIself :: IIdents 
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9678 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 72 "src/Analysis/Python.ag" #-}
                   IGlobal _varsIself _label
                   {-# LINE 9683 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9688 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 9693 "src/Analysis/Python.hs" #-}
                   )
              __tup10 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup10
                   {-# LINE 9700 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup10
                   {-# LINE 9705 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9710 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9715 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 9720 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IGlobal _varsIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9727 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9732 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9737 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9742 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9747 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 9752 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IGlobal.lhs.upGLabel"
                   {-# LINE 9757 "src/Analysis/Python.hs" #-}
                   )
              ( _varsIself) =
                  vars_ 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IImport :: T_IImportItems  ->
                          T_Label  ->
                          T_IStatement 
sem_IStatement_IImport items_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup11 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _itemsIself :: IImportItems 
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9797 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 63 "src/Analysis/Python.ag" #-}
                   IImport _itemsIself _label
                   {-# LINE 9802 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9807 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 9812 "src/Analysis/Python.hs" #-}
                   )
              __tup11 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup11
                   {-# LINE 9819 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup11
                   {-# LINE 9824 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9829 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9834 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 9839 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IImport _itemsIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9846 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9851 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9856 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9861 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9866 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 9871 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IImport.lhs.upGLabel"
                   {-# LINE 9876 "src/Analysis/Python.hs" #-}
                   )
              ( _itemsIself) =
                  items_ 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_INonLocal :: T_IIdents  ->
                            T_Label  ->
                            T_IStatement 
sem_IStatement_INonLocal vars_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup12 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _varsIself :: IIdents 
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9916 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 73 "src/Analysis/Python.ag" #-}
                   INonLocal _varsIself _label
                   {-# LINE 9921 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 9926 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 9931 "src/Analysis/Python.hs" #-}
                   )
              __tup12 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup12
                   {-# LINE 9938 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup12
                   {-# LINE 9943 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9948 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 9953 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 9958 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  INonLocal _varsIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 9965 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 9970 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 9975 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 9980 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 9985 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 9990 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.INonLocal.lhs.upGLabel"
                   {-# LINE 9995 "src/Analysis/Python.hs" #-}
                   )
              ( _varsIself) =
                  vars_ 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IPass :: T_Label  ->
                        T_IStatement 
sem_IStatement_IPass label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              __tup13 :: ((Label,Label))
              _lhsOcounter :: Label
              _label :: Label
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 10033 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 69 "src/Analysis/Python.ag" #-}
                   IPass _label
                   {-# LINE 10038 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 10043 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 10048 "src/Analysis/Python.hs" #-}
                   )
              __tup13 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_lhsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup13
                   {-# LINE 10055 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup13
                   {-# LINE 10060 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10065 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10070 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 10075 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IPass _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10082 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10087 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10092 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10097 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10102 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 10107 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IPass.lhs.upGLabel"
                   {-# LINE 10112 "src/Analysis/Python.hs" #-}
                   )
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IPrint :: Bool ->
                         T_IExprs  ->
                         Bool ->
                         T_Label  ->
                         T_IStatement 
sem_IStatement_IPrint chevron_ exprs_ trailcomma_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow :: ControlFlow
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup14 :: ((Label,Label))
              _exprsOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _exprsOcallLabels :: (Map String [(Label, Label)])
              _exprsOdownGLabel :: ([Label])
              _exprsOdownLabel :: ([Label])
              _exprsOfunLabels :: (Map String Label)
              _exprsOfunName :: String
              _exprsOfunParams :: (Map String [Var])
              _exprsOretLabels :: (Map String [Label])
              _exprsIcallLabels :: (Map String [(Label, Label)])
              _exprsIcontrolFlow :: ControlFlow
              _exprsIcounter :: Label
              _exprsIfunLabels :: (Map String Label)
              _exprsIfunName :: String
              _exprsIfunParams :: (Map String [Var])
              _exprsIinterFlow :: InterFlow
              _exprsIlabels :: ([Label])
              _exprsIretLabels :: (Map String [Label])
              _exprsIself :: IExprs 
              _exprsIstartLabel :: ( Maybe Label )
              _exprsItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprsIupGLabel :: ([Label])
              _exprsIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 60 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 10173 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 74 "src/Analysis/Python.ag" #-}
                   IPrint chevron_ _exprsIself trailcomma_ _label
                   {-# LINE 10178 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 196 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 10183 "src/Analysis/Python.hs" #-}
                   )
              _startLabel =
                  ({-# LINE 197 "src/Analysis/Python.ag" #-}
                   Just _label
                   {-# LINE 10188 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 200 "src/Analysis/Python.ag" #-}
                   createFlow IntraFlow _exprsIupLabel [_label    ] ++ _exprsIcontrolFlow
                   {-# LINE 10193 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 270 "src/Analysis/Python.ag" #-}
                   Map.singleton _label     $ Unary id
                   {-# LINE 10198 "src/Analysis/Python.hs" #-}
                   )
              __tup14 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_exprsOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup14
                   {-# LINE 10205 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup14
                   {-# LINE 10210 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprsIinterFlow
                   {-# LINE 10215 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IPrint chevron_ _exprsIself trailcomma_ _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprsIcallLabels
                   {-# LINE 10222 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprsIcounter
                   {-# LINE 10227 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprsIfunLabels
                   {-# LINE 10232 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprsIfunName
                   {-# LINE 10237 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprsIfunParams
                   {-# LINE 10242 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprsIretLabels
                   {-# LINE 10247 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _startLabel
                   {-# LINE 10252 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprsIupGLabel
                   {-# LINE 10257 "src/Analysis/Python.hs" #-}
                   )
              _exprsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10262 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 10267 "src/Analysis/Python.hs" #-}
                   )
              _exprsOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 10272 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10277 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10282 "src/Analysis/Python.hs" #-}
                   )
              _exprsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10287 "src/Analysis/Python.hs" #-}
                   )
              _exprsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10292 "src/Analysis/Python.hs" #-}
                   )
              ( _exprsIcallLabels,_exprsIcontrolFlow,_exprsIcounter,_exprsIfunLabels,_exprsIfunName,_exprsIfunParams,_exprsIinterFlow,_exprsIlabels,_exprsIretLabels,_exprsIself,_exprsIstartLabel,_exprsItransFunctions,_exprsIupGLabel,_exprsIupLabel) =
                  exprs_ _exprsOcallLabels _exprsOcounter _exprsOdownGLabel _exprsOdownLabel _exprsOfunLabels _exprsOfunName _exprsOfunParams _exprsOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IRaise :: T_IRaiseExpr  ->
                         T_IStatement 
sem_IStatement_IRaise expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprIself :: IRaiseExpr 
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10328 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10333 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10338 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 10343 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IRaise _exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10352 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 10357 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10362 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10367 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10372 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10377 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IRaise.lhs.startLabel"
                   {-# LINE 10382 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IRaise.lhs.upGLabel"
                   {-# LINE 10387 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   error "missing rule: IStatement.IRaise.lhs.upLabel"
                   {-# LINE 10392 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIself) =
                  expr_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IReturn :: T_MybExpr  ->
                          T_Label  ->
                          T_IStatement 
sem_IStatement_IReturn expr_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOcontrolFlow :: ControlFlow
              _lhsOretLabels :: (Map String [Label])
              _lhsOupLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup15 :: ((Label,Label))
              _exprOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOdownGLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: MybExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 57 "src/Analysis/Python.ag" #-}
                   _label    :(_exprIlabels)
                   {-# LINE 10451 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 68 "src/Analysis/Python.ag" #-}
                   IReturn _exprIself _label
                   {-# LINE 10456 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 191 "src/Analysis/Python.ag" #-}
                   (createFlow IntraFlow _exprIupLabel [_label    ]) ++ _exprIcontrolFlow
                   {-# LINE 10461 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 192 "src/Analysis/Python.ag" #-}
                   Map.insertWith (++) _lhsIfunName [_label    ] _lhsIretLabels
                   {-# LINE 10466 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 193 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 10471 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 194 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 10476 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 265 "src/Analysis/Python.ag" #-}
                   let tf = case _exprIself of
                                 Nothing -> Unary $ \(c, env) -> (init c, Map.insert _rVar     (prevTypesOf' env _rVar    ) env)
                                 Just e -> Unary $ \(c, env) -> (init c, Map.insert _rVar     (Set.union (prevTypesOf env _rVar    ) (typesOf env e)) env)
                                               in Map.singleton _label     tf
                   {-# LINE 10484 "src/Analysis/Python.hs" #-}
                   )
              _rVar =
                  ({-# LINE 269 "src/Analysis/Python.ag" #-}
                   "r"++(_lhsIfunName)
                   {-# LINE 10489 "src/Analysis/Python.hs" #-}
                   )
              __tup15 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_exprOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup15
                   {-# LINE 10496 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup15
                   {-# LINE 10501 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprIinterFlow
                   {-# LINE 10506 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IReturn _exprIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 10513 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 10518 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 10523 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 10528 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 10533 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _exprIstartLabel
                   {-# LINE 10538 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 10543 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10548 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 10553 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10558 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10563 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10568 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10573 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IStmtExpr :: T_IExpr  ->
                            T_IStatement 
sem_IStatement_IStmtExpr expr_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _exprOcallLabels :: (Map String [(Label, Label)])
              _exprOcounter :: Label
              _exprOdownGLabel :: ([Label])
              _exprOdownLabel :: ([Label])
              _exprOfunLabels :: (Map String Label)
              _exprOfunName :: String
              _exprOfunParams :: (Map String [Var])
              _exprOretLabels :: (Map String [Label])
              _exprIcallLabels :: (Map String [(Label, Label)])
              _exprIcontrolFlow :: ControlFlow
              _exprIcounter :: Label
              _exprIfunLabels :: (Map String Label)
              _exprIfunName :: String
              _exprIfunParams :: (Map String [Var])
              _exprIinterFlow :: InterFlow
              _exprIlabels :: ([Label])
              _exprIretLabels :: (Map String [Label])
              _exprIself :: IExpr 
              _exprIstartLabel :: ( Maybe Label )
              _exprItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _exprIupGLabel :: ([Label])
              _exprIupLabel :: ([Label])
              _lhsOstartLabel =
                  ({-# LINE 198 "src/Analysis/Python.ag" #-}
                   case _exprIstartLabel of
                      Just _ -> _exprIstartLabel
                   {-# LINE 10631 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _exprIcontrolFlow
                   {-# LINE 10636 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _exprIinterFlow
                   {-# LINE 10641 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _exprIlabels
                   {-# LINE 10646 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _exprItransFunctions
                   {-# LINE 10651 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IStmtExpr _exprIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _exprIcallLabels
                   {-# LINE 10660 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exprIcounter
                   {-# LINE 10665 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _exprIfunLabels
                   {-# LINE 10670 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _exprIfunName
                   {-# LINE 10675 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _exprIfunParams
                   {-# LINE 10680 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _exprIretLabels
                   {-# LINE 10685 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _exprIupGLabel
                   {-# LINE 10690 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _exprIupLabel
                   {-# LINE 10695 "src/Analysis/Python.hs" #-}
                   )
              _exprOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10700 "src/Analysis/Python.hs" #-}
                   )
              _exprOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 10705 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 10710 "src/Analysis/Python.hs" #-}
                   )
              _exprOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 10715 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10720 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10725 "src/Analysis/Python.hs" #-}
                   )
              _exprOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10730 "src/Analysis/Python.hs" #-}
                   )
              _exprOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10735 "src/Analysis/Python.hs" #-}
                   )
              ( _exprIcallLabels,_exprIcontrolFlow,_exprIcounter,_exprIfunLabels,_exprIfunName,_exprIfunParams,_exprIinterFlow,_exprIlabels,_exprIretLabels,_exprIself,_exprIstartLabel,_exprItransFunctions,_exprIupGLabel,_exprIupLabel) =
                  expr_ _exprOcallLabels _exprOcounter _exprOdownGLabel _exprOdownLabel _exprOfunLabels _exprOfunName _exprOfunParams _exprOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_ITry :: T_ISuite  ->
                       T_IHandlers  ->
                       T_ISuite  ->
                       T_ISuite  ->
                       T_IStatement 
sem_IStatement_ITry body_ excepts_ else_ finally_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _exceptsOcounter :: Label
              _elseOcallLabels :: (Map String [(Label, Label)])
              _elseOcounter :: Label
              _elseOdownGLabel :: ([Label])
              _elseOdownLabel :: ([Label])
              _elseOfunLabels :: (Map String Label)
              _elseOfunName :: String
              _elseOfunParams :: (Map String [Var])
              _elseOretLabels :: (Map String [Label])
              _finallyOcallLabels :: (Map String [(Label, Label)])
              _finallyOcounter :: Label
              _finallyOdownGLabel :: ([Label])
              _finallyOdownLabel :: ([Label])
              _finallyOfunLabels :: (Map String Label)
              _finallyOfunName :: String
              _finallyOfunParams :: (Map String [Var])
              _finallyOretLabels :: (Map String [Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _exceptsIcounter :: Label
              _exceptsIlabels :: ([Label])
              _exceptsIself :: IHandlers 
              _exceptsIstartLabel :: ( Maybe Label )
              _elseIcallLabels :: (Map String [(Label, Label)])
              _elseIcontrolFlow :: ControlFlow
              _elseIcounter :: Label
              _elseIfunLabels :: (Map String Label)
              _elseIfunName :: String
              _elseIfunParams :: (Map String [Var])
              _elseIinterFlow :: InterFlow
              _elseIlabels :: ([Label])
              _elseIretLabels :: (Map String [Label])
              _elseIself :: ISuite 
              _elseIstartLabel :: ( Maybe Label )
              _elseItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _elseIupGLabel :: ([Label])
              _elseIupLabel :: ([Label])
              _finallyIcallLabels :: (Map String [(Label, Label)])
              _finallyIcontrolFlow :: ControlFlow
              _finallyIcounter :: Label
              _finallyIfunLabels :: (Map String Label)
              _finallyIfunName :: String
              _finallyIfunParams :: (Map String [Var])
              _finallyIinterFlow :: InterFlow
              _finallyIlabels :: ([Label])
              _finallyIretLabels :: (Map String [Label])
              _finallyIself :: ISuite 
              _finallyIstartLabel :: ( Maybe Label )
              _finallyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _finallyIupGLabel :: ([Label])
              _finallyIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _bodyIcontrolFlow ++ _elseIcontrolFlow ++ _finallyIcontrolFlow
                   {-# LINE 10842 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _bodyIinterFlow ++ _elseIinterFlow ++ _finallyIinterFlow
                   {-# LINE 10847 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _bodyIlabels ++ _exceptsIlabels ++ _elseIlabels ++ _finallyIlabels
                   {-# LINE 10852 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _bodyItransFunctions `Map.union` _elseItransFunctions `Map.union` _finallyItransFunctions
                   {-# LINE 10857 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  ITry _bodyIself _exceptsIself _elseIself _finallyIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _finallyIcallLabels
                   {-# LINE 10866 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _finallyIcounter
                   {-# LINE 10871 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _finallyIfunLabels
                   {-# LINE 10876 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _finallyIfunName
                   {-# LINE 10881 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _finallyIfunParams
                   {-# LINE 10886 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _finallyIretLabels
                   {-# LINE 10891 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _finallyIstartLabel
                   {-# LINE 10896 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _finallyIupGLabel
                   {-# LINE 10901 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _finallyIupLabel
                   {-# LINE 10906 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 10911 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 10916 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 10921 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 10926 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 10931 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 10936 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 10941 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 10946 "src/Analysis/Python.hs" #-}
                   )
              _exceptsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 10951 "src/Analysis/Python.hs" #-}
                   )
              _elseOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 10956 "src/Analysis/Python.hs" #-}
                   )
              _elseOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _exceptsIcounter
                   {-# LINE 10961 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 10966 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 10971 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 10976 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 10981 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 10986 "src/Analysis/Python.hs" #-}
                   )
              _elseOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 10991 "src/Analysis/Python.hs" #-}
                   )
              _finallyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _elseIcallLabels
                   {-# LINE 10996 "src/Analysis/Python.hs" #-}
                   )
              _finallyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _elseIcounter
                   {-# LINE 11001 "src/Analysis/Python.hs" #-}
                   )
              _finallyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11006 "src/Analysis/Python.hs" #-}
                   )
              _finallyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 11011 "src/Analysis/Python.hs" #-}
                   )
              _finallyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _elseIfunLabels
                   {-# LINE 11016 "src/Analysis/Python.hs" #-}
                   )
              _finallyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _elseIfunName
                   {-# LINE 11021 "src/Analysis/Python.hs" #-}
                   )
              _finallyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _elseIfunParams
                   {-# LINE 11026 "src/Analysis/Python.hs" #-}
                   )
              _finallyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _elseIretLabels
                   {-# LINE 11031 "src/Analysis/Python.hs" #-}
                   )
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
              ( _exceptsIcounter,_exceptsIlabels,_exceptsIself,_exceptsIstartLabel) =
                  excepts_ _exceptsOcounter 
              ( _elseIcallLabels,_elseIcontrolFlow,_elseIcounter,_elseIfunLabels,_elseIfunName,_elseIfunParams,_elseIinterFlow,_elseIlabels,_elseIretLabels,_elseIself,_elseIstartLabel,_elseItransFunctions,_elseIupGLabel,_elseIupLabel) =
                  else_ _elseOcallLabels _elseOcounter _elseOdownGLabel _elseOdownLabel _elseOfunLabels _elseOfunName _elseOfunParams _elseOretLabels 
              ( _finallyIcallLabels,_finallyIcontrolFlow,_finallyIcounter,_finallyIfunLabels,_finallyIfunName,_finallyIfunParams,_finallyIinterFlow,_finallyIlabels,_finallyIretLabels,_finallyIself,_finallyIstartLabel,_finallyItransFunctions,_finallyIupGLabel,_finallyIupLabel) =
                  finally_ _finallyOcallLabels _finallyOcounter _finallyOdownGLabel _finallyOdownLabel _finallyOfunLabels _finallyOfunName _finallyOfunParams _finallyOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IWhile :: T_IExpr  ->
                         T_ISuite  ->
                         T_ISuite  ->
                         T_Label  ->
                         T_IStatement 
sem_IStatement_IWhile cond_ body_ else_ label_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: IStatement 
              _lhsOcontrolFlow :: ControlFlow
              _bodyOdownLabel :: ([Label])
              _elseOdownLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              __tup16 :: ((Label,Label))
              _condOcounter :: Label
              _label :: Label
              _lhsOinterFlow :: InterFlow
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _condOcallLabels :: (Map String [(Label, Label)])
              _condOdownGLabel :: ([Label])
              _condOdownLabel :: ([Label])
              _condOfunLabels :: (Map String Label)
              _condOfunName :: String
              _condOfunParams :: (Map String [Var])
              _condOretLabels :: (Map String [Label])
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _elseOcallLabels :: (Map String [(Label, Label)])
              _elseOcounter :: Label
              _elseOdownGLabel :: ([Label])
              _elseOfunLabels :: (Map String Label)
              _elseOfunName :: String
              _elseOfunParams :: (Map String [Var])
              _elseOretLabels :: (Map String [Label])
              _condIcallLabels :: (Map String [(Label, Label)])
              _condIcontrolFlow :: ControlFlow
              _condIcounter :: Label
              _condIfunLabels :: (Map String Label)
              _condIfunName :: String
              _condIfunParams :: (Map String [Var])
              _condIinterFlow :: InterFlow
              _condIlabels :: ([Label])
              _condIretLabels :: (Map String [Label])
              _condIself :: IExpr 
              _condIstartLabel :: ( Maybe Label )
              _condItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _condIupGLabel :: ([Label])
              _condIupLabel :: ([Label])
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _elseIcallLabels :: (Map String [(Label, Label)])
              _elseIcontrolFlow :: ControlFlow
              _elseIcounter :: Label
              _elseIfunLabels :: (Map String Label)
              _elseIfunName :: String
              _elseIfunParams :: (Map String [Var])
              _elseIinterFlow :: InterFlow
              _elseIlabels :: ([Label])
              _elseIretLabels :: (Map String [Label])
              _elseIself :: ISuite 
              _elseIstartLabel :: ( Maybe Label )
              _elseItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _elseIupGLabel :: ([Label])
              _elseIupLabel :: ([Label])
              _labelIself :: Label 
              _lhsOlabels =
                  ({-# LINE 55 "src/Analysis/Python.ag" #-}
                   _label    :(_bodyIlabels ++ _elseIlabels)
                   {-# LINE 11142 "src/Analysis/Python.hs" #-}
                   )
              _lhsOself =
                  ({-# LINE 75 "src/Analysis/Python.ag" #-}
                   IWhile _condIself _bodyIself _elseIself _label
                   {-# LINE 11147 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 162 "src/Analysis/Python.ag" #-}
                   createFlow IntraFlow _exitIWhile     [_label    ] ++ _bodyIcontrolFlow ++ _elseIcontrolFlow
                   {-# LINE 11152 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 163 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 11157 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownLabel =
                  ({-# LINE 164 "src/Analysis/Python.ag" #-}
                   [_label    ]
                   {-# LINE 11162 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 165 "src/Analysis/Python.ag" #-}
                   _elseIupLabel
                   {-# LINE 11167 "src/Analysis/Python.hs" #-}
                   )
              _exitIWhile =
                  ({-# LINE 166 "src/Analysis/Python.ag" #-}
                   nub $ _lhsIdownLabel ++ _bodyIupLabel
                   {-# LINE 11172 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 261 "src/Analysis/Python.ag" #-}
                   let transBodyElse = Map.union _bodyItransFunctions _elseItransFunctions
                   in Map.insert _label     (Unary id) transBodyElse
                   {-# LINE 11178 "src/Analysis/Python.hs" #-}
                   )
              __tup16 =
                  let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, label) -> (__cont, label)} )
              (_condOcounter,_) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup16
                   {-# LINE 11185 "src/Analysis/Python.hs" #-}
                   )
              (_,_label) =
                  ({-# LINE 51 "src/Analysis/Python.ag" #-}
                   __tup16
                   {-# LINE 11190 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _condIinterFlow ++ _bodyIinterFlow ++ _elseIinterFlow
                   {-# LINE 11195 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IWhile _condIself _bodyIself _elseIself _labelIself
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _elseIcallLabels
                   {-# LINE 11202 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _elseIcounter
                   {-# LINE 11207 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _elseIfunLabels
                   {-# LINE 11212 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _elseIfunName
                   {-# LINE 11217 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _elseIfunParams
                   {-# LINE 11222 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _elseIretLabels
                   {-# LINE 11227 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _elseIstartLabel
                   {-# LINE 11232 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _elseIupGLabel
                   {-# LINE 11237 "src/Analysis/Python.hs" #-}
                   )
              _condOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 11242 "src/Analysis/Python.hs" #-}
                   )
              _condOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11247 "src/Analysis/Python.hs" #-}
                   )
              _condOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 11252 "src/Analysis/Python.hs" #-}
                   )
              _condOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 11257 "src/Analysis/Python.hs" #-}
                   )
              _condOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 11262 "src/Analysis/Python.hs" #-}
                   )
              _condOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 11267 "src/Analysis/Python.hs" #-}
                   )
              _condOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 11272 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _condIcallLabels
                   {-# LINE 11277 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _condIcounter
                   {-# LINE 11282 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11287 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _condIfunLabels
                   {-# LINE 11292 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _condIfunName
                   {-# LINE 11297 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _condIfunParams
                   {-# LINE 11302 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _condIretLabels
                   {-# LINE 11307 "src/Analysis/Python.hs" #-}
                   )
              _elseOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 11312 "src/Analysis/Python.hs" #-}
                   )
              _elseOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 11317 "src/Analysis/Python.hs" #-}
                   )
              _elseOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11322 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 11327 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 11332 "src/Analysis/Python.hs" #-}
                   )
              _elseOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 11337 "src/Analysis/Python.hs" #-}
                   )
              _elseOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 11342 "src/Analysis/Python.hs" #-}
                   )
              ( _condIcallLabels,_condIcontrolFlow,_condIcounter,_condIfunLabels,_condIfunName,_condIfunParams,_condIinterFlow,_condIlabels,_condIretLabels,_condIself,_condIstartLabel,_condItransFunctions,_condIupGLabel,_condIupLabel) =
                  cond_ _condOcallLabels _condOcounter _condOdownGLabel _condOdownLabel _condOfunLabels _condOfunName _condOfunParams _condOretLabels 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
              ( _elseIcallLabels,_elseIcontrolFlow,_elseIcounter,_elseIfunLabels,_elseIfunName,_elseIfunParams,_elseIinterFlow,_elseIlabels,_elseIretLabels,_elseIself,_elseIstartLabel,_elseItransFunctions,_elseIupGLabel,_elseIupLabel) =
                  else_ _elseOcallLabels _elseOcounter _elseOdownGLabel _elseOdownLabel _elseOfunLabels _elseOfunName _elseOfunParams _elseOretLabels 
              ( _labelIself) =
                  label_ 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_IStatement_IWith :: T_IContext  ->
                        T_ISuite  ->
                        T_IStatement 
sem_IStatement_IWith context_ body_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: IStatement 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _contextOcounter :: Label
              _bodyOcallLabels :: (Map String [(Label, Label)])
              _bodyOcounter :: Label
              _bodyOdownGLabel :: ([Label])
              _bodyOdownLabel :: ([Label])
              _bodyOfunLabels :: (Map String Label)
              _bodyOfunName :: String
              _bodyOfunParams :: (Map String [Var])
              _bodyOretLabels :: (Map String [Label])
              _contextIcounter :: Label
              _contextIlabels :: ([Label])
              _contextIself :: IContext 
              _contextIstartLabel :: ( Maybe Label )
              _bodyIcallLabels :: (Map String [(Label, Label)])
              _bodyIcontrolFlow :: ControlFlow
              _bodyIcounter :: Label
              _bodyIfunLabels :: (Map String Label)
              _bodyIfunName :: String
              _bodyIfunParams :: (Map String [Var])
              _bodyIinterFlow :: InterFlow
              _bodyIlabels :: ([Label])
              _bodyIretLabels :: (Map String [Label])
              _bodyIself :: ISuite 
              _bodyIstartLabel :: ( Maybe Label )
              _bodyItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _bodyIupGLabel :: ([Label])
              _bodyIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _bodyIcontrolFlow
                   {-# LINE 11409 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _bodyIinterFlow
                   {-# LINE 11414 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _contextIlabels ++ _bodyIlabels
                   {-# LINE 11419 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _bodyItransFunctions
                   {-# LINE 11424 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  IWith _contextIself _bodyIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _bodyIcallLabels
                   {-# LINE 11433 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _bodyIcounter
                   {-# LINE 11438 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _bodyIfunLabels
                   {-# LINE 11443 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _bodyIfunName
                   {-# LINE 11448 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _bodyIfunParams
                   {-# LINE 11453 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _bodyIretLabels
                   {-# LINE 11458 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _bodyIstartLabel
                   {-# LINE 11463 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _bodyIupGLabel
                   {-# LINE 11468 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _bodyIupLabel
                   {-# LINE 11473 "src/Analysis/Python.hs" #-}
                   )
              _contextOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 11478 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 11483 "src/Analysis/Python.hs" #-}
                   )
              _bodyOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _contextIcounter
                   {-# LINE 11488 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11493 "src/Analysis/Python.hs" #-}
                   )
              _bodyOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 11498 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 11503 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 11508 "src/Analysis/Python.hs" #-}
                   )
              _bodyOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 11513 "src/Analysis/Python.hs" #-}
                   )
              _bodyOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 11518 "src/Analysis/Python.hs" #-}
                   )
              ( _contextIcounter,_contextIlabels,_contextIself,_contextIstartLabel) =
                  context_ _contextOcounter 
              ( _bodyIcallLabels,_bodyIcontrolFlow,_bodyIcounter,_bodyIfunLabels,_bodyIfunName,_bodyIfunParams,_bodyIinterFlow,_bodyIlabels,_bodyIretLabels,_bodyIself,_bodyIstartLabel,_bodyItransFunctions,_bodyIupGLabel,_bodyIupLabel) =
                  body_ _bodyOcallLabels _bodyOcounter _bodyOdownGLabel _bodyOdownLabel _bodyOfunLabels _bodyOfunName _bodyOfunParams _bodyOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- ISuite ------------------------------------------------------
-- cata
sem_ISuite :: ISuite  ->
              T_ISuite 
sem_ISuite list  =
    (Prelude.foldr sem_ISuite_Cons sem_ISuite_Nil (Prelude.map sem_IStatement list) )
-- semantic domain
type T_ISuite  = (Map String [(Label, Label)]) ->
                 Label ->
                 ([Label]) ->
                 ([Label]) ->
                 (Map String Label) ->
                 String ->
                 (Map String [Var]) ->
                 (Map String [Label]) ->
                 ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),ISuite ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_ISuite  = Inh_ISuite {callLabels_Inh_ISuite :: (Map String [(Label, Label)]),counter_Inh_ISuite :: Label,downGLabel_Inh_ISuite :: ([Label]),downLabel_Inh_ISuite :: ([Label]),funLabels_Inh_ISuite :: (Map String Label),funName_Inh_ISuite :: String,funParams_Inh_ISuite :: (Map String [Var]),retLabels_Inh_ISuite :: (Map String [Label])}
data Syn_ISuite  = Syn_ISuite {callLabels_Syn_ISuite :: (Map String [(Label, Label)]),controlFlow_Syn_ISuite :: ControlFlow,counter_Syn_ISuite :: Label,funLabels_Syn_ISuite :: (Map String Label),funName_Syn_ISuite :: String,funParams_Syn_ISuite :: (Map String [Var]),interFlow_Syn_ISuite :: InterFlow,labels_Syn_ISuite :: ([Label]),retLabels_Syn_ISuite :: (Map String [Label]),self_Syn_ISuite :: ISuite ,startLabel_Syn_ISuite :: ( Maybe Label ),transFunctions_Syn_ISuite :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_ISuite :: ([Label]),upLabel_Syn_ISuite :: ([Label])}
wrap_ISuite :: T_ISuite  ->
               Inh_ISuite  ->
               Syn_ISuite 
wrap_ISuite sem (Inh_ISuite _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_ISuite _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_ISuite_Cons :: T_IStatement  ->
                   T_ISuite  ->
                   T_ISuite 
sem_ISuite_Cons hd_ tl_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _hdOdownLabel :: ([Label])
              _hdOdownGLabel :: ([Label])
              _tlOdownLabel :: ([Label])
              _tlOdownGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: ISuite 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _hdOcallLabels :: (Map String [(Label, Label)])
              _hdOcounter :: Label
              _hdOfunLabels :: (Map String Label)
              _hdOfunName :: String
              _hdOfunParams :: (Map String [Var])
              _hdOretLabels :: (Map String [Label])
              _tlOcallLabels :: (Map String [(Label, Label)])
              _tlOcounter :: Label
              _tlOfunLabels :: (Map String Label)
              _tlOfunName :: String
              _tlOfunParams :: (Map String [Var])
              _tlOretLabels :: (Map String [Label])
              _hdIcallLabels :: (Map String [(Label, Label)])
              _hdIcontrolFlow :: ControlFlow
              _hdIcounter :: Label
              _hdIfunLabels :: (Map String Label)
              _hdIfunName :: String
              _hdIfunParams :: (Map String [Var])
              _hdIinterFlow :: InterFlow
              _hdIlabels :: ([Label])
              _hdIretLabels :: (Map String [Label])
              _hdIself :: IStatement 
              _hdIstartLabel :: ( Maybe Label )
              _hdItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _hdIupGLabel :: ([Label])
              _hdIupLabel :: ([Label])
              _tlIcallLabels :: (Map String [(Label, Label)])
              _tlIcontrolFlow :: ControlFlow
              _tlIcounter :: Label
              _tlIfunLabels :: (Map String Label)
              _tlIfunName :: String
              _tlIfunParams :: (Map String [Var])
              _tlIinterFlow :: InterFlow
              _tlIlabels :: ([Label])
              _tlIretLabels :: (Map String [Label])
              _tlIself :: ISuite 
              _tlIstartLabel :: ( Maybe Label )
              _tlItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _tlIupGLabel :: ([Label])
              _tlIupLabel :: ([Label])
              _hdOdownLabel =
                  ({-# LINE 119 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 11622 "src/Analysis/Python.hs" #-}
                   )
              _hdOdownGLabel =
                  ({-# LINE 120 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11627 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownLabel =
                  ({-# LINE 121 "src/Analysis/Python.ag" #-}
                   _hdIupLabel
                   {-# LINE 11632 "src/Analysis/Python.hs" #-}
                   )
              _tlOdownGLabel =
                  ({-# LINE 122 "src/Analysis/Python.ag" #-}
                   _hdIupGLabel
                   {-# LINE 11637 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 123 "src/Analysis/Python.ag" #-}
                   maybe _tlIstartLabel (\_ -> _hdIstartLabel) _hdIstartLabel
                   {-# LINE 11642 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _hdIcontrolFlow ++ _tlIcontrolFlow
                   {-# LINE 11647 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _hdIinterFlow ++ _tlIinterFlow
                   {-# LINE 11652 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _hdIlabels ++ _tlIlabels
                   {-# LINE 11657 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _hdItransFunctions `Map.union` _tlItransFunctions
                   {-# LINE 11662 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _tlIcallLabels
                   {-# LINE 11671 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _tlIcounter
                   {-# LINE 11676 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _tlIfunLabels
                   {-# LINE 11681 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _tlIfunName
                   {-# LINE 11686 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _tlIfunParams
                   {-# LINE 11691 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _tlIretLabels
                   {-# LINE 11696 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _tlIupGLabel
                   {-# LINE 11701 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _tlIupLabel
                   {-# LINE 11706 "src/Analysis/Python.hs" #-}
                   )
              _hdOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 11711 "src/Analysis/Python.hs" #-}
                   )
              _hdOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 11716 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 11721 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 11726 "src/Analysis/Python.hs" #-}
                   )
              _hdOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 11731 "src/Analysis/Python.hs" #-}
                   )
              _hdOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 11736 "src/Analysis/Python.hs" #-}
                   )
              _tlOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _hdIcallLabels
                   {-# LINE 11741 "src/Analysis/Python.hs" #-}
                   )
              _tlOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _hdIcounter
                   {-# LINE 11746 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _hdIfunLabels
                   {-# LINE 11751 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _hdIfunName
                   {-# LINE 11756 "src/Analysis/Python.hs" #-}
                   )
              _tlOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _hdIfunParams
                   {-# LINE 11761 "src/Analysis/Python.hs" #-}
                   )
              _tlOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _hdIretLabels
                   {-# LINE 11766 "src/Analysis/Python.hs" #-}
                   )
              ( _hdIcallLabels,_hdIcontrolFlow,_hdIcounter,_hdIfunLabels,_hdIfunName,_hdIfunParams,_hdIinterFlow,_hdIlabels,_hdIretLabels,_hdIself,_hdIstartLabel,_hdItransFunctions,_hdIupGLabel,_hdIupLabel) =
                  hd_ _hdOcallLabels _hdOcounter _hdOdownGLabel _hdOdownLabel _hdOfunLabels _hdOfunName _hdOfunParams _hdOretLabels 
              ( _tlIcallLabels,_tlIcontrolFlow,_tlIcounter,_tlIfunLabels,_tlIfunName,_tlIfunParams,_tlIinterFlow,_tlIlabels,_tlIretLabels,_tlIself,_tlIstartLabel,_tlItransFunctions,_tlIupGLabel,_tlIupLabel) =
                  tl_ _tlOcallLabels _tlOcounter _tlOdownGLabel _tlOdownLabel _tlOfunLabels _tlOfunName _tlOfunParams _tlOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_ISuite_Nil :: T_ISuite 
sem_ISuite_Nil  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOupLabel :: ([Label])
              _lhsOupGLabel :: ([Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: ISuite 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOupLabel =
                  ({-# LINE 124 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 11800 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 125 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 11805 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 126 "src/Analysis/Python.ag" #-}
                   Nothing
                   {-# LINE 11810 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 11815 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 11820 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 11825 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 11830 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 11839 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 11844 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 11849 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 11854 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 11859 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 11864 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- Label -------------------------------------------------------
-- cata
sem_Label :: Label  ->
             T_Label 
sem_Label ( x1)  =
    (sem_Label_Tuple x1 )
-- semantic domain
type T_Label  = ( Label )
data Inh_Label  = Inh_Label {}
data Syn_Label  = Syn_Label {self_Syn_Label :: Label }
wrap_Label :: T_Label  ->
              Inh_Label  ->
              Syn_Label 
wrap_Label sem (Inh_Label )  =
    (let ( _lhsOself) = sem 
     in  (Syn_Label _lhsOself ))
sem_Label_Tuple :: Int ->
                   T_Label 
sem_Label_Tuple x1_  =
    (let _lhsOself :: Label 
         _self =
             (x1_)
         _lhsOself =
             _self
     in  ( _lhsOself))
-- LabelAnnot --------------------------------------------------
-- cata
sem_LabelAnnot :: LabelAnnot  ->
                  T_LabelAnnot 
sem_LabelAnnot (Label1 _l1 )  =
    (sem_LabelAnnot_Label1 (sem_Label _l1 ) )
sem_LabelAnnot (Label2 _l1 _l2 )  =
    (sem_LabelAnnot_Label2 (sem_Label _l1 ) (sem_Label _l2 ) )
sem_LabelAnnot (NoLabel )  =
    (sem_LabelAnnot_NoLabel )
-- semantic domain
type T_LabelAnnot  = ( LabelAnnot )
data Inh_LabelAnnot  = Inh_LabelAnnot {}
data Syn_LabelAnnot  = Syn_LabelAnnot {self_Syn_LabelAnnot :: LabelAnnot }
wrap_LabelAnnot :: T_LabelAnnot  ->
                   Inh_LabelAnnot  ->
                   Syn_LabelAnnot 
wrap_LabelAnnot sem (Inh_LabelAnnot )  =
    (let ( _lhsOself) = sem 
     in  (Syn_LabelAnnot _lhsOself ))
sem_LabelAnnot_Label1 :: T_Label  ->
                         T_LabelAnnot 
sem_LabelAnnot_Label1 l1_  =
    (let _lhsOself :: LabelAnnot 
         _l1Iself :: Label 
         _self =
             Label1 _l1Iself
         _lhsOself =
             _self
         ( _l1Iself) =
             l1_ 
     in  ( _lhsOself))
sem_LabelAnnot_Label2 :: T_Label  ->
                         T_Label  ->
                         T_LabelAnnot 
sem_LabelAnnot_Label2 l1_ l2_  =
    (let _lhsOself :: LabelAnnot 
         _l1Iself :: Label 
         _l2Iself :: Label 
         _self =
             Label2 _l1Iself _l2Iself
         _lhsOself =
             _self
         ( _l1Iself) =
             l1_ 
         ( _l2Iself) =
             l2_ 
     in  ( _lhsOself))
sem_LabelAnnot_NoLabel :: T_LabelAnnot 
sem_LabelAnnot_NoLabel  =
    (let _lhsOself :: LabelAnnot 
         _self =
             NoLabel
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MybExpr -----------------------------------------------------
-- cata
sem_MybExpr :: MybExpr  ->
               T_MybExpr 
sem_MybExpr (Prelude.Just x )  =
    (sem_MybExpr_Just (sem_IExpr x ) )
sem_MybExpr Prelude.Nothing  =
    sem_MybExpr_Nothing
-- semantic domain
type T_MybExpr  = (Map String [(Label, Label)]) ->
                  Label ->
                  ([Label]) ->
                  ([Label]) ->
                  (Map String Label) ->
                  String ->
                  (Map String [Var]) ->
                  (Map String [Label]) ->
                  ( (Map String [(Label, Label)]),ControlFlow,Label,(Map String Label),String,(Map String [Var]),InterFlow,([Label]),(Map String [Label]),MybExpr ,( Maybe Label ),(Map.Map Label (TransferFunction Context Environment)),([Label]),([Label]))
data Inh_MybExpr  = Inh_MybExpr {callLabels_Inh_MybExpr :: (Map String [(Label, Label)]),counter_Inh_MybExpr :: Label,downGLabel_Inh_MybExpr :: ([Label]),downLabel_Inh_MybExpr :: ([Label]),funLabels_Inh_MybExpr :: (Map String Label),funName_Inh_MybExpr :: String,funParams_Inh_MybExpr :: (Map String [Var]),retLabels_Inh_MybExpr :: (Map String [Label])}
data Syn_MybExpr  = Syn_MybExpr {callLabels_Syn_MybExpr :: (Map String [(Label, Label)]),controlFlow_Syn_MybExpr :: ControlFlow,counter_Syn_MybExpr :: Label,funLabels_Syn_MybExpr :: (Map String Label),funName_Syn_MybExpr :: String,funParams_Syn_MybExpr :: (Map String [Var]),interFlow_Syn_MybExpr :: InterFlow,labels_Syn_MybExpr :: ([Label]),retLabels_Syn_MybExpr :: (Map String [Label]),self_Syn_MybExpr :: MybExpr ,startLabel_Syn_MybExpr :: ( Maybe Label ),transFunctions_Syn_MybExpr :: (Map.Map Label (TransferFunction Context Environment)),upGLabel_Syn_MybExpr :: ([Label]),upLabel_Syn_MybExpr :: ([Label])}
wrap_MybExpr :: T_MybExpr  ->
                Inh_MybExpr  ->
                Syn_MybExpr 
wrap_MybExpr sem (Inh_MybExpr _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels )  =
    (let ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel) = sem _lhsIcallLabels _lhsIcounter _lhsIdownGLabel _lhsIdownLabel _lhsIfunLabels _lhsIfunName _lhsIfunParams _lhsIretLabels 
     in  (Syn_MybExpr _lhsOcallLabels _lhsOcontrolFlow _lhsOcounter _lhsOfunLabels _lhsOfunName _lhsOfunParams _lhsOinterFlow _lhsOlabels _lhsOretLabels _lhsOself _lhsOstartLabel _lhsOtransFunctions _lhsOupGLabel _lhsOupLabel ))
sem_MybExpr_Just :: T_IExpr  ->
                    T_MybExpr 
sem_MybExpr_Just just_  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: MybExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _justOcallLabels :: (Map String [(Label, Label)])
              _justOcounter :: Label
              _justOdownGLabel :: ([Label])
              _justOdownLabel :: ([Label])
              _justOfunLabels :: (Map String Label)
              _justOfunName :: String
              _justOfunParams :: (Map String [Var])
              _justOretLabels :: (Map String [Label])
              _justIcallLabels :: (Map String [(Label, Label)])
              _justIcontrolFlow :: ControlFlow
              _justIcounter :: Label
              _justIfunLabels :: (Map String Label)
              _justIfunName :: String
              _justIfunParams :: (Map String [Var])
              _justIinterFlow :: InterFlow
              _justIlabels :: ([Label])
              _justIretLabels :: (Map String [Label])
              _justIself :: IExpr 
              _justIstartLabel :: ( Maybe Label )
              _justItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _justIupGLabel :: ([Label])
              _justIupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   _justIcontrolFlow
                   {-# LINE 12024 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   _justIinterFlow
                   {-# LINE 12029 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _justIlabels
                   {-# LINE 12034 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   _justItransFunctions
                   {-# LINE 12039 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  Just _justIself
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _justIcallLabels
                   {-# LINE 12048 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _justIcounter
                   {-# LINE 12053 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _justIfunLabels
                   {-# LINE 12058 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _justIfunName
                   {-# LINE 12063 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _justIfunParams
                   {-# LINE 12068 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _justIretLabels
                   {-# LINE 12073 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _justIstartLabel
                   {-# LINE 12078 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   _justIupGLabel
                   {-# LINE 12083 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   _justIupLabel
                   {-# LINE 12088 "src/Analysis/Python.hs" #-}
                   )
              _justOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 12093 "src/Analysis/Python.hs" #-}
                   )
              _justOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 12098 "src/Analysis/Python.hs" #-}
                   )
              _justOdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   _lhsIdownGLabel
                   {-# LINE 12103 "src/Analysis/Python.hs" #-}
                   )
              _justOdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   _lhsIdownLabel
                   {-# LINE 12108 "src/Analysis/Python.hs" #-}
                   )
              _justOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 12113 "src/Analysis/Python.hs" #-}
                   )
              _justOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 12118 "src/Analysis/Python.hs" #-}
                   )
              _justOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 12123 "src/Analysis/Python.hs" #-}
                   )
              _justOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 12128 "src/Analysis/Python.hs" #-}
                   )
              ( _justIcallLabels,_justIcontrolFlow,_justIcounter,_justIfunLabels,_justIfunName,_justIfunParams,_justIinterFlow,_justIlabels,_justIretLabels,_justIself,_justIstartLabel,_justItransFunctions,_justIupGLabel,_justIupLabel) =
                  just_ _justOcallLabels _justOcounter _justOdownGLabel _justOdownLabel _justOfunLabels _justOfunName _justOfunParams _justOretLabels 
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
sem_MybExpr_Nothing :: T_MybExpr 
sem_MybExpr_Nothing  =
    (\ _lhsIcallLabels
       _lhsIcounter
       _lhsIdownGLabel
       _lhsIdownLabel
       _lhsIfunLabels
       _lhsIfunName
       _lhsIfunParams
       _lhsIretLabels ->
         (let _lhsOcontrolFlow :: ControlFlow
              _lhsOinterFlow :: InterFlow
              _lhsOlabels :: ([Label])
              _lhsOtransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _lhsOself :: MybExpr 
              _lhsOcallLabels :: (Map String [(Label, Label)])
              _lhsOcounter :: Label
              _lhsOfunLabels :: (Map String Label)
              _lhsOfunName :: String
              _lhsOfunParams :: (Map String [Var])
              _lhsOretLabels :: (Map String [Label])
              _lhsOstartLabel :: ( Maybe Label )
              _lhsOupGLabel :: ([Label])
              _lhsOupLabel :: ([Label])
              _lhsOcontrolFlow =
                  ({-# LINE 98 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 12160 "src/Analysis/Python.hs" #-}
                   )
              _lhsOinterFlow =
                  ({-# LINE 232 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 12165 "src/Analysis/Python.hs" #-}
                   )
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   []
                   {-# LINE 12170 "src/Analysis/Python.hs" #-}
                   )
              _lhsOtransFunctions =
                  ({-# LINE 254 "src/Analysis/Python.ag" #-}
                   Map.empty
                   {-# LINE 12175 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  Nothing
              _lhsOself =
                  _self
              _lhsOcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   _lhsIcallLabels
                   {-# LINE 12184 "src/Analysis/Python.hs" #-}
                   )
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 12189 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   _lhsIfunLabels
                   {-# LINE 12194 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   _lhsIfunName
                   {-# LINE 12199 "src/Analysis/Python.hs" #-}
                   )
              _lhsOfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   _lhsIfunParams
                   {-# LINE 12204 "src/Analysis/Python.hs" #-}
                   )
              _lhsOretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   _lhsIretLabels
                   {-# LINE 12209 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   error "missing rule: MybExpr.Nothing.lhs.startLabel"
                   {-# LINE 12214 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupGLabel =
                  ({-# LINE 107 "src/Analysis/Python.ag" #-}
                   error "missing rule: MybExpr.Nothing.lhs.upGLabel"
                   {-# LINE 12219 "src/Analysis/Python.hs" #-}
                   )
              _lhsOupLabel =
                  ({-# LINE 105 "src/Analysis/Python.ag" #-}
                   error "missing rule: MybExpr.Nothing.lhs.upLabel"
                   {-# LINE 12224 "src/Analysis/Python.hs" #-}
                   )
          in  ( _lhsOcallLabels,_lhsOcontrolFlow,_lhsOcounter,_lhsOfunLabels,_lhsOfunName,_lhsOfunParams,_lhsOinterFlow,_lhsOlabels,_lhsOretLabels,_lhsOself,_lhsOstartLabel,_lhsOtransFunctions,_lhsOupGLabel,_lhsOupLabel)))
-- PairExprMybExpr ---------------------------------------------
-- cata
sem_PairExprMybExpr :: PairExprMybExpr  ->
                       T_PairExprMybExpr 
sem_PairExprMybExpr ( x1,x2)  =
    (sem_PairExprMybExpr_Tuple (sem_IExpr x1 ) x2 )
-- semantic domain
type T_PairExprMybExpr  = Label ->
                          ( Label,([Label]),PairExprMybExpr ,( Maybe Label ))
data Inh_PairExprMybExpr  = Inh_PairExprMybExpr {counter_Inh_PairExprMybExpr :: Label}
data Syn_PairExprMybExpr  = Syn_PairExprMybExpr {counter_Syn_PairExprMybExpr :: Label,labels_Syn_PairExprMybExpr :: ([Label]),self_Syn_PairExprMybExpr :: PairExprMybExpr ,startLabel_Syn_PairExprMybExpr :: ( Maybe Label )}
wrap_PairExprMybExpr :: T_PairExprMybExpr  ->
                        Inh_PairExprMybExpr  ->
                        Syn_PairExprMybExpr 
wrap_PairExprMybExpr sem (Inh_PairExprMybExpr _lhsIcounter )  =
    (let ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel) = sem _lhsIcounter 
     in  (Syn_PairExprMybExpr _lhsOcounter _lhsOlabels _lhsOself _lhsOstartLabel ))
sem_PairExprMybExpr_Tuple :: T_IExpr  ->
                             (Maybe IExpr) ->
                             T_PairExprMybExpr 
sem_PairExprMybExpr_Tuple x1_ x2_  =
    (\ _lhsIcounter ->
         (let _lhsOlabels :: ([Label])
              _lhsOself :: PairExprMybExpr 
              _lhsOcounter :: Label
              _lhsOstartLabel :: ( Maybe Label )
              _x1OcallLabels :: (Map String [(Label, Label)])
              _x1Ocounter :: Label
              _x1OdownGLabel :: ([Label])
              _x1OdownLabel :: ([Label])
              _x1OfunLabels :: (Map String Label)
              _x1OfunName :: String
              _x1OfunParams :: (Map String [Var])
              _x1OretLabels :: (Map String [Label])
              _x1IcallLabels :: (Map String [(Label, Label)])
              _x1IcontrolFlow :: ControlFlow
              _x1Icounter :: Label
              _x1IfunLabels :: (Map String Label)
              _x1IfunName :: String
              _x1IfunParams :: (Map String [Var])
              _x1IinterFlow :: InterFlow
              _x1Ilabels :: ([Label])
              _x1IretLabels :: (Map String [Label])
              _x1Iself :: IExpr 
              _x1IstartLabel :: ( Maybe Label )
              _x1ItransFunctions :: (Map.Map Label (TransferFunction Context Environment))
              _x1IupGLabel :: ([Label])
              _x1IupLabel :: ([Label])
              _lhsOlabels =
                  ({-# LINE 41 "src/Analysis/Python.ag" #-}
                   _x1Ilabels
                   {-# LINE 12278 "src/Analysis/Python.hs" #-}
                   )
              _self =
                  (_x1Iself,x2_)
              _lhsOself =
                  _self
              _lhsOcounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _x1Icounter
                   {-# LINE 12287 "src/Analysis/Python.hs" #-}
                   )
              _lhsOstartLabel =
                  ({-# LINE 44 "src/Analysis/Python.ag" #-}
                   _x1IstartLabel
                   {-# LINE 12292 "src/Analysis/Python.hs" #-}
                   )
              _x1OcallLabels =
                  ({-# LINE 101 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.callLabels"
                   {-# LINE 12297 "src/Analysis/Python.hs" #-}
                   )
              _x1Ocounter =
                  ({-# LINE 37 "src/Analysis/Python.ag" #-}
                   _lhsIcounter
                   {-# LINE 12302 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownGLabel =
                  ({-# LINE 106 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.downGLabel"
                   {-# LINE 12307 "src/Analysis/Python.hs" #-}
                   )
              _x1OdownLabel =
                  ({-# LINE 104 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.downLabel"
                   {-# LINE 12312 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunLabels =
                  ({-# LINE 102 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.funLabels"
                   {-# LINE 12317 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunName =
                  ({-# LINE 99 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.funName"
                   {-# LINE 12322 "src/Analysis/Python.hs" #-}
                   )
              _x1OfunParams =
                  ({-# LINE 103 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.funParams"
                   {-# LINE 12327 "src/Analysis/Python.hs" #-}
                   )
              _x1OretLabels =
                  ({-# LINE 100 "src/Analysis/Python.ag" #-}
                   error "missing rule: PairExprMybExpr.Tuple.x1.retLabels"
                   {-# LINE 12332 "src/Analysis/Python.hs" #-}
                   )
              ( _x1IcallLabels,_x1IcontrolFlow,_x1Icounter,_x1IfunLabels,_x1IfunName,_x1IfunParams,_x1IinterFlow,_x1Ilabels,_x1IretLabels,_x1Iself,_x1IstartLabel,_x1ItransFunctions,_x1IupGLabel,_x1IupLabel) =
                  x1_ _x1OcallLabels _x1Ocounter _x1OdownGLabel _x1OdownLabel _x1OfunLabels _x1OfunName _x1OfunParams _x1OretLabels 
          in  ( _lhsOcounter,_lhsOlabels,_lhsOself,_lhsOstartLabel)))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings  ->
               T_Strings 
sem_Strings list  =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list )
-- semantic domain
type T_Strings  = ( Strings )
data Inh_Strings  = Inh_Strings {}
data Syn_Strings  = Syn_Strings {self_Syn_Strings :: Strings }
wrap_Strings :: T_Strings  ->
                Inh_Strings  ->
                Syn_Strings 
wrap_Strings sem (Inh_Strings )  =
    (let ( _lhsOself) = sem 
     in  (Syn_Strings _lhsOself ))
sem_Strings_Cons :: String ->
                    T_Strings  ->
                    T_Strings 
sem_Strings_Cons hd_ tl_  =
    (let _lhsOself :: Strings 
         _tlIself :: Strings 
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_ 
     in  ( _lhsOself))
sem_Strings_Nil :: T_Strings 
sem_Strings_Nil  =
    (let _lhsOself :: Strings 
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))