{-# LANGUAGE FlexibleInstances #-}
-------------------------------------------------------------------------------
-- Module    :  IPython.Typing
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade   
module IPython.Typing where

import Data.Set (Set, empty, singleton, unions, toList, fromList)
import Data.Map (Map, lookup, member, (!))
import Data.Maybe

import IPython.AST
import IPython.Conversion (toOp)

type Context = [Int]

-- According to http://docs.python.org/library/stdtypes.html. 
-- We only support a subset of the BaseType but adding the support for others should be a matter of data-entry.
data BaseType =
    Int
  | Float
  | Long
  | Complex
  | Boolean
  | String
  | Unicode
  | List  { item   :: Set Type   }
  | Tuple { elems  :: [ Set Type ] }
  | Fun   { params :: [ Set Type ] , returnF :: Set Type }
  deriving (Eq, Show, Ord)

instance Show ([BaseType] -> Set BaseType) where
  show a = "analysisFunction"

-- A type can be a base type or the Python type None
data Type =  Type BaseType
          |  None
  deriving (Eq, Show, Ord)
  
type Var = String

-- Our Lattice haskell type
type Environment = Map Var (Set Type)

-- Utility functions to get the types of expressions given a lattice
typesOf :: Environment -> IExpr -> Set Type
typesOf env (IInt _ _)           = singleton $ Type Int
typesOf env (IFloat _ _)         = singleton $ Type Float
typesOf env (IVar x)             = case Data.Map.lookup x env of
                                     Nothing -> empty
                                     Just x  -> x
typesOf env (IBinaryOp op e1 e2) = fromList $ concat [binaryOperatorsTable op t1 t2 | t1 <- toList $ typesOf env e1
                                                                                    , t2 <- toList $ typesOf env e2]
typesOf env (IString _)      = singleton $ Type String
typesOf env (IBool _)        = singleton $ Type Boolean
typesOf env (ILongInt _ _)   = singleton $ Type Long
typesOf env (IImaginary _ _) = singleton $ Type Complex
typesOf env (IList exprs)    = singleton $ Type $ List (unions [typesOf env expr | expr <- exprs])
typesOf env (ICall (IVar x) _ _ _)  | member ("r"++x) env = env ! ("r"++x)
typesOf env x                    = singleton None

mtypesOf :: Environment -> MybExpr -> Set Type
mtypesOf env = maybe empty (typesOf env)

typesOfAugmented :: String -> IAssignOp -> Environment -> IExpr -> Set Type
typesOfAugmented to op env expr = fromList $ concat [binaryOperatorsTable (toOp op) t1 t2 | t1 <- toList $ fromJust $ Data.Map.lookup to env
                                                                                          , t2 <- toList $ typesOf env expr]

-- Debug Function that is used over the project 
fromJustWError :: String -> Maybe a -> a
fromJustWError _ (Just x) = x
fromJustWError str Nothing = error $ "fromJust failed: " ++ str

{-
 - This is how we actually infer the types. If an operation is applied to two terms for which we know the possible types,
 - we can establish the possible types of the result. typesOf is used to combine all the posibilities to a set.
 -
 - This is all based on testing, not on a specification.
 -}
binaryOperatorsTable :: IOp -> Type -> Type -> [Type]
binaryOperatorsTable _ None _ = [None]
binaryOperatorsTable _ _ None = [None]
binaryOperatorsTable IMultiply (Type Float) (Type Int) = [(Type Float)]
binaryOperatorsTable IMultiply (Type Int) (Type Float) = [(Type Float)]
binaryOperatorsTable IMultiply (Type Float) (Type Float) = [(Type Float)]
binaryOperatorsTable IMultiply (Type Int) (Type String) = [(Type String)]
binaryOperatorsTable IMultiply (Type String) (Type Int) = [(Type String)]
binaryOperatorsTable IMultiply (Type Int) (Type Int) = [(Type Int)]
binaryOperatorsTable IMultiply (Type Boolean) (Type Boolean) = [(Type Int)]
binaryOperatorsTable IMultiply (Type Float) (Type Boolean) = [(Type Float)]
binaryOperatorsTable IMultiply (Type Boolean) (Type Float) = [(Type Float)]
binaryOperatorsTable IMultiply (Type Boolean) (Type String) = [(Type String)]
binaryOperatorsTable IMultiply (Type String) (Type Boolean) = [(Type String)]
binaryOperatorsTable IMultiply (Type Complex) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Complex) (Type Float) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Float) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Complex) (Type Int) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Int) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Complex) (Type Boolean) = [(Type Complex)]
binaryOperatorsTable IMultiply (Type Boolean) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IMultiply _ _ = []
binaryOperatorsTable IPlus (Type Int) (Type Int) = [(Type Int)]
binaryOperatorsTable IPlus (Type Int) (Type Float) = [(Type Float)]
binaryOperatorsTable IPlus (Type Float) (Type Int) = [(Type Float)]
binaryOperatorsTable IPlus (Type Float) (Type Float) = [(Type Float)]
binaryOperatorsTable IPlus (Type String) (Type String) = [(Type String)]
binaryOperatorsTable IPlus (Type Boolean) (Type Boolean) = [(Type Int)]
binaryOperatorsTable IPlus (Type Boolean) (Type Int) = [(Type Int)]
binaryOperatorsTable IPlus (Type Int) (Type Boolean) = [(Type Int)]
binaryOperatorsTable IPlus (Type Boolean) (Type Float) = [(Type Float)]
binaryOperatorsTable IPlus (Type Float) (Type Boolean) = [(Type Float)]
binaryOperatorsTable IPlus (Type Complex) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Complex) (Type Float) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Float) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Complex) (Type Int) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Int) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Complex) (Type Boolean) = [(Type Complex)]
binaryOperatorsTable IPlus (Type Boolean) (Type Complex) = [(Type Complex)]
binaryOperatorsTable IPlus _ _ = []
binaryOperatorsTable ILessThan l r =          numericComparison l r
binaryOperatorsTable ILessThanEquals l r =    numericComparison l r
binaryOperatorsTable IGreaterThan l r =       numericComparison l r
binaryOperatorsTable IGreaterThanEquals l r = numericComparison l r 
binaryOperatorsTable _ _ _    = [None]

numericComparison _ _ = [(Type Boolean)]