

{-# LANGUAGE DeriveDataTypeable #-}
-- UUAGC 0.9.38.6 (src/IPython/AST.ag)
module IPython.AST where

import Data.Data  
  
defaultStartLabel :: Label
defaultStartLabel = -1

magicReturnVariable :: String
magicReturnVariable = "*return"

{-# LINE 3 "src/IPython/AST.ag" #-}

-------------------------------------------------------------------------------
-- Module    :  IPython.AST
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade 
-- This AG module contains the AST that we convert the parser result from
-- The analyzed fields are annotated with Label.  
{-# LINE 23 "src/IPython/AST.hs" #-}
-- IArgs -------------------------------------------------------
type IArgs  = [IArgument ]
-- IArgument ---------------------------------------------------
data IArgument  = IArgExpr (IExpr ) (Label ) 
                | IArgNotSupported 
                | IArgVarArgsPos (IExpr ) 
                deriving ( Data,Eq,Show,Typeable)
-- IAssignOp ---------------------------------------------------
data IAssignOp  = IBinAndAssign 
                | IBinOrAssign 
                | IBinXorAssign 
                | IDivAssign 
                | IFloorDivAssign 
                | ILeftShiftAssign 
                | IMinusAssign 
                | IModAssign 
                | IMultAssign 
                | IPlusAssign 
                | IPowAssign 
                | IRightShiftAssign 
                deriving ( Data,Eq,Show,Typeable)
-- IContext ----------------------------------------------------
type IContext  = [PairExprMybExpr ]
-- IDecorator --------------------------------------------------
data IDecorator  = IDecorator (IDottedName ) (IArgs ) 
                 deriving ( Data,Eq,Show,Typeable)
-- IDecorators -------------------------------------------------
type IDecorators  = [IDecorator ]
-- IDottedName -------------------------------------------------
type IDottedName  = [(String)]
-- IExceptClause -----------------------------------------------
data IExceptClause  = IExceptClause ((Maybe IExceptClauseType)) 
                    deriving ( Data,Eq,Show,Typeable)
-- IExceptClauseType -------------------------------------------
type IExceptClauseType  = ( IExpr ,(Maybe IExpr))
-- IExceptClauseType2 ------------------------------------------
type IExceptClauseType2  = ( IExpr ,(Maybe IExceptClauseType))
-- IExpr -------------------------------------------------------
data IExpr  = IBinaryOp (IOp ) (IExpr ) (IExpr ) 
            | IBool (Bool) 
            | ICall (IExpr ) (IArgs ) (Label ) (Label ) 
            | ICondExpr (IExpr ) (IExpr ) (IExpr ) 
            | IExprNotSupported 
            | IFloat (Double) (String) 
            | IImaginary (Double) (String) 
            | IInt (Integer) (String) 
            | ILambda (IParams ) (IExpr ) 
            | IList (IExprs ) 
            | ILongInt (Integer) (String) 
            | INone 
            | IParen (IExpr ) 
            | ISet (IExprs ) 
            | IString (Strings ) 
            | IStringConversion (IExpr ) 
            | ISubscript (IExpr ) (IExpr ) 
            | ITuple (IExprs ) 
            | IUnaryOp (IOp ) (IExpr ) 
            | IVar (String) 
            deriving ( Data,Eq,Show,Typeable)
-- IExprs ------------------------------------------------------
type IExprs  = [IExpr ]
-- IFromItem ---------------------------------------------------
data IFromItem  = IFromItem (String) ((Maybe String)) 
                deriving ( Data,Eq,Show,Typeable)
-- IFromItems --------------------------------------------------
data IFromItems  = IFromItems (ILFromItem ) 
                 | IImportEverything 
                 deriving ( Data,Eq,Show,Typeable)
-- IGuard ------------------------------------------------------
data IGuard  = IGuard (IExpr ) (ISuite ) (Label ) 
             deriving ( Data,Eq,Show,Typeable)
-- IGuards -----------------------------------------------------
type IGuards  = [IGuard ]
-- IHandler ----------------------------------------------------
data IHandler  = IHandler (IExceptClause ) (ISuite ) 
               deriving ( Data,Eq,Show,Typeable)
-- IHandlers ---------------------------------------------------
type IHandlers  = [IHandler ]
-- IIdent ------------------------------------------------------
type IIdent  = ( (String))
-- IIdents -----------------------------------------------------
type IIdents  = [(String)]
-- IImportItem -------------------------------------------------
data IImportItem  = IImportItem (IDottedName ) ((Maybe String)) 
                  deriving ( Data,Eq,Show,Typeable)
-- IImportItems ------------------------------------------------
type IImportItems  = [IImportItem ]
-- IImportRelative ---------------------------------------------
data IImportRelative  = IImportRelative (Int) ((Maybe IDottedName)) 
                      deriving ( Data,Eq,Show,Typeable)
-- ILFromItem --------------------------------------------------
type ILFromItem  = [IFromItem ]
-- IModule -----------------------------------------------------
data IModule  = IModule (ISuite ) 
              deriving ( Data,Eq,Show,Typeable)
-- IOp ---------------------------------------------------------
data IOp  = IAnd 
          | IBinaryAnd 
          | IBinaryOr 
          | IDivide 
          | IDot 
          | IEquality 
          | IExponent 
          | IFloorDivide 
          | IGreaterThan 
          | IGreaterThanEquals 
          | IIn 
          | IInvert 
          | IIs 
          | IIsNot 
          | ILessThan 
          | ILessThanEquals 
          | IMinus 
          | IModulo 
          | IMultiply 
          | INot 
          | INotEquals 
          | INotEqualsV2 
          | INotIn 
          | IOr 
          | IPlus 
          | IShiftLeft 
          | IShiftRight 
          | IXor 
          deriving ( Data,Eq,Show,Typeable)
-- IParameter --------------------------------------------------
data IParameter  = IParam (String) (MybExpr ) (MybExpr ) 
                 | IParamNotSupported 
                 | IVarArgsPos (String) (MybExpr ) 
                 deriving ( Data,Eq,Show,Typeable)
-- IParams -----------------------------------------------------
type IParams  = [IParameter ]
-- IRaiseExpr --------------------------------------------------
data IRaiseExpr  = IRaiseV2 ((Maybe IExceptClauseType2)) 
                 | IRaiseV3 ((Maybe IExceptClauseType)) 
                 deriving ( Data,Eq,Show,Typeable)
-- IStatement --------------------------------------------------
data IStatement  = IAssert (IExprs ) 
                 | IAssign (IExprs ) (IExpr ) (Label ) 
                 | IAugmentedAssign (IExpr ) (IAssignOp ) (IExpr ) (Label ) 
                 | IBreak (Label ) 
                 | IClass (String) (IArgs ) (ISuite ) 
                 | IConditional (IGuards ) (ISuite ) 
                 | IContinue (Label ) 
                 | IDecorated (IDecorators ) (IStatement ) 
                 | IDelete (IExprs ) 
                 | IExec (IExpr ) ((Maybe PairExprMybExpr)) 
                 | IFor (IExprs ) (IExpr ) (ISuite ) (ISuite ) 
                 | IFromImport (IImportRelative ) (IFromItems ) (Label ) 
                 | IFun (String) (IParams ) (MybExpr ) (ISuite ) (Label ) 
                 | IGlobal (IIdents ) (Label ) 
                 | IImport (IImportItems ) (Label ) 
                 | INonLocal (IIdents ) (Label ) 
                 | IPass (Label ) 
                 | IPrint (Bool) (IExprs ) (Bool) (Label ) 
                 | IRaise (IRaiseExpr ) 
                 | IReturn (MybExpr ) (Label ) 
                 | IStmtExpr (IExpr ) 
                 | ITry (ISuite ) (IHandlers ) (ISuite ) (ISuite ) 
                 | IWhile (IExpr ) (ISuite ) (ISuite ) (Label ) 
                 | IWith (IContext ) (ISuite ) 
                 deriving ( Data,Eq,Show,Typeable)
-- ISuite ------------------------------------------------------
type ISuite  = [IStatement ]
-- Label -------------------------------------------------------
type Label  = ( (Int))
-- LabelAnnot --------------------------------------------------
data LabelAnnot  = Label1 (Label ) 
                 | Label2 (Label ) (Label ) 
                 | NoLabel 
                 deriving ( Show)
-- MybExpr -----------------------------------------------------
type MybExpr  = Maybe IExpr 
-- PairExprMybExpr ---------------------------------------------
type PairExprMybExpr  = ( IExpr ,(Maybe IExpr))
-- Strings -----------------------------------------------------
type Strings  = [(String)]