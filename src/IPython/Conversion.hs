{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-------------------------------------------------------------------------------
-- Module    :  IPython.Conversion
-- Copyright :  (c) 2011 Marcelo Sousa, Alessandro Vermeulen, Thijs Alkemade
-- Converts the parser result to our AST   
module IPython.Conversion where

import Language.Python.Common

import IPython.AST                

mapConvertStat :: Suite SrcSpan -> ISuite
mapConvertStat = map convertStat

convert :: ModuleSpan -> IModule
convert (Module lstats) = IModule $ mapConvertStat lstats
                                     
convertStat :: Statement SrcSpan -> IStatement
convertStat (Import items _) 				  = IImport          (map convertItem items) defaultStartLabel  						      								       
convertStat (FromImport fimod fitems _)       = IFromImport      (convertImportRelative fimod) (convertFromItems fitems) defaultStartLabel						           
convertStat (While wcond wbody welse _)       = IWhile           (convertExpr wcond) (mapConvertStat wbody) (mapConvertStat welse) defaultStartLabel                       
convertStat (For ftar fgen fbody felse _)     = IFor             (map convertExpr ftar) (convertExpr fgen) (mapConvertStat fbody) (mapConvertStat felse) 
convertStat (Fun fname fargs fres fbody _)    = IFun             (convertIdent fname) (map convertParam fargs) (convertRes fres) (mapConvertStat fbody) defaultStartLabel
convertStat (Class cname cargs cbody _)       = IClass           (convertIdent cname) (map convertArg cargs) (mapConvertStat cbody) 					   
convertStat (Conditional cguards celse _)     = IConditional     (map convertGuard cguards) (mapConvertStat celse)										   
convertStat (Assign ato aexpr _)              = IAssign          (map convertExpr ato) (convertExpr aexpr) defaultStartLabel
convertStat (AugmentedAssign aato aaop aae _) = IAugmentedAssign (convertExpr aato) (convertAssignOp aaop) (convertExpr aae) defaultStartLabel
convertStat (Decorated dlist ddef _)		  = IDecorated 		 (map convertDecorator dlist) (convertStat ddef) 
convertStat (Return rexpr _)                  = IReturn 		 (convertRes rexpr) defaultStartLabel
convertStat (Try tbody texc telse tfin _)     = ITry 			 (mapConvertStat tbody) (map convertHandl texc) (mapConvertStat telse) (mapConvertStat tfin)
convertStat (Raise rexpr _)					  = IRaise			 (convertRaise rexpr) 
convertStat (With wcont wbody _)			  = IWith			 (map convertContext wcont) (mapConvertStat wbody) 
convertStat (Pass _)						  = IPass			 defaultStartLabel
convertStat (Break _)						  = IBreak			 defaultStartLabel
convertStat (Continue _)					  = IContinue		 defaultStartLabel
convertStat (Delete dexprs _)				  = IDelete			 (map convertExpr dexprs) 
convertStat (StmtExpr stexpr _)               = IStmtExpr 		 (convertExpr stexpr) 
convertStat (Global vars _)					  = IGlobal			 (map convertIdent vars) defaultStartLabel
convertStat (NonLocal vars _)				  = INonLocal		 (map convertIdent vars) defaultStartLabel
convertStat (Assert aexpr _)				  = IAssert			 (map convertExpr aexpr) 
convertStat (Print chevron pexpr ptc _)		  = IPrint			 chevron (map convertExpr pexpr) ptc defaultStartLabel
convertStat (Exec eexpr eglobloc _)			  = IExec			 (convertExpr eexpr) (convertGlobLoc eglobloc) 

                                                                  
convertItem :: ImportItem SrcSpan -> IImportItem
convertItem (ImportItem name asname _) = IImportItem (convertDotted name) (fmap convertIdent asname)
                                 
convertImportRelative :: ImportRelative SrcSpan -> IImportRelative
convertImportRelative (ImportRelative dots modul _) = IImportRelative dots (fmap convertDotted modul)

convertFromItems :: FromItems SrcSpan -> IFromItems
convertFromItems (ImportEverything _) = IImportEverything
convertFromItems (FromItems items _)  = IFromItems (map convertFromItem items)

convertFromItem :: FromItem SrcSpan -> IFromItem
convertFromItem (FromItem name asname _) = IFromItem (convertIdent name) (fmap convertIdent asname)
      
convertDecorator :: Decorator SrcSpan -> IDecorator
convertDecorator (Decorator name args _) = IDecorator (convertDotted name) (map convertArg args)

convertHandl :: Handler SrcSpan -> IHandler
convertHandl (Handler clause suite _) = IHandler (convertExceptClause clause) (mapConvertStat suite)

convertExceptClause :: ExceptClause SrcSpan -> IExceptClause
convertExceptClause (ExceptClause clause _) = IExceptClause $ fmap (\(expr,mexpr) -> (convertExpr expr, fmap convertExpr mexpr)) clause

convertRaise :: RaiseExpr SrcSpan -> IRaiseExpr
convertRaise (RaiseV3 raise) = IRaiseV3 $ fmap (\(expr,mexpr) -> (convertExpr expr, fmap convertExpr mexpr)) raise
convertRaise (RaiseV2 raise) = IRaiseV2 $ fmap (\(expr,clause') -> (convertExpr expr, fmap (\(expr',mexpr) -> (convertExpr expr', fmap convertExpr mexpr)) clause')) raise

convertContext :: (Expr SrcSpan, Maybe (Expr SrcSpan)) -> (IExpr, Maybe IExpr)
convertContext (expr, mexpr) = (convertExpr expr, fmap convertExpr mexpr)

convertGlobLoc :: Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)) -> Maybe (IExpr, Maybe IExpr)  
convertGlobLoc = fmap (\(expr, mexpr) -> (convertExpr expr, fmap convertExpr mexpr)) 

convertDotted :: DottedName SrcSpan -> [String]
convertDotted = map convertIdent

convertIdent :: Ident SrcSpan -> String
convertIdent (Ident str _) = str

convertRes :: Maybe (Expr SrcSpan) -> MybExpr
convertRes = fmap convertExpr

type Guard  = (Expr SrcSpan, Suite SrcSpan)           
convertGuard :: Guard -> IGuard
convertGuard (expr,suite) = IGuard (convertExpr expr) 
                                   (mapConvertStat suite)
                                   defaultStartLabel

convertParam :: Parameter SrcSpan -> IParameter
convertParam (Param      pname ppyannot pdefault _) = IParam      (convertIdent pname) (convertRes ppyannot) (convertRes pdefault)
convertParam (VarArgsPos pname ppyannot          _) = IVarArgsPos (convertIdent pname) (convertRes ppyannot)
convertParam _                                      = IParamNotSupported 
              
convertArg :: Argument SrcSpan -> IArgument
convertArg (ArgExpr aexpr _)       = IArgExpr (convertExpr aexpr) defaultStartLabel
convertArg (ArgVarArgsPos aexpr _) = IArgVarArgsPos (convertExpr aexpr)
convertArg _					   = IArgNotSupported
                                             

convertExpr :: Expr SrcSpan -> IExpr
convertExpr (Var       vname        _) | cname == "True"  = IBool True
                                       | cname == "False" = IBool False
                                       | otherwise        = IVar cname
                                       where cname = convertIdent vname
convertExpr (Int       ival expr    _) = IInt ival expr
convertExpr (LongInt   ival expr    _) = ILongInt ival expr
convertExpr (Float     lval expr    _) = IFloat lval expr
convertExpr (Imaginary ival expr    _) = IImaginary ival expr
convertExpr (Bool bval 				_)       = IBool bval
convertExpr (ByteStrings strings    _) = IString strings
convertExpr (Strings     strings    _) = IString strings
convertExpr (None                   _) = INone 
convertExpr (Call cfun cargs        _) = ICall (convertExpr cfun) (map convertArg cargs) defaultStartLabel defaultStartLabel
convertExpr (Subscript s sexpr      _) = ISubscript (convertExpr s) (convertExpr sexpr)
convertExpr (CondExpr ct cc cf      _) = ICondExpr  (convertExpr ct) (convertExpr cc) (convertExpr cf)
convertExpr (BinaryOp op lhs rhs    _) = IBinaryOp  (convertOp op) (convertExpr lhs) (convertExpr rhs)
convertExpr (UnaryOp op arg         _) = IUnaryOp   (convertOp op) (convertExpr arg)
convertExpr (Lambda largs     lexpr _) = ILambda (map convertParam largs) (convertExpr lexpr)
convertExpr (Tuple            lexpr _) = ITuple $ map convertExpr lexpr
convertExpr (List             lexpr _) = IList  $ map convertExpr lexpr
convertExpr (Set              lexpr _) = ISet   $ map convertExpr lexpr
convertExpr (Paren            lexpr _) = IParen (convertExpr lexpr)
convertExpr (StringConversion lexpr _) = IStringConversion $ convertExpr lexpr
convertExpr _                          = IExprNotSupported

convertOp :: Op SrcSpan -> IOp
convertOp (And 				 _) = IAnd
convertOp (Or 				 _) = IOr
convertOp (Not 				 _) = INot
convertOp (Exponent 		 _) = IExponent
convertOp (LessThan 		 _) = ILessThan
convertOp (GreaterThan 		 _) = IGreaterThan
convertOp (Equality 		 _) = IEquality
convertOp (GreaterThanEquals _) = IGreaterThanEquals
convertOp (LessThanEquals 	 _) = ILessThanEquals
convertOp (NotEquals  		 _) = INotEquals
convertOp (NotEqualsV2  	 _) = INotEqualsV2
convertOp (In 				 _) = IIn
convertOp (Is 				 _) = IIs
convertOp (IsNot             _) = IIsNot
convertOp (NotIn             _) = INotIn
convertOp (BinaryOr          _) = IBinaryOr
convertOp (Xor               _) = IXor
convertOp (BinaryAnd         _) = IBinaryAnd
convertOp (ShiftLeft         _) = IShiftLeft
convertOp (ShiftRight        _) = IShiftRight
convertOp (Multiply          _) = IMultiply
convertOp (Plus 	         _) = IPlus
convertOp (Minus 	         _) = IMinus
convertOp (Divide	         _) = IDivide
convertOp (FloorDivide       _) = IFloorDivide
convertOp ( Invert           _) = IInvert
convertOp (Modulo            _) = IModulo
convertOp (Dot               _) = IDot
   
convertAssignOp :: AssignOp SrcSpan -> IAssignOp
convertAssignOp (PlusAssign       _) = IPlusAssign
convertAssignOp (MinusAssign      _) = IMinusAssign
convertAssignOp (MultAssign       _) = IMultAssign
convertAssignOp (DivAssign        _) = IDivAssign
convertAssignOp (ModAssign        _) = IModAssign
convertAssignOp (PowAssign        _) = IPowAssign
convertAssignOp (BinAndAssign     _) = IBinAndAssign
convertAssignOp (BinOrAssign      _) = IBinOrAssign
convertAssignOp (BinXorAssign     _) = IBinXorAssign
convertAssignOp (LeftShiftAssign  _) = ILeftShiftAssign
convertAssignOp (RightShiftAssign _) = IRightShiftAssign
convertAssignOp (FloorDivAssign   _) = IFloorDivAssign

toOp :: IAssignOp -> IOp
toOp IPlusAssign = IPlus
toOp IMinusAssign = IMinus
toOp IMultAssign = IMultiply
toOp IDivAssign = IDivide
toOp IModAssign = IModulo
toOp IPowAssign = IExponent
toOp IBinAndAssign = IBinaryAnd
toOp IBinOrAssign = IBinaryOr
toOp IBinXorAssign = IXor
toOp ILeftShiftAssign = IShiftLeft
toOp IRightShiftAssign = IShiftRight
toOp IFloorDivAssign = IFloorDivide

-- Converting back to the annoted source for pretty printing :)

class From a b where
  from :: a -> b

instance From IModule (Module LabelAnnot) where
  from = fromModule
  
instance From IStatement (Statement LabelAnnot) where
  from = fromStatement
  
instance From IImportItem (ImportItem LabelAnnot) where
  from (IImportItem name asname) = ImportItem (from name) (fmap from asname) NoLabel
  
instance From IImportItems ([ImportItem LabelAnnot ]) where
  from = map from
  
instance From IDottedName (DottedName LabelAnnot) where
  from = map from

instance From String (Ident LabelAnnot) where
  from s = Ident s NoLabel
  
instance From IFromItems (FromItems LabelAnnot) where
  from IImportEverything  = ImportEverything NoLabel
  from (IFromItems items) = FromItems (map from items) NoLabel
  
instance From IFromItem (FromItem LabelAnnot) where
  from (IFromItem name asname) = FromItem (from name) (fmap from asname) NoLabel
    
instance From IImportRelative (ImportRelative LabelAnnot) where
  from (IImportRelative dots modul) = ImportRelative dots (fmap from modul) NoLabel
  
instance From ISuite (Suite LabelAnnot) where
  from = map from
  
instance From IExpr (Expr LabelAnnot) where
  from = fromExpr
  
instance From IExprs ([Expr LabelAnnot]) where
  from = map from
  
instance From IParams [Parameter LabelAnnot] where
  from = map from
  
instance From IParameter (Parameter LabelAnnot) where
  from (IParam pname ppyannot pdefault) = Param (from pname) (from ppyannot) (from pdefault) NoLabel
  from (IVarArgsPos pname ppyannot)     = VarArgsPos (from pname) (from ppyannot) NoLabel

instance From MybExpr (Maybe (Expr LabelAnnot)) where
  from = fmap from

instance From IArgs [Argument LabelAnnot] where
  from = map from
  
instance From IArgument (Argument LabelAnnot) where
  from (IArgExpr aexpr label) = ArgExpr (from aexpr) (Label1 label)
  from (IArgVarArgsPos aexpr) = ArgVarArgsPos (from aexpr) NoLabel
  
instance From IGuard (Expr LabelAnnot, Suite LabelAnnot) where
  from (IGuard expr suite label) = ((from expr) {expr_annot = Label1 label}, from suite) --losing labels here!!! :(
  
instance From IAssignOp (AssignOp LabelAnnot) where
  from IPlusAssign       = PlusAssign       NoLabel
  from IMinusAssign      = MinusAssign      NoLabel
  from IMultAssign       = MultAssign       NoLabel
  from IDivAssign        = DivAssign        NoLabel
  from IModAssign        = ModAssign        NoLabel
  from IPowAssign        = PowAssign        NoLabel
  from IBinAndAssign     = BinAndAssign     NoLabel
  from IBinOrAssign      = BinOrAssign      NoLabel
  from IBinXorAssign     = BinXorAssign     NoLabel
  from ILeftShiftAssign  = LeftShiftAssign  NoLabel
  from IRightShiftAssign = RightShiftAssign NoLabel
  from IFloorDivAssign   = FloorDivAssign   NoLabel

instance From IDecorators [Decorator LabelAnnot] where
  from = map from
  
instance From IDecorator (Decorator LabelAnnot) where
  from (IDecorator name args) = Decorator (from name) (from args) NoLabel
  
instance From IHandler (Handler LabelAnnot) where
  from (IHandler clause suite) = Handler (from clause) (from suite) NoLabel

instance From IExceptClause (ExceptClause LabelAnnot) where
  from (IExceptClause clause) = ExceptClause (fmap (\(expr, mexpr) -> (from expr, fmap from mexpr)) clause) NoLabel

instance From IRaiseExpr (RaiseExpr LabelAnnot) where
  from (IRaiseV3 raise) = RaiseV3 $ fmap (\(expr,mexpr) -> (from expr, fmap from mexpr)) raise
  from (IRaiseV2 raise) = RaiseV2 $ fmap (\(expr,clause') -> (from expr, fmap (\(expr',mexpr) -> (from expr', fmap from mexpr)) clause')) raise
  
instance From IContext [(Expr LabelAnnot, Maybe (Expr LabelAnnot))] where
  from = map from
  
instance From PairExprMybExpr (Expr LabelAnnot, Maybe (Expr LabelAnnot)) where
  from (expr, mexpr) = (from expr, fmap from mexpr)
  
instance From (Maybe PairExprMybExpr) (Maybe (Expr LabelAnnot, Maybe (Expr LabelAnnot))) where
  from = fmap from
  
instance From IOp (Op LabelAnnot) where
  from IAnd 			        = And               NoLabel
  from IOr 				        = Or                NoLabel
  from INot 			        = Not               NoLabel
  from IExponent 	        = Exponent          NoLabel
  from ILessThan 	        = LessThan          NoLabel
  from IGreaterThan 		  = GreaterThan       NoLabel
  from IEquality 		      = Equality          NoLabel
  from IGreaterThanEquals = GreaterThanEquals NoLabel
  from ILessThanEquals 	  = LessThanEquals    NoLabel
  from INotEquals  		    = NotEquals         NoLabel
  from INotEqualsV2  	    = NotEqualsV2       NoLabel
  from IIn 				        = In                NoLabel
  from IIs 				        = Is                NoLabel
  from IIsNot             = IsNot             NoLabel
  from INotIn             = NotIn             NoLabel
  from IBinaryOr          = BinaryOr          NoLabel
  from IXor               = Xor               NoLabel
  from IBinaryAnd         = BinaryAnd         NoLabel
  from IShiftLeft         = ShiftLeft         NoLabel
  from IShiftRight        = ShiftRight        NoLabel
  from IMultiply          = Multiply          NoLabel
  from IPlus 	            = Plus              NoLabel
  from IMinus 	          = Minus             NoLabel
  from IDivide	          = Divide            NoLabel
  from IFloorDivide       = FloorDivide       NoLabel
  from IInvert            = Invert            NoLabel
  from IModulo            = Modulo            NoLabel
  from IDot               = Dot               NoLabel

-- convertContext (expr, mexpr) = (convertExpr expr, fmap convertExpr mexpr)
fromModule :: IModule -> Module LabelAnnot
fromModule (IModule stats) = Module (map from stats)

fromStatement :: IStatement -> Statement LabelAnnot
fromStatement (IImport items label) = Import (from items) (Label1 label)
fromStatement (IFromImport fimod fitems label)       = FromImport (from fimod) (from fitems) (Label1 label)
fromStatement (IWhile wcond wbody welse label)       = While (from wcond) (from wbody) (from welse) (Label1 label)
fromStatement (IFor ftar fgen fbody felse)           = For (from ftar) (from fgen) (from fbody) (from felse) NoLabel
fromStatement (IFun fname fargs fres fbody label)    = Fun (from fname) (from fargs) (from fres) (from fbody) (Label1 label)
fromStatement (IClass cname cargs cbody)             = Class (from cname) (from cargs) (from cbody) NoLabel
fromStatement c@(IConditional cguards celse)           = Conditional (map from cguards) (from celse) NoLabel
fromStatement (IAssign ato aexpr label)              = Assign (map from ato) (from aexpr) (Label1 label)
fromStatement (IAugmentedAssign aato aaop aae label) = AugmentedAssign (from aato) (from aaop) (from aae) (Label1 label)
fromStatement (IDecorated dlist ddef)                = Decorated (from dlist) (from ddef) NoLabel
fromStatement (IReturn rexpr label)                  = Return (from rexpr) (Label1 label)
fromStatement (ITry tbody texc telse tfin)           = Try (from tfin) (map from texc) (map from telse) (from tfin) NoLabel
fromStatement (IRaise rexpr)                         = Raise (from rexpr) NoLabel
fromStatement (IWith wcont wbody)                    = With (map from wcont) (from wbody) NoLabel
fromStatement (IPass label)                          = Pass (Label1 label)
fromStatement (IBreak label)                         = Break (Label1 label)
fromStatement (IContinue label)                      = Continue (Label1 label)
fromStatement (IDelete dexprs)                       = Delete (from dexprs) NoLabel
fromStatement (IStmtExpr stexpr)                     = StmtExpr (from stexpr) NoLabel
fromStatement (IGlobal vars label)                   = Global (map from vars) (Label1 label)
fromStatement (INonLocal vars label)                 = NonLocal (map from vars) (Label1 label)
fromStatement (IAssert aexpr)                        = Assert (map from aexpr) NoLabel
fromStatement (IPrint chevron pexpr ptc label)       = Print chevron (map from pexpr) ptc (Label1 label)
fromStatement (IExec eexpr eglobloc)                 = Exec (from eexpr) (from eglobloc) NoLabel

fromExpr :: IExpr -> Expr LabelAnnot
fromExpr (IVar     ident)         = Var (from ident) NoLabel
fromExpr (IInt     ival expr)     = Int ival expr NoLabel
fromExpr (ILongInt ival expr)     = LongInt ival expr NoLabel
fromExpr (IFloat ival expr)       = Float ival expr NoLabel
fromExpr (IImaginary ival expr)   = Imaginary ival expr NoLabel
fromExpr (IBool    bval       )   = Bool bval NoLabel
fromExpr (IString strings)        = Strings strings NoLabel
fromExpr (INone)                  = None NoLabel
fromExpr (ICall cfun cargs cL rL) = Call (from cfun) (from cargs) (Label2 cL rL)
fromExpr (ISubscript s sexpr)     = Subscript (from s) (from sexpr) NoLabel
fromExpr (ICondExpr ct cc cf)     = CondExpr (from ct) (from cc) (from cf) NoLabel
fromExpr (IBinaryOp op lhs rhs)   = BinaryOp (from op) (from lhs) (from rhs) NoLabel
fromExpr (IUnaryOp op arg)        = UnaryOp (from op) (from arg) NoLabel
fromExpr (ILambda largs lexpr)    = Lambda (from largs) (from lexpr) NoLabel
fromExpr (ITuple lexpr)           = Tuple (from lexpr) NoLabel
fromExpr (IList lexpr)            = List (from lexpr) NoLabel
fromExpr (ISet lexpr)             = Set (map from lexpr) NoLabel
fromExpr (IParen lexpr)           = Paren (from lexpr) NoLabel
fromExpr (IStringConversion expr) = StringConversion (from expr) NoLabel