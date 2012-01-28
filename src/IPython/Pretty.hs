{-# Language TypeSynonymInstances #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      : Language.Python.Version2.Syntax.PrettyAST
-- Copyright   : (c) 2009 Bernie Pope 
-- License     : BSD-style
-- Maintainer  : bjpop@csse.unimelb.edu.au
-- Stability   : experimental
-- Portability : ghc
--
-- Pretty printing of the Python abstract syntax (version 2.x and 3.x). 
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
---
--- ATTENTION: THIS HAS BEEN SHAMELESSLY COPIED FROM THE AFOREMENTIONED
---            MODULE. IT HAS BEEN MODIFIED TO PRINT THE ANNOTATIONS. FOR
---            BENEFIT OF PRINTING OUR LABELS.
---
-----------------------------------------------------------------------------
module IPython.Pretty where
  
import Text.PrettyPrint

-- import Language.Python.Common.Pretty ( Pretty() , pretty, perhaps, commaList)
import Language.Python.Common.AST 

import IPython.AST ( LabelAnnot(..) )

--------------------------------------------------------------------------------

-- | All types which can be transformed into a 'Doc'.
class Pretty a where
   pretty :: a -> Doc

-- | Transform values into strings.
prettyText :: Pretty a => a -> String
prettyText = render . pretty


-- | Print just the prefix of something
prettyPrefix :: Pretty a => Int -> a -> Doc
prettyPrefix maxLen x
   | length fullText <= maxLen = pretty fullText
   | otherwise = pretty (take maxLen fullText) <+> text "..." 
   where
   fullText = prettyText x 

instance Pretty String where
   pretty s = text s

-- | Conditionally wrap parentheses around an item.
parensIf :: Pretty a => (a -> Bool) -> a -> Doc
parensIf test x = if test x then parens $ pretty x else pretty x 

perhaps :: Pretty a => Maybe a -> Doc -> Doc
perhaps Nothing doc = empty
perhaps (Just {}) doc = doc 

-- | A list of things separated by commas.
commaList :: Pretty a => [a] -> Doc
commaList = hsep . punctuate comma . map pretty 

instance Pretty Int where
  pretty = int

instance Pretty Integer where
  pretty = integer

instance Pretty Double where
   pretty = double

instance Pretty Bool where
  pretty True = text "True"
  pretty False = text "False"

instance Pretty a => Pretty (Maybe a) where
   pretty Nothing = empty
   pretty (Just x) = pretty x
   
   
dot :: Doc
dot = char '.'

indent :: Doc -> Doc
indent doc = nest 4 doc

-- XXX is there a better way to do this?
blankLine :: Doc
blankLine = text []

prettyString :: String -> Doc
   -- XXX should handle the escaping properly
-- prettyString str = text (show str)
prettyString str = text str
    

instance Pretty (Module LabelAnnot) where
   pretty (Module stmts) = vcat $ map pretty stmts 

instance Pretty (Ident LabelAnnot) where
   pretty name@(Ident {}) = text $ ident_string name

prettyDottedName :: DottedName LabelAnnot -> Doc
prettyDottedName [] = empty
prettyDottedName [name] = pretty name
prettyDottedName (name:rest@(_:_))
   = pretty name <> dot <> prettyDottedName rest

instance Pretty (ImportItem LabelAnnot) where
   pretty (ImportItem {import_item_name = name, import_as_name = asName})
      = prettyDottedName name <+> (maybe empty (\n -> text "as" <+> pretty n) asName)

instance Pretty (FromItem LabelAnnot) where
   pretty (FromItem { from_item_name = name, from_as_name = asName })
      = pretty name <+> (maybe empty (\n -> text "as" <+> pretty n) asName) 

instance Pretty (FromItems LabelAnnot) where
   pretty ImportEverything {} = char '*'
   pretty (FromItems { from_items_items = [item] }) = pretty item 
   pretty (FromItems { from_items_items = items }) = parens (commaList items)

instance Pretty (ImportRelative LabelAnnot) where
   pretty (ImportRelative { import_relative_dots = dots, import_relative_module = mod }) 
      = case mod of
           Nothing -> dotDoc 
           Just name -> dotDoc <> prettyDottedName name 
      where
      dotDoc = text (replicate dots '.')

prettySuite :: [Statement LabelAnnot] -> Doc
prettySuite stmts = vcat $ map pretty stmts 

optionalKeywordSuite :: String -> [Statement LabelAnnot] -> Doc
optionalKeywordSuite _ [] = empty
optionalKeywordSuite keyword stmts = text keyword <> colon $+$ indent (prettySuite stmts)

prettyParenList :: Pretty a => [a] -> Doc
prettyParenList = parens . commaList 

prettyOptionalList :: Pretty a => [a] -> Doc
prettyOptionalList [] = empty
prettyOptionalList list = parens $ commaList list

prettyGuards :: [(Expr LabelAnnot, Suite LabelAnnot)] -> Doc
prettyGuards [] = empty
prettyGuards ((cond,body):guards)
   = text "elif" <+> pretty cond <> colon $+$ indent (prettySuite body) $+$
     prettyGuards guards
     

instance Pretty (Statement LabelAnnot) where
  pretty s = pretty' s
    where
     pretty' (Import { import_items = items}) = text "import" <+> commaList items 
     pretty' stmt@(FromImport {})
        = text "from" <+> pretty (from_module stmt) <+> text "import" <+> pretty (from_items stmt)
     pretty' stmt@(While {})
        = text "while" <+> pretty (while_cond stmt) <> prettyLabel (annot stmt) colon $+$
          indent (prettySuite (while_body stmt)) $+$ optionalKeywordSuite "else" (while_else stmt)
     pretty' stmt@(For {})
        = text "for" <+> commaList (for_targets stmt) <+> text "in" <+> pretty (for_generator stmt) <> colon $+$
          indent (prettySuite (for_body stmt)) $+$ optionalKeywordSuite "else" (for_else stmt)
     pretty' stmt@(Fun {})
        = text "def" <+> pretty (fun_name stmt) <> parens (commaList (fun_args stmt)) <+> 
          perhaps (fun_result_annotation stmt) (text "->") <+>
          pretty (fun_result_annotation stmt) <> prettyLabel (annot stmt) colon $+$ indent (prettySuite (fun_body stmt)) 
     pretty' stmt@(Class {})
        = text "class" <+> pretty (class_name stmt) <> prettyOptionalList (class_args stmt) <> 
          colon $+$ indent (prettySuite (class_body stmt)) 
     pretty' stmt@(Conditional { cond_guards = guards, cond_else = optionalElse })
        = case guards of
             (cond,body):xs -> 
                text "if" <+> pretty cond <> colon $+$ indent (prettySuite body) $+$ 
                prettyGuards xs $+$
                optionalKeywordSuite "else" optionalElse
     -- XXX is the assign_to always a singleton?
     pretty' a@(Assign { assign_to = pattern, assign_expr = e })
        = prettyLabel (annot a) $ commaList pattern <+> equals <+> pretty e
     pretty' a@(AugmentedAssign { aug_assign_to = to_expr, aug_assign_op = op, aug_assign_expr = e})
        = prettyLabel (annot a) $ pretty to_expr <+> pretty op <+> pretty e 
     pretty' (Decorated { decorated_decorators = decs, decorated_def = stmt})
        = vcat (map pretty decs) $+$ pretty stmt
     pretty' r@(Return { return_expr = e }) = prettyLabel (annot r) $ text "return" <+> pretty e
     pretty' (Try { try_body = body, try_excepts = handlers, try_else = optionalElse, try_finally = finally})
        = text "try" <> colon $+$ indent (prettySuite body) $+$
          prettyHandlers handlers $+$ optionalKeywordSuite "else" optionalElse $+$ 
          optionalKeywordSuite "finally" finally 
     pretty' (Raise { raise_expr = e })
        = text "raise" <+> pretty e
     pretty' (With { with_context = context, with_body = body })
        = text "with" <+> hcat (punctuate comma (map prettyWithContext context)) <+> colon $+$
          indent (prettySuite body)
     pretty' Pass {} = text "pass"
     pretty' Break {} = text "break"
     pretty' Continue {} = text "continue"
     pretty' (Delete { del_exprs = es }) = text "del" <+> commaList es
     pretty' se@(StmtExpr { stmt_expr = e }) = prettyLabel (annot se) (pretty e)
     pretty' (Global { global_vars = idents }) = text "global" <+> commaList idents
     pretty' (NonLocal { nonLocal_vars = idents }) = text "nonlocal" <+> commaList idents
     pretty' (Assert { assert_exprs = es }) = text "assert" <+> commaList es
     pretty' p@(Print { print_chevron = have_chevron, print_exprs = es, print_trailing_comma = trail_comma }) =
        prettyLabel (annot p) $
        text "print" <> (if have_chevron then text " >>" else empty) <+>
        hcat (punctuate comma (map pretty es)) <>
        if trail_comma then comma else empty
     pretty' (Exec { exec_expr = e, exec_globals_locals = gls }) = 
        text "exec" <+> pretty e <+> 
        maybe empty (\ (globals, next) -> text "in" <+> pretty globals <+>
        maybe empty (\locals -> comma <+> pretty locals) next) gls

prettyWithContext :: (Expr LabelAnnot, Maybe (Expr LabelAnnot)) -> Doc
prettyWithContext (e, Nothing) = pretty e
prettyWithContext (e, Just as) = pretty e <+> text "as" <+> pretty as

prettyHandlers :: [Handler LabelAnnot] -> Doc
prettyHandlers = foldr (\next rec -> pretty next $+$ rec) empty


instance Pretty (Handler LabelAnnot) where
   pretty (Handler { handler_clause = exceptClause, handler_suite = suite })
      = pretty exceptClause <> colon $+$ indent (prettySuite suite)

instance Pretty (ExceptClause LabelAnnot) where
   pretty (ExceptClause { except_clause = Nothing }) = text "except"
   pretty (ExceptClause { except_clause = Just (e, target)}) 
      = text "except" <+> pretty e <+> maybe empty (\t -> text "as" <+> pretty t) target

instance Pretty (RaiseExpr LabelAnnot) where
   pretty (RaiseV3 e) = 
      maybe empty (\ (x, fromE) -> pretty x <+> (maybe empty (\f -> text "from" <+> pretty f) fromE)) e
   pretty (RaiseV2 exp) = 
      maybe empty (\ (e1, next1) -> pretty e1 <> 
      maybe empty (\ (e2, next2) -> comma <+> pretty e2 <> 
      maybe empty (\ e3 -> comma <+> pretty e3) next2) next1) exp

instance Pretty (Decorator LabelAnnot) where
   pretty (Decorator { decorator_name = name, decorator_args = args })
      = char '@' <> prettyDottedName name <+> prettyOptionalList args

instance Pretty (Parameter LabelAnnot) where
   pretty p@(Param { param_name = ident, param_py_annotation = annot', param_default = def })
      = prettyLabel (annot p) $ pretty ident <> (maybe empty (\e -> colon <> pretty e <> space) annot') <> 
        maybe empty (\e -> equals <> pretty e) def 
   pretty (VarArgsPos { param_name = ident, param_py_annotation = annot})
      = char '*' <> pretty ident <> (maybe empty (\e -> colon <> pretty e) annot)
   pretty (VarArgsKeyword { param_name = ident, param_py_annotation = annot })
      = text "**" <> pretty ident <> (maybe empty (\e -> colon <> pretty e) annot)
   pretty EndPositional {} = char '*' 
   pretty (UnPackTuple { param_unpack_tuple = tuple, param_default = def })
      = pretty tuple <> maybe empty (\e -> equals <> pretty e) def

instance Pretty (ParamTuple LabelAnnot) where
   pretty (ParamTupleName { param_tuple_name = name }) = pretty name
   pretty (ParamTuple { param_tuple = tuple }) = prettyParenList tuple

instance Pretty (Argument LabelAnnot) where
   pretty a@(ArgExpr { arg_expr = e }) = prettyLabel (annot a) (pretty e)
   pretty a@(ArgVarArgsPos { arg_expr = e}) = prettyLabel (annot a) $ char '*' <> pretty e
   pretty a@(ArgVarArgsKeyword { arg_expr = e }) = prettyLabel (annot a) $ text "**" <> pretty e
   pretty a@(ArgKeyword { arg_keyword = ident, arg_expr = e }) 
      = prettyLabel (annot a) $ pretty ident <> equals <> pretty e

instance Pretty t => Pretty (Comprehension t LabelAnnot) where
   pretty (Comprehension { comprehension_expr = e, comprehension_for = for }) 
      = pretty e <+> pretty for 

instance Pretty (CompFor LabelAnnot) where
   pretty (CompFor { comp_for_exprs = es, comp_in_expr = e, comp_for_iter = iter }) 
      = text "for" <+> commaList es <+> text "in" <+> pretty e <+> pretty iter

instance Pretty (CompIf LabelAnnot) where
   pretty (CompIf { comp_if = e, comp_if_iter = iter }) 
      = text "if" <+> pretty e <+> pretty iter 

instance Pretty (CompIter LabelAnnot) where
   pretty (IterFor { comp_iter_for = compFor }) = pretty compFor 
   pretty (IterIf { comp_iter_if = compIf }) = pretty compIf

instance Pretty (Expr LabelAnnot) where
  pretty e = prettyLabel (annot e) (pretty' e)
   where  
     pretty' (Var { var_ident = i }) = pretty i
     pretty' (Int { expr_literal = str }) = text str 
     pretty' (LongInt { expr_literal = str }) = text str 
     pretty' (Float { expr_literal = str }) = text str 
     pretty' (Imaginary { expr_literal = str }) = text str 
     pretty' (Bool { bool_value = b}) = pretty b
     pretty' None {} = text "None"
     pretty' Ellipsis {} = text "..."
     pretty' (ByteStrings { byte_string_strings = bs }) = hcat (map pretty bs)
     pretty' (Strings { strings_strings = ss }) = hcat (map prettyString ss)
     pretty' (Call { call_fun = f, call_args = args }) = pretty f <> prettyParenList args
     pretty' (Subscript { subscriptee = e, subscript_expr = sub })
        = pretty e <> brackets (pretty sub)
     pretty' (SlicedExpr { slicee = e, slices = ss })
        = pretty e <> brackets (commaList ss) 
     pretty' (CondExpr { ce_true_branch = trueBranch, ce_condition = cond, ce_false_branch = falseBranch })
        = pretty trueBranch <+> text "if" <+> pretty cond <+> text "else" <+> pretty falseBranch
     pretty' (BinaryOp { operator = op, left_op_arg = left, right_op_arg = right })
        = pretty left <> (if isDot op then dot else space <> pretty op <> space) <> pretty right
        where
        isDot (Dot {}) = True
        isDot _other = False
     pretty' (UnaryOp { operator = op, op_arg = e }) = pretty op <+> pretty e
     pretty' (Lambda { lambda_args = args, lambda_body = body })
        = text "lambda" <+> commaList args <> colon <+> pretty body
     pretty' (Tuple { tuple_exprs = [] }) = text "()" 
     pretty' (Tuple { tuple_exprs = es }) = commaList es
     pretty' (Yield { yield_expr = e })
        = text "yield" <+> pretty e
     pretty' (List { list_exprs = es }) = brackets (commaList es)
     pretty' (Dictionary { dict_mappings = mappings })
        = braces (hsep (punctuate comma $ map (\ (e1,e2) -> pretty e1 <> colon <> pretty e2) mappings))
     pretty' (Set { set_exprs = es }) = braces $ commaList es
     pretty' (ListComp { list_comprehension = lc }) = brackets $ pretty lc
     pretty' (Generator { gen_comprehension = gc }) = parens $ pretty gc
     pretty' (Paren { paren_expr = e }) = parens $ pretty e

instance Pretty (Slice LabelAnnot) where
   pretty (SliceProper { slice_lower = lower, slice_upper = upper, slice_stride = stride })
      = pretty lower <> colon <> pretty upper <> (maybe empty (\s -> colon <> pretty s) stride)
   pretty (SliceExpr { slice_expr = e }) = pretty e

instance Pretty (Op LabelAnnot) where
   pretty (And {}) = text "and"
   pretty (Or {}) = text "or"
   pretty (Not {}) = text "not"
   pretty (Exponent {}) = text "**"
   pretty (LessThan {}) = text "<"
   pretty (GreaterThan {}) = text ">"
   pretty (Equality {}) = text "=="
   pretty (GreaterThanEquals {}) = text ">="
   pretty (LessThanEquals {}) = text "<="
   pretty (NotEquals {}) = text "!="
   pretty (NotEqualsV2 {}) = text "<>"
   pretty (In {}) = text "in"
   pretty (Is {}) = text "is"
   pretty (IsNot {}) = text "is not"
   pretty (NotIn {}) = text "not in"
   pretty (BinaryOr {}) = text "|"
   pretty (Xor {}) = text "^"
   pretty (BinaryAnd {}) = text "&"
   pretty (ShiftLeft {}) = text "<<"
   pretty (ShiftRight {}) = text ">>"
   pretty (Multiply {}) = text "*"
   pretty (Plus {}) = text "+"
   pretty (Minus {}) = text "-"
   pretty (Divide {}) = text "/"
   pretty (FloorDivide {}) = text "//"
   pretty (Invert {}) = text "~"
   pretty (Modulo {}) = text "%"
   pretty (Dot {}) = dot

instance Pretty (AssignOp a) where
   pretty (PlusAssign {}) = text "+="
   pretty (MinusAssign {}) = text "-="
   pretty (MultAssign {}) = text "*="
   pretty (DivAssign {}) = text "/="
   pretty (ModAssign {}) = text "%="
   pretty (PowAssign {}) = text "**="
   pretty (BinAndAssign {}) = text "&="
   pretty (BinOrAssign {}) = text "|="
   pretty (BinXorAssign {}) = text "^="
   pretty (LeftShiftAssign {}) = text "<<="
   pretty (RightShiftAssign {}) = text ">>="
   pretty (FloorDivAssign {}) = text "//="
   
prettyLabel :: LabelAnnot -> Doc -> Doc 
prettyLabel l = 
  case l of
    NoLabel -> id
    Label1 l      -> (<+> text ("[" ++ show l ++ "]"))
    Label2 l1 l2  -> (<+> text ("[" ++ show l1 ++ " , " ++ show l2 ++ "]"))