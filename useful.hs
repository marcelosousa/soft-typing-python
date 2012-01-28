{
{--	
attr IModule ISuite IArgs IStatement IGuards IGuard IExpr
  syn labels use {++} {[]} :: {[ Label ]}

attr IStatement ISuite IExpr IExprs IArgument IArgs IGuards IGuard PairExprMybExpr IHandler IHandlers IContext IExceptClauseType IExceptClauseType2 IDecorator IDecorators IParameter IParams MybExpr
  inh prev       :: {[Label]}
  syn nextPrev  use {++} {error "Define!"} :: {[Label]}
  
attr IGuards
  chn lastGuardLabel :: {Label}
  
attr IGuard
  syn guardLabel :: {Label}                

--- Control Flow
attr IModule ISuite IStatement IExpr IArgument IArgs IGuards IGuard
  syn controlFlow use {++} {[]} :: {ControlFlow}
  
attr IModule ISuite IStatement IExpr IArgument IArgs IGuards IGuard
  syn interFlow   use {++} {[]} :: {InterFlow}
  
attr ISuite IStatement IGuards IGuard IHandler IHandlers IArgument IArgs IContext IExpr IExprs IDecorators IExceptClauseType IExceptClauseType2 IDecorator PairExprMybExpr IParameter IParams MybExpr
  inh returnLabel :: {Label}

attr IExpr
  syn isVar :: {Maybe IIdent}

attr IModule ISuite IStatement IExprs IExpr IArgument IArgs IGuard IGuards MybExpr
  syn transferFunctions use {`union_`} {Map.empty} :: {Map.Map Label (TransferFunction Environment (Set.Set Type))}  

-- Function Environment : Match (Start,End) labels for each Function identifier.
{
type FunEnv = Map.Map IIdent (Label, Label)
}

attr IModule 
  syn funEnv :: {FunEnv}

attr IStatement IExpr IExprs IGuard IGuards IParams IArgument IExceptClauseType IExceptClauseType2 PairExprMybExpr IHandler IHandlers IContext IArgs IDecorator IDecorators IParameter MybExpr
  inh funEnv  :: {FunEnv}
  syn funEnv  :: {FunEnv}

attr ISuite
  inh funEnv  :: {FunEnv}
  syn uFunEnv :: {FunEnv}  
  
attr IStatement
  syn updateEnv :: {Maybe (IIdent , (Label, Label))}
    
attr IModule ISuite IStatement IExpr
  syn startLabel :: {Maybe Label}
        
------------------------------
sem MybExpr
	| Just    lhs.transferFunctions = @just.transferFunctions
	| Nothing lhs.transferFunctions = Map.empty


sem IModule 
	| IModule stats.funEnv = Map.empty
	   	      stats.counter = 1
	   	      stats.prev = []
	   	      stats.returnLabel = undefined
	   	      lhs.funEnv = @stats.uFunEnv
	   	      lhs.labels = @stats.labels

sem ISuite
	| Cons lhs.startLabel = case @hd.startLabel of
								Just _  -> @hd.startLabel
								Nothing -> @tl.startLabel
		   hd.funEnv      = @tl.uFunEnv                   
		   tl.funEnv      = case @hd.updateEnv of
								Just (name, labels) -> Map.insert name labels @lhs.funEnv
								Nothing -> @lhs.funEnv
		   hd.prev        = @lhs.prev
		   tl.prev        = @hd.nextPrev
		   lhs.nextPrev   = @tl.nextPrev
		   lhs.labels       = @hd.labels ++ @tl.labels
	| Nil  lhs.startLabel = Just defaultStartLabel
		   lhs.uFunEnv    = @lhs.funEnv   
		   lhs.nextPrev   = @lhs.prev
		   lhs.labels       = []
           
sem IStatement
	| IAssign   lhs.controlFlow = @expr.controlFlow ++ createIntraFlow [@loc.uref] @expr.nextPrev
	            lhs.interFlow   = @expr.interFlow
                 lhs.transferFunctions = Map.insert @loc.uref (Unary $ \env -> traceShow env $ Map.insert (varOf @to.self) (maybe (typesOf env @expr.self) id ((fname @expr.self) >>= (\x -> Map.lookup x @lhs.funEnv) >>= (\x -> (Map.lookup ("*return" ++ (show $ snd $ x)) env)))) env) @expr.transferFunctions
                 lhs.labels = @loc.uref : @expr.labels
                 lhs.nextPrev = [@loc.uref]
                 lhs.startLabel = case @expr.startLabel of
 	                                  Just _ -> @expr.startLabel
 	                                  _      -> @loc.startLabel
  | IAugmentedAssign lhs.controlFlow = @expr.controlFlow ++ @loc.controlFlow
                 lhs.interFlow = @expr.interFlow              
                 lhs.transferFunctions = Map.insert @loc.uref (Unary $ \env -> Map.insert (varOf_ @to.self) (typesOfAugmented (varOf_ @to.self) @op.self env @expr.self) env) @expr.transferFunctions
	| IStmtExpr    lhs.interFlow = @expr.interFlow
	               lhs.self   = IStmtExpr @expr.self (@loc.uref)
	               lhs.transferFunctions = Map.insert @loc.uref (Unary id) @expr.transferFunctions
	               lhs.controlFlow = @loc.controlFlow ++ @expr.controlFlow
 	               lhs.labels = @loc.uref : @expr.labels
 	               lhs.startLabel = case @expr.startLabel of
 	                                  Just _ -> @expr.startLabel
 	                                  _      -> @loc.startLabel
	| IFun       lhs.updateEnv     = Just (@name , (@loc.entry , @loc.return))
				 body.funEnv       = Map.insert @name (@loc.entry , @loc.return) @lhs.funEnv
				 body.returnLabel  = @loc.return
				 loc.entry         = @loc.uref -- Re-use the default label for consistency in the labelling (nice)
				 loc.return        :: uniqueref counter   
				lhs.labels  = @loc.entry : @loc.return : @body.labels
                 lhs.self   = IFun @name @args.self @result.self @body.self @loc.entry @loc.return 
                 body.prev  = [@loc.entry]
                 lhs.controlFlow  = @body.controlFlow
                 lhs.interFlow    = []
                 lhs.nextPrev     = @lhs.prev
                 lhs.transferFunctions = Map.insert (@loc.entry) (Unary id) $ Map.insert @loc.return (Unary id) $ @body.transferFunctions
                 lhs.startLabel   = Nothing
	| IReturn    lhs.transferFunctions = Map.insert (@loc.uref) (Unary (\env -> Map.insert ("*return" ++ (show @lhs.returnLabel)) (mtypesOf env @expr.self) env)) @expr.transferFunctions
                 lhs.controlFlow = @loc.controlFlow ++ [InterFlow (@loc.uref , @lhs.returnLabel)]
  | IConditional lhs.controlFlow = @guards.controlFlow ++ @else.controlFlow
                 lhs.interFlow   = @guards.interFlow   ++ @else.interFlow
	               lhs.self   = IConditional @guards.self @else.self
	               lhs.labels = (@guards.labels ++ @else.labels)
	               lhs.transferFunctions = Map.insert @loc.uref (Unary id) $ @guards.transferFunctions `union_` @else.transferFunctions
                 lhs.nextPrev = (@guards.nextPrev ++ @else.nextPrev)
	               else.prev = [@guards.lastGuardLabel]
	               guards.lastGuardLabel = undefined
  | IWhile       lhs.controlFlow = @cond.controlFlow ++ @body.controlFlow ++ @else.controlFlow
                 lhs.interFlow = @cond.interFlow ++ @body.interFlow ++ @else.interFlow
                 lhs.labels = @loc.uref : (@cond.labels ++ @body.labels ++ @else.labels)
                 lhs.self   = IWhile @cond.self @body.self @else.self
                 lhs.transferFunctions = Map.insert @loc.uref (Unary id) (@cond.transferFunctions `union_` @body.transferFunctions `union_` @else.transferFunctions)
                 lhs.nextPrev = (@cond.nextPrev ++ @body.nextPrev ++ @else.nextPrev)
  | IPrint       lhs.interFlow = []
                 lhs.transferFunctions = Map.insert @loc.uref (Unary id) @exprs.transferFunctions
  | *            loc.controlFlow  = createIntraFlow [@loc.uref] @lhs.prev
                 loc.uref  :: uniqueref counter
  | * - IFun     loc.startLabel = Just @loc.uref
				 lhs.updateEnv = Nothing  
  | * - IFun - IConditional - IAssign - IWhile loc.labels     = [@loc.uref]
                                               lhs.nextPrev   = [@loc.uref]

sem IExpr
  | ICall        lhs.controlFlow = -- flow into the arguments, evaluated left to right
                                   -- then flow to the function Interflow
                                   -- then flow from the exit points to the return site
                                   let (funEntry , funExit) = @loc.funLabels
                                       callFlow =              [IntraFlow (l , @loc.call) | l <- @call_args.nextPrev]
                                                            ++ [InterFlow (@loc.call , funEntry),
                                                                InterFlow (funExit , @loc.return)]
                                   in -- TODO: Fix this! 
                                      @call_args.controlFlow ++ callFlow

                 lhs.interFlow   = let (funEntry , funExit) = @loc.funLabels
                                    in [(@loc.call, funEntry, funExit, @loc.return)]
                 call_args.prev  = @lhs.prev
                 loc.call        :: uniqueref counter
                 loc.return      :: uniqueref counter
                 loc.funLabels   = let funName = case @call_fun.isVar of
                                                  (Just n) -> n
                                                  _        -> errorNoDynamicDispatch @call_fun.self
                                    in findWithDefault (error $ "Cannot find function reference" ++ show @call_fun.self ++ " in " ++ show @lhs.funEnv) funName @lhs.funEnv
                 
                 lhs.self        = ICall @call_fun.self @call_args.self @loc.call @loc.return
                 lhs.labels      = [@loc.call, @loc.return]
                 lhs.transferFunctions = Map.fromList [(@loc.call, Unary id), (@loc.return, Unary id)]
                 lhs.nextPrev    = [@loc.return]
                 lhs.startLabel  = Just @loc.call
  | * - ICall    lhs.nextPrev    = @lhs.prev
                 lhs.interFlow   = []
                 lhs.startLabel  = Nothing
  | IVar         lhs.isVar       = Just @var_ident
  | * - IVar     lhs.isVar       = Nothing
  
sem IArgs
  | Cons   hd.prev        = @lhs.prev
           tl.prev        = @hd.nextPrev
           lhs.nextPrev   = @tl.nextPrev
  | Nil    lhs.nextPrev   = @lhs.prev

sem IGuards
  | Cons   tl.lastGuardLabel = @hd.guardLabel
		   hd.prev        = @lhs.prev
           tl.prev        = @hd.nextPrev
           lhs.nextPrev   = @tl.nextPrev
			lhs.labels       = @hd.labels ++ @tl.labels
  | Nil    lhs.lastGuardLabel = @lhs.lastGuardLabel
		   lhs.nextPrev   = @lhs.prev
			lhs.labels       = []

sem IGuard
  | IGuard              
--                 body.prev       = [@loc.uref]
                 lhs.interFlow   = @body.interFlow
                 lhs.controlFlow = [IntraFlow (l, @loc.uref) | l <- @lhs.prev] ++ @body.controlFlow
--                 lhs.guardLabel  = @loc.uref                
--                 lhs.labels      = @cond.label : @body.labels
--                 lhs.transferFunctions = (Map.fromList [(@loc.uref, Unary id)]) `union_` @body.transferFunctions
--}
}