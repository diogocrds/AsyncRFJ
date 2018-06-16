-- Haskell interpreter for Featherweight Java
-- Author: Samuel da Silva Feitosa
-- Date: 01/2018
---------------------------------------------
module FJInterpreter where
import FJParserA
import FJUtils
import FJTypeChecker
import Data.Maybe
import Data.List
import Data.Map

data Thread = Thread Int EnvG CT Input Term
            | ThreadNull
            deriving (Show,Eq)

data EProgram = EProgram { evalT :: Maybe Term , threads :: [Thread] } deriving (Show,Eq)
data TypedProgram = TypedProgram { env :: [(String, Term)] , ct :: CT , i :: Input  , typedT :: Term} deriving (Show,Eq)

-- Function: eval'
-- Objective: Evaluate an expression.
-- Params: Class table, Expression.
-- Returns: An expression after processing one reduction step.
--------------------------------------------------------------
eval' :: EnvG -> CT -> Input -> Int -> Term -> EProgram
eval' ctx ct input numT (CreateObject c p) = -- RC-New-Arg
  let p' = Data.List.map (\x -> case (eval' ctx ct input numT x) of EProgram (Just x') t -> x') p in (EProgram (Just (CreateObject c p')) [])
eval' ctx ct input numT (SignalTerm (Int v)) = EProgram (Just (SignalTerm (Int v))) []
eval' ctx ct input numT (SignalTerm (BooleanLiteral v)) = EProgram (Just (SignalTerm (BooleanLiteral v))) []
eval' ctx ct input numT (Int v) = EProgram (Just (Int v)) []
eval' ctx ct input numT (BooleanLiteral b) = EProgram (Just (BooleanLiteral b)) []
eval' ctx ct input numT (Var v) = 
  case (Data.Map.lookup v input) of 
    Just (v',_,_) -> EProgram (Just (SignalTerm v')) [] 
    Nothing -> EProgram (Data.Map.lookup v ctx) []
eval' ctx ct input numT (SignalTerm (Var v)) = 
  case eval' ctx ct input numT (Var v) of 
    (EProgram (Just v) t) -> (EProgram (Just v) t)
    _ -> (EProgram (Just (Var v)) [])
eval' ctx ct input numT (Plus a b) = -- R-Plus
  case a of
    (Int a') -> case b of
                  (Int b') -> EProgram (Just (Int (evalOperation (Plus a b)))) []
                  (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Plus a (Int b')))))) []
                  _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Plus a b')
    (SignalTerm (Int a')) -> case b of
                              (Int b') -> EProgram (Just (SignalTerm (Int (evalOperation (Plus (Int a') b))))) []
                              (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Plus (Int a') (Int b')))))) []
                              _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Plus a b')
    _ -> case (eval' ctx ct input numT a) of EProgram (Just a') t -> eval' ctx ct input numT (Plus a' b)
eval' ctx ct input numT (Minus a b) = -- R-Minus
  case a of
    (Int a') -> case b of
                  (Int b') -> EProgram (Just (Int (evalOperation (Minus a b)))) []
                  (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Minus a (Int b')))))) []
                  _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Minus a b')
    (SignalTerm (Int a')) -> case b of
                              (Int b') -> EProgram (Just (SignalTerm (Int (evalOperation (Minus (Int a') b))))) []
                              (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Minus (Int a') (Int b')))))) []
                              _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Minus a b')
    _ -> case (eval' ctx ct input numT a) of EProgram (Just a') t -> eval' ctx ct input numT (Minus a' b)
eval' ctx ct input numT (Divide a b) = -- R-Divide
  case a of
    (Int a') -> case b of
                  (Int b') -> EProgram (Just (Int (evalOperation (Divide a b)))) []
                  (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Divide a (Int b')))))) []
                  _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Divide a b')
    (SignalTerm (Int a')) -> case b of
                              (Int b') -> EProgram (Just (SignalTerm (Int (evalOperation (Divide (Int a') b))))) []
                              (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Divide (Int a') (Int b')))))) []
                              _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Divide a b')
    _ -> case (eval' ctx ct input numT a) of EProgram (Just a') t -> eval' ctx ct input numT (Divide a' b)
eval' ctx ct input numT (Times a b) = -- R-Times
  case a of
    (Int a') -> case b of
                  (Int b') -> EProgram (Just (Int (evalOperation (Times a b)))) []
                  (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Times a (Int b')))))) []
                  _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Times a b')
    (SignalTerm (Int a')) -> case b of
                              (Int b') -> EProgram (Just (SignalTerm (Int (evalOperation (Times (Int a') b))))) []
                              (SignalTerm (Int b')) -> EProgram (Just (SignalTerm (Int (evalOperation (Times (Int a') (Int b')))))) []
                              _ -> case (eval' ctx ct input numT b) of EProgram (Just b') t -> eval' ctx ct input numT (Times a b')
    _ -> case (eval' ctx ct input numT a) of EProgram (Just a') t -> eval' ctx ct input numT (Times a' b)
eval' ctx ct input numT (AttrAccess e f) = 
  if (isValue ct e) then -- R-Field
    case e of 
      (CreateObject c p) ->
        case (fields c ct) of
          Just flds -> 
            case (Data.List.findIndex (\(tp,nm) -> f == nm) flds) of
              Just idx -> EProgram (Just (p !! idx)) []
  else -- RC-Field
    case (eval' ctx ct input numT e) of 
      EProgram (Just e') t -> EProgram (Just (AttrAccess e' f)) t
      _ -> EProgram Nothing []
eval' ctx ct input numT (MethodAccess e m p) =
  if (isValue ct e) then 
    -- R-Invk-Arg
    let p' = Data.List.map (\x -> case (eval' ctx ct input numT x) of EProgram (Just x') t -> x') p in 
      case e of -- R-Invk
        (CreateObject c cp) -> 
          case (mbody m c ct) of
            Just (fpn, e') -> EProgram (subst (fpn ++ ["this"])  (p' ++ [e]) e') []
        _ -> EProgram Nothing []
  else -- R-Invk-Recv
    case (eval' ctx ct input numT e) of 
      EProgram (Just e') t -> EProgram (Just (MethodAccess e' m p)) t
      _ -> EProgram Nothing []
{-eval' ctx ct (Cast c e) = 
  if (isValue ct e) then -- R-Cast
    case e of 
      (CreateObject c' p) -> if (subtyping c' c ct) then
                               Just (CreateObject c' p)
                             else
                               Nothing
  else -- RC-Cast
    case (eval' ctx ct e) of
      Just e' -> Just (Cast c e')
      _ -> Nothing -}
eval' ctx ct input numT (Let v e1 e2) = 
  let e1' = eval' ctx ct input numT e1 -- R-Let
    in case e1 of
        (Lift p e t) -> 
          case e1' of
          (EProgram (Just (SignalTerm e'')) t') ->
            let input' = (Data.Map.insert v (e'',NoChange e'',numT+1) input) 
            in case (eval' ctx ct input' (numT+(length t')) e2) of
                (EProgram (Just e2') t'') -> EProgram (Just e2') (t'++t'')
        (Foldp p e acc t) -> 
          case e1' of
          (EProgram (Just (SignalTerm e'')) t') ->
            let input' = (Data.Map.insert v (e'',NoChange e'',numT+1) input) 
            in case (eval' ctx ct input' (numT+(length t')) e2) of
                (EProgram (Just e2') t'') -> EProgram (Just e2') (t'++t'')
        (Async e) -> 
          case e1' of
          (EProgram (Just (SignalTerm e'')) t') ->
            let input' = (Data.Map.insert v (e'',NoChange e'',numT+1) input) 
            in case (eval' ctx ct input' (numT+(length t')) e2) of
                (EProgram (Just e2') t'') -> EProgram (Just e2') (t'++t'')
        _ -> case e1' of
             (EProgram (Just (SignalTerm e)) t) -> 
               let input' = (Data.Map.insert v (e,NoChange e,-1) input) 
               in case (eval' ctx ct input' numT e2) of (EProgram e2' t') -> EProgram e2' (t++t')
             (EProgram (Just e) t) -> let ctx' = (Data.Map.insert v e ctx) in (eval ctx' ct input numT e2)
eval' ctx ct input numT (If a e1 e2) = -- R-If
    case (eval ctx ct input numT a) of 
      EProgram (Just a') t -> if (a'==(BooleanLiteral BLTrue)) then (eval' ctx ct input numT e1) else (eval' ctx ct input numT e2)
eval' ctx ct input numT (ClosureDef p t) = EProgram (Just (ClosureDef p t)) [] -- R-Closure
eval' ctx ct input numT (InvokeClosure (ClosureDef par e) t) = -- R-InvokeClosure
    let p' = Data.List.zipWith (\(ty,var) (val) -> case (eval' ctx ct input numT val) of (EProgram (Just val') t) -> (var,val')) par t
        ctx' = Data.Map.union (Data.Map.fromList p') ctx
    in eval' ctx' ct input numT e
eval' ctx ct input numT l@(Lift p e t) = -- R-Lift
  let t' = (Data.List.map (\x -> case (eval' ctx ct input (numT+1) x) of EProgram (Just x') r -> r) t)
  in case (eval' ctx ct input (numT+1+(length t')) (InvokeClosure (ClosureDef p e) t)) of
      (EProgram (Just (SignalTerm e')) t'') -> let tList = (Thread (numT+1) ctx ct input l) in EProgram (Just (SignalTerm e')) ([tList]++(Data.List.concat t')++t'')
      (EProgram (Just e') t'') -> let tList = (Thread (numT+1) ctx ct input l) in EProgram (Just (SignalTerm e')) ([tList]++(Data.List.concat t')++t'')
eval' ctx ct input numT f@(Foldp p e acc t) = -- R-Foldp
  let t' = case (eval' ctx ct input (numT+1) t) of (EProgram ev tr) -> tr
      res' = (eval' ctx ct input (numT+1+(length t')) (InvokeClosure (ClosureDef p e) ([t]++[acc])))
      input' = case res' of (EProgram (Just rres) tres) -> (Data.Map.insert "acc" (rres,NoChange rres,-1) input) 
  in case res' of
      (EProgram (Just (SignalTerm e')) t'') -> let tList = (Thread (numT+1) ctx ct input' f) in EProgram (Just (SignalTerm e')) ([tList]++t'++t'')
      (EProgram (Just e') t'') -> let tList = (Thread (numT+1) ctx ct input' f) in EProgram (Just (SignalTerm e')) ([tList]++t'++t'')
eval' ctx ct input numT (SignalTerm (Async e)) = eval' ctx ct input numT (Async e)-- R-Async
eval' ctx ct input numT a@(Async e) = -- R-Async
  let t' = case (eval' ctx ct input (numT+1) e) of (EProgram ev tr) -> tr
      res' = (eval' ctx ct input (numT+1+(length t')) e)
      input' = case res' of (EProgram (Just rres) tres) -> (Data.Map.insert "async" (rres,NoChange rres,-1) input) 
  in case res' of
      (EProgram (Just (SignalTerm e')) t'') -> let tList = (Thread (numT+1) ctx ct input' a) in EProgram (Just (SignalTerm e')) ([tList]++t'++t'')
      (EProgram (Just e') t'') -> let tList = (Thread (numT+1) ctx ct input' a) in EProgram (Just (SignalTerm e')) ([tList]++t'++t'')
      _ -> error ("e: "++(show e)++"/"++(show input)++"/"++(show res'))
eval' _ _ _ numT t = EProgram Nothing []--error ("cant eval "++(show t))

evalOperation :: Term -> Int
evalOperation (Plus (Int a) (Int b)) = a+b
evalOperation (Minus (Int a) (Int b)) = a-b
evalOperation (Divide (Int a) (Int b)) = a `div` b
evalOperation (Times (Int a) (Int b)) = a*b
evalOperation t = error ("op: "++(show t))

findThreadById :: [Thread] -> Int -> Thread
findThreadById (h@(Thread i ctx ct input term):hs) id = if (i == id) then h else (findThreadById hs id)
findThreadById [] id = error "Thread not found."

findThreadByTerm :: [Thread] -> Term -> Thread
findThreadByTerm (h@(Thread i ctx ct input term):hs) t = if (term == t) then h else (findThreadByTerm hs t)
findThreadByTerm [] term = error "Thread not found."

extThreads :: [Thread] -> [Thread] -> (String,Term) -> [(Status,Thread)]
extThreads allT (t@(Thread id ctx ct input term):ts) ged = 
  case (extSingleThread allT t ged) of
    (s,i) -> [(s,(Thread id ctx ct i term))]++(extThreads allT ts ged)
extThreads allT [] ged = []

extSingleThread :: [Thread] -> Thread -> (String, Term) -> (Status,Input)
extSingleThread allT (Thread id ctx ct input term) (v,t) = 
  let old = Data.Map.map (\(t0,st,tr)->case st of Change v -> (t0,NoChange v, tr)
                                                  NoChange v -> (t0,NoChange v, tr)) input
      input' = Data.Map.mapWithKey (\idT (t0,(NoChange st),tr) -> if (idT == v) then (t0,(Change t),tr) else (t0,(NoChange st),tr)) old
  in evalSignal ctx ct input' term allT (v,t)

evalSignal :: EnvG -> CT -> Input -> Term -> [Thread] -> (String,Term) -> (Status,Input)
evalSignal ctx ct input (SignalTerm e) v event = evalSignal ctx ct input e v event
--evalSignal ctx ct input (CreateObject c p) v =
evalSignal ctx ct input (Var e) v event = 
  case (Data.Map.lookup e input) of 
    Just (t,s,i) -> if (i == -1) then (s,input) else case (findThreadById v i) of (thr) -> extSingleThread v thr event
    Nothing -> case (Data.Map.lookup e ctx) of
                Just e' -> (NoChange e',input)
                Nothing -> error "Var not found"
evalSignal ctx ct input (Int e) v event = (NoChange (Int e),input)
evalSignal ctx ct input (BooleanLiteral e) v event = (NoChange (BooleanLiteral e),input)
evalSignal ctx ct input (Plus e1 e2) v event =
  case (evalSignal ctx ct input e1 v event) of
    (NoChange t1,i) -> case (evalSignal ctx ct input e2 v event) of
                    (Change t2,i') -> let t1' = getSignalInt t1
                                          t2' = getSignalInt t2
                                      in (Change (Int (evalOperation (Plus t1' t2'))),input)
                    (NoChange t2,i') -> let t1' = getSignalInt t1
                                            t2' = getSignalInt t2
                                        in (NoChange (Int (evalOperation (Plus t1' t2'))),input)
    (Change t1,i) -> case (evalSignal ctx ct input e2 v event) of
                    (Change t2,i') -> let t1' = getSignalInt t1
                                          t2' = getSignalInt t2
                                      in (Change (Int (evalOperation (Plus t1' t2'))),input)
                    (NoChange t2,i') -> let t1' = getSignalInt t1
                                            t2' = getSignalInt t2
                                        in (Change (Int (evalOperation (Plus t1' t2'))),input)
--evalSignal ctx ct input (Minus e1 e2) v =
--evalSignal ctx ct input (Times e1 e2) v =
--evalSignal ctx ct input (Divide e1 e2) v =
--evalSignal ctx ct input (AttrAccess e f) v =
--evalSignal ctx ct input (MethodAccess e m p) v =
evalSignal ctx ct input (Let var e1 e2) v event = 
  let e1' = evalSignal ctx ct input e1 v event in
    case e1' of
    (Change e,i) -> let ctx' = (Data.Map.insert var e ctx) in 
      case (evalSignal ctx' ct input e2 v event) of
        (Change e2',i') -> (Change e2',input)
        (NoChange e2',i') -> (Change e2',input)
    (NoChange e,i) -> let ctx' = (Data.Map.insert var e ctx) in (evalSignal ctx' ct input e2 v event)
--evalSignal ctx ct input (If a e1 e2) v =
evalSignal ctx ct input (ClosureDef p t) v event = (NoChange (ClosureDef p t),input)
evalSignal ctx ct input (InvokeClosure (ClosureDef par e2) e1) v event =
    let p' = Data.List.zipWith (\(ty,var) (val) -> (var,val)) par e1
        ctx' = Data.Map.union (Data.Map.fromList p') ctx
    in evalSignal ctx' ct input e2 v event
evalSignal ctx ct input (Lift p e e1) v event = --R-ThreadLift
  let e1'' = (Data.List.map (\x -> evalSignal ctx ct input x v event) e1)
      e1' = (Data.List.map (\(x,i) -> x) e1'')
      newE1 = (Data.List.map (\x -> getStatus x) e1')
      changeB = hasChanged e1'
  in if not changeB then (evalSignal ctx ct input (InvokeClosure (ClosureDef p e) newE1) v event)
    else case (evalSignal ctx ct input (InvokeClosure (ClosureDef p e) newE1) v event) of
      (Change v',i) -> (Change v',input)
      (NoChange v',i) -> (Change v',input)
evalSignal ctx ct input (Foldp p e acc e1) v event = --R-ThreadFoldp
  let e1'' = (evalSignal ctx ct input e1 v event)
      e1' = (case e1'' of (x,i) -> x)
      newE1 = (getStatus e1')
      acc' = case (Data.Map.lookup "acc" input) of Just (t0,(NoChange v),tr) -> v
      changeB = case e1' of (Change v) -> True
                            (NoChange v) -> False
      res' = (evalSignal ctx ct input (InvokeClosure (ClosureDef p e) ([newE1]++[acc'])) v event)
      input' = case res' of (NoChange val, i) -> Data.Map.mapWithKey (\idT (t0,st,tr) -> if (idT=="acc") then (t0,(NoChange val),tr) else (t0,st,tr)) input
  in if changeB then case res' of
                       (Change v',i) -> (Change v',input')
                       (NoChange v',i) -> (Change v',input')
     else res'
evalSignal ctx ct input (Async e) v event = --R-ThreadAsync
  case (Data.Map.lookup "async" input) of 
    Just (t0,(NoChange async'),tr) -> let e1'' = (evalSignal ctx ct input e v event)
                                          e1' = (case e1'' of (x,i) -> x)
                                          newE1 = (getStatus e1')
                                          input' = Data.Map.mapWithKey (\idT (t0,st,tr) -> if (idT=="async") then (t0,(NoChange newE1),tr) else (t0,st,tr)) input
                                      in (NoChange async',input')
    _ -> case (findThreadByTerm v (Async e)) of (thr) -> extSingleThread v thr event

evalEvent :: (EProgram, [(String,Term)]) -> [[Status]]
evalEvent ((EProgram (Just e) t), (g:gs)) = 
  let thisT = (extThreads t t g)
      t' = Data.List.map (\(_,newT)->newT) thisT
      s' = Data.List.map (\(newS,_)->newS) thisT
  in [s']++(evalEvent ((EProgram (Just e) t'),gs))
evalEvent ((EProgram (Just e) t), []) = []

evalInit :: TypedProgram -> (EProgram, [(String,Term)])
evalInit (TypedProgram ged ct input t) = ((eval (Data.Map.empty) ct input 0 t),reverse ged)

eval :: EnvG -> CT -> Input -> Int -> Term -> EProgram
eval ctx ct i numT e = 
  case (eval' ctx ct i numT e) of
    (EProgram (Just e') t) -> if ((isValue ct e') || (isSignalValue e')) then EProgram (Just e') t 
        else case eval ctx ct i numT e' of
          EProgram e'' t' -> EProgram e'' (t++t')
    (EProgram Nothing t) -> EProgram (Just e) t
    
hasChanged :: [Status] -> Bool
hasChanged ((Change v):hs) = True || (hasChanged hs)
hasChanged ((NoChange v):hs) = False || (hasChanged hs)
hasChanged [] = False

getStatus :: Status -> Term
getStatus (Change v) = v
getStatus (NoChange v) = v

getSignalInt :: Term -> Term
getSignalInt (Int v) = (Int v)
getSignalInt (SignalTerm (Int v)) = (Int v)
    
-- Function: subst
-- Objective: Replace actual parameters in method body expression. 
-- Params: List of formal parameters names, List of actual parameters,
-- Method body expression.
-- Returns: A new changed expression.
-------------------------------------------
subst :: [String] -> [Term] -> Term -> Maybe Term
subst p v (Var x) = case (Data.List.elemIndex x p) of 
                      Just idx -> Just (v !! idx)
subst p v (Plus a b) = case (subst p v a) of
                        Just a' -> case (subst p v b) of
                                    Just b' -> Just (Plus a' b')
subst p v (AttrAccess e f) = case (subst p v e) of
                                Just e' -> Just (AttrAccess e' f)
subst p v (ThisAccessAttr f) = case (Data.List.elemIndex "this" p) of 
                                Just idx -> Just (AttrAccess (v !! idx) f)
subst p v (MethodAccess e n ap) = 
  let ap' = Data.List.map (\x -> case (subst p v x) of Just x' -> x') ap in
    case (subst p v e) of 
      Just e' -> Just (MethodAccess e' n ap')
subst p v (CreateObject c ap) = 
  let ap' = Data.List.map (\x -> case (subst p v x) of Just x' -> x') ap in
    Just (CreateObject c ap')
subst p v (Cast c e) = case (subst p v e) of 
                         Just e' -> Just (Cast c e')

