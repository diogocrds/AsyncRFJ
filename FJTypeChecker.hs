-- Haskell type checker for Featherweight Java
-- Author: Samuel da Silva Feitosa
-- Date: 01/2018
----------------------------------------------
module FJTypeChecker where
import FJParserA
import FJUtils
import Data.Map
import Data.List
import Data.Either

data TypeError = VariableNotFound String
               | FieldNotFound String
               | ClassNotFound String
               | MethodNotFound String String
               | WrongCast String Term
               | ParamsTypeMismatch [(Term,Type)]
               | UnknownError Term
               deriving (Show,Eq)

-- Function: throwError
-- Objective: Launching a type error.
-- Params: Expected type, Found type, Expression presenting the error.
-- Returns: A type error structure.
----------------------------------------------------------------------
throwError :: TypeError -> Either TypeError Type
throwError e = Left e

-- Function: typeof
-- Objective: Check the type of a given expression.
-- Params: Type context, ClassDef table, Expression.
-- Returns: The type of a given term or a type error.
-----------------------------------------------------
typeof :: Env -> CT -> Input -> Term -> Either TypeError Type
typeof ctx ct input (Int i) = Right (TypeInt)
typeof ctx ct input (Str i) = Right (TypeString)
typeof ctx ct input (Plus a b) =
  case (typeof ctx ct input a) of
    (Right TypeInt) -> case (typeof ctx ct input b) of
                         (Right TypeInt) -> Right TypeInt
                         (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                         _ -> error "OP: non-int type"
    (Right (SignalType TypeInt)) -> case (typeof ctx ct input b) of
                                  (Right TypeInt) -> (Right (SignalType TypeInt))
                                  (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                                  _ -> error "OP: non-int type"
typeof ctx ct input (Minus a b) =  
  case (typeof ctx ct input a) of
    (Right TypeInt) -> case (typeof ctx ct input b) of
                         (Right TypeInt) -> Right TypeInt
                         (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                         _ -> error "OP: non-int type"
    (Right (SignalType TypeInt)) -> case (typeof ctx ct input b) of
                                  (Right TypeInt) -> (Right (SignalType TypeInt))
                                  (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                                  _ -> error "OP: non-int type"
typeof ctx ct input (Times a b) = 
  case (typeof ctx ct input a) of
    (Right TypeInt) -> case (typeof ctx ct input b) of
                         (Right TypeInt) -> Right TypeInt
                         (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                         _ -> error "OP: non-int type"
    (Right (SignalType TypeInt)) -> case (typeof ctx ct input b) of
                                  (Right TypeInt) -> (Right (SignalType TypeInt))
                                  (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                                  _ -> error "OP: non-int type"
typeof ctx ct input (Divide a b) = 
  case (typeof ctx ct input a) of
    (Right TypeInt) -> case (typeof ctx ct input b) of
                         (Right TypeInt) -> Right TypeInt
                         (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                         _ -> error "OP: non-int type"
    (Right (SignalType TypeInt)) -> case (typeof ctx ct input b) of
                                  (Right TypeInt) -> (Right (SignalType TypeInt))
                                  (Right (SignalType TypeInt)) -> (Right (SignalType TypeInt))
                                  _ -> error "OP: non-int type"
typeof ctx ct input (Var v) = -- T-Var
  case (Data.Map.lookup v input) of 
    Just (Var t,_,_) -> Right (SignalType (TypeClass v))
    Just (BooleanLiteral t,_,_) -> Right (SignalType TypeBool)
    Just (Int t,_,_) -> Right (SignalType TypeInt)
    Just (Str t,_,_) -> Right (SignalType TypeString)
    _ -> case (Data.Map.lookup v ctx) of 
           Just var -> return var
           _ -> throwError (VariableNotFound v) 
typeof ctx ct input (BooleanLiteral t) = Right (TypeBool)
typeof ctx ct input (AttrAccess e f) = -- T-Field
  case (typeof ctx ct input e) of
    Right (TypeClass c) ->
      case (fields c ct) of 
        Just flds ->
          case (Data.List.find (\(tp,nm) -> f == nm) flds) of
            Just (tp,nm) -> return tp
            _ -> throwError (FieldNotFound f)
        _ -> throwError (ClassNotFound c)
    _ -> error "Non-object access"
    --e -> e -- Error: Expression type not found
typeof ctx ct input (ThisAccessAttr f) = -- T-Field
  case (Data.Map.lookup "this" ctx) of
    Just (TypeClass c) ->
      case (fields c ct) of 
        Just flds ->
          case (Data.List.find (\(tp,nm) -> f == nm) flds) of
            Just (tp,nm) -> return tp
            _ -> throwError (FieldNotFound f)
        _ -> throwError (ClassNotFound c)
    e -> error "Error: Expression type not found"
typeof ctx ct input (MethodAccess e m p) = -- T-Invk
  case (typeof ctx ct input e) of
    Right (TypeClass c) -> 
      case (mtype m c ct) of 
        Just (pt, rt) -> 
          let tmp = Data.List.zipWith (\e t -> (e, t)) p pt in
            if (Data.List.all (\(e, t') -> 
                  case (typeof ctx ct input e) of
                    Right (TypeClass tp') -> subtyping tp' (getClassType t') ct
                    Right (TypeBool) -> (t'==TypeBool)
                    Right (TypeInt) -> (t'==TypeInt)
                    _ -> False
               ) tmp) then
              return rt
            else
              throwError (ParamsTypeMismatch tmp) 
        _ -> throwError (MethodNotFound m c)
    e -> e -- Error: Expression type not found
typeof ctx ct input (CreateObject c p) = -- T-New
  case (fields c ct) of 
    Just flds -> 
      let tmp = Data.List.zipWith (\e (tp,_) -> (e,tp)) p flds in
        if (Data.List.all (\(e,t) ->
             case (typeof ctx ct input e) of 
               Right (TypeClass tp') -> subtyping tp' (getClassType t) ct
               Right (TypeBool) -> (t==TypeBool)
               Right (TypeInt) -> (t==TypeInt)
               _ -> False
           ) tmp) then
          return (TypeClass c)
        else 
          throwError (ParamsTypeMismatch tmp)
    _ -> throwError (ClassNotFound c)
typeof ctx ct input (Cast c e) = 
  case (typeof ctx ct input e) of 
    Right (TypeClass tp)  
      | (subtyping tp c ct) -> return (TypeClass c) -- T-UCast
      | (subtyping c tp ct) && (c /= tp) -> return (TypeClass c) -- T-DCast
      | (not (subtyping c tp ct)) && (not (subtyping tp c ct)) -> 
          return (TypeClass c) -- T-SCast
      | otherwise -> throwError (WrongCast c e)
    e -> e -- Error: Expression type not found
typeof ctx ct input (Let v t1 t2) = let t1' = typeof ctx ct input t1 -- T-Let
                                        ctx' = Data.Map.insert v (getRight t1') ctx
                                in typeof ctx' ct input t2
typeof ctx ct input (If a t1 t2) = case (typeof ctx ct input a) of  -- T-If
                                Right (TypeBool) ->
                                    case (typeof ctx ct input t1) of
                                        Right ty1 -> case (typeof ctx ct input t2) of
                                            Right ty2 -> if (ty1 == ty2) then Right ty1 else error "IF Error: Non-equal types"
                                t -> error ("IF Error: Non-boolean conditional"++(show ctx))
typeof ctx ct input (ClosureDef p t) = -- T-Lam
  let p' = Data.List.map (\(t,n) -> (n,t)) p
      tp' =  (Data.List.map (\(t,n) -> t) p)
      ctx' = Data.Map.union (Data.Map.fromList p') ctx in
    case (typeof ctx' ct input t) of
      Right t -> Right (TypeClosure t tp')
typeof ctx ct input (InvokeClosure c@(ClosureDef p t1) t) = -- T-Invok
  if ((Data.List.length p)==(Data.List.length t)) then
    let p' = Data.List.zipWith (\(tp,_) tE -> (tp,(typeof ctx ct input tE))) p t in
      if (Data.List.all (\(p1,p2) -> (p1==(getRight p2))) p') then
        case (typeof ctx ct input c) of
          Right (TypeClosure r p) ->  Right r
      else error ("Closure: miss-match type of parameters"++(show p'))
  else error "Closure: params miss-match"
typeof ctx ct input (Lift p e t) = -- T-Lift
    if ((Data.List.length p)==(Data.List.length t)) then
      let p' = Data.List.zipWith (\(tp,_) tE -> (tp,(typeof ctx ct input tE))) p t in
        if (Data.List.all (\(p1,p2) -> (p1==(getRight p2))) p') then
          let ctx' = Data.Map.union (Data.Map.fromList (Data.List.map (\(t,n) -> (n,t)) p)) ctx
          in case (typeof ctx' ct input e) of
            Right t -> Right (SignalType t)
        else error ("Lift: miss-match type of parameters"++(show p'))
    else error "Lift: miss-matched number of parameters"
typeof ctx ct input (Foldp p e acc t) = -- T-Foldp
    if ((Data.List.length p)==2) then
    let p' = Data.List.zipWith (\(tp,_) tE -> (tp,(typeof ctx ct input tE))) p ([t]++[acc]) in
      if (Data.List.all (\(p1,p2) -> (p1==(getRight p2))) p') then
        let ctx' = Data.Map.union (Data.Map.fromList (Data.List.map (\(t,n) -> (n,t)) p)) ctx
        in case (typeof ctx' ct input e) of
          Right t -> Right (SignalType t)
      else error "Foldp: miss-match type of parameters"
    else error "Foldp: miss-matched number of parameters"
typeof ctx ct input (Async e) = typeof ctx ct input e
typeof ctx ct input _ = error "type not found"

getRight :: (Either TypeError Type) -> Type
getRight (Right (TypeClass tp)) = TypeClass tp
getRight (Right (TypeBool)) = TypeBool
getRight (Right (TypeInt)) = TypeInt
getRight (Right (SignalType (TypeClass tp))) = (TypeClass tp)
getRight (Right (SignalType TypeBool)) = TypeBool
getRight (Right (SignalType TypeInt)) = TypeInt
getRight (Right (SignalType TypeString)) = TypeString
getRight (Left (VariableNotFound e)) = error ("Var Error: Declaration not Found."++(show e))
getRight (Left (ParamsTypeMismatch e)) = error "CreateObject Error: Parameters miss-match."
getRight _ = error "nt r"

getClassType :: Type -> String
getClassType (TypeClass t) = t
getClassType _ = ""
-- Function: methodTyping
-- Objective: Check if a method is well formed.
-- Params: MethodDef, ClassDef, Type context, ClassDef table.
-- Returns: True for a well formed method, False otherwise.
-----------------------------------------------------------
methodTyping :: Env -> CT -> ClassDef -> Input -> MethodDef -> Bool
methodTyping ctx ct (ClassDef c b _ _ _) i (MethodDef r m p e) = 
  let p' = Data.List.map (\(t,n) -> (n,t)) p 
      ctx' = Data.Map.union (Data.Map.fromList p') ctx
      ctx'' = Data.Map.insert "this" (TypeClass c) ctx' in
    case (typeof ctx'' ct i e) of 
      Right (TypeClass tp) -> 
        if (subtyping tp (getClassType r) ct) then
          case (mtype m b ct) of 
            Just (pm, rm) -> 
              (pm == (Data.List.map (\(t,n) -> t) p)) && (rm == r)
            _ -> True
        else 
          error "Return type diff"
      Right (TypeBool) -> case (mtype m b ct) of 
                          Just (pm, rm) -> (pm == (Data.List.map (\(t,n) -> t) p)) && (rm == r)
                          _ -> True
      Right (TypeInt) -> case (mtype m b ct) of 
                          Just (pm, rm) -> (pm == (Data.List.map (\(t,n) -> t) p)) && (rm == r)
                          _ -> True
      _ -> error "metT"--False

-- Function: classTyping
-- Objective: Check if a class is well formed.
-- Params: ClassDef, Type context, ClassDef table.
-- Returns: True for a well formed class, False otherwise.
----------------------------------------------------------
classTyping :: ClassDef -> Env -> CT -> Input -> Bool
classTyping cl@(ClassDef c b attrs (ConstrDef cn pc s ths) meths) ctx ct i = 
  case (fields b ct) of 
    Just flds -> 
      if (pc == (flds ++ attrs)) then
        if (Data.List.all (\(n',n'') -> n' == n'') ths) then
          let p' = Data.List.map (\(tp, nm) -> nm) pc 
              p'' = s ++ (Data.List.map (\(n',n'') -> n') ths) 
            in (p' == p'') && (Data.List.all (methodTyping ctx ct cl i) meths)
        else 
          False
      else 
         False
    _ -> False

