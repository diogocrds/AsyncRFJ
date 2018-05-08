-- Utilitary functions for Featherweight Java interpreter
-- Author: Samuel da Silva Feitosa
-- Date: 01/2018
---------------------------------------------------------
module FJUtils where
import FJParserA
import Data.Map
import Data.List

-- Function: subtyping
-- Objective: Check classes for subtyping.
-- Params: ClassDef A, ClassDef B, ClassDef table
-- Returns: Returns if class A is subtype of class B.
-----------------------------------------------------
subtyping :: String -> String -> CT -> Bool
subtyping _ "Object" _ = True
subtyping "Object" _ _ = False
subtyping c c' ct 
    | c == c' = True
    | otherwise = case (Data.Map.lookup c ct) of
                    Just (ClassDef _ c'' _ _ _) -> 
                      if c' == c'' then
                        True
                      else
                        subtyping c'' c' ct
                    _ -> False

-- Function: fields
-- Objective: Search for a class on class table and returns its fields.
-- Params: ClassDef name, ClassDef table.
-- Returns: A monad Maybe containing the field list or Nothing.
-----------------------------------------------------------------------
fields :: String -> CT -> Maybe [(Type,String)]
fields "Object" _ = Just []
fields c ct = case (Data.Map.lookup c ct) of 
                Just (ClassDef _ c'' attrs _ _) ->
                  case (fields c'' ct) of 
                    Just base -> Just (base ++ attrs)
                    _ -> Nothing
                _ -> Nothing

-- Function: methods
-- Objective: Search for a class on class table and returns its methods.
-- Params: ClassDef name, ClassDef table.
-- Returns: A monad Maybe containing the methd list of Nothing.
------------------------------------------------------------------------
methods :: String -> CT -> Maybe [MethodDef]
methods "Object" _ = Just []
methods c ct = case (Data.Map.lookup c ct) of 
                 Just (ClassDef _ c'' _ _ meths) ->
                   case (methods c'' ct) of
                     Just bmeths -> Just (meths ++ bmeths)
                     _ -> Nothing
                 _ -> Nothing


-- Function: mtype
-- Objective: Search for a class on class table, then looks up for a method 
-- and returns its type.
-- Params: MethodDef name, ClassDef name, ClassDef table.
-- Returns: A monad Maybe containing the method type.
---------------------------------------------------------------------------
mtype :: String -> String -> CT -> Maybe ([Type], Type)
mtype _ "Object" _ = Nothing
mtype m c ct = 
  case (Data.Map.lookup c ct) of
    Just (ClassDef _ c' _ _ meths) ->
      case (Data.List.find (\(MethodDef _ n _ _) -> m == n) meths) of
        Just (MethodDef r _ p _) -> Just (Data.List.map (\(tp, nm) -> tp) p, r)
        _ -> mtype m c' ct
    _ -> Nothing

-- Function: mbody
-- Objective: Search for a class on class table, then looks up for a method
-- and returns its body.
-- Params: MethodDef name, ClassDef name, ClassDef table.
-- Returns: A monad Maybe containing the method body or Nothing.
---------------------------------------------------------------------------
mbody :: String -> String -> CT -> Maybe ([String], Term)
mbody _ "Object" _ = Nothing
mbody m c ct = 
  case (Data.Map.lookup c ct) of
    Just (ClassDef _ c' _ _ meths) -> 
      case (Data.List.find (\(MethodDef _ n _ _) -> m == n) meths) of
        Just (MethodDef _ _ p e) -> Just (Data.List.map (\(tp, nm) -> nm) p, e)
        _ -> mbody m c' ct
    _ -> Nothing

-- Function: isValue 
-- Objective: Check if an expression represents a value.
-- Params: Expression, ClassDef table.
-- Returns: Boolean indicating if an expression is a value.
-----------------------------------------------------------
isValue :: CT -> Term -> Bool
isValue _ (CreateObject c []) = True
isValue ct (CreateObject c p) = Data.List.all (isValue ct) p
isValue ct (BooleanLiteral t) = True
isValue ct (Int t) = True
isValue _ _ = False

isSignalValue :: Term -> Bool
isSignalValue (SignalTerm (BooleanLiteral t)) = True
isSignalValue (SignalTerm (Int t)) = True
isSignalValue (SignalTerm (Var t)) = True
isSignalValue _ = False