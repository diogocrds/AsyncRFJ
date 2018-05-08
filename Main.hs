module Main where

import FJInterpreter
import FJParserA
import FJTypeChecker
import Data.Foldable
import FJUtils
import Data.List
import Data.Maybe
import Data.Map

printType :: TypedProgram -> Either TypeError Type
printType (TypedProgram ged ct i t) = (typeof Data.Map.empty ct i t)--(Data.Map.fromList ct) (Data.Map.fromList (Data.List.map (\(x,y,z) -> ( x,(y,z) )) i)) t)

printEval :: (EProgram,[(String,Term)]) -> String
printEval ((EProgram (Just e) t),ged) = (show e)++(printThreads t)++"\n\n GED ="++(show ged)

printThreads :: [Thread] -> String
printThreads ((Thread id ctx ct input term ti):hs) = ("\n\n=> Thread "++(show id)++"\n Contex: "++(show ctx)++"\n CT: "++(show ct)++"\n Input: "++(show input)++"\n Term: "++(show term)++"\n T: "++(show ti))++(printThreads hs)
printThreads [] = "."

typecheck :: Program -> TypedProgram
typecheck (Program ct i ged t) = let typeCT = (checkCTable ct i)
                                     typeTerm =(checkTerm ct i t)
                           in if(typeCT && typeTerm) then 
                             let i' = Data.List.map (\(n,t,s) -> (n,(t,s,-1))) i
                             in (TypedProgram ged (Data.Map.fromList ct) (Data.Map.fromList i') t) 
                           else error "Typecheck Error"

checkCTable :: [(String, ClassDef)] -> [(String, Term, Status)] -> Bool
checkCTable ct i = 
            (Data.List.all 
                (\(c,cl) -> classTyping cl Data.Map.empty (Data.Map.fromList ct) (Data.Map.fromList (Data.List.map (\(x,y,z) -> ( x,(y,z,-1) )) i))) (ct))
                
checkTerm :: [(String, ClassDef)] -> [(String, Term, Status)] -> Term -> Bool
checkTerm ct i t = 
            case (typeof Data.Map.empty (Data.Map.fromList ct) (Data.Map.fromList (Data.List.map (\(x,y,z) -> ( x,(y,z,-1) )) i)) t) of
               Right (TypeClass t) -> True
               Right (TypeBool) -> True
               Right (TypeInt) -> True
               Right (SignalType (TypeClass t)) -> True
               Right (SignalType TypeBool) -> True
               Right (SignalType TypeInt) -> True
               Left (VariableNotFound e) -> error ("Var Error: Declaration not Found. "++(show e))
               Left (ParamsTypeMismatch e) -> error ("Error: Parameters miss-match. "++(show e))
               Left (ClassNotFound e) -> error ("Error: Class not Found. "++(show e))
               Left (FieldNotFound e) -> error ("Error: Field Not Found. "++(show e))
               Left (MethodNotFound e s) -> error ("Error: Method Not Found. "++(show e)++", "++(show s))
               t -> error ("Error: "++(show t))
x = Data.Map.fromList [(1,("um",-1)),(2,("d",2)),(3,("t",-1))]
--(Data.Map.mapMaybe ( \(v,i)-> if (i == -1) then (Just (v,i)) else (Just (v,i+1)) ) x)
--(Data.Map.updateAt (\ _ _ -> Just "x") (Data.Map.findIndex 3 x) x)
--(Data.Map.mapWithKey (\id (s,i) -> if id ==2 then (s,i+20) else (s,i)) x)
--[[Change (Int 4),Change (Int 3),NoChange (BooleanLiteral BLTrue),NoChange (Int 12)],[Change (Int 5),Change (Int 4),NoChange (BooleanLiteral BLTrue),NoChange (Int 12)]]
main = do readFile "input.txt" >>= print.evalEvent.evalInit.typecheck.parser.lexer
    

--[(words,""), (mouse.x,0), (mouse.y,0), (Keyboard.shift,true)]

--lift (,) words (lift toFrench words)

--[("bola",1), (22,2), (10,3), ("casa",1)]

--lift ((boolean x,int w, int y) -> if (x) { w+y } else { w-y }) (false,3,5);
--((boolean x,int w, int y) -> if (x) { w+y } else { w-y }).invoke(false,3,5);
--let x = 2 in if (true) {x+2} else {x-2};