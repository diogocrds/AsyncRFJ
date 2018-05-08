{
-- Gerador de um parser para a definição básica do Featherweight JAVA
-- Autor: Samuel da Silva Feitosa
-- Data: 28/05/2014
-------------------------------------------------------------------------------

module FJParserA where
import Data.Char
import Data.Map
}

%name parser
%tokentype { Token }
%error { parseError }

%token
-- Palavras reservadas da linguagem FlyJ
    class	{ TokenKWClass }
    extends	{ TokenKWExtends }
    super	{ TokenKWSuper }
    this	{ TokenKWThis }
    new		{ TokenKWNew }
    return	{ TokenKWReturn }
    Object	{ TokenKWObject }
    if 		{ TokenKWIf }
    else	{ TokenKWElse }
    let		{ TokenKWLet }
    in		{ TokenKWIn }
    invoke	{ TokenKWInvoke }
    boolean	{ TokenKWBoolean }
    true	{ TokenKWTrue }
    false	{ TokenKWFalse }
    int     { TokenKWInt }
    lift    { TokenKWLift }
-- Caracteres especiais
    '{'		{ TokenLBrace }
    '}'		{ TokenRBrace }
    '('		{ TokenLParen }
    ')'		{ TokenRParen }
    ','		{ TokenComma }
    ';'		{ TokenSemi }
    '.'		{ TokenDot }
    '='		{ TokenAssign }
    '<'		{ TokenLT }
    '>'         { TokenGT }
    "->"	{ TokenArrow }
    '*'		{ TokenTimes }
    '/'		{ TokenDivide }
    '+'		{ TokenPlus }
    '-'		{ TokenMinus }
    "=="    { TokenEqual }
-- Nomes definidos pelo programador (classes, metodos, atributos)
    name	{ TokenName $$ }
    number	{ TokenNumber $$ }

-- Definição de precedências
%nonassoc "==" 
%right in
%right '+'
%right '-'
%left '*'

%%

-- Codigos do programa
Program		: ClassList InputList EventList Term ';' 		{ Program $1 $2 $3 $4 }

-- Lista de Inputs
InputList   : '{' InputDefList '}'                          { $2 }

InputDefList : '(' name ',' Term ')'                        { [($2,$4,(NoChange $4))] }
        | InputDefList ',' '(' name ',' Term ')'            { ($4,$6,(NoChange $6)):$1 }

-- Lista de Events
EventList   : '{' EventDefList '}'                             { $2 }

EventDefList : '(' name ',' Term ')'                        { [($2,$4)] }
        | EventDefList ',' '(' name ',' Term ')'            { ($4,$6):$1 }

-- Lista de classes
ClassList	: ClassDef									    { [$1] }
		| ClassList ClassDef							    { $2 : $1 }

-- Definicao de classe
ClassDef	: class ClassName extends ClassName '{' AttrList ConstrDef MethodList '}' { ($2,ClassDef $2 $4 $6 $7 $8) }

-- Definicao de construtor
ConstrDef	: ClassName '(' ParamList ')' '{' super '(' ArgList ')' ';' AttrAssignList '}'	{ ConstrDef $1 $3 $8 $11 }

-- Lista de implementacao de metodos
MethodList	: {- empty -}									{ [] }
		| MethodList MethodDef								{ $2 : $1 }

-- Definicao de metodos
--MethodDef	: GenericDefList TypeDef name '(' ParamList ')' '{' return Term ';' '}'		{ MethodDef $1 $2 $3 $5 $9 }
MethodDef	: TypeDef name '(' ParamList ')' '{' return Term ';' '}'			{ MethodDef $1 $2 $4 $8 }

-- Lista de declaracao de parametros para construtores e definicao de funcoes 
-- Parametros Formais
ParamList	: {- empty -}									{ [] }
		| IdentStmt									        { [$1] }
		| ParamList ',' IdentStmt							{ $3 : $1 }

-- Lista de argumentos utilizados para passar informações nas chamadas de funções
-- Parametros Atuais
ArgList		: {- empty -}									{ [] }
		| name										        { [$1] }
		| ArgList ',' name								    { $3 : $1 }

-- Lista de atributos de classe (declaracao)
AttrList	: {- empty -}									{ [] }
		| AttrList IdentStmt ';'							{ $2 : $1 }

-- Lista de atribuicao interna de atributos (utilizada no construtor da classe)
AttrAssignList 	: {- empty -}								{ [] }
		| AttrAssign									    { [$1] }
		| AttrAssignList AttrAssign							{ $2 : $1 }

-- Atribuicao interna de atributos
AttrAssign	: this '.' name '=' name ';'					{ ($3,$5) }

-- Definicao de atributos ou parametros
IdentStmt	: TypeDef name									{ ($1,$2) }

-- Definicao de tipos
TypeDef		: boolean									    { TypeBool }
		| ClassName								            { TypeClass $1 }
		| '(' TypeList "->" TypeDef ')'						{ TypeClosure $4 $2 }
		| '{' TypeList '}'								    { TypeTuple $2 }
        | int                                             { TypeInt }

-- Lista de tipos utilizados para as Closures
TypeList 	: {- empty -}									{ [] }
		| TypeDef									        { [$1] }
		| TypeList ',' TypeDef								{ $3 : $1 }

-- Definicao de tipos genericos
GenericDefList	: {- empty -}								{ [] }
		| '<' ExtendsList '>'								{ $2 }

ExtendsList	: ClassName extends ClassName					{ [($1,$3)] }
		| ExtendsList ',' ClassName extends ClassName		{ ($3,$5) : $1 }

GenericList	: {- empty -}									{ [] }
		| '<' TypeList '>'								    { $2 }

--ClassNameList 	: ClassName								{ [$1] }
--		| ClassNameList ',' ClassName						{ $3 : $1 }

-- Nomes de classes
ClassName	: Object									    { "Object" }
		| name										        { $1 }

-- Lista de termos
TermList	: {- empty -}									{ [] }
		| Term										        { [$1] }
		| TermList ',' Term								    { $3 : $1 }

-- Termos (utilizados no corpo dos métodos)
Term		: BooleanLiteral								{ BooleanLiteral $1 }
		| name										        { Var $1 }
		| this '.' name									    { ThisAccessAttr $3 }
		| this '.' name '(' TermList ')'					{ ThisAccessMeth $3 $5 }
		| Term '.' name									    { AttrAccess $1 $3 }
--		| Term '.' name '(' TermList ')'		            { MethodAccess $1 $3 $5 }
		| Term '.' name '(' TermList ')'					{ MethodAccess $1 $3 $5 }
		| new ClassName '(' TermList ')'		            { CreateObject $2 $4 }
		| '(' ClassName ')' Term							{ Cast $2 $4 }
		| if '(' Term ')' '{' Term '}' else '{' Term '}'	{ If $3 $6 $10 }
		| let name '=' Term in Term							{ Let $2 $4 $6 }
		| '(' ParamList ')' "->" Term					    { ClosureDef $2 $5 }
		| '(' Term ')' '.' invoke '(' TermList ')' 			{ InvokeClosure $2 $7 }
		| '{' TermList '}'	 							    { Tuple $2 }
		| Term '.' number								    { TupleAccess $1 $3 }
		| Term "==" Term								    { RelEquals $1 $3 }
        | number                                            { Int $1 }
        | Term '*' Term                                     { Times $1 $3 }
        | Term '/' Term                                     { Divide $1 $3 }
        | Term '+' Term                                     { Plus $1 $3 }
        | Term '-' Term                                     { Minus $1 $3 }
        | lift '(' '(' ParamList ')' "->" Term ')' '(' TermList ')' { Lift $4 $7 $10 }



-- Booleanos
BooleanLiteral	: true										{ BLTrue }
		| false										{ BLFalse }


-- Inicio da codificacao do Lexer
---------------------------------
{

parseError :: [Token] -> a
parseError _ = error "Sintax Error: Sequencia de caracteres invalida para analise." 

--instance Show Term where
--  show (EmptyTerm) = ""
--  show (BooleanLiteral BLFalse) = "false"
--  show (BooleanLiteral BLTrue) = "true"
--  show (Var v) = v
--  show (ThisAccessAttr a) = "this." ++ a
--  show (ThisAccessMeth m p) = "this." ++ m ++ show p
--  show (AttrAccess t a) = show t ++ "." ++ a
--  show (MethodAccess t m p) = show t ++ "." ++ m ++ "(" ++ show (reverse p) 
--                                   ++ ")"
--  show (CreateObject c p) = "new " ++ c ++ show (reverse p)
--  show (Cast c t) = "(" ++ c ++ ")" ++ show t
--  show (If t1 t2 t3) = "if (" ++ show t1 ++ ") { " ++ show t2 ++ 
--                             " } else { " ++ show t3 ++ " }"
--  show (Let v t1 t2) = v ++ " = " ++ show t1 ++ " in " ++ show t2
--  show (ClosureDef p t) = "(" ++ show (reverse p) ++ ") -> " ++ show t
--  show (InvokeClosure t tl) = "(" ++ show t ++ ").invoke(" ++ show tl ++ ")"
--  show (Tuple tl) = "{" ++ show (reverse tl) ++ "}"
--  show (TupleAccess t i) = show t ++ "." ++ show i
--  show (RelEquals t1 t2) = show t1 ++ " == " ++ show t2

-- Definições sintáticas da linguagem FlyJ
------------------------------------------
data Program		= Program [(String,ClassDef)] [(String, Term, Status)] [(String, Term)] Term
			deriving (Show, Eq)

data ClassDef		= ClassDef String String [(Type,String)] ConstrDef [MethodDef]
			deriving (Show, Eq)

data ConstrDef		= ConstrDef String [(Type,String)] [String] [(String,String)]
			deriving (Show, Eq)

--data MethodDef		= MethodDef [(String,String)] Type String [(Type,String)] Term
data MethodDef		= MethodDef Type String [(Type,String)] Term
			deriving (Show, Eq)

data Term		= EmptyTerm
			| BooleanLiteral BooleanLiteral
            | Int Int
			| Var String
			| ThisAccessAttr String
			| ThisAccessMeth String [Term]
			| AttrAccess Term String
--			| MethodAccess Term String [Term]
			| MethodAccess Term String [Term]
			| CreateObject String [Term]
			| Cast String Term
			| If Term Term Term
			| Let String Term Term
			| ClosureDef [(Type,String)] Term
			| InvokeClosure Term [Term]
			| Tuple [Term]
			| TupleAccess Term Int
			| RelEquals Term Term
            | Times Term Term
            | Divide Term Term
            | Minus Term Term
            | Plus Term Term
            | Lift [(Type,String)] Term [Term]
            | SignalTerm Term
                       deriving (Show,Eq)

data TermNL		= VarNL Int
			| ClosureDefNL [Type] TermNL
			| InvokeClosureNL TermNL [TermNL]
			deriving (Show, Eq)

data BooleanLiteral	= BLTrue
			| BLFalse
			deriving (Show, Eq)

-- Tipos de dados - adicionado em 14/11/2014 para suportar
-- tipos de objetos e tipos de closures.
-------------------------------------------------------------------------------
data Status		= Change Term
            | NoChange Term
            deriving (Show, Eq)

data Type		= TypeBool
			| TypeClass String
			| TypeClosure Type [Type]
			| TypeTuple [Type]
            | TypeInt
            | SignalType Type
            deriving (Show, Eq)

type Input = Map String (Term,Status,Int)
type EnvG = Map String Term
type Env = Map String Type
type CT = Map String ClassDef
data Token		= TokenKWClass
			| TokenKWExtends
			| TokenKWSuper
			| TokenKWThis
			| TokenKWNew
			| TokenKWReturn
			| TokenKWObject
			| TokenKWIf
			| TokenKWElse
			| TokenKWLet
			| TokenKWIn
			| TokenKWInvoke
			| TokenKWBoolean
			| TokenKWTrue
			| TokenKWFalse
            | TokenKWInt
			| TokenKWMZero
			| TokenKWMReturn
			| TokenKWMPlus
			| TokenKWMMinus
			| TokenArrow
			| TokenTimes
			| TokenDivide
			| TokenPlus
			| TokenMinus
			| TokenEqual
			| TokenLBrace
			| TokenRBrace
			| TokenLParen
			| TokenRParen
			| TokenComma
			| TokenSemi
			| TokenDot
			| TokenAssign
			| TokenLT
			| TokenGT
			| TokenName String
			| TokenNumber Int
            | TokenKWLift
			deriving (Show)

-- Leitura de código fonte e transformação em lista de Tokens (análise léxica)
------------------------------------------------------------------------------

-- Função: isToken
-- Objetivo: Verificar se o caracter lido pertence aos definidos para os 
-- operadores da linguagem
-- Autor: Samuel
-- Data: 22/12/2014
-------------------------------------------------------------------------------
isToken :: Char -> Bool
isToken c = elem c "<>=-*$"


-- Função: lexer
-- Objetivo: Analisador léxico da linguagem
-- Autor: Samuel
-------------------------------------------------------------------------------
lexer :: String -> [Token]
lexer [] = []
lexer ('{':cs) = TokenLBrace : lexer cs
lexer ('}':cs) = TokenRBrace : lexer cs
lexer ('(':cs) = TokenLParen : lexer cs
lexer (')':cs) = TokenRParen : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer (';':cs) = TokenSemi : lexer cs
lexer ('.':cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('/':cs) = TokenDivide : lexer cs
lexer ('*':cs) = TokenTimes : lexer cs
lexer (c:cs)	| isSpace c = lexer cs
		| isAlpha c = lexStr (c:cs)
		| isDigit c = lexDigit (c:cs)
		| isToken c = lexSymbol (c:cs)

lexStr cs = case span isAlpha cs of
		("class", rest)		-> TokenKWClass : lexer rest
		("extends", rest)	-> TokenKWExtends : lexer rest
		("super", rest)		-> TokenKWSuper : lexer rest
		("this", rest)		-> TokenKWThis : lexer rest
		("new", rest)		-> TokenKWNew : lexer rest
		("return", rest)	-> TokenKWReturn : lexer rest
		("Object", rest)	-> TokenKWObject : lexer rest
		("if", rest)		-> TokenKWIf : lexer rest
		("else", rest)		-> TokenKWElse : lexer rest
		("let", rest)		-> TokenKWLet : lexer rest
		("in", rest)		-> TokenKWIn : lexer rest
		("invoke", rest)	-> TokenKWInvoke : lexer rest
		("boolean", rest)	-> TokenKWBoolean : lexer rest
		("true", rest)		-> TokenKWTrue : lexer rest
		("false", rest)		-> TokenKWFalse : lexer rest
		("int", rest)		-> TokenKWInt : lexer rest
		("lift", rest)		-> TokenKWLift : lexer rest
		(name, rest)		-> TokenName name : lexer rest

lexDigit cs = case span isDigit cs of
		(number, rest)		-> TokenNumber (read number :: Int) : lexer rest

lexSymbol cs = case span isToken cs of
        ("->", rest)		-> TokenArrow : lexer rest
        ("==", rest)		-> TokenEqual : lexer rest
        ("=", rest)		-> TokenAssign : lexer rest
        ("-", rest)		-> TokenMinus : lexer rest
--        ("*", rest)		-> TokenTimes : lexer rest
--        ("/", rest)		-> TokenDivide : lexer rest
        ("<", rest)		-> TokenLT : lexer rest
        (">", rest)		-> TokenGT : lexer rest


-- main = getContents >>= print . parser . lexer

}

