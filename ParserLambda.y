{
module ParserLambda where
import Data.Char
}

%name parserlamb
%tokentype { Token }
%error { parseError }

%token
	lam { TokenLam } 
	var { TokenVar $$ }
	'.' { TokenPoint }
	'(' { TokenOB }
	')' { TokenCB }

%right '.'
%left APP	

%%

-- regras de producao da gramatica


LamExp : var                   { LamVar $1 }
	 | lam var  '.' LamExp     { LamAbs $2 $4}
	 | LamExp LamExp  %prec APP  { LamApp $1 $2 }
	 | '(' LamExp ')'          { $2 }


{

parseError :: [Token] -> a
parseError b = error "Parse Error"


data LamExp = LamVar Char
          | LamAbs Char LamExp
          | LamApp LamExp LamExp deriving (Show, Eq)



data Token 
		= TokenVar Char
		| TokenPoint
		| TokenOB
		| TokenCB
		| TokenLam 
	deriving Show


-- ToDo
-- Função que recebe uma string e gera uma lista de tokens
lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
    | isSpace c = lexer cs
    | c == '.'  = TokenPoint : lexer cs
    | c == '('  = TokenOB : lexer cs
    | c == ')'  = TokenCB : lexer cs
    | isAlpha c = let (a,rest) = span isAlpha (c:cs)
                  in if (a == "lam") then TokenLam : lexer rest
                     else (TokenVar c) : lexer rest 	



main = getContents >>= print . parserlamb .lexer

}
