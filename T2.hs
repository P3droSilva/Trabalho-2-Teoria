module T2 where

import Data.List
import ParserLambda --(lexer, parserlamb, LamExp(LamVar, LamAbs, LamApp))


----------------------------------- Tipos -----------------------------------

-- Working in canonical form
-- Lambda Expression Nameless
data LamExpNL = LamVarNL Int
            | LamAbsNL LamExpNL
            | LamAppNL LamExpNL LamExpNL
     deriving (Show, Eq)

-- Context of free variables  
--indice de De Bruijn (dicionário)
type Index = [(Char,Int)]

-- (lamda b. y(lambda a . x )0)1

-------------------------------- applyBruijn -------------------------------

-- Conversão LamExp para LamExpNL = LamExpo NameLess Lambda
applyBruijn :: LamExp -> Index -> LamExpNL
applyBruijn (LamVar x) c   = LamVarNL (findfirst x c)

applyBruijn (LamAbs x t) c = let t' = applyBruijn t (insertChar x c) 
                          in  LamAbsNL t'
applyBruijn (LamApp t1 t2) c = let t1' = applyBruijn t1 c
                                   t2' = applyBruijn t2 c
                          in LamAppNL t1' t2'                             

-- Insere um Char no Index e atualiza o Index
insertChar :: Char -> Index -> Index
insertChar x c = [(fst a,snd a +1) |  a <- c]++[(x,0)]

-- Pega primeiro Int do Char correspondente
findfirst :: Char -> Index -> Int
findfirst x [] = error "Variable not in Context"
findfirst x c = if x == fst (last c) then snd(last c) else findfirst x (init c)

-- Pega primeiro Char do Int correspondente
findfirst' :: Int -> Index -> Char
findfirst' x c = if x == snd (last c) then fst(last c) else findfirst' x (init c)

----------------------------------------------------------------------------
------------------------------- Restorenames -------------------------------
----------------------------------------------------------------------------

-- Conversão LamExpNL para LamExp
restorenames :: LamExpNL -> Index -> LamExp
restorenames (LamVarNL x) c = LamVar (findfirst' x c)
restorenames (LamAbsNL t) c = let a = geraChar c ['a'..'z']
                                  t' = restorenames t (insertChar a c)
                           in LamAbs a t'
restorenames (LamAppNL t1 t2) c = let t1' = restorenames t1 c
                                      t2' = restorenames t2 c
                               in LamApp t1' t2' 

-- verifica se o char c está no Index
verificaCC :: Index -> Char -> Bool
verificaCC [] c = False
verificaCC ((a,_):b) c = (a == c) || verificaCC b c

-- gera uma var nova que não está no Index 
geraChar :: Index -> [Char] -> Char
geraChar c [] = error "todas as letras usadas"
geraChar c (a:b) = if verificaCC c a then geraChar c b else a


----------------------------------------------------------------------------
------------------------------ Shifting LamExpNL -----------------------------
----------------------------------------------------------------------------

-- Shifting recebe tres parametros: o valor de incremento "d", o valor de
-- cutoff "c" (a partir de qual numero deve ser incrementado e o LamExpo)

shifting :: Int -> Int -> LamExpNL -> LamExpNL
shifting d c (LamVarNL k) = if k < c
                         then LamVarNL k
                         else LamVarNL (k + d)
shifting d c (LamAbsNL t) = LamAbsNL(shifting d (c+1) t)
shifting d c (LamAppNL t1 t2) = LamAppNL (shifting d c t1)(shifting d c t2)


----------------------------------------------------------------------------
------------------------------- Substitution -------------------------------
----------------------------------------------------------------------------

-- Busca as variáveis livres do Termo
-- freeVars :: LamExp -> [Char]
-- freeVars (LamVar x)     = [x] 
-- freeVars (LamAbs x t)   = delete x (freeVars t)
-- freeVars (LamApp t1 t2) = freeVars t1 ++ freeVars t2

-- -- Faz a substituição de um Termo
-- subs :: Char -> LamExp -> LamExp -> LamExp
-- subs x t (LamVar y) = if x == y then t else LamVar y
-- subs x t (LamAbs y t12) = if x /= y && notElem x (freeVars t12) then LamAbs x (subs x t t12) else LamAbs y t12
-- subs x t (LamApp t1 t2) = LamApp (subs x t t1) (subs x t t2)      

-- -- Verifica se é variável ou abstração/aplicação
-- isVal :: LamExp -> Bool
-- isVal (LamAbs x t21) = True
-- isVal (LamVar x)     = True
-- isVal _           = False

-- -- Semantica operacional Call-by-value (ordem de avaliacao)
-- eval :: LamExp -> LamExp
-- eval (LamApp (LamAbs x t12) t2) = if isVal t2 then subs x t2 t12 
--                             else let t2' = eval t2
--                                  in LamApp (LamAbs x t12) t2'
-- eval (LamApp t1 t2) = let t1'= eval t1
--                    in LamApp t1' t2
-- eval x                    = x              

-- -- Funcao que aplica recursivamente eval ate que nao tenha mais redex
-- interpret :: LamExp -> LamExp
-- interpret t = let t' = eval t
--               in if t==t' then t else interpret t'

----------------------------------------------------------------------------
-------------------------- Substitution Nameless ---------------------------
----------------------------------------------------------------------------

-- Busca as variáveis livres do Termo nameless
-- freeVarsNL :: LamExpNL -> Int -> [Int]
-- freeVarsNL (LamVarNL x) t2     = [x | x >= t2]
-- freeVarsNL (LamAbsNL t0) t2  = freeVarsNL t0 (t2 + 1)
-- freeVarsNL (LamAppNL t0 t1) t2 = freeVarsNL t0 t2 ++ freeVarsNL t0 t2

--Tem muito mais problema aqui?
-- erro brabo aqui
subsNL :: (Int, LamExpNL) -> LamExpNL -> LamExpNL
subsNL (j, s) (LamVarNL k) = if k == j then s else LamVarNL k
subsNL (j, s) (LamAbsNL t1) = LamAbsNL (subsNL (j+1, shifting 1 0 s) t1)
subsNL (j, s) (LamAppNL t1 t2) = LamAppNL (subsNL (j, s) t1) (subsNL (j, s) t2)


----------------------------------------------------------------------------
-- Se trocar o ultimo caso pra True, parece que ele funciona mais....
-- Verifica se é variável nameless ou abstração/aplicação nameless
isValNL :: LamExpNL -> Bool
isValNL (LamAbsNL y) = True
isValNL (LamVarNL x) = True
isValNL _         = True

-- Semantica operacional Call-by-value (ordem de avaliacao)
evalNL :: LamExpNL -> LamExpNL
evalNL (LamAppNL (LamAbsNL t12) t2) = if isValNL t2 then subsNL (0, t2) t12 
                            else let t2' = evalNL t2
                                 in LamAppNL (LamAbsNL t12) t2'
evalNL (LamAppNL t1 t2) = let t1'= evalNL t1
                   in LamAppNL t1' t2
evalNL x = x     

-- Funcao que aplica recursivamente eval ate que nao tenha mais redex
interpretNL :: LamExpNL -> LamExpNL
interpretNL t = let t' = evalNL t
              in if t==t' then t else interpretNL t'

-- Funcao principal que aplica Brujin e depois interpreta a expressao
evalBruijn :: LamExp -> LamExpNL
evalBruijn t = interpretNL (applyBruijn t varList)

evalBruijn' :: LamExp -> LamExp
evalBruijn' t = restorenames (interpretNL (applyBruijn t varList)) varList

----------------------------------------------------------------------------
--------------------------- Variáveis e Exmplos ----------------------------
----------------------------------------------------------------------------

-- Variáveis
-- t1 = LamApp (LamAbs 'b' (LamApp (LamVar 'b') (LamAbs 'x' (LamVar 'b')))) (LamApp (LamVar 'a') (LamAbs 'z' (LamVar 'a')))

varList :: Index
varList = [ ('z', 2), ('y', 1), ('x', 0)]

-- termot2 :: LamExpNL
-- termot2 = LamAppNL (LamAppNL (LamVarNL 1) (LamAbsNL (LamVarNL 2))) (LamAbsNL (LamAppNL (LamVarNL 2) (LamAbsNL (LamVarNL 3))))
--        LamApp (LamApp (LamVar 'y') (LamAbs 'a' (LamVar 'y'))) (LamAbs 'a' (LamApp (LamVar 'y') (LamAbs 'b' (LamVar 'y'))))

-- Exemplos
{-
shifting 2 0 (l.l. 2(0 2)) = l . shifting 2 1 (l. 2 (0 2))
                           = l . l .shifting 2 2 (2 (0 2))
                           = l . l. (shifting 2 2 2) (shifting 2 2 (0 2))
                           = l . l. 4 ( (shifting 2 2 0) (shifting 2 2 2))
                           = l . l. 4 (0 4)
-}

-- Exemplo : [0 -> 1 (l . 2)] (0 (l . 1)) = (1 (l . 2) (l . 2 ( l. 3))
-- (0, LamAppNL (LamVarNL 1) (LamAbsNL (LamVarNL 2))) (LamAppNL (LamVarNL 0) (LamAbsNL (LamVarNL 1)))
-- subs (0, LamAppNL (LamVarNL 1) (LamAbsNL (LamVarNL 2))) (LamAppNL (LamVarNL 0) (LamAbsNL (LamVarNL 1)))

-- applyBruijn (LamAbs 'x' (LamVar 'x')) [] = LamAbsNL (LamVarNL 0)
-- applyBruijn (LamAbs 'x' (LamAbs 'y' (LamApp (LamVar 'z')(LamApp (LamVar 'y') (LamVar 'z'))))) varList

----------------------------------------------------------------------------
---------------------------------- Main ------------------------------------
----------------------------------------------------------------------------

--main = getContents >>= print . evalBruijn . parserlamb . lexer -- Printa o resultado da avaliação Nameless
main = getContents >>= print . evalBruijn' . parserlamb . lexer -- Printa o resultado da avaliação Nameless revertido para nomes
