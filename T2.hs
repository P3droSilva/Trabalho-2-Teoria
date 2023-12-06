------- Trabalho 2 - Teoria da Computação --------
--            Alfredo Cossetin Neto             --
--         Mauro Roberto Machado Trevisan       --
--        Pedro Henrique da Silva Hinerasky     --      
--              Ramon Godoy Izidoro             --
--------------------------------------------------


module T2 where

import Data.List
import ParserLambda --(lexer, parserlamb, LamExp(LamVar, LamAbs, LamApp))
import Foreign (free)


data LamExpNL = LamVarNL Int
            | LamAbsNL LamExpNL
            | LamAppNL LamExpNL LamExpNL
     deriving (Show, Eq)

--indice de De Bruijn (dicionário)
type Index = [(Char,Int)]


-- Conversão LamExp para LamExpNL = LamExp NameLess 
applyBruijn :: LamExp -> Index -> LamExpNL
applyBruijn (LamVar x) i     = LamVarNL (findfirstInt x i)
applyBruijn (LamAbs x t) i   = LamAbsNL $ applyBruijn t (insertChar x i)
applyBruijn (LamApp t1 t2) i = LamAppNL (applyBruijn t1 i) (applyBruijn t2 i)

-- Insere um Char no Index e atualiza o Index
insertChar :: Char -> Index -> Index
insertChar x i = (x,0) : [(fst a,snd a+1) |  a <- i]

-- Pega primeiro Int do Char correspondente
findfirstInt :: Char -> Index -> Int
findfirstInt x [] = error "Variable not in Index"
findfirstInt x (i:is) = if x == fst i then snd i else findfirstInt x is

-- Pega primeiro Char do Int correspondente
findfirstChar :: Int -> Index -> Char
findfirstChar x (i:is) = if x == snd i then fst i else findfirstChar x is


-- Conversão LamExpNL para LamExp
restorenames :: LamExpNL -> Index -> LamExp
restorenames (LamVarNL x) i = LamVar (findfirstChar x i)
restorenames (LamAbsNL t) i = LamAbs a (restorenames t (insertChar a i))
       where a = genChar i ['a'..'z']
restorenames (LamAppNL t1 t2) i = LamApp (restorenames t1 i) (restorenames t2 i)

-- verifica se o char c está no Index
checkCharInIndex :: Index -> Char -> Bool
checkCharInIndex [] c = False
checkCharInIndex ((a,_):is) c = (a == c) || checkCharInIndex is c

-- gera uma var nova que não está no Index 
genChar :: Index -> [Char] -> Char
genChar i [] = error "todas as letras usadas"
genChar i (a:as) = if checkCharInIndex i a then genChar i as else a


-- Shifting recebe tres parametros: o valor de incremento "d", o valor de
-- cutoff "c" (a partir de qual numero deve ser incrementado e o LamExp)
shifting :: Int -> Int -> LamExpNL -> LamExpNL
shifting d c ex = case ex of
       LamVarNL k | k < c     -> LamVarNL k
                  | otherwise -> LamVarNL (k + d)
       LamAbsNL t     -> LamAbsNL (shifting d (c+1) t)
       LamAppNL t1 t2 -> LamAppNL (shifting d c t1) (shifting d c t2)

-- Busca as variáveis livres na expressão
freeVars :: LamExp -> [Char]
freeVars (LamVar x)     = [x]
freeVars (LamAbs x t)   = delete x (freeVars t)
freeVars (LamApp t1 t2) = freeVars t1 ++ freeVars t2

-- Busca as variáveis livres na expressão nameless
freeVarsNL :: LamExpNL -> Int -> [Int]
freeVarsNL (LamVarNL x) t2     = [x | x >= t2]
freeVarsNL (LamAbsNL t0) t2  = freeVarsNL t0 (t2 + 1)
freeVarsNL (LamAppNL t0 t1) t2 = freeVarsNL t0 t2 ++ freeVarsNL t0 t2

-- Faz a substituição de uma expressão nameless
subsNL :: (Int, LamExpNL) -> LamExpNL -> LamExpNL
subsNL (j, s) ex = case ex of
       LamVarNL k     -> if k == j then s else LamVarNL k
       LamAbsNL t1    -> LamAbsNL (subsNL (j+1, shifting 1 0 s) t1)
       LamAppNL t1 t2 -> LamAppNL (subsNL (j, s) t1) (subsNL (j, s) t2)

-- Verifica se é variável nameless ou abstração nameless
isValNL :: LamExpNL -> Bool
isValNL (LamAbsNL y) = True
isValNL (LamVarNL x) = True
isValNL _         = False

-- Semantica operacional Call-by-value (ordem de avaliacao)
evalNL :: LamExpNL -> LamExpNL
evalNL (LamAppNL (LamAbsNL t12) t2)
       | isValNL t2 = subsNL (0, t2) t12
       | otherwise  = LamAppNL (LamAbsNL t12) (evalNL t2)
evalNL (LamAppNL t1 t2) = LamAppNL (evalNL t1) t2                      
evalNL x = x

-- Funcao que aplica recursivamente eval ate que nao tenha mais redex
interpretNL :: LamExpNL -> LamExpNL
interpretNL t = if t==t' then t else interpretNL t'
                where t' = evalNL t

-- Funcao principal que aplica Brujin e depois interpreta a expressao
evalBruijn :: LamExp -> LamExpNL
evalBruijn t = interpretNL (applyBruijn t varList)
       where varList = zip (freeVars t) [0..]

-- Funcao principal que aplica Brujin e depois interpreta a expressao, retornando o resultado com os nomes originais
evalBruijn' :: LamExp -> LamExp
evalBruijn' t = restorenames (interpretNL (applyBruijn t varList)) varList
       where varList = zip (freeVars t) [0..]


--main = getContents >>= print . evalBruijn . parserlamb . lexer -- Printa o resultado da avaliação Nameless
main = getContents >>= print . evalBruijn' . parserlamb . lexer -- Printa o resultado da avaliação Nameless revertido para nomes
