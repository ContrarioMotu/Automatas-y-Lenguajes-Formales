module Pertenencia where

import Data.List

--  |--------------------------------------------------------------------------------------|
--  |---------------------- Autómatas y Lenguajes Formales 2022-1. ------------------------|
--  |----------------------------- Proyecto 1. Pertenencia. -------------------------------|
--  |------------------------------------------------------------ Ayala Morales Mauricio. -|
--  |------------------------------------------------------------------------------------ -|
--  |--------------------------------------------------------------------------------------|

 -- Tipo de dato algebráico para representar Expresiones Regulares
data ExpReg = Void
            | Epsilon
            | Symbol Char           -- El símbolo representado por el caracter que recibe
            | Star ExpReg           -- r*
            | Concat ExpReg ExpReg  -- (rs)
            | Add ExpReg ExpReg     -- (r + s)
            deriving (Eq)

-- Sinónimo para representar lenguajes como listas de cadenas.
type Lenguaje = [String]

 -- Instancia de Show del tipo Regex, para que se impriman con formato en la consola. 
instance Show ExpReg where
   show Void = "ø"
   show Epsilon = "ε"
   show (Symbol c) = c:[]
   show (Star r) = show r ++ "*"
   show (Concat r s) = "(" ++ show r ++ show s ++ ")"
   show (Add r s) = "(" ++ show r ++ " + " ++ show s ++ ")"

------------------- DENOTACIÓN -----------------------

-- EJERCICIO 1
-- Función que recibe una expresión regular (ExpReg) y regresa la expresión regular
-- simplificada usando equivalencias.
simpl :: ExpReg -> ExpReg
simpl Void = Void
simpl Epsilon = Epsilon
simpl (Symbol a) = (Symbol a)
simpl (Concat a Epsilon) = simpl a
simpl (Concat Epsilon a) = simpl a
simpl (Concat a Void) = Void
simpl (Concat Void a) = Void
simpl (Concat (Star a) (Star b)) = if a == b then simpl (Star a)
                                   else (Concat (simpl (Star a)) (simpl (Star b)))
simpl (Concat a b) = (Concat (simpl a) (simpl b))
simpl (Add a Void) = simpl a
simpl (Add Void a) = simpl a
simpl (Add (Concat x a) (Concat y b)) = if x == y then simpl (Concat x (Add a b))
                                        else if a == b then (Concat (Add x y) a) 
                                        else (Add (simpl (Concat x a)) (simpl (Concat y b)))
simpl (Add Epsilon (Concat a (Star b))) = if a == b then simpl (Star a) 
                                          else (Add Epsilon (simpl (Concat a (Star b))))
simpl (Add a b) = if a == b then simpl a 
                  else (Add (simpl a) (simpl b))
simpl (Star Epsilon) = Epsilon
simpl (Star Void) = Epsilon
simpl (Star (Star a)) = simpl (Star a)
simpl (Star (Add (Star a) (Star b))) = simpl (Star (Add a b))
simpl (Star a) = (Star (simpl a))


-- EJERCICIO 2
-- Función que recibe una expresión regular (ExpReg) y regresa todas las cadenas
-- que pertenecen al lenguaje. En caso de que la expresión contenga a la estrella
-- de Kleen solamente se imprimen las cadenas de las primeras 7 iteraciones de
-- la concatenación de la expresión regular.
denot :: ExpReg -> Lenguaje
denot Void = []
denot Epsilon = [""]
denot (Symbol a) = [a]:[]
denot (Add a b) = (denot (simpl a))++(denot (simpl b))
denot (Concat a b) = (concatLeng (denot (simpl a)) (denot (simpl b)))
denot (Star a) = (concatStar (simpl a) (7))++["..."]

-- Función auxiliar que recibe dos lenguajes (Lenguaje) y la concatenación de estos.
-- Usada para la denotación de la concatenación de dos expresiones regulares.
concatLeng :: Lenguaje -> Lenguaje -> Lenguaje
concatLeng (x:[]) (y:[]) = (x++y):[]
concatLeng (x:[]) (y:ys) = (x++y):(concatLeng (x:[]) (ys))
concatLeng (x:xs) (y:[]) = (x++y):(concatLeng (xs) (y:[]))
concatLeng (x:xs) (y:ys) = (x++y):(concatLeng (x:[]) (ys))++(concatLeng (xs) (ys))++(concatLeng (xs) (y:[]))

-- Función auxiliar que recibe una expresión regular α y un número entero n y regresa
-- la concatenación de α n veces.
-- Usada para concatenar la misma expresión en la función: concatStar.
nConcat :: ExpReg -> Integer -> ExpReg
nConcat (a) (0) = Epsilon
nConcat (a) (1) = a
nConcat (a) (n) = (Concat a (nConcat a (n - 1)))

-- Función auxiliar que recibe una expresión regular α y un entero n, y regresa el
-- lenguaje de la expresión regular α^n.
-- Usada para intentar simular el lenguaje generado por la estrella de Kleen, en la
-- denotación de las cadenas que pertenecen al lenguaje (función denot) y para
-- decidir si una cadena pertenece al lenguaje (función enLeng).
concatStar :: ExpReg -> Integer -> Lenguaje
concatStar (a) (0) = (denot (nConcat (a) (0)))
concatStar (a) (n) = (concatStar (a) (n - 1))++(denot (nConcat (a) (n)))

-- EJERCICIO 3
-- Función que recibe una cadena de caracteres y una expresión regular, y regresa True
-- si la cadena pertenece al lenguaje, regresa Fals en otro caso.
enLeng :: String -> ExpReg -> Bool
enLeng (st) (Void) = False
enLeng (st) (Epsilon) = (st == "")
enLeng (st) (Symbol a) = (st == [a])
enLeng (st) (Add (a) (b)) = (enLeng (st) (simpl a)) || (enLeng (st) (simpl b))
enLeng (st) (Concat (a) (b)) = or([(enLeng (s1) (simpl a)) && (enLeng (s2) (simpl b)) 
                                   | (s1,s2) <- (possibleSplits (st))])
enLeng (st) (Star (a)) = (any (st ==) (concatStar (simpl a) (toInteger (length (st)))))

possibleSplits :: String -> [(String,String)]
possibleSplits st = [(splitAt n st) | n <- [0..(length st)]]

------------------- DERIVADAS -----------------------

-- EJERCICIO 1
-- Función que recibe una cadena de caracteres y una expresión regular, y regresa la
-- derivada de la expresión regular con respecto a la cadena.
derivadaCad :: String -> ExpReg -> ExpReg
derivadaCad ("") (a) = a
derivadaCad (st) (a) = (derivadaSim (last (st)) (derivadaCad (init (st)) (a)))


-- Función auxiliar que recibe una expresión regular y calcula su función de nulidad
-- Usada para calcular la derivada de una expresión regular con respecto de un
-- símbolo (función derivadaSim).
nulidad :: ExpReg -> ExpReg
nulidad (Epsilon) = Epsilon
nulidad (Void) = Void
nulidad (Symbol a) = Void
nulidad (Add (a) (b)) = (simpl (Add (nulidad (a)) (nulidad (b))))
nulidad (Concat (a) (b)) = (simpl (Concat (nulidad (a)) (nulidad (b))))
nulidad (Star a) = Epsilon


-- Función auxiliar que recibe un caracter y una expresión regular, y regresa la
-- derivada de la expresión regular con respecto al caracter.
-- Usada para calcular la derivada de una expresión regular con respecto de una
-- cadena (función derivadaCad).
derivadaSim :: Char -> ExpReg -> ExpReg
derivadaSim (a) (Void) = Void
derivadaSim (a) (Epsilon) = Void
derivadaSim (a) (Symbol b) = if a == b then Epsilon else Void
derivadaSim (a) (Add (x) (y)) = (simpl (Add (derivadaSim (a) (x)) (derivadaSim (a) (y))))
derivadaSim (a) (Concat (x) (y)) = (simpl (Add (Concat (derivadaSim (a) (x)) (y)) 
                                               (Concat (nulidad (x)) (derivadaSim (a) (y)))))
derivadaSim (a) (Star b) = (simpl (Concat (derivadaSim (a) (b)) (Star b)))

-- EJERCICIO 2
-- Función que recibe una cadena de caracteres y una expresion regular, y decide
-- si la cadena pertenece al lenguaje generado por la expresión regular mediante
-- derivadas. Regresa True si la cadena pertenece al lenguaje, False en otro caso.
enLengDeriv :: String -> ExpReg -> Bool
enLengDeriv (st) (a) = (enLeng ("") (derivadaCad (st) (a)))
