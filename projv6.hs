module Main where

import Control.Monad.Error
import Data.List

--- Result Monad to be able to throw errors
type Result a = Either String a

-- Aliases
type Name = String
type Context = [(Name, Value)]
type Env = [(Name, Value)] 
type Type = Term
type TypedName = (Name, Type)

data Term  = Term :< Type                  -- Type assignment
           | V Name                        -- Variable
           | L TypedName Term              -- Lambda abstraction 
           | Term :$ Term                  -- Application
           | TypedName :-> Term            -- Pi Type
           | Star                          -- Type of types 
           | Nat                           -- Nat type
           | Vec Term Term                 -- Vector type const
           | Cons Type Term Term Term      -- vector data cons
           | Nil Type                      -- Nil Cons
           | Zero                          -- Zero
           | Succ Term deriving (Show, Eq) -- Succ

-- Examples of terms
-- ex1_Term = L ("x", Nat) ((V "x"))  -- λx.(x ∈ Nat)
-- ex2_Term = V "x"
-- ex3_Term = (L ("x", Nat) (x+1)) :$ 2

-- Normalised terms (post evaluation)
data Value = VLam Name (Term, Env)           
           | VStar                           
           | VPi Name Value (Term, Env)      
           | VVar Name
           | VNat
           | VSucc Value
           | VZero
           | VVec Value Value
           | VCons Value Value Value Value
           | VNil Value deriving (Show, Eq)

--------------- Turn numbers into internal number rep ----------------
toNatural :: Integer -> Term
toNatural x | x < 0 = error "shouldnt get a num < 0"
            | otherwise = convertIntToNat x Zero

convertIntToNat :: Integer -> Term -> Term
convertIntToNat 0 x = x 
convertIntToNat i x = convertIntToNat (i-1) (Succ x)

addSucc :: Term -> Term -> Term
addSucc Zero y = y
addSucc (Succ x) y = Succ (addSucc x y)
addSucc x y = error ("unmatched pattern in addSucc " ++ (show x) ++ " " ++ (show y))

addSucc_aux (V x) (V y) = error "Invalid number" -- change this so we can add two vars
addSucc_aux (V x) y = addSucc y (V x)
addSucc_aux x (V y) = addSucc x (V y)

-- type coercion for numbers to terms
instance Num Term where
  signum = id
  x * y = undefined
  abs = id
  fromInteger = toNatural
  x + y = addSucc_aux x y

------------------------------interpretation -------------------------
evalTerm :: Term -> Env -> Result Value

evalTerm (t :< _) e = evalTerm t e

evalTerm (V x)  e = 
  case lookup x e of
    Just(x) -> return x
    Nothing -> throwError ("Variable not found : " ++ x ++ "env is " ++ (show e))

evalTerm (t :$ u) e = 
  do f <- evalTerm t e
     a <- evalTerm u e
     (f $$$ a) -- apply

evalTerm (L (n, t) t') e = 
  return (VLam n (t', e))

evalTerm (Cons t1 t2 t3 t4) env = 
  do t1' <- evalTerm t1 env
     t2' <- evalTerm t2 env
     t3' <- evalTerm t3 env
     t4' <- evalTerm t4 env
     return (VCons t1' t2' t3' t4')

evalTerm (Nil t) env = 
  do v <- evalTerm t env
     return (VNil v)

evalTerm Star env = typeConv Star env

evalTerm (Zero) env = typeConv Zero env

evalTerm (Succ x) env =
  do v <- evalTerm x env
     return (VSucc (v))

evalTerm (Vec t1 t2) env = 
  do v <- evalTerm t1 env
     v' <- evalTerm t2 env
     return (VVec v v')

evalTerm (Nat) env = typeConv Nat env

evalTerm ((n, t) :-> t') env = 
  do v <- evalTerm t env
     return (VPi n v (t', env))

------------------------ Type Conv Functions -------------------------
typeConv Star _ = return VStar

typeConv (Zero) e = return VZero

typeConv (Succ x) e = return (VSucc (convNumToVal x))
typeConv (Vec t1 t2) env = 
  do v <- typeConv t1 env
     return (VVec v (convNumToVal t2))

typeConv (Nat) _ = return VNat

typeConv ((n, t) :-> t') env = 
  do v <- typeConv t env
     return (VPi n v (t', env))
typeConv (V x) env = return (VVar x)

typeConv a b     = 
  throwError ("Malformed term to convert " ++ (show a)) 
--------------------- Type Conv helper functions ---------------------
convNumToVal :: Term -> Value
convNumToVal (Succ (V x)) = VSucc (VVar x)
convNumToVal (Succ x) = VSucc(convNumToVal x)
convNumToVal Zero = VZero
convNumToVal (V x)  = (VVar x)

convTyToVal :: Term -> Value
convTyToVal Nat = VNat
convTyToVal (V a) = (VVar a)
convTyToVal (Vec (V t) n) = (VVec (VVar t) (convNumToVal n))

---------------------------Apply function ---------------------------
($$$) :: Value -> Value -> Result Value
(VLam n (t, env)) $$$ a = evalTerm t ((n, a):env)
_ $$$ a = throwError ("cant appy to non lambda" ++ (show a)) 

----------------------Type Checker interface ------------------------
typeCheck :: Term -> (Context, Env) -> Result Bool
typeCheck e (gamma, env) = 
  do v <- checkType e (gamma, env)
     return True

----------------Type Checking--------------------------
checkType :: Term -> (Context, Env) -> Result Value

checkType (e :$ e') (gamma, env) = 
  do s <- checkType e (gamma, env)
     case s of 
       VPi n t (t', lenv) -> 
         do checkTypeEq e' t (gamma, env)
            v' <- evalTerm e' env
            evalTerm t' ((n, v'):lenv)
       a -> return a 

checkType (e :< p) (gamma, env) = 
  do checkTypeEq p VStar (gamma, env)
     t <- typeConv p env 
     checkTypeEq e t (gamma, env)
     return t

checkType (V x) (gamma, env) = 
  case lookup x gamma of -- look up the type
    Just t -> return t
    Nothing -> throwError ("unknown var : " ++ x)

checkType (Nat) _ = return VStar

checkType (Star) (gamma,env) = return VStar

checkType ((n, p) :-> p') (gamma, env) = 
  do checkTypeEq p VStar (gamma, env)
     t <- evalTerm p gamma 
     t' <- checkType p' (((n,t):gamma), env)
     unless (t' == VStar) (throwError "unbound type")
     return VStar

checkType (Vec t n) (gamma, env) =
  do checkTypeEq t VStar (gamma, env) 
     checkTypeEq n VNat (gamma, env)
     return VStar

checkType (Nil t) (gamma, env) =
  do checkTypeEq t VStar (gamma, env)
     v <- typeConv t env
     return (VVec v (VZero))

checkType (Cons t n x xs) (gamma, env) =
  do checkTypeEq t VStar (gamma, env)
     v <- typeConv t env
     checkTypeEq n VNat (gamma, env)
     checkTypeEq x v (gamma, env)
     checkTypeEq xs (VVec v (convNumToVal n)) (gamma, env)
     return (VVec v (VSucc (convNumToVal n)))

checkType Zero (gamma, env) = return VNat
checkType (Succ x) (gamma, env) =
  do checkTypeEq x VNat (gamma, env)
     return VNat

checkType x _ = throwError ("check type: malformed type" ++ (show x))

--------------------------- Type Equality ----------------------------
checkTypeEq :: Term -> Value -> (Context, Env) -> Result ()

checkTypeEq (L (ln,lt) lte) (VPi pn pty (pte, penv)) (gamma, env)  =
  do typeNormEq lt pty env
     vte <- typeConv pte env
     checkTypeEq lte vte (((ln, pty):gamma), env)

checkTypeEq (Vec (V t) n) (VVec (VVar t') n') (gamma, env) =
  if (t == t') then checkNumEq n n' else throwError "vectors have different element types"

checkTypeEq e v (gamma, env) = 
  do v' <- checkType e (gamma, env)
     unless (v == v') (throwError ("type error e:v = " ++ (show e) ++ " : " ++ (show v') ++ " and v : " ++ (show v) 
                       ++ " - Gamma is " ++ (show gamma) ++ " - env is " ++ (show env)))

typeNormEq :: Term -> Value -> Env -> Result ()
typeNormEq x y env = 
  do v <- typeConv x env 
     unless (v == y) (throwError ("type mismatch x: " ++ (show x) ++ " y: " ++ (show y)))

checkNumEq :: Term -> Value -> Result ()
checkNumEq (Succ x) (VSucc y) = checkNumEq x y
checkNumEq Zero (VSucc y) = throwError "Nat value mismatch in type"
checkNumEq (Succ x) (VZero) = throwError "Nat value mismatch in type"
checkNumEq (V x) (VVar y) = 
  if (x == y) then return () else  throwError "diffierent varibles - cant type check"
checkNumEq Zero VZero = return ()
checkNumEq _ _ = throwError "invalid types"
     
------------------------------- Output --------------------------------
showValue :: Value -> String
showValue (VLam n (t, env)) = "(\\" ++ n ++ "( " ++ show(t) ++ ") )"
showValue VStar = "*"
showValue (VPi n v (t, env) ) = 
  ("PI " ++ n ++ ":" ++ (showValue v) ++ (show t) ++ " ")
showValue (VVar name) = name
showValue (VSucc i) = " Succ(" ++ (showValue i) ++ ") "
showValue (VZero) = "Zero"
showValue VNat = "Nat"
showValue (VVec v1 v2) = 
  "Vec" ++ showValue v1 ++ " " ++ showValue v2
showValue (VCons v1 v2 v3 v4) = 
  "< " ++ " " ++ (showValue v3) ++ (showValue v4) ++ " >"
showValue (VNil v) = "< Nil >"

showResult :: (Result Value) -> String
showResult (Right v) = showValue v 

showTypeCheck :: (Result Bool) -> String
showTypeCheck (Right b) = "Type Check OK"

-------------------------------- Test Data ---------------------------
gamma1 = [("A", VStar), ("x", VVar "A")]
env1 = [("x", VSucc(VZero)) ]

env = (gamma1, env1)

id1  = (L ("A",Star) (L ("x", V "A") (V "x"))) :< (("A", Star) :-> (("x", (V "A")) :-> (V "A") ))

cons = L ("a", Star) ((L ("x", Nat) (L ("d", V "a")  (L ("v", (Vec (V "a") (V "x")))  (Cons (V "a")  (V "x") (V "d") (V "v"))))))
consTy = ("a", Star) :-> (("x", Nat) :-> (("d", (V "a")) :-> (("v", Vec (V "a") (V "x")) :-> (Vec (V "a") ((V "x") + 1)))))
cl = cons :< consTy

capp = cl :$ Nat :$ 0 :$ 1 :$ (Nil Nat)
capp2 = cl :$ Nat :$ 1 :$ 1 :$ (Cons Nat 0 2 (Nil Nat))



term = capp


--Type Check Tests
----------------------------------
tyTest1 = checkType id1 env
tyTest2 = checkType cl env
tyTest3 = checkType capp env
tyTest4 = checkType capp2 env

-- Eval tests
---------------------------
evTest1 = evalTerm capp env1
evTest2 = evalTerm capp2 env1 

-------------------------------- Main --------------------------------
main = 
  do print (showTypeCheck (typeCheck term env))
     putStrLn ("")
     print (showResult(evalTerm term env1)) 
