--
-- interpreter examples: assume types are checked
-- f $ a b c.... means f (a b c...)
--

data Expr =
    Num Int
  | Lit Bool
  | If Expr Expr Expr
  | Apply Expr Expr
  | Plus Expr Expr
  | Eq Expr Expr
  -- note: HOAS used here, use haskell closures to avoid substitution issues
  | Recfun (Expr -> Expr -> Expr)

--
-- by-name: substitute directly during an apply, don't eval argument x
-- function values store unevaluated expressions
--
data Val = BV Bool | IV Int | FV (Expr -> Expr -> Expr)
instance Show Val where
  show (BV b) = show b
  show (IV i) = show i
  show (FV f) = "F"

evalByName :: Expr -> Val
evalByName (Num i) = IV i
evalByName (Lit b) = BV b
evalByName (If v l r) = case evalByName v of
    BV b -> if b then evalByName l else evalByName r
    _ -> undefined
evalByName (Plus x y) = case (evalByName x,evalByName y) of
  (IV x',IV y') -> IV $ x' + y'
  _ -> undefined
evalByName (Eq x y) = case (evalByName x,evalByName y) of
  (IV x',IV y') -> BV $ x' == y'
  (BV x', BV y') -> BV $ x' == y'
  _ -> undefined
-- important cases!
evalByName (Recfun f) = FV f 
evalByName (Apply f x) =
  case evalByName f of
    FV f' -> evalByName $ f' f x
    _ -> undefined

--
-- by-value: eval argument first before applying function
--
data Value = B Bool | I Int | F (Value -> Value)
instance Show Value where
  show (B b) = show b
  show (I i) = show i
  show (F f) = show "F"

val_to_expr :: Value -> Expr
val_to_expr (I i) = Num i
val_to_expr (B b) = Lit b
val_to_expr (F f) = Recfun $ \g x -> val_to_expr $ f (evalByVal x)

evalByVal :: Expr -> Value
evalByVal (Num i) = I i
evalByVal (Lit b) = B b
evalByVal (If v l r) = case evalByVal v of
    B b -> if b then evalByVal l else evalByVal r
    _ -> undefined
evalByVal (Plus x y) = case (evalByVal x,evalByVal y) of
  (I x',I y') -> I $ x' + y'
  _ -> undefined
evalByVal (Eq x y) = case (evalByVal x,evalByVal y) of
  (I x',I y') -> B $ x' == y'
  (B x', B y') -> B $ x' == y'
  _ -> undefined
-- important cases!
evalByVal (Recfun f) = F $ \x -> evalByVal (f (Recfun f) (val_to_expr x))
evalByVal (Apply f x) =
  case evalByVal f of
    F f' -> f' $ evalByVal x
    _ -> undefined

--
-- examples
--

-- cheeky metalanguage shortcuts
eq0 x = (Eq x (Num 0))
minus1 x = Plus x (Num (-1))

-- we do manual currying to express products
prod :: Expr
prod = Recfun $ \g n ->
  Recfun $ \f x ->
  If (eq0 x)
  (Num 0) $
  Plus n (Apply f (minus1 x))

-- try: evalByName (Apply fact (Num 9))
-- try: evalByVal  (Apply fact (Num 9))
-- note the difference in speed!
-- why?! If you can explain why this happens you're good to go for as1 ;)
fact' :: Expr
fact' = 
  Recfun $ \f n ->
  Recfun $ \_ accum ->
  If (eq0 n)
  accum
  (Apply (Apply f (minus1 n)) (Apply (Apply prod accum) n))

fact :: Expr
fact = Recfun $ \_ n -> Apply (Apply fact' n) (Num 1) 

-- higher order functions test
ide :: Expr
ide = Recfun $ \self x -> x

idm :: Expr
idm = Recfun $ \self x-> If (Eq x (Num 0))
  ide $
  Apply self (Plus x (Num (-1)))

comp :: Expr
comp = Recfun $ \_ f -> Recfun $ \_ g -> Recfun $ \_ x -> Apply f (Apply g x)
