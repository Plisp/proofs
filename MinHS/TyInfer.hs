module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b")
                  `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b")
                  `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv (TypeVar x) = [x]
tv (Prod  a b) = tv a `union` tv b
tv (Sum   a b) = tv a `union` tv b
tv (Arrow a b) = tv a `union` tv b
tv (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

bindName :: Bind -> String
bindName (Bind id _ _ _) = id

freshVars :: Int -> TC [Type]
freshVars 0 = return []
freshVars n = do a <- fresh
                 l <- (freshVars (n - 1))
                 return $ a:l

-- impl

infer :: Program -> Either TypeError Program
infer program = do (p', _, _) <- runTC $ inferProgram initialGamma program
                   return p'

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [Bind "main" ty [] e] =
  do (e, t, s) <- (inferExp env e);
     return ([Bind "main" (Just (generalise env t)) [{-no params-}]
              (allTypes (substQType s) e)],
             t,
             s)

unify :: Type -> Type -> TC Subst
unify (TypeVar a) (TypeVar b) = return $ if a == b then emptySubst else (a =: (TypeVar b))
unify (Base a) (Base b) = if a == b
                          then return emptySubst
                          else typeError $ TypeMismatch (Base a) (Base b)

unify (Arrow a1 a2) (Arrow b1 b2) = do s1 <- a1 `unify` b1
                                       s2 <- substitute s1 a2 `unify` substitute s1 b2
                                       return $ s1 <> s2
unify (Prod a1 a2) (Prod b1 b2) = do s1 <- a1 `unify` b1
                                     s2 <- substitute s1 a2 `unify` substitute s1 b2
                                     return $ s1 <> s2
unify (Sum a1 a2) (Sum b1 b2) = do s1 <- a1 `unify` b1
                                   s2 <- substitute s1 a2 `unify` substitute s1 b2
                                   return $ s1 <> s2

unify (TypeVar v) t = case elem v (tv t) of
                        True -> typeError $ OccursCheckFailed v t
                        False -> return (v =: t)
unify t (TypeVar v) = case elem v (tv t) of
                        True -> typeError $ OccursCheckFailed v t
                        False -> return (v =: t)
unify a b = typeError $ TypeMismatch a b

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (Num n) = return ((Num n), (Base Int), emptySubst)
inferExp g (Var x) =
  case E.lookup g x of
    Just ty -> do ty' <- unquantify ty
                  return ((Var x), ty', emptySubst)
    Nothing -> typeError $ NoSuchVariable x

inferExp g (Con c) =
  case constType c of
    Just ty -> do ty' <- unquantify ty
                  return ((Con c), ty', emptySubst)
    Nothing -> typeError $ NoSuchConstructor c

inferExp g (Prim o) =
  do ty' <- unquantify (primOpType o)
     return ((Prim o), ty', emptySubst)

inferExp g (App e1 e2) =
  do (e1e, t1, e1s) <- inferExp g e1
     (e2e, t2, e2s) <- inferExp (substGamma e1s g) e2
     alpha <- fresh
     u <- (substitute e2s t1) `unify` (Arrow t2 alpha)
     return ((App e1e e2e), (substitute u alpha), u <> e2s <> e1s)

inferExp g (If e e1 e2) =
  do (ee, t, es) <- inferExp g e
     u <- t `unify` Base Bool
     (e1e, t1, e1s) <- inferExp (substGamma (u <> es) g) e1
     (e2e, t2, e2s) <- inferExp (substGamma (e1s <> u <> es) g) e2
     u' <- (substitute e2s t1) `unify` t2
     return ((If ee e1e e2e), (substitute u' t2), u' <> e2s <> e1s <> u <> es)

inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) =
  do (ee, t, es) <- inferExp g e
     al <- fresh
     ar <- fresh
     (e1e, tl, e1s) <- inferExp (substGamma es (E.add g (x, (Ty al)))) e1
     (e2e, tr, e2s) <- inferExp (substGamma (e1s <> es) (E.add g (y, (Ty ar)))) e2
     u <- (substitute (e2s <> e1s <> es) (Sum al ar)) `unify` (substitute (e2s <> e1s) t)
     u' <- (substitute (u <> e2s) tl) `unify` (substitute u tr)
     return ((Case ee [Alt "Inl" [x] e1e, Alt "Inr" [y] e2e]), (substitute (u' <> u) tr),
             u' <> u <> e2s <> e1s <> es)
inferExp g (Case e _) = typeError MalformedAlternatives

inferExp g (Recfun (Bind f _ params e)) =
  do as <- freshVars (length params)
     a2 <- fresh -- whole function type for recursive binding

     let vars = (zip params (map (\a -> Ty a) as))
     (ee, t, es) <- inferExp (E.addAll g ( (f, (Ty a2)) : vars)) e

     let fty = substitute es (foldr (\a b -> (Arrow a b)) t as)
     u <- (substitute es a2) `unify` fty
     let ty = substitute u fty
     return ((Recfun (Bind f (Just (Ty ty)) params ee)), ty, u <> es)

inferExp g (Let binds e) =
  do (bs, ts, s) <- letBindTypes True g binds
     (e2e, t', e2s) <- inferExp (substGamma s (E.addAll g (zip (map bindName bs) ts))) e
     return ((Let bs e2e), t', s <> e2s)

inferExp g (Letrec bindings e) =
  do as <- freshVars (length bindings)
     let vars = (zip (map bindName bindings) (map (\a -> Ty a) as))
     (bs, ts, s) <- letBindTypes False (E.addAll g vars) bindings

     (e2e, t', e2s) <- inferExp (substGamma s (E.addAll g (zip (map bindName bs) ts))) e
     return ((Letrec bs e2e), substitute s t', s <> e2s)

letBindTypes :: Bool -> Gamma -> [Bind] -> TC ([Bind], [QType], Subst)
letBindTypes gen g [] = return ([], [], emptySubst)
letBindTypes gen g ((Bind x _ [] e):rest) =
  do (ee, t, es) <- inferExp g e
     -- this extra unification is needed by letrec, since g contains fresh vars
     u <- if gen then return emptySubst
          else let (Just (Ty bty)) = E.lookup g x in
                 (substitute es bty) `unify` t

     let gty = if gen then generalise (substGamma (u <> es) g) t
               else (Ty (substitute u t))
     -- overwrites env containing letrec free typevars, and compute the rest
     (bs, ts, ss) <- letBindTypes gen (substGamma (u <> es) (E.add g (x, gty))) rest
     return $ ((Bind x (Just gty) [] ee):bs, gty:ts, u <> es <> ss)
-- let functions
letBindTypes gen g ((Bind x _ params e):rest) =
  do as <- freshVars (length params)
     (ee, t, es) <- inferExp (E.addAll g (zip params (map (\a -> Ty a) as))) e
     let fty = substitute es (foldr (\a b -> (Arrow a b)) t as) in
       -- this extra unification is needed by letrec
       do u <- if gen then return emptySubst
            else let (Just (Ty bty)) = E.lookup g x in
                   (substitute es bty) `unify` fty

          let gty = if gen then generalise (substGamma (u <> es) g) (substitute u fty)
                    else (Ty (substitute u fty))
           -- recursively compute the rest in order
          (bs, ts, ss) <- letBindTypes gen (substGamma (u <> es) (E.add g (x, gty))) rest
          return $ ((Bind x (Just gty) params ee):bs, gty:ts, u <> es <> ss)

generalise :: Gamma -> Type -> QType
generalise g t = generalise' ((tv t) \\ (tvGamma g)) (Ty t)
generalise' :: [Id] -> QType -> QType
generalise' [] ty = ty
generalise' (v:vs) ty = generalise' vs (Forall v ty)

unquantify :: QType -> TC Type
unquantify = unquantify' 0 emptySubst
-- replace all prenex quantified vars by numbers, then substitute letters back in to avoid capture
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =: TypeVar (show i)) t)
