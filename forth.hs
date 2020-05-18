{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}

-- An inferred stack language, with unification of type variables
import Control.Arrow
import Control.Monad.Except
import Control.Monad.State
import Data.Function
import qualified Data.Set as S

data Pgrm
  = Done
  | Continue
  | LitI Int Pgrm
  | LitB Bool Pgrm
  | Cmd String Pgrm
  | Func Pgrm Pgrm
  | App Pgrm
  deriving (Show, Eq)

assembleP p = foldl (&) Done p
assembleF p = Func (foldl (&) Continue p)

ex1 = assembleP [LitI 3, LitI 5, Cmd "add"]

data Val
  = I Int
  | B Bool
  deriving (Show)

type Stack = [Val]

stackError :: (MonadError String m) => String -> Stack -> m a
stackError f s = throwError (unwords ["incorrect argument to", f, show s])

-- Exec, a compositional mapping from programs to partial stack
-- transformers.
exec :: Pgrm -> (Stack -> Either String Stack)
exec Done s = pure s
exec (Cmd "add" p) s = do
  v <- exec p s
  case v of
    (I a:I b:r) -> pure (I (a + b) : r)
    _ -> stackError "add" s
exec (Cmd "not" p) s = do
  v <- exec p s
  case v of
    (B a:r) -> pure (B (not a) : r)
    _ -> stackError "not" s
exec (Cmd "dup" p) s = do
  v <- exec p s
  case v of
    (a:r) -> pure (a : a : r)
    _ -> stackError "dup" s
exec (Cmd "swap" p) s = do
  v <- exec p s
  case v of
    (a:b:r) -> pure (b : a : r)
    _ -> stackError "swap" s
exec (Cmd s _) _ = throwError ("unknown command: " <> s)
exec (LitI i p) s = (I i :) <$> exec p s
exec (LitB i p) s = (B i :) <$> exec p s

infixr 4 :-

infixr 5 :->

data Type
  = T String      -- Saturated type (Int, Bool, etc.)
  | Type :- Type  -- Stack with head and tail
  | Type :-> Type -- Function type
  | TV String     -- Type variable
  | Bot           -- Bottom of stack
  deriving (Show)

newtype Gather a =
  Gather
    { unGather :: State ([(Type, Type)], Int) a
    }
  deriving (Functor, Applicative, Monad, MonadState ([(Type, Type)], Int))


gensym :: Gather String
gensym = do
  (cs, i) <- get
  put (cs, i + 1)
  pure $ 't' : show i

-- Generate a new type variable
newTV :: Gather Type
newTV = do
  s <- gensym
  pure $ TV $ s

-- Gather the constraints on a program
gather :: [(String, Type)] -> Pgrm -> Gather Type
gather gamma pgrm =
  case pgrm of
    Done -> pure Bot
    Continue -> let Just tf = lookup "s" gamma
                in pure tf
    LitI i p -> gatherLit "Int" p
    LitB i p -> gatherLit "Bool" p
    Cmd s p -> do
      -- Lookup the function type.
      let Just tf = lookup s gamma
      -- Get all the free type variables from the function type.
      let fv = freeVars tf
      -- Rename all free variables in the function type.
      tf' <- rename tf fv
      -- Gather constraints for the rest of the program.
      a <- gather gamma p
      b <- newTV
      (cs, i) <- get
      -- Add a constraint, the function type must take a to b.
      put ((tf', a :-> b) : cs, i)
      -- The whole command returns something of type b.
      pure b
    Func f p -> do
      tx <- newTV
      tt <- gather (("s", tx):gamma) f
      tp <- gather gamma p
      pure $ (tx :-> tt) :- tp
  where
    -- Literal cases
    gatherLit t p = do
      -- Gather constraints for the rest of the program.
      s <- gather gamma p
      tl <- newTV
      (cs, i) <- get
      -- The result type.
      let res = T t :- s
      put ((tl, res) : cs, i)
      pure res

-- Get all free type variables in a type.
freeVars :: Type -> [String]
freeVars t = S.toList (f t mempty)
  where
    f (TV s) l = S.insert s l
    f (a :-> b) l = f b (f a l)
    f (a :- b) l = f b (f a l)
    f _ l = l

rename :: Type -> [String] -> Gather Type
rename t s = do
  s' <- mapM (\s -> (s, ) <$> newTV) s
  pure (foldr sub t s')

typecheck gamma p = gather gamma p & unGather & (`runState` ([], 0))

newtype Unifier a =
  Unifier
    { unUnifier :: ExceptT String (State [(String, Type)]) a
    }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError String
           , MonadState [(String, Type)]
           )

-- Unification and occurs check
unify :: [(Type, Type)] -> Unifier [(String, Type)]
unify [] = get >>= pure
unify ((tx :- ty, ux :- uy):rest) = unify ((tx, ux) : (ty, uy) : rest)
unify ((tx :-> ty, ux :-> uy):rest) = unify ((tx, ux) : (ty, uy) : rest)
unify ((T t, T u):rest)
  | t == u = unify rest
  | otherwise = throwError (unwords ["Failed to unify", t, "and", u])
unify ((TV v, TV w):rest)
  | v == w = unify rest
unify ((TV x, t):rest) =
  if occurs t
    then throwError
           (unwords ["Cannot construct the infinite type", x, "~", show t])
    else do
      modify ((x, t) :)
      unify (join (***) (sub (x, t)) <$> rest)
  where
    occurs (t :-> u) = occurs t || occurs u
    occurs (t :- u) = occurs t || occurs u
    occurs (TV y)
      | x == y = True
    occurs _ = False
unify ((t, v@(TV _)):rest) = unify ((v, t) : rest)
unify _ = throwError "unification failed"

-- Substitute a type variable x for t in the y.
-- In math notation, sub (x, t) y = y[t/x]
sub :: (String, Type) -> Type -> Type
sub (x, t) y =
  case y of
    TV x'
      | x == x' -> t
    a :- b -> sub (x, t) a :- sub (x, t) b
    a :-> b -> sub (x, t) a :-> sub (x, t) b
    _ -> y

defaultWords =
  [ ("dup", dupType)
  , ("swap", swapType)
  , ("drop", dropType)
  , ("not", notType)
  , ("add", addType)
  ]
  where
    dupType  = (TV "a" :- TV "s") :-> (TV "a" :- TV "a" :- TV "s")
    swapType = (TV "a" :- TV "b" :- TV "s") :-> (TV "b" :- TV "a" :- TV "s")
    dropType = (TV "a" :- TV "s") :-> TV "s"
    notType  = (T "Bool" :- TV "s") :-> (T "Bool" :- TV "s")
    addType  = (T "Int" :- T "Int" :- TV "s") :-> (T "Int" :- TV "s")

runUnifier u = u & unUnifier & runExceptT & (`evalState` [])

solve :: [(String, Type)] -> Pgrm -> Either String Type
solve gamma x = foldr sub ty <$> runUnifier (unify cs)
  where
    (ty, (cs, _)) = typecheck gamma x

{- Examples
λ> solve defaultWords (assembleP [LitI 1, LitI 2, Cmd "add"])
Right (T "Int" :- Bot)

λ> solve defaultWords (assembleP [LitI 3, LitB False, Cmd "swap"])
Right (T "Int" :- (T "Bool" :- Bot))

λ> solve defaultWords (assembleP [LitI 1, LitB False, Cmd "add"])
Left "Failed to unify Int and Bool"

λ> solve defaultWords (assembleP [assembleF [Cmd "swap", Cmd "drop", Cmd "add"]])
Right ((T "Int" :- (TV "t2" :- (T "Int" :- TV "t1"))) :-> (T "Int" :- TV "t1") :- Bot)
-}
