{-# Language TypeOperators, TemplateHaskell, TypeFamilies, GADTs, DataKinds,
             KindSignatures, ScopedTypeVariables, BlockArguments, RankNTypes,
             TypeInType #-}
{-# OPTIONS_GHC -Wall #-}
module Demo where

import Control.Monad                    ((<=<))
import Data.Kind                        (Type)
import Data.Functor.Const               (Const(..))
import Data.Parameterized.Context
import Data.Parameterized.TraversableFC (FunctorFC(..), FoldableFC(..), TraversableFC(..),
                                         fmapFCDefault, foldMapFCDefault)
import Data.Parameterized.TH.GADT       (structuralTypeEquality, structuralTraversal)
import Data.Parameterized.Classes       (TestEquality(..), (:~:)(Refl))
import Data.Parameterized.Ctx.Proofs    (assoc)
import Data.Parameterized.Some
import Data.Proxy                       (Proxy(Proxy))

------------------------------------------------------------------------
-- Universe of types in our language -----------------------------------
------------------------------------------------------------------------

-- | New data kind of values in this language
data {- kind -} U :: Type where BoolT, IntT :: U

-- Helpers to avoid needing to use the leading tick in most circumstance
type BoolT = 'BoolT
type IntT  = 'IntT

------------------------------------------------------------------------
-- Haskell representaion of types in this language for evaluators ------
------------------------------------------------------------------------

type family Value (t :: U) :: Type where
  Value 'IntT  = Int
  Value 'BoolT = Bool

-- | Newtype around 'Value' that supports partial application.
-- This will be useful to combine with 'Assignment'
newtype Value' t = Value { getValue :: Value t }

------------------------------------------------------------------------
-- Value level representations of types in our language ----------------
------------------------------------------------------------------------

-- | Value-level representation of 'U'
data URep :: U -> Type where
  BoolRep :: URep BoolT
  IntRep  :: URep IntT

return [] -- Allow testEquality to see URep

instance TestEquality URep where
  testEquality = $(structuralTypeEquality [t|URep|] [])

-- | Convenience class for generating 'URep' values for known types
class    KnownRep t      where knownRep :: URep t
instance KnownRep 'IntT  where knownRep = IntRep
instance KnownRep 'BoolT where knownRep = BoolRep

-- | Convenience class for things that can determine their own types
class    HasType f       where hasType :: f t -> URep t
instance HasType URep    where hasType = id

cast :: HasType f => URep u -> f t -> Maybe (f u)
cast rep x =
  case testEquality (hasType x) rep of
    Just Refl -> Just x
    Nothing   -> Nothing

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------

-- | Flat syntax of expressions in the language parameterized by:
--
-- 1. The type of subexpression values
-- 2. The logical type of the expression in the language being modeled
data ExprF :: (U -> Type) -> (U -> Type) where
  Bool    :: Bool    ->            ExprF e BoolT -- ^ constant boolean
  Int     :: Int     ->            ExprF e IntT  -- ^ constant integer
  And     :: e BoolT -> e BoolT -> ExprF e BoolT -- ^ logical and
  Add     :: e IntT  -> e IntT  -> ExprF e IntT  -- ^ arithetic adition
  NonZero :: e IntT  ->            ExprF e BoolT -- ^ non-zero test

return [] -- allow structuralTraversal to see ExprF

instance FunctorFC     ExprF where fmapFC    = fmapFCDefault
instance FoldableFC    ExprF where foldMapFC = foldMapFCDefault
instance TraversableFC ExprF where
  traverseFC = $(structuralTraversal [t|ExprF|] [])

-- | Compute the logical type of an expression formed by an 'ExprF'
instance HasType (ExprF e) where
  hasType Bool   {} = knownRep
  hasType Int    {} = knownRep
  hasType And    {} = knownRep
  hasType Add    {} = knownRep
  hasType NonZero{} = knownRep

evalExprF :: ExprF Value' t -> Value' t
evalExprF e =
  case e of
    Bool   b                    -> Value b
    Int    i                    -> Value i
    And     (Value x) (Value y) -> Value (x && y)
    Add     (Value x) (Value y) -> Value (x + y)
    NonZero (Value x)           -> Value (x /= 0)

------------------------------------------------------------------------
-- Type-annotated variables --------------------------------------------
------------------------------------------------------------------------

data Variable :: Ctx U -> U -> Type where
  Variable ::
    { varType :: URep t
    , varIndex :: Index env t
    } -> Variable env t

instance HasType (Variable env) where hasType = varType

weakenVariable :: Diff l r -> Variable l t -> Variable r t
weakenVariable d (Variable t i) = Variable t (extendIndex' d i)

evalVariable :: Assignment Value' env -> Variable env t -> Value t
evalVariable env v = getValue (env ! varIndex v)

lastVar :: KnownRep t => Size env -> Variable (env ::> t) t
lastVar s = Variable knownRep (nextIndex s)

------------------------------------------------------------------------
-- Recursively defined expression trees with variables -----------------
------------------------------------------------------------------------

-- | Recursively defined expression trees with variables
data Expr :: Ctx U -> U -> Type where
  ExprVar  :: Variable env     t -> Expr env t
  ExprF    :: ExprF (Expr env) t -> Expr env t

instance HasType (Expr env) where
  hasType (ExprVar v) = hasType v
  hasType (ExprF   e) = hasType e

evalExpr ::
  Assignment Value' env {- ^ variable environment -} ->
  Expr env t            {- ^ expression           -} ->
  Value t               {- ^ evaluated expression -}
evalExpr env (ExprVar v) = evalVariable env v
evalExpr env (ExprF exprf) =
  getValue (evalExprF (fmapFC (Value . evalExpr env) exprf))

------------------------------------------------------------------------
-- Simple expressions --------------------------------------------------
------------------------------------------------------------------------

data Simple :: Ctx U -> U -> Type where
  SimpleVar :: Variable env t -> Simple env t
  SimpleVal :: Value        t -> Simple env t

weakenSimple :: Diff env env' -> Simple env t -> Simple env' t
weakenSimple _ (SimpleVal x) = SimpleVal x
weakenSimple d (SimpleVar x) = SimpleVar (weakenVariable d x)

evalSimple :: Assignment Value' env -> Simple env t -> Value t
evalSimple env (SimpleVar v) = evalVariable env v
evalSimple _   (SimpleVal v) = v

------------------------------------------------------------------------
-- Single assignment low-level target language -------------------------
------------------------------------------------------------------------

data SSA :: Ctx U -> U -> Type where
  SSASimple :: Simple env t -> SSA env t
  (:>>)     :: ExprF (Simple env) t -> SSA (env ::> t) u -> SSA env u

infixr 5 :>>

compile :: Size env -> Expr env t -> SSA env t
compile s e = compileK s noDiff e \_ -> SSASimple

type M src dst t u = Size dst -> Diff src dst -> t -> SSA dst u

compileK ::
  forall src tgt t u.
  Size tgt ->
  Diff src tgt ->
  Expr src t ->
  (forall env. Diff tgt env -> Simple env t -> SSA env u) ->
  SSA tgt u
compileK s1 d1 e k =
  case e of
    ExprVar v -> k noDiff (SimpleVar (weakenVariable d1 v))
    ExprF ef ->
      case ef of
        Bool b -> k noDiff (SimpleVal b)
        Int  i -> k noDiff (SimpleVal i)

        NonZero x -> compileK s1 d1 x \d2 x' -> let s2 = extSize s1 d2 in
                     NonZero x' :>>
                     k (extendRight d2) (SimpleVar (lastVar s2))

        And x y -> binOp And x y
        Add x y -> binOp Add x y

  where
    binOp ::
      forall t1 t2.
      KnownRep t =>
      (forall e. e t1 -> e t2 -> ExprF e t) ->
      (Expr src t1 -> Expr src t2 -> SSA tgt u)
    binOp op x y =
      compileK s1 d1          x \d2 x' -> let s2 = extSize s1 d2 in
      compileK s2 (d1 <+> d2) y \d3 y' -> let s3 = extSize s2 d3 in
      op (weakenSimple d3 x') y' :>>
      k (extendRight (d2 <+> d3))
        (SimpleVar (lastVar s3))

evalSSA :: Assignment Value' env -> SSA env t -> Value t
evalSSA env (SSASimple s) = evalSimple env s
evalSSA env (s :>> ssa) = evalSSA (extend env sval) ssa
  where
    sval = evalExprF (fmapFC (Value . evalSimple env) s)

------------------------------------------------------------------------
-- Example expression --------------------------------------------------
------------------------------------------------------------------------

ex1 :: Expr EmptyCtx IntT
ex1 = ExprF (Add fiveTen fiveTen)
  where
    fiveTen =
      ExprF (Add (ExprF (Int 5))
                 (ExprF (Int 10)))

-- | Evaluate an expression using 'evalExpr' and also with
-- 'evalSSA' after compiling with 'compile' checking  if
-- the outputs are equal.
compileTest :: Assignment Value' env -> Expr env t -> Bool
compileTest env e =
  case hasType e of
    BoolRep -> evalExpr env e == evalSSA env (compile (size env) e)
    IntRep  -> evalExpr env e == evalSSA env (compile (size env) e)

------------------------------------------------------------------------
-- Untyped syntax ------------------------------------------------------
------------------------------------------------------------------------

-- | Untyped expressions
data UExpr :: Type where
  UVar   :: String -> UExpr
  UExprF :: ExprF (Const UExpr) t -> UExpr

typeCheck ::
  forall env.
  (String -> Maybe (Some (Variable env))) ->
  UExpr ->
  Maybe (Some (Expr env))
typeCheck checkVar (UVar name) = mapSome ExprVar <$> checkVar name
typeCheck checkVar (UExprF ef) =
  case ef of
    Int i     -> done (Int i)
    Bool i    -> done (Bool i)
    NonZero x -> done =<< NonZero <$> helper x
    And x y   -> done =<< And <$> helper x <*> helper y
    Add x y   -> done =<< Add <$> helper x <*> helper y
  where
    helper :: forall (z :: U) t. KnownRep t => Const UExpr z -> Maybe (Expr env t)
    helper = viewSome (cast knownRep) <=< typeCheck checkVar . getConst

    done = Just . Some . ExprF

------------------------------------------------------------------------
-- Missing parameterized-utils functionality ---------------------------
------------------------------------------------------------------------

(<+>) :: forall a b c. Diff a b -> Diff b c -> Diff a c
(<+>) ab bc
  | IsAppend x <- diffIsAppend ab
  , IsAppend y <- diffIsAppend bc
  , Refl       <- assoc (Proxy :: Proxy a) x y
  = appendDiff (addSize x y)
{-# INLINE (<+>) #-}
