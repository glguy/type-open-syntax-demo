{-# Language TypeOperators, TemplateHaskell, TypeFamilies, GADTs, DataKinds,
             KindSignatures, ScopedTypeVariables, BlockArguments, RankNTypes,
             TypeInType, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}
module Demo where

import Data.Kind                        (Type)
import Data.Parameterized.Context       (Assignment, Ctx, EmptyCtx, (::>),
                                         Index, Diff, Size, extendIndex',
                                         nextIndex, (!), noDiff, extend, size,
                                         KnownDiff(knownDiff), extSize)
import Data.Parameterized.TraversableFC (FunctorFC(..), FoldableFC(..), TraversableFC(..),
                                         fmapFCDefault, foldMapFCDefault)
import Data.Parameterized.TH.GADT       (structuralTypeEquality, structuralTraversal)
import Data.Parameterized.Classes       (ShowF(showsPrecF), TestEquality(..), (:~:)(Refl))
-- import Data.Parameterized.Some          (Some(Some), mapSome, viewSome)
import Control.Category
import Prelude                          hiding ((.), id)

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
  Ifte    :: URep r -> e BoolT -> e r -> e r -> ExprF e r -- ^ if-then-else
  Add     :: e IntT  -> e IntT  -> ExprF e IntT  -- ^ arithetic adition
  Negate  :: e IntT  ->            ExprF e IntT  -- ^ negate integer
  NonZero :: e IntT  ->            ExprF e BoolT -- ^ non-zero test
  Not     :: e BoolT ->            ExprF e BoolT -- ^ boolean not
  Bool    :: Bool    ->            ExprF e BoolT -- ^ constant boolean
  Int     :: Int     ->            ExprF e IntT  -- ^ constant integer

return [] -- allow structuralTraversal to see ExprF

instance FunctorFC     ExprF where fmapFC    = fmapFCDefault
instance FoldableFC    ExprF where foldMapFC = foldMapFCDefault
instance TraversableFC ExprF where
  traverseFC = $(structuralTraversal [t|ExprF|] [])

-- | Compute the logical type of an expression formed by an 'ExprF'
instance HasType (ExprF e) where
  hasType Add    {} = knownRep
  hasType Bool   {} = knownRep
  hasType Int    {} = knownRep
  hasType Negate {} = knownRep
  hasType NonZero{} = knownRep
  hasType Not    {} = knownRep
  hasType (Ifte rep _ _ _) = rep

evalExprF :: ExprF Value' t -> Value' t
evalExprF e =
  case e of
    Bool b                      -> Value b
    Int i                       -> Value i
    Add (Value x) (Value y)     -> Value (x + y)
    NonZero (Value x)           -> Value (x /= 0)
    Not (Value x)               -> Value (not x)
    Negate (Value x)            -> Value (negate x)
    Ifte _ (Value c) x y        -> if c then x else y

------------------------------------------------------------------------
-- Type-annotated variables --------------------------------------------
------------------------------------------------------------------------

-- | Type-annotated variables
data Variable :: Ctx U -> U -> Type where
  Variable :: URep t -> Index env t -> Variable env t

instance HasType (Variable env) where
  hasType (Variable rep _) = rep

weakenVariable :: Diff l r -> Variable l t -> Variable r t
weakenVariable d (Variable t i) = Variable t (extendIndex' d i)

evalVariable :: Assignment Value' env -> Variable env t -> Value t
evalVariable env (Variable _ i) = getValue (env ! i)

lastVar :: URep t -> Size env -> Variable (env ::> t) t
lastVar rep s = Variable rep (nextIndex s)

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
evalExpr env (ExprF x) = getValue (evalExprF (fmapFC (Value . evalExpr env) x))

------------------------------------------------------------------------
-- Simple expressions --------------------------------------------------
------------------------------------------------------------------------

data Simple :: Ctx U -> U -> Type where
  SimpleVar :: Variable env t -> Simple env t
  SimpleInt :: Int            -> Simple env IntT
  SimpleBool:: Bool           -> Simple env BoolT

weakenSimple :: Diff env env' -> Simple env t -> Simple env' t
weakenSimple _ (SimpleInt  x) = SimpleInt  x
weakenSimple _ (SimpleBool x) = SimpleBool x
weakenSimple d (SimpleVar  x) = SimpleVar (weakenVariable d x)

evalSimple :: Assignment Value' env -> Simple env t -> Value t
evalSimple env (SimpleVar  x) = evalVariable env x
evalSimple _   (SimpleInt  x) = x
evalSimple _   (SimpleBool x) = x

------------------------------------------------------------------------
-- Single assignment low-level target language -------------------------
------------------------------------------------------------------------

-- | Single, static assignment statements. Each statement can refer back
-- to previously bound statements. The final statemnt is a return value.
data SSA :: Ctx U -> U -> Type where
  -- | Final return value
  Return :: Simple env t ->                              SSA env t
  -- | Add binding to current evironment for given expression
  (:>>)  :: ExprF (Simple env) t -> SSA (env ::> t) u -> SSA env u

infixr 5 :>>

compile :: Size env -> Expr env t -> SSA env t
compile s e = compileK (D noDiff s) e \_ -> Return

data D src tgt = D
  { dDiff :: !(Diff src tgt)
  , dSize :: !(Size tgt)
  }

extD :: KnownDiff b c => D a b -> D a c
extD (D d s) = D (knownDiff . d) (extSize s knownDiff)

truncD :: D src tgt -> D tgt tgt
truncD d = D noDiff (dSize d)

(<+>) :: D a b -> D b c -> D a c
(<+>) ab bc = D (dDiff bc . dDiff ab) (dSize bc)

compileK ::
  forall src tgt t u.
  D src tgt ->
  Expr src t ->
  (forall env. D tgt env -> Simple env t -> SSA env u) ->
  SSA tgt u
compileK d e k =
  case e of
    ExprVar v -> k (truncD d) (SimpleVar (weakenVariable (dDiff d) v))
    ExprF ef -> compileExprFK d ef k

compileExprFK ::
  forall src tgt t u.
  D src tgt ->
  ExprF (Expr src) t ->
  (forall env. D tgt env -> Simple env t -> SSA env u) ->
  SSA tgt u
compileExprFK d1 ef k =
  case ef of
    Bool b -> k (truncD d1) (SimpleBool b)
    Int  i -> k (truncD d1) (SimpleInt  i)

    NonZero x -> unary NonZero x
    Not     x -> unary Not     x
    Negate  x -> unary Negate  x

    Add x y ->
      compileK d1          x \d2 x' ->
      compileK (d1 <+> d2) y \d3 y' ->

      Add (weakenSimple (dDiff d3) x') y' :>>
      k (extD (d2 <+> d3)) (answerVar knownRep d3)

    Ifte rep x y z ->
      compileK d1                 x \d2 x' ->
      compileK (d1 <+> d2       ) y \d3 y' ->
      compileK (d1 <+> d2 <+> d3) z \d4 z' ->

      Ifte rep (weakenSimple (dDiff (d3 <+> d4)) x')
               (weakenSimple (dDiff (d4       )) y')
               (                                 z') :>>
      k (extD (d2 <+> d3 <+> d4)) (answerVar rep d4)
  where
    answerVar rep d = SimpleVar (lastVar rep (dSize d))

    unary ::
      KnownRep t =>
      (forall e. e a -> ExprF e t) ->
      Expr src a -> SSA tgt u
    unary op x =
      compileK d1 x \d2 x' -> op x' :>> k (extD d2) (answerVar knownRep d2)


evalSSA :: Assignment Value' env -> SSA env t -> Value t
evalSSA env (Return s) = evalSimple env s
evalSSA env (s :>> ssa) = evalSSA (extend env sval) ssa
  where
    sval = evalExprF (fmapFC (Value . evalSimple env) s)

------------------------------------------------------------------------
-- Example expression --------------------------------------------------
------------------------------------------------------------------------

ex1 :: Expr EmptyCtx IntT
ex1 = ExprF (Add fiveTen sixEleven)
  where
    fiveTen =
      ExprF (Add (ExprF (Int 5))
                 (ExprF (Int 10)))
    sixEleven =
      ExprF (Add (ExprF (Int 6))
                 (ExprF (Int 11)))

-- | Evaluate an expression using 'evalExpr' and also with
-- 'evalSSA' after compiling with 'compile' checking  if
-- the outputs are equal.
compileTest :: forall env t. Assignment Value' env -> Expr env t -> Bool
compileTest env e = evalExpr env e
                === evalSSA env (compile (size env) e)
  where
    (===) =
      case hasType e of
        BoolRep -> (==)
        IntRep  -> (==)

------------------------------------------------------------------------
-- Untyped syntax ------------------------------------------------------
------------------------------------------------------------------------

{- Doesn't really work since adding polymorphic Ifte primitive

-- | Untyped expressions
data UExpr :: Type where
  UVar   :: String -> UExpr
  UExprF :: ExprF UArg t -> UExpr

data UArg t = KnownRep t => UArg UExpr

typeCheck ::
  forall env.
  (String -> Maybe (Some (Variable env))) ->
  UExpr ->
  Maybe (Some (Expr env))
typeCheck checkVar (UVar name) = mapSome ExprVar <$> checkVar name
typeCheck checkVar (UExprF ef) = Some . ExprF <$> traverseFC checkArg ef
  where
    checkArg :: UArg t -> Maybe (Expr env t)
    checkArg (UArg e) = viewSome (cast knownRep) =<< typeCheck checkVar e

-}

------------------------------------------------------------------------
-- Show instances ------------------------------------------------------
------------------------------------------------------------------------

deriving instance Show (URep t)

instance ShowF e => Show (ExprF e t) where
  showsPrec p e =
    showParen (p >= 11)
    case e of
      Negate  x     -> showString "Negate"  . argF x
      Not     x     -> showString "Not"     . argF x
      Bool    x     -> showString "Bool"    . arg  x
      Int     x     -> showString "Int"     . arg  x
      NonZero x     -> showString "NonZero" . argF x
      Add     x y   -> showString "Add"     . argF x . argF y
      Ifte r  x y z -> showString "Ifte"    . arg  r . argF x . argF y . argF z
    where
      arg  x = showChar ' ' . showsPrec  11 x
      argF x = showChar ' ' . showsPrecF 11 x

deriving instance Show (Variable env t)
deriving instance Show (Expr env t)
deriving instance Show (Simple env t)
deriving instance Show (SSA env t)

instance ShowF e => ShowF (ExprF e)
instance ShowF (Variable env)
instance ShowF (Expr env)
instance ShowF (Simple env)

-- deriving instance Show (UArg t)
-- deriving instance Show UExpr
-- instance ShowF UArg
