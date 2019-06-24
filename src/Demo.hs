{-# Language TypeOperators, TemplateHaskell, TypeFamilies, GADTs, DataKinds,
             KindSignatures, ScopedTypeVariables, BlockArguments, RankNTypes,
             TypeInType, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wall #-}
module Demo where

import Data.Kind                        (Type)
import Data.Parameterized.Context       (Assignment, Ctx, EmptyCtx, (::>),
                                         Index, Diff, Size, extendIndex',
                                         nextIndex, (!), noDiff, extSize,
                                         extendRight, extend, size)
import Data.Parameterized.TraversableFC (FunctorFC(..), FoldableFC(..), TraversableFC(..),
                                         fmapFCDefault, foldMapFCDefault)
import Data.Parameterized.TH.GADT       (structuralTypeEquality, structuralTraversal)
import Data.Parameterized.Classes       (ShowF(showsPrecF), TestEquality(..), (:~:)(Refl))
import Data.Parameterized.Some          (Some(Some), mapSome, viewSome)
import Control.Category                 ((.))
import Prelude                          hiding ((.))

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
  Add     :: e IntT  -> e IntT  -> ExprF e IntT  -- ^ arithetic adition
  NonZero :: e IntT  ->            ExprF e BoolT -- ^ non-zero test
  Ifte    :: URep r -> e BoolT -> e r -> e r -> ExprF e r -- ^ if-then-else

return [] -- allow structuralTraversal to see ExprF

instance FunctorFC     ExprF where fmapFC    = fmapFCDefault
instance FoldableFC    ExprF where foldMapFC = foldMapFCDefault
instance TraversableFC ExprF where
  traverseFC = $(structuralTraversal [t|ExprF|] [])

-- | Compute the logical type of an expression formed by an 'ExprF'
instance HasType (ExprF e) where
  hasType Bool   {} = knownRep
  hasType Int    {} = knownRep
  hasType Add    {} = knownRep
  hasType NonZero{} = knownRep
  hasType (Ifte rep _ _ _) = rep

evalExprF :: ExprF Value' t -> Value' t
evalExprF e =
  case e of
    Bool b                      -> Value b
    Int i                       -> Value i
    Add (Value x) (Value y)     -> Value (x + y)
    NonZero (Value x)           -> Value (x /= 0)
    Ifte _ (Value True ) x _    -> x
    Ifte _ (Value False) _ x    -> x

------------------------------------------------------------------------
-- Type-annotated variables --------------------------------------------
------------------------------------------------------------------------

data Variable :: Ctx U -> U -> Type where
  Variable :: URep t -> Index env t -> Variable env t

instance HasType (Variable env) where
  hasType (Variable rep _) = rep

weakenVariable :: Diff l r -> Variable l t -> Variable r t
weakenVariable d (Variable t i) = Variable t (extendIndex' d i)

evalVariable :: Assignment Value' env -> Variable env t -> Value t
evalVariable env (Variable _ i) = getValue (env ! i)

lastVar :: KnownRep t => Size env -> Variable (env ::> t) t
lastVar = lastVar' knownRep

lastVar' :: URep t -> Size env -> Variable (env ::> t) t
lastVar' rep s = Variable rep (nextIndex s)

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
compile s e = compileK s noDiff e \_ -> Return

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
        Bool b -> k noDiff (SimpleBool b)
        Int  i -> k noDiff (SimpleInt  i)

        NonZero x ->
          compileK s1 d1 x \d2 x' -> let s2 = extSize s1 d2 in

          NonZero x' :>>
          k (extendRight d2) (SimpleVar (lastVar s2))

        Add x y ->
          compileK s1 (     d1) x \d2 x' -> let s2 = extSize s1 d2 in
          compileK s2 (d2 . d1) y \d3 y' -> let s3 = extSize s2 d3 in

          Add (weakenSimple d3 x') y' :>>
          k (extendRight (d3 . d2))
            (SimpleVar (lastVar s3))

        Ifte rep x y z ->
          compileK s1 (          d1) x \d2 x' -> let s2 = extSize s1 d2 in
          compileK s2 (     d2 . d1) y \d3 y' -> let s3 = extSize s2 d3 in
          compileK s3 (d3 . d2 . d1) z \d4 z' -> let s4 = extSize s3 d4 in

          Ifte rep (weakenSimple (d4 . d3) x')
                   (weakenSimple (d4     ) y')
                   (                       z') :>>
          k (extendRight (d4 . d3 . d2))
            (SimpleVar (Variable rep (nextIndex s4)))


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


------------------------------------------------------------------------
-- Show instances ------------------------------------------------------
------------------------------------------------------------------------

deriving instance Show (URep t)

instance ShowF e => Show (ExprF e t) where
  showsPrec p e =
    showParen (p >= 11)
    case e of
      Bool    b   -> showString "Bool "    . showsPrec  11 b
      Int     i   -> showString "Int "     . showsPrec  11 i
      NonZero x   -> showString "NonZero " . showsPrecF 11 x
      Add     x y -> showString "Add "     . showsPrecF 11 x
                            . showChar ' ' . showsPrecF 11 y
      Ifte rep x y z -> showString "Ifte " . showsPrec  11 rep
                            . showChar ' ' . showsPrecF 11 x
                            . showChar ' ' . showsPrecF 11 y
                            . showChar ' ' . showsPrecF 11 z

deriving instance Show (Variable env t)
deriving instance Show (UArg t)
deriving instance Show UExpr
deriving instance Show (Expr env t)
deriving instance Show (Simple env t)
deriving instance Show (SSA env t)

instance ShowF UArg
instance ShowF e => ShowF (ExprF e)
instance ShowF (Variable env)
instance ShowF (Expr env)
instance ShowF (Simple env)
