module TyCoRep where

import GhcPrelude

import Outputable ( SDoc )
import Data.Data  ( Data )
import {-# SOURCE #-} Var( Var, ArgFlag, AnonArgFlag )

data Type
data TyThing
data Coercion
data CoercionHole
data UnivCoProvenance
data TCvSubst
data TyLit
data TyCoBinder
data MCoercion

type PredType = Type
type Kind = Type
type ThetaType = [PredType]
type CoercionN = Coercion
type MCoercionN = MCoercion

pprKind :: Kind -> SDoc
pprType :: Type -> SDoc
mkFunTy   :: AnonArgFlag -> Type -> Type -> Type
mkForAllTy :: Var -> ArgFlag -> Type -> Type

isRuntimeRepTy :: Type -> Bool

coHoleCoVar :: CoercionHole -> Var

instance Data Type  -- To support Data instances in CoAxiom
