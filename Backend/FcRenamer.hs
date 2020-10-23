{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Backend.FcRenamer (fcRename) where

import Backend.FcTypes

import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint
import Utils.Utils
import Utils.Annotated
import Utils.FreeVars
import Utils.Trace

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.List (nub)
import Control.Arrow (second)

-- * Renaming monad
-- ------------------------------------------------------------------------------

-- | The renaming context maps parsed term and type variables to renamed term
-- and type variables, respectively.
type RnCtx = Ctx PsFcTmVar RnFcTmVar PsFcTyVar RnFcTyVar

type RnM = UniqueSupplyT (ReaderT RnCtx (ExceptT String (Writer Trace)))

-- * Basic Monadic Setters and Getters
-- ------------------------------------------------------------------------------

-- | Assign a unique to a plain symbol
rnSym :: MonadUnique m => Sym -> m Name
rnSym s = getUniqueM >>= return . mkName s

-- | Lookup an already-bound method name
-- * Rename Types
-- ------------------------------------------------------------------------------

-- | Rename a type variable
rnTyVar :: PsFcTyVarWithKind -> RnM RnFcTyVar
rnTyVar (a :| kind) = flip mkRnFcTyVar kind <$> rnSym (symOf a)

-- | Rename a type, abstracted over System F/Bidirectional types
rnFcType :: PsFcType s -> RnM (RnFcType s)
rnFcType  FcTyBool       = return FcTyBool
rnFcType (FcTyVar v)     = FcTyVar <$> lookupTyVarM v
rnFcType (FcTyArr t1 t2) = FcTyArr <$> rnFcType t1 <*> rnFcType t2
rnFcType (FcTyAbs a  ty) = do
  rna  <- rnTyVar a
  rnty <- extendCtxTyM (labelOf a) rna (rnFcType ty)
  return (FcTyAbs (rna :| kindOf rna) rnty)
rnFcType (FcTyApp t1 t2) = FcTyApp <$> rnFcType t1 <*> rnFcType t2

-- * Rename Terms
-- ------------------------------------------------------------------------------

-- | Rename a term variable
rnTmVar :: PsFcTmVar -> RnM RnFcTmVar
rnTmVar psx = mkRnFcTmVar <$> rnSym (symOf psx)

-- | Rename a term
rnFcTerm :: PsFcTerm s -> RnM (RnFcTerm s)
rnFcTerm  FcTmTrue = return FcTmTrue
rnFcTerm  FcTmFalse = return FcTmFalse
rnFcTerm (FcTmAbs x ty tm) = do
  rnx  <- rnTmVar x
  rnty <- rnFcType ty
  rntm <- extendCtxTmM x rnx (rnFcTerm tm)
  return (FcTmAbs rnx rnty rntm)
rnFcTerm (FcTmVar x) = FcTmVar <$> lookupTmVarM x
rnFcTerm (FcTmApp t1 t2) = FcTmApp <$> rnFcTerm t1 <*> rnFcTerm t2
rnFcTerm (FcTmTyAbs a tm) = do
  rna  <- rnTyVar a
  rntm <- extendCtxTyM (labelOf a) rna (rnFcTerm tm)
  return (FcTmTyAbs (rna :| kindOf rna) rntm)
rnFcTerm (FcTmTyApp tm ty) = FcTmTyApp <$> rnFcTerm tm <*> rnFcType ty
rnFcTerm (FcTmLet x ty tm1 tm2) = do
  rnx   <- rnTmVar x
  rnty  <- rnFcType ty
  rntm1 <- extendCtxTmM x rnx (rnFcTerm tm1)
  rntm2 <- extendCtxTmM x rnx (rnFcTerm tm2)
  return (FcTmLet rnx rnty rntm1 rntm2)

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTmVars :: [(PsFcTmVar, RnFcTmVar)] -> RnM a -> RnM a
extendTmVars binds m = extendCtxTmsM xs xs' m
  where (xs,xs') = unzip binds

-- GEORGE: Make this a separate function in Utils.Ctx?
extendTyVars :: [(PsFcTyVar, RnFcTyVar)] -> RnM a -> RnM a
extendTyVars binds m = extendCtxTysM as as' m
  where (as,as') = unzip binds

-- * Invoke the complete renamer
-- ------------------------------------------------------------------------------

fcRename :: UniqueSupply -> PsFcTerm s
         -> (Either String (RnFcTerm s, UniqueSupply), Trace)
fcRename us tm = runWriter
               $ runExceptT
               $ flip runReaderT rn_init_ctx
               $ flip runUniqueSupplyT us
               $ rnFcTerm tm
  where
    rn_init_ctx     = mempty

-- | Throw an error
throwErrorRnM :: Doc -> RnM a
throwErrorRnM d = throwError (renderError d)
