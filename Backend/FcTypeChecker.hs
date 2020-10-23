{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}

module Backend.FcTypeChecker (fcTypeCheck, tcTerm) where

import Backend.FcTypes
import Backend.Typechecking

import Utils.Annotated
import Utils.Substitution
import Utils.Var
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint
import Utils.Errors
import Utils.Utils
import Utils.Trace

import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Except

-- * Type checking
-- ----------------------------------------------------------------------------

-- | Type check a System F term
tcTerm :: (FcTerm SF) -> FcM FcType
tcTerm (FcTmAbs x ty1 tm) = do
  kind <- tcType ty1 -- GEORGE: Should have kind star
  unless (kind == KStar) $
    throwError "tcTerm: Kind mismatch (FcTmAbs)"
  ty2  <- extendCtxTmM x ty1 (tcTerm tm)
  return (mkFcArrowTy ty1 ty2)
tcTerm (FcTmVar x) = lookupTmVarM x
tcTerm (FcTmApp tm1 tm2)  = do
  ty1 <- tcTerm tm1
  ty2 <- tcTerm tm2
  case isFcArrowTy ty1 of
    Just (ty1a, ty1b) -> alphaEqFcTypes ty1a ty2 >>= \case
      True  -> return ty1b
      False -> throwErrorM (text "tcTerm" <+> text "FcTmApp" $$ pprPar ty1a $$ pprPar ty2)
    Nothing           -> throwErrorM (text "Wrong function FcType application"
                                      $$ parens (text "ty1=" <+> ppr ty1)
                                      $$ parens (text "ty2=" <+> ppr ty2))

tcTerm (FcTmTyAbs (a :| k) tm) = do
  tyVarNotInFcCtxM a -- GEORGE: Ensure not already bound
  ty <- extendCtxTyM a k (tcTerm tm)
  return (FcTyAbs (a :| k) ty)
tcTerm (FcTmTyApp tm ty) = do
  kind <- tcType ty
  tcTerm tm >>= \case
    FcTyAbs (a :| k) tm_ty
      | k == kind -> return $ substVar a ty tm_ty
    _other               -> throwError "Malformed type application"

tcTerm (FcTmLet x ty tm1 tm2) = do
  tmVarNotInFcCtxM x -- GEORGE: Ensure not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    throwError "tcTerm: Kind mismatch (FcTmLet)"
  ty1  <- extendCtxTmM x ty (tcTerm tm1)
  alphaEqFcTypes ty ty1 >>= \case
    True  -> extendCtxTmM x ty (tcTerm tm2)
    False -> throwErrorM (text "Let type doesnt match"
                          $$ parens (text "ty1=" <+> ppr ty)
                          $$ parens (text "ty2=" <+> ppr ty1))

tcTerm (FcTmDataCon dc) = mkDataConTy <$> lookupDataConTyM dc
tcTerm (FcTmCase scr alts) = do
  scr_ty <- tcTerm scr
  tcAlts tcTerm scr_ty alts

-- * Invoke the complete System F type checker
-- ----------------------------------------------------------------------------

-- GEORGE: Refine the type and also print more stuff out

fcTypeCheck :: (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)
            -> UniqueSupply -> FcProgram SF
            -> (Either String ((FcType, UniqueSupply), FcGblEnv), Trace)
fcTypeCheck (tc_env, dc_env) us pgm = runWriter
                                    $ runExceptT
                                    $ flip runStateT  fc_init_gbl_env
                                    $ flip runReaderT fc_init_ctx
                                    $ flip runUniqueSupplyT us
                                    $ tcProgram tcTerm pgm
  where
    fc_init_ctx     = mempty
    fc_init_gbl_env = FcGblEnv tc_env dc_env
