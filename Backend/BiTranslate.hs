{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE BangPatterns         #-}

module Backend.BiTranslate (biTranslate) where

import Backend.FcTypes
import Backend.Typechecking

import Utils.Annotated
import Utils.Substitution
import Utils.Kind
import Utils.Unique
import Utils.AssocList
import Utils.Ctx
import Utils.PrettyPrint
import Utils.Errors
import Utils.Utils
import Utils.Trace

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Debug.Trace

import Data.List.Extra (allSame)

-- * Type checking
-- ----------------------------------------------------------------------------

data Mode = Synth | Check

showMode :: Mode -> String
showMode Synth = "Synth"
showMode Check = "Check"

-- FIXME
isMonoTy :: FcType -> Bool
isMonoTy (FcTyAbs _ _) = False
isMonoTy (FcTyApp _ _) = True
isMonoTy (FcTyVar _) = True
isMonoTy (FcTyCon _) = True 

-- | Type check a System F term and translate it to the bidirectional system
transTerm :: (FcTerm 'SF) -> Mode -> FcM (FcType, FcTerm 'Bi)
-- transTerm !tm s | trace ("translating:\n" ++ (render $ ppr tm) ++ "\n\n##With mode " ++ showMode s ++ "\n\n\n") False = undefined
transTerm (FcTmAbs x ty1 tm) s = do
  kind <- tcType ty1 -- GEORGE: Should have kind star
  unless (kind == KStar) $
    throwError "transTerm: Kind mismatch (FcTmAbs)"
  (ty2,tm2) <- extendCtxTmM x ty1 (transTerm tm Check)
  let fcTy  = mkFcArrowTy ty1 ty2
      tmBi' = (FcTmAbsBi x tm2)
      tmBi  = case s of
                Synth -> FcTmAnn tmBi' fcTy
                Check -> tmBi'
      in return (fcTy , tmBi)
transTerm (FcTmVar x) _ = do
  ty <- lookupTmVarM x
  return (ty, FcTmVar x)

transTerm (FcTmApp tm1 tm2) s
  | isData tm1 = do
      (ty1, tmBi1) <- transTerm tm1 Check
      case isFcArrowTy ty1 of
        Nothing           -> throwErrorM (text "Wrong function FcType application"
                                      $$ (text "Not a function: " <+> ppr ty1))
        Just (ty1a, ty1b) -> do
          (ty2, tmBi2) <- case isMonoTy ty1a of
                       False -> transTerm tm2 Synth
                       True  -> transTerm tm2 Check
          alphaEqFcTypes ty2 ty1a >>= \case
              False -> throwErrorM (text "Argument types don't match" 
                                $$ (text "Expected: " <+> ppr ty1a
                                $$ (text "Got:      " <+> ppr ty2)))
              True  -> case s of 
                         Synth -> return (ty1b, (FcTmAnn (FcTmApp tmBi1 tmBi2) ty1b))
                         Check -> return (ty1b, (FcTmApp tmBi1 tmBi2))

transTerm (FcTmApp tm1 tm2) _ = do
  -- application always switches to synthesis mode
  (ty1, tmBi1) <- transTerm tm1 Synth
  (ty2, tmBi2) <- case isMonoTy ty1 of
    True  -> transTerm tm2 Check
    False -> transTerm tm2 Synth
  case isFcArrowTy ty1 of
    Just (ty1a, ty1b) -> alphaEqFcTypes ty1a ty2 >>= \case
      True  -> return (ty1b, (FcTmApp tmBi1 tmBi2))
      False -> throwErrorM (text "transTerm" <+> text "FcTmApp" $$ pprPar ty1a $$ pprPar ty2)
    Nothing           -> throwErrorM (text "Wrong function FcType application"
                                      $$ parens (text "ty1=" <+> ppr ty1)
                                      $$ parens (text "ty2=" <+> ppr ty2))

transTerm (FcTmTyAbs (a :| k) tm) s = do
  tyVarNotInFcCtxM a -- GEORGE: Ensure not already bound
  -- either we're in checking mode already or the bi term must be annotated
  (ty, tmBi) <- extendCtxTyM a k (transTerm tm Check)
  let ty' = (FcTyAbs (a :| k) ty)
  tmBi' <- case s of
            Synth -> pure $ FcTmAnn tmBi ty'
            Check -> pure $ tmBi
  pure (ty' , tmBi')

transTerm (FcTmTyApp tm ty) s
  | isData tm = do
  kind <- tcType ty
  (tyTm, tmBi) <- transTerm tm Check
  case tyTm of
    (FcTyAbs (a :| k) tm_ty) 
      | k == kind -> let tyTm' = substVar a ty tm_ty
                         tmBi' = case s of
                           Synth   -> FcTmAnn tmBi tyTm'
                           Check -> tmBi
                         in return ((substVar a ty tm_ty) , tmBi')
    _  -> throwError "Malformed type application"

transTerm (FcTmTyApp tm ty) s = do
  kind <- tcType ty
  (tyTm, tmBi) <- transTerm tm Synth
  case tyTm of
    (FcTyAbs (a :| k) tm_ty) 
      | k == kind -> let tyTm' = substVar a ty tm_ty
                         tmBi' = case s of
                           Synth   -> FcTmAnn tmBi tyTm'
                           Check -> tmBi
                         in return ((substVar a ty tm_ty) , tmBi')
    _  -> throwError "Malformed type application"

transTerm (FcTmLet x ty tm1 tm2) _ = do
  tmVarNotInFcCtxM x -- GEORGE: Ensure not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    throwError "transTerm: Kind mismatch (FcTmLet)"
  (ty1, tmBi1) <- extendCtxTmM x ty (transTerm tm1 Check)
  (ty2, tmBi2) <- extendCtxTmM x ty (transTerm tm2 Synth)
  eq <- alphaEqFcTypes ty ty1
  case eq of
    True  -> return (ty2, (FcTmLet x ty tmBi1 tmBi2))
    False -> throwErrorM (text "Let type doesnt match"
                          $$ parens (text "ty1=" <+> ppr ty)
                          $$ parens (text "ty2=" <+> ppr ty1))

transTerm (FcTmDataCon dc) _ = do
  ty <- mkDataConTy <$> lookupDataConTyM dc
  return (ty, FcTmDataCon dc)
transTerm (FcTmCase scr alts) s = do
  dc_tys <- mapM getConTy alts
  unless (allSame dc_tys) $
    throwErrorM (text "Cases do not belong to same datatype")
  (scrTy,biScr) <- transTerm scr Synth
  (tmTy,biAlts) <- transAlts alts scrTy
  case s of
    Synth -> return (tmTy, FcTmAnn (FcTmCase biScr biAlts) tmTy)
    Check -> return (tmTy, FcTmCase biScr biAlts)
  where getConTy :: FcAlt s -> FcM FcTyCon
        getConTy (FcAlt (FcConPat dc _) _) = do
          (_,_,tc) <- lookupDataConTyM dc
          return tc

transAlts :: [FcAlt 'SF] -> FcType -> FcM (FcType, [FcAlt 'Bi])
transAlts alts scr_ty = do
  biAlts <- mapM (\x -> checkAlt x scr_ty) alts
  let biAlts' = map (\(_,tm) -> tm) biAlts
  let ((ty,_):_) = biAlts
  return (ty, biAlts')

checkAlt :: FcAlt 'SF -> FcType -> FcM (FcType, FcAlt 'Bi)
checkAlt (FcAlt (FcConPat dc xs) rhs) scr_ty = case tyConAppMaybe scr_ty of
  Just (tc, tys) -> do
    tmVarsNotInFcCtxM xs
    (as, arg_tys, dc_tc) <- lookupDataConTyM dc
    unless (dc_tc == tc) $
      throwErrorM (text "checkAlt" <+> colon <+> text "The type of the scrutinee does not match that of the pattern")
    let ty_subst     = mconcat (zipWithExact (|->) as tys)
    let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys  
    (ty,biRhs) <- extendCtxTmsM xs real_arg_tys (transTerm rhs Check)
    return (ty, FcAlt (FcConPat dc xs) biRhs)
  Nothing -> throwErrorM (text "destructScrTy" <+> colon <+> text "Not a tycon application")

transValBind :: FcValBind 'SF -> FcM (FcCtx, FcValBind 'Bi)
transValBind (FcValBind x ty tm) = do
  tmVarNotInFcCtxM x  -- GEORGE: Ensure is not already bound
  kind <- tcType ty
  unless (kind == KStar) $
    throwError "tcValBind: Kind mismatch (FcValBind)"
  (ty',tm') <- extendCtxTmM x ty (transTerm tm Check)
  unless (ty `eqFcTypes` ty') $ throwErrorM (text "Global let type doesnt match:"
                                $$ parens (text "given:" <+> ppr ty)
                                $$ parens (text "inferred:" <+> ppr ty'))
  ctx <- extendCtxTmM x ty ask -- GEORGE: Return the extended environment
  return (ctx, (FcValBind x ty' tm'))
 
transProg :: FcProgram 'SF -> FcM (FcProgram 'Bi)
transProg (FcPgmDataDecl datadecl pgm) = do
  tcFcDataDecl datadecl
  biPgm <- transProg pgm
  return (FcPgmDataDecl datadecl biPgm)
transProg (FcPgmValDecl valbind pgm) = do
  (fc_ctx, biBind) <- transValBind valbind
  biPgm <- setCtxM fc_ctx $ transProg pgm
  return (FcPgmValDecl biBind biPgm)
transProg (FcPgmTerm tm) = do
  (_, biTm) <- transTerm tm Synth
  return (FcPgmTerm biTm)

-- * Invoke the complete System F type checker
-- ----------------------------------------------------------------------------

-- GEORGE: Refine the type and also print more stuff out

biTranslate :: (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)
            -> UniqueSupply -> (FcProgram 'SF)
            -> (Either String (((FcProgram 'Bi), UniqueSupply), FcGblEnv),  Trace)
biTranslate (tc_env, dc_env) us tm = runWriter
                                   $ runExceptT
                                   $ flip runStateT  fc_init_gbl_env
                                   $ flip runReaderT fc_init_ctx
                                   $ flip runUniqueSupplyT us
                                   $ transProg tm
  where
    fc_init_ctx     = mempty
    fc_init_gbl_env = FcGblEnv tc_env dc_env
