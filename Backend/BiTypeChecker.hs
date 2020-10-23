{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE BangPatterns         #-}

module Backend.BiTypeChecker (biTypeCheck) where

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
import Utils.Trace hiding (traceM)
import Utils.Unify
import Utils.FreeVars

import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Except

import Debug.Trace

import Data.List.Extra (allSame)

-- * Type checking
-- ----------------------------------------------------------------------------

tcBiProgram :: FcProgram 'Bi -> FcM FcType
tcBiProgram = tcProgram synthTerm
tcBiValBind = tcValBind synthTerm

-- | synthesize a term's type (=> direction)
synthTerm :: FcTerm 'Bi -> FcM FcType
-- synthTerm tm | trace ("Synthing: " ++ (showTm tm) ++ "\n\n") False = undefined 
--synthTerm q@(FcTmVar x) | trace ("Synth Var: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmVar x)        = lookupTmVarM x
--synthTerm q@(FcTmAnn tm t) | trace ("Synth Ann: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmAnn tm t)     = do
  k <- tcType t
  case k of
    KStar -> (checkTerm tm t) >> (return t)
    _     -> throwErrorM (text "Wrong kind for type annotation. Expected KStar, got " <+> ppr k)
--synthTerm q@(FcTmApp tm1 tm2) | trace ("Synth App: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmApp tm1 tm2)  = do
  tyF <- synthTerm tm1
  case isFcArrowTy tyF of
    Just (tyA, tyR) -> checkTerm tm2 tyA >> return tyR
    Nothing         -> throwErrorM (text "Wrong function FcType application"
                                    $$ parens (text "Not a function type:"
                                               <+> ppr tyF))
--synthTerm q@(FcTmLet a ty tm1 tm2) | trace ("Synth Let: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmLet a ty tm1 tm2) = do
  tmVarNotInFcCtxM a
  k <- tcType ty
  unless (k == KStar) $
    throwErrorM (text "Wrong kind for type annotation. Expected KStar, got " <+> ppr k)
  extendCtxTmM a ty (checkTerm tm1 ty)
  extendCtxTmM a ty (synthTerm tm2)
--synthTerm q@(FcTmAbsBi {}) | trace ("Synth Lam: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmAbsBi {}) = throwErrorM
  $ text "synthTerm: Cannot synthesize type for lambda abstraction"
--synthTerm q@(FcTmDataCon dc) | trace ("Synth Dc:  " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmDataCon dc) = mkDataConTy <$> lookupDataConTyM dc
--synthTerm q@(FcTmCase _ _) | trace ("Synth Cas: " ++ (showTm q) ++ "\n\n") False = undefined
synthTerm (FcTmCase _ _) = throwErrorM
  $ text "synthTerm: Cannot synthesize type for case expression"

showTm :: FcTerm 'Bi -> String
showTm = printTm

printTm :: FcTerm 'Bi -> String
printTm (FcTmVar x) = render $ ppr x
printTm (FcTmAnn tm ty) = "((" ++ printTm tm ++ "):(" ++ (render $ ppr ty) ++ "))"
printTm (FcTmApp tm1 tm2) = "((" ++ printTm tm1 ++ ")app(" ++ printTm tm2 ++ "))"
printTm (FcTmLet a ty tm1 tm2) = "let " ++ (render $ ppr a) ++ "=" ++ printTm tm1 ++ " in " ++ printTm tm2
printTm (FcTmAbsBi x tm) = "(\\" ++ (render $ ppr x) ++ "." ++ printTm tm ++ ")"
printTm (FcTmDataCon dc) = render $ ppr dc
printTm (FcTmCase scr alts) = "(case " ++ printTm scr ++ " of " ++ printAlts alts ++ ")"

printAlts :: FcAlts 'Bi -> String
printAlts = foldl (++) "" . map printAlt

printAlt :: FcAlt 'Bi -> String
printAlt (FcAlt pat tm) = "(" ++ (render $ ppr pat) ++ "+>" ++ printTm tm ++ ")"
  
showTy :: FcType -> String
showTy = render . ppr

-- | check a term's type (<= direction)
checkTerm :: FcTerm 'Bi -> FcType -> FcM ()
--checkTerm tm ty | trace ("Checking: " ++ (showTm tm) ++ "\n Against: " ++ (showTy ty) ++ "\n\n") False = undefined 
checkTerm tm (FcTyAbs ak ty) = do
  k <- tcType (FcTyAbs ak ty)
  unless (k == KStar) $
    throwErrorM (text "Wrong kind for term. Expected KStar, got " <+> ppr k)
  let (a :| k') = ak
  extendCtxTyM a k' (checkTerm tm ty)
checkTerm tm@(FcTmApp tm1 tm2) ty
  | isData tm1 = do checkData tm ty
checkTerm (FcTmAbsBi x tm) ty
  | Just (tyA, tyR) <- isFcArrowTy ty = extendCtxTmM x tyA (checkTerm tm tyR)
checkTerm (FcTmCase scr []  ) ty = throwError "Case alternatives empty"
checkTerm (FcTmCase scr alts) ty = do
  dc_tys <- mapM getConTy alts
  unless (dc_tys /= []) $
    throwErrorM (text "No constructor type found")
  unless (allSame dc_tys) $
    throwErrorM (text "Cases do not belong to same datatype")
  scr_ty <- synthTerm scr
  checkAlts alts scr_ty ty
  where getConTy :: FcAlt 'Bi -> FcM FcTyCon
        getConTy (FcAlt (FcConPat dc _) _) = do
          (_,_,tc) <- lookupDataConTyM dc
          return tc
checkTerm tm ty = do
  k <- tcType ty
  unless (k == KStar) $
    throwErrorM (text "Wrong kind for term. Expected KStar, got " <+> ppr k)
  ty2 <- synthTerm tm
  eq  <- alphaEqFcTypes ty ty2
  case ty2 of
    FcTyAbs ak _       -> unify (ftyvsOf ty) [ty :-: (skipForall ty2)] >> return ()
    _other | eq        -> return ()
           | otherwise -> throwErrorM (text "Type mismatch in checking."
                                        $$ (text "Expected: " <+> ppr ty)
                                        $$ (text "Got:      " <+> ppr ty2))

skipForall :: FcType -> FcType
skipForall (FcTyAbs _ ty) = skipForall ty
skipForall ty             = ty

checkData :: FcTerm 'Bi -> FcType -> FcM ()
checkData tm ty = do
  -- traceM "---------------------"
  -- traceM (render $ ppr tm)
  -- traceM (render $ ppr ty)
  let dc = getData tm
  -- traceM (render $ ppr dc)
  (vars, argTys, tc) <- lookupDataConTyM dc
  -- traceM (render $ ppr vars)
  -- traceM (render $ ppr argTys)
  -- traceM (render $ ppr tc)
  let (checkTc,checkTys) = getTys ty []
  -- traceM (render $ ppr checkTc)
  -- traceM (render $ ppr checkTys)
  unless (tc == checkTc) $
    throwErrorM (text "Datatype did not match."
                $$ (text "Expected: " <+> ppr checkTc)
                $$ (text "Got:      " <+> ppr tc))
  tcArgs <- lookupTyConArgsM tc
  -- traceM (render $ ppr tcArgs)
  let tcArgs' = map FcTyVar tcArgs
  let tys = reverse $ foldl substTy argTys (zipWith (|->) tcArgs checkTys)
  -- traceM (render $ ppr tys)
  check tm tys
  where getData :: FcTerm 'Bi -> FcDataCon
        getData (FcTmDataCon dc) = dc
        getData (FcTmApp tm _)   = getData tm
        substTy :: [FcType] -> FcTySubst -> [FcType]
        substTy tys sub = map (substFcTyInTy sub) tys
        getTys :: FcType -> [FcType] -> (FcTyCon,[FcType])
        getTys (FcTyApp ty1 ty2) tys = getTys ty1 (ty2:tys)
        getTys (FcTyCon tc) tys      = (tc,tys)
        getTys ty _ = error (render $ ppr ty)
        check :: FcTerm 'Bi -> [FcType] -> FcM ()
        check (FcTmDataCon dc) [] = return () 
        check (FcTmApp tm1 tm2) (ty:tys) = check tm1 tys >> checkTerm tm2 ty

checkAlts :: [FcAlt 'Bi] -> FcType -> FcType -> FcM ()
checkAlts alts scr_ty res_ty = do
  mapM (\x -> checkAlt x scr_ty res_ty) alts
  return ()

checkAlt :: FcAlt 'Bi -> FcType -> FcType -> FcM ()
checkAlt (FcAlt (FcConPat dc xs) rhs) scr_ty res_ty = case tyConAppMaybe scr_ty of
  Just (tc, tys) -> do
    tmVarsNotInFcCtxM xs
    (as, arg_tys, dc_tc) <- lookupDataConTyM dc
    unless (dc_tc == tc) $
      throwErrorM (text "checkAlt" <+> colon <+> text "The type of the scrutinee does not match that of the pattern")
    let ty_subst     = mconcat (zipWithExact (|->) as tys)
    let real_arg_tys = map (substFcTyInTy ty_subst) arg_tys  
    extendCtxTmsM xs real_arg_tys (checkTerm rhs res_ty)
  Nothing -> throwErrorM (text "destructScrTy" <+> colon <+> text "Not a tycon application")

-- * Invoke the complete System F type checker
-- ----------------------------------------------------------------------------

-- GEORGE: Refine the type and also print more stuff out

biTypeCheck :: (AssocList FcTyCon FcTyConInfo, AssocList FcDataCon FcDataConInfo)
            -> UniqueSupply -> FcProgram 'Bi
            -> (Either String ((FcType, UniqueSupply), FcGblEnv), Trace)
biTypeCheck (tc_env, dc_env) us pgm = runWriter
                                    $ runExceptT
                                    $ flip runStateT  fc_init_gbl_env
                                    $ flip runReaderT fc_init_ctx
                                    $ flip runUniqueSupplyT us
                                    $ tcBiProgram pgm
  where
    fc_init_ctx     = mempty
    fc_init_gbl_env = FcGblEnv tc_env dc_env
