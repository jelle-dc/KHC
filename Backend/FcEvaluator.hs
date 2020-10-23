{-# LANGUAGE GADTs      #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Backend.FcEvaluator (fcEvaluate) where

import Backend.FcTypes

import Utils.Annotated
import Utils.Kind
import Utils.PrettyPrint
import Utils.SnocList
import Utils.Substitution
import Utils.Unique
import Utils.Var

import Data.Maybe
import Debug.Trace

import Control.Monad.Reader

-- * Evaluation Monad
-- ----------------------------------------------------------------------------

type Ctx a = [FcValBind a]
type FcEM a = ReaderT (Ctx a) UniqueSupplyM

-- * Term Evaluation
-- ----------------------------------------------------------------------------

fcEvalTmStep :: FcTerm a -> FcEM a (Maybe (FcTerm a))
fcEvalTmStep (FcTmApp tm1 tm2) = case tm1 of
  FcTmAbs x ty tm3 -> do
    tm2' <- freshenFcVars tm2
    return $ Just $ substFcTmInTm (x |-> tm2') tm3
  FcTmAbsBi x tm3 -> do
    tm2' <- freshenFcVars tm2
    return $ Just $ substFcTmInTm (x |-> tm2') tm3
  _                -> fcEvalTmStep tm1 >>= \case
    Nothing   -> return Nothing
    Just tm1' -> return $ Just $ FcTmApp tm1' tm2
fcEvalTmStep (FcTmTyApp tm1 ty) = case tm1 of
  FcTmTyAbs (a :| k) tm2 -> return $ Just $ substFcTyInTm (a |-> ty) tm2
  _               -> fcEvalTmStep tm1 >>= \case
    Nothing   -> return Nothing
    Just tm1' -> return $ Just $ FcTmTyApp tm1' ty
fcEvalTmStep (FcTmLet x ty tm1 tm2) = do
  tm3 <- freshenFcVars (FcTmLet x ty tm1 tm1)
  return $ Just $ substFcTmInTm (x |-> tm3) tm2
fcEvalTmStep (FcTmAnn tm ty) = return (Just tm)
fcEvalTmStep (FcTmCase scr alts) = do
  case getTmConAndArgs scr of
    Just (dc, args) -> do
      let alt = getMatchingAlt dc alts
      let (vars, rhs) = fromJust alt
      return $ Just $ foldl (flip substFcTmInTm) rhs (zipWith (\x y -> (x |-> y)) vars args)
    Nothing -> do
      tm <- fcEvalTmStep scr
      case tm of
        Just tm' -> return $ Just $ FcTmCase tm' alts
        Nothing  -> undefined
fcEvalTmStep (FcTmVar x) = lookupVbM x >>= \case
  Just (tm, ty) -> return $ Just tm
  Nothing -> error "Encountered unbound variable during execution"
fcEvalTmStep (FcTmAbs _ _ _)   = return Nothing
fcEvalTmStep (FcTmAbsBi _ _)   = return Nothing
fcEvalTmStep (FcTmTyAbs _ _)   = return Nothing
fcEvalTmStep (FcTmDataCon _)   = return Nothing

fcEvalTm :: FcTerm a -> FcEM a (FcTerm a)
fcEvalTm tm = fcEvalTmStep tm >>= \case
  Nothing    -> return tm
  (Just tm') -> fcEvalTm tm'

getTmConAndArgs :: FcTerm a -> Maybe (FcDataCon, [FcTerm a])
getTmConAndArgs = flip getTmConAndArgs' $ []
  where getTmConAndArgs' :: FcTerm a -> [FcTerm a] -> Maybe (FcDataCon, [FcTerm a])
        getTmConAndArgs' (FcTmTyApp tm _)  args = getTmConAndArgs' tm   args
        getTmConAndArgs' (FcTmApp tm1 tm2) args = getTmConAndArgs' tm1 (tm2:args)
        getTmConAndArgs' (FcTmDataCon dc)  args = Just (dc, args)
        getTmConAndArgs' _                 _    = Nothing

getMatchingAlt :: FcDataCon -> [FcAlt a] -> Maybe ([FcTmVar], FcTerm a)
getMatchingAlt con alts =
  listToMaybe [ (vars, rhs) | (FcAlt (FcConPat altCon vars) rhs) <- alts, con == altCon]

freshenFcVars :: FcTerm a -> FcEM a (FcTerm a)
freshenFcVars (FcTmAbs x1 ty tm1) = do
  x2 <- lift freshFcTmVar
  let tm2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tm1
  FcTmAbs x2 ty <$> freshenFcVars tm2
freshenFcVars (FcTmAbsBi x1 tm1) = do
  x2 <- lift freshFcTmVar
  let tm2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tm1
  FcTmAbsBi x2 <$> freshenFcVars tm2
freshenFcVars (FcTmVar x) = return $ FcTmVar x
freshenFcVars (FcTmApp tm1 tm2) = FcTmApp <$> freshenFcVars tm1 <*> freshenFcVars tm2
freshenFcVars (FcTmTyAbs (a1 :| k1) tm1) = do
  a2 <- lift (freshFcTyVar k1)
  let tm2 = substFcTyInTm (a1 |-> (FcTyVar a2)) tm1
  FcTmTyAbs (a2 :| k1) <$> freshenFcVars tm2
freshenFcVars (FcTmTyApp tm1 ty) = flip FcTmTyApp ty <$> freshenFcVars tm1
freshenFcVars (FcTmLet x1 ty tmL1 tmR1) = do
  x2 <- lift freshFcTmVar
  let tmL2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tmL1
      tmR2 = substFcTmInTm (x1 |-> (FcTmVar x2)) tmR1
  FcTmLet x2 ty <$> freshenFcVars tmL2 <*> freshenFcVars tmR2
freshenFcVars (FcTmAnn tm ty) = FcTmAnn <$> freshenFcVars tm <*> (return ty)
freshenFcVars (FcTmCase scr alts) = FcTmCase <$> freshenFcVars scr <*> freshenAlts alts
freshenFcVars (FcTmDataCon dc) = return (FcTmDataCon dc)

freshenAlts :: [FcAlt a] -> FcEM a [FcAlt a]
freshenAlts alts = mapM freshenAlt alts

freshenAlt :: FcAlt a -> FcEM a (FcAlt a)
freshenAlt (FcAlt (FcConPat dc vars) tm) = do
  vars' <- getVars vars
  let tm' = foldl (flip substFcTmInTm) tm (zipWith (\x y -> (x |-> y)) vars (map (FcTmVar) vars'))
  FcAlt (FcConPat dc vars') <$> freshenFcVars tm'
  where getVars :: [FcTmVar] -> FcEM a [FcTmVar]
        getVars [] = return []
        getVars (_:xs) = do
          x <- lift freshFcTmVar
          xs' <- getVars xs
          return (x:xs')

lookupVbM :: (MonadReader (Ctx a) m) => FcTmVar -> m (Maybe (FcTerm a, FcType))
lookupVbM a = do
  ctx <- ask
  return $ lookupVb a ctx

lookupVb :: FcTmVar -> Ctx a -> Maybe (FcTerm a, FcType)
lookupVb _ [] = Nothing
lookupVb a (x:xs)
  | a == fval_bind_var x = Just (fval_bind_tm x, fval_bind_ty x)
  | otherwise            = lookupVb a xs

-- * Invoke the complete System F evaluator
-- ----------------------------------------------------------------------------

fcEvaluateTm :: UniqueSupply -> Ctx a -> FcTerm a -> FcTerm a
fcEvaluateTm us vbs tm = fst $ flip runUniqueSupplyM us $ flip runReaderT vbs $ fcEvalTm tm

fcEvaluate :: UniqueSupply -> FcProgram a -> FcTerm a
fcEvaluate us pr = fcEvaluate' us [] pr
  where fcEvaluate' :: UniqueSupply -> Ctx a -> FcProgram a-> FcTerm a
        fcEvaluate' us vbs (FcPgmDataDecl _  pr) = fcEvaluate'  us vbs pr
        fcEvaluate' us vbs (FcPgmValDecl  vb pr) = fcEvaluate'  us (vb:vbs) pr
        fcEvaluate' us vbs (FcPgmTerm        tm) = fcEvaluateTm us vbs tm
