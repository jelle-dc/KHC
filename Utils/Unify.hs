{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
module Utils.Unify where

import Utils.Substitution
import Utils.Var
import Utils.PrettyPrint
import Utils.Annotated
import Utils.Errors

import Backend.FcTypes
  
import Control.Monad.Except
import Control.Arrow (second)

-- | Type Unification. The first argument are the untouchables (rigid) variables.
unify :: MonadError String m => [FcTyVar] -> FcEqCs -> m FcTySubst
unify _untchs [] = return mempty
unify  untchs eqs
  | Just ((subst1, eqs'), eqs'') <- go (one_step untchs) eqs
  = do subst2 <- unify untchs (substInFcEqCs subst1 (eqs' ++ eqs''))
       return (subst2 <> subst1)
  | otherwise = throwErrorM $ vcat [ text "Unification failed."
                                   , text "Residual constraints" <+> colon <+> ppr eqs
                                   , text "Untouchables"         <+> colon <+> ppr untchs ]
  where
    one_step :: [FcTyVar] -> FcEqCt -> Maybe (FcTySubst, FcEqCs)
    one_step _us (FcTyVar v1 :-: FcTyVar v2)
      | v1 == v2 = Just (mempty, [])
    one_step us (FcTyVar v :-: ty)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
    one_step us (ty :-: FcTyVar v)
      | v `notElem` us, occursCheck v ty = Just (v |-> ty, [])
    one_step us (FcTyAbs v1 ty1 :-: FcTyAbs v2 ty2)
      | v1 == v2  = Just(mempty, [ty1 :-: ty2]) -- alphaEq
      | otherwise = Nothing
    one_step _us (FcTyApp ty1 ty2 :-: FcTyApp ty3 ty4)
      = Just (mempty, [ty1 :-: ty3, ty2 :-: ty4])
    one_step _us (FcTyCon tc1 :-: FcTyCon tc2)
      | tc1 == tc2 = Just (mempty, [])
    one_step _us (_ :-: _) = Nothing

    go :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
    go _p []     = Nothing
    go  p (x:xs) | Just y <- p x = Just (y, xs)
                 | otherwise     = second (x:) <$> go p xs

  
-- | returns True if check succeeds, i.e. if the var does NOT occur
occursCheck :: FcTyVar -> FcType -> Bool
occursCheck v (FcTyVar w)          = v /= w
occursCheck v (FcTyAbs (w :| _) t) = v == w || occursCheck v t
occursCheck v (FcTyApp t1 t2)      = occursCheck v t1 && occursCheck v t2
occursCheck v (FcTyCon tc)         = True
