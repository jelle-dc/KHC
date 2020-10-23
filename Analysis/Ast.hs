{-# LANGUAGE GADTs #-}

module Analysis.Ast (analyze) where

import Backend.FcTypes

countTerms :: Integral n => FcTerm a -> n
countTerms = count 1 (const 0)

countTypes :: Integral n => FcTerm a -> n
countTypes = count 0 (const 1)

typeSize :: Integral n => FcTerm a -> n
typeSize = count 0 size
  where size :: Integral n => FcType -> n
        size (FcTyVar _) = 1
        size (FcTyApp ty1 ty2) = 1 + size ty1 + size ty2
        size (FcTyAbs _ ty) = 1 + size ty
        size (FcTyCon _) = 1

count :: Integral n => n -> (FcType -> n) -> FcTerm a -> n
count tmCost tyCost = count'
  where count' (FcTmAbs _ ty tm) = tmCost + tyCost ty + count' tm
        count' (FcTmAbsBi _ tm)  = tmCost + count' tm
        count' (FcTmVar _)       = tmCost
        count' (FcTmApp tm1 tm2) = tmCost + count' tm1 + count' tm2
        count' (FcTmTyAbs _ tm)  = tmCost + count' tm
        count' (FcTmTyApp tm ty) = tmCost + tyCost ty + count' tm
        count' (FcTmLet _ ty tm1 tm2) = tmCost + count' tm1 + count' tm2 + tyCost ty
        count' (FcTmAnn tm ty) = tmCost + tyCost ty + count' tm
        count' (FcTmDataCon _) = tmCost
        count' (FcTmCase scr alts) = tmCost + count' scr + countAlts alts
        countAlts = sum . (map countAlt)
        countAlt (FcAlt _ tm) = count' tm

analyze :: Integral n => FcProgram a -> (n,n,n)
analyze = analyze' 0 0 0
  where analyze' nTm nTy sTy (FcPgmDataDecl _ pgm) = analyze' nTm nTy sTy pgm
        analyze' nTm nTy sTy (FcPgmValDecl (FcValBind var ty val) pgm) = analyze' (nTm + countTerms val) (nTy + countTypes val) (sTy + typeSize val) pgm 
        analyze' nTm nTy sTy (FcPgmTerm tm) = (nTm + countTerms tm, nTy + countTypes tm, sTy + typeSize tm)