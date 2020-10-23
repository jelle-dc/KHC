{-# LANGUAGE LambdaCase #-}

module Main (main, runTest, runAnalysis) where

import Frontend.HsParser      (hsParse)
import Frontend.HsRenamer     (hsRename)
import Frontend.HsTypeChecker (hsElaborate)
import Backend.FcTypeChecker  (fcTypeCheck)
import Backend.BiTypeChecker  (biTypeCheck)
import Backend.BiTranslate    (biTranslate)
import Backend.FcEvaluator    (fcEvaluate)
import Analysis.Ast

import Utils.Unique  (newUniqueSupply)
import Utils.PrettyPrint

import Text.Printf

import System.Environment (getArgs)

main :: IO ()
main = getArgs >>= \case
  [filename] -> runTest filename
  _other     -> putStrLn "Usage: ghc <filename>"

-- | Run a single testfile
runTest :: FilePath -> IO ()
runTest file = do
  -- Parsing
  hsParse file >>= \case
    Left err     -> throwMainError "parser" err
    Right ps_pgm -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err,_) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          case hsElaborate rn_env us1 rn_pgm of
            (Left err,_) -> throwMainError "typechecker" err
            (Right ((((fc_pgm, tc_ty, theory), envs), us2), _tc_env), _) -> do
              putStrLn "---------------------------- Elaborated Program ---------------------------"
              putStrLn $ renderWithColor $ ppr fc_pgm
              putStrLn "------------------------------- Program Type ------------------------------"
              putStrLn $ renderWithColor $ ppr tc_ty
              putStrLn "------------------------------ Program Theory -----------------------------"
              putStrLn $ renderWithColor $ ppr theory
              case fcTypeCheck envs us2 fc_pgm of
                (Left err,_) -> throwMainError "System F typechecker" err
                (Right ((fc_ty, us3), _fc_env), _trace) -> do
                  putStrLn "---------------------------- Elaborated Program ---------------------------"
                  putStrLn $ renderWithColor $ ppr fc_pgm
                  putStrLn "------------------------------- Program Type ------------------------------"
                  putStrLn $ renderWithColor $ ppr tc_ty
                  putStrLn "------------------------------ Program Theory -----------------------------"
                  putStrLn $ renderWithColor $ ppr theory
                  putStrLn "-------------------------- System F Program Type --------------------------"
                  putStrLn $ renderWithColor $ ppr fc_ty
                  let res = fcEvaluate us3 fc_pgm
                  putStrLn "-------------------------- System F Result --------------------------------"
                  putStrLn $ renderWithColor $ ppr res
                  case biTranslate envs us3 fc_pgm of
                    (Left err,_) -> throwMainError "Bi Translation" err
                    (Right ((bi_pgm, us4), _bi_env), _trace) -> do
                        putStrLn "---------------------------- Bi Program ---------------------------"
                        putStrLn $ renderWithColor $ ppr bi_pgm
                        case biTypeCheck envs us4 bi_pgm of
                          (Left err,_) -> throwMainError "Bi typechecker" err
                          (Right ((bi_ty, us5), _bi_env), _trace) -> do
                            putStrLn "--------------------------- Bi Type ------------------------"
                            putStrLn $ renderWithColor $ ppr bi_ty
                            let resBi = fcEvaluate us5 bi_pgm
                            putStrLn "---------------------------- Bi Result ------------------------"
                            putStrLn $ renderWithColor $ ppr resBi
                      
throwMainError :: String -> String -> IO ()
throwMainError phase e
  | label <- colorDoc red (text phase <+> text "failure")
  , msg   <- brackets label <+> colorDoc red (text e)
  = putStrLn (renderWithColor msg)

runAnalysis :: FilePath -> IO ()
runAnalysis file = do
  -- Parsing
  hsParse file >>= \case
    Left err     -> throwMainError "parser" err
    Right ps_pgm -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err,_) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          case hsElaborate rn_env us1 rn_pgm of
            (Left err,_) -> throwMainError "typechecker" err
            (Right ((((fc_pgm, _, _), envs), us2), _tc_env), _) -> do
              let (terms, types, tySize) = analyze fc_pgm
              putStrLn "+----+-----------+-----------+-----------+-----------+"
              putStrLn "|    |   terms   |   types   | type size |   total   |"
              putStrLn "+----+-----------+-----------+-----------+-----------+"
              putStrLn ("| SF | " ++ p9 terms ++ " | " ++ p9 types ++ " | " ++ p9 tySize ++ " | " ++ p9 (terms + tySize) ++ " |") 
              putStrLn "+----+-----------+-----------+-----------+-----------+"
              case biTranslate envs us2 fc_pgm of
                (Left err,_) -> throwMainError "biTranslate" err
                (Right ((bi_pgm, _), _), _) -> do
                  let (biTms, biTys, biSize) = analyze bi_pgm
                  putStrLn ("| Bi | " ++ p9 biTms ++ " | " ++ p9 biTys ++ " | " ++ p9 biSize ++ " | " ++ p9 (biTms + biSize) ++ " |") 
                  putStrLn "+----+-----------+-----------+-----------+-----------+"
              
  where p9 :: Integer -> String
        p9 = printf "%9d"