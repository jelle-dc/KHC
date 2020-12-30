-- List

data Unit = None
data UnitList = Nil | Cons Unit UnitList
data Bool = True | False

map :: (Unit -> Unit) -> UnitList -> UnitList
     = \f.\xs. case xs of
                 Cons y ys -> Cons (f y) (map f ys)
                 Nil       -> Nil

ifU :: Bool -> Unit -> Unit -> Unit
     = \b. \x. \y. case b of
                     True  -> x
                     False -> y

ifL :: Bool -> UnitList -> UnitList -> UnitList
     = \b. \x. \y. case b of
                     True  -> x
                     False -> y
    
id :: Unit -> Unit
    = \x. x

filter :: (Unit -> Bool) -> UnitList -> UnitList
        = \f.\xs. case xs of
                    Cons y ys -> case (f y) of
                                   True  -> (Cons y) (filter f ys)
                                   False -> filter f ys
                    Nil       -> Nil

null :: UnitList -> Bool
      = \xs. case xs of
               Cons y ys -> False
               Nil       -> True

head :: UnitList -> Unit
      = \xs. case xs of
               Cons y ys -> y

tail :: UnitList -> UnitList
      = \xs. case xs of
               Cons y ys -> ys

last :: UnitList -> Unit
      = \xs. case xs of
               Cons y ys -> ifU (null ys) y (last ys)

init :: UnitList -> UnitList
      = \xs. case xs of
               Cons y ys -> ifL (null ys) Nil (Cons y (init ys))

scanl :: (Unit -> Unit -> Unit) -> Unit -> UnitList -> UnitList
       = \f.\b.\xs. Cons b (ifL (null xs) Nil (scanl f (f b (head xs)) (tail xs)))

scanr :: (Unit -> Unit -> Unit) -> Unit -> UnitList -> UnitList
       = \f.\b.\xs. let qs = scanr f b (tail xs)
                    in  ifL (null xs) (Cons b Nil) (Cons (f (head xs) (head qs)) qs)

iterate :: (Unit -> Unit) -> Unit -> UnitList
         = \f.\x. Cons x (iterate f (f x))

repeat :: Unit -> UnitList
        = \x. let xs = Cons x xs in xs

dropWhile :: (Unit -> Bool) -> UnitList -> UnitList
           = \f.\xs. case xs of
                       Cons y ys -> ifL (f y) (dropWhile f ys) ys
                       Nil       -> Nil

takeWhile :: (Unit -> Bool) -> UnitList -> UnitList
           = \f.\xs. case xs of
                       Cons y ys -> ifL (f y) (Cons y (takeWhile f ys)) Nil
                       Nil       -> Nil

(None)