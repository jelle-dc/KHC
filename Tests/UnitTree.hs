data Bool = False | True
data Unit = Unit
data Ordering = LT | EQ | GT

compare :: Unit -> Unit -> Ordering
         = \x. \y. EQ

data Color = Red | Black -- Color of Red-Black-Tree nodes

data Tree = Leaf | Node Color Unit Tree Tree -- Red-Black-Tree: Node node-color node-value left-subtree right-subtree

empty :: Tree
       = Leaf

member :: Unit -> Tree -> Bool
        = \x.\t. case t of
                   Leaf                    -> False
                   Node col top left right -> case compare x top of
                                                EQ -> True
                                                LT -> member x left
                                                GT -> member x right

reverseTree :: Tree -> Tree
             = \t. case t of
                     Leaf                    -> Leaf
                     Node col top left right -> Node col top right left

data Flow (a :: *) (b :: *) = Input a | Output b -- Support for more complex guards: represents a result in a stream of alternatives where either no alternaive applied (Input) or an earlier alternative did apply (Output)

correct :: Tree -> Tree
         = let flow = \f.\x. case x of -- Models alternatives/guards
                               Input  y -> f y
                               Output y -> Output y
           in let case1 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Red ->
                                          case nleft of
                                            Leaf ->
                                              case nright of
                                                Leaf -> Output t
                                                Node c a l r -> Input t
                                            Node c a l r -> Input t
                                        Black -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case2 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Red ->
                                          case nleft of
                                            Node c1col c1top c1left c1right ->
                                              case c1col of
                                                Black ->
                                                  case nright of
                                                    Node c2col c2top c2left c2right ->
                                                      case c2col of
                                                        Black -> Output t
                                                        Red -> Input t
                                                    Leaf -> Input t
                                                Red -> Input t
                                            Leaf -> Input t
                                        Black -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case3 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Black -> Output t
                                        Red -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case4 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case gright of
                                                Node ucol utop uleft uright ->
                                                  case ucol of
                                                    Red -> Output (Node Red gtop (Node Black ptop pleft pright) (Node Black utop uleft uright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in let case5 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case pright of
                                                Node ncol ntop nleft nright ->
                                                  case ncol of
                                                    Red -> Output (correct (Node Black gtop (Node Red ntop (Node Red ptop pleft nleft) nright) gright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in let case6 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case pleft of
                                                Node ncol ntop nleft nright ->
                                                  case ncol of
                                                    Red -> Output (Node Black ptop (Node Red ntop nleft nright) (Node Red gtop pright gright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in  \t. case flow case6 (flow case5 (flow case4 (flow case3 (flow case2 (flow case1 (Input t)))))) of
                     Output r -> r

-- insert' :: Unit -> Tree -> Tree
--          = \x.\t. case t of
--                     Leaf                    -> Node Red x Leaf Leaf
--                     Node col top left right -> case compare x top of
--                                                  EQ -> t
--                                                  LT -> correct (Node col top (insert' x left) right)
--                                                  GT -> reverseTree (correct (reverseTree (Node col top left (insert' x right))))

-- insert :: Unit -> Tree -> Tree
--         = \x.\t. case insert' x t of
--                    Node col top left right -> Node Black top left right

-- data Maybe = Nothing | Just Unit

-- maybe :: Unit -> (Unit -> Unit) -> Maybe Unit -> Unit
--        = \b.\f.\x. case x of
--                      Nothing -> b
--                      Just a  -> f a

-- id :: Unit -> Unit
--     = \x.x

-- lessThan :: Unit -> Unit -> Bool
--           = \x.\y. case compare x y of
--                      LT -> True
--                      EQ -> False
--                      GT -> False

-- rightmost :: Tree -> Maybe
--            = \t. case t of
--                    Leaf -> Nothing
--                    Node col top left right -> Just (maybe top id (rightmost right))

-- leftmost :: Tree -> Maybe
--           = \t. case t of
--                   Leaf -> Nothing
--                   Node col top left right -> Just (maybe top id (leftmost left))

-- issortedAscending :: Tree -> Bool
--                    = \t. case t of
--                            Leaf -> True
--                            Node col top left right ->
--                              case maybe True (\x. lessThan x top) (rightmost left) of
--                                False -> False
--                                True  -> case maybe True (\x. lessThan top x) (leftmost right) of
--                                           False -> False
--                                           True  -> case issortedAscending left of
--                                                      False -> False
--                                                      True  -> issortedAscending right

-- issortedDescending :: Tree -> Bool
--                     = \t. case t of
--                             Leaf -> True
--                             Node col top left right ->
--                               case maybe True (\x. lessThan top x) (rightmost left) of
--                                 False -> False
--                                 True  -> case maybe True (\x. lessThan x top) (leftmost right) of
--                                            False -> False
--                                            True  -> case issortedDescending left of
--                                                       False -> False
--                                                       True  -> issortedDescending right

-- issortedAsEither :: Tree -> Bool
--                   = \t. case issortedAscending t of
--                           True  -> True
--                           False -> issortedDescending t

-- -- main = foldr insert empty [5.0, 4.0, 1.0, 3.0, 2.0]
-- (let e5 = Unit
--  in let e4 = Unit
--     in let e3 = Unit
--        in let e2 = Unit
--           in let e1 = Unit
-- in insert e5 (insert e4 (insert e3 (insert e2 (insert e1 empty)))))

(False)