
data Tree a = Node (Tree a) a (Tree a)

unfold :: (b -> (b,a,b)) -> b -> Tree a
unfold f e = Node (unfold f l) x (unfold f r)
  where (l,x,r) = f e

bf :: Tree a -> [a]
bf t = bf_acc [t]
  where
  bf_acc :: [Tree a] -> [a]
  bf_acc ((Node l x r) : rest) = x : (bf_acc (rest ++ [l,r]))
  

ex :: Tree Int
ex = unfold (\x -> (2*x, x, 2*x+1)) 1

