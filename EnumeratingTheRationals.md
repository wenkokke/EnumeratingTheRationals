% Enumerating The Rationals
% Gibbons; Lester; Bird
% June 27th, 2013

## Enumerating The Rationals

  1. Naive approach;
  2. Stern-Brocot Tree;
  3. Calkin-Wilf Tree.
  
## CoLists and CoTrees

<!--
  On programming and proving with infinite trees.
  -->
  
## Naive Approach

    step : Q -> Q*Q*Q
    step n/d = (n+1/d, n/d, n/d+1)
    
    tree : cotree Q
    tree = unfold step 1/1
  
## Stern-Brocot Tree

    step : Q*Q -> (Q*Q)*Q*(Q*Q)
    step (a/b, c/d) =
      ((a/b, (a+c)/(b+d)), (a+c)/(b+d), ((a+c)/(b+d), c/d))
    
    tree : cotree Q
    tree = unfold step (0/1, 1/0)
    
## Stern-Brocot Tree (cont'd)

<!--
  On the relation between the Stern-Brocot tree and `gcd`.
  
  Link to the above algorithm.
  -->
  
## Problems with Stern-Brocot Tree

> - Unfolding requires the "pseudo-rationals" $0/1$ and $1/0$ as input;

<!--
  Proving relation between $Q$ reduction and position in the tree
  requires both algorithms to be based on the same implementation
  of `gcd`--but standard implementation does not provide a trace.
  -->

> - Relation between $Q$-reduction and path in the Stern-Brocot tree
    requires both to use equivalent implementations of `gcd`;
  
## Conclusion

  
    
## Calkin-Wilf Tree

    step : Q -> Q*Q*Q
    step m/n = (m/m+n, m/n, m+n/n)
    
    tree : cotree Q
    tree = unfold step 1/1
    
## Calkin-Wilf Tree

<!--
  On the relation between the Calkin-Wilf tree and the Stern-Brocot tree.
  -->
