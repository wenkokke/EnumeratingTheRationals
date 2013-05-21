Require Import Streams.

Inductive Tree {A: Type} :=
  | Leaf : Tree A
  | Node : Tree A -> A -> Tree A -> Tree A.

Fixpoint fold {A B: Type} (f: (B*A*B) -> B) (e: B) (t: Tree A) : B :=
  match t with
  | Leaf       => e
  | Node l x r => f (fold f e l,x,fold f e r)
  end.

CoInductive CoTree {A: Type} :=
  | CoNode : CoTree A -> A -> CoTree A -> CoTree A.

CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : CoTree A :=
  match f e with
  | (l,x,r) => CoNode (unfold f l) x (unfold f r)
  end.
 

 
