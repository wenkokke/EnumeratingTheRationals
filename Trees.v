Inductive tree {A: Type} :=
  | leaf : tree A
  | node : tree A -> A -> tree A -> tree A.

Fixpoint tree_fold {A B: Type} (f: (B*A*B) -> B) (e: B) (t: tree A) : B :=
  match t with
  | leaf       => e
  | node l x r => f (fold f e l, x, fold f e r)
  end.

CoInductive colist {A: Type} :=
  | cocons : A -> colist A -> colist A.

CoFixpoint colist_unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
  match f e with
  | (x,xs) => cocons x (unfold f xs)
  end.

CoInductive cotree {A: Type} :=
  | conode : cotree A -> A -> cotree A -> cotree A.

CoFixpoint cotree_unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
  match f e with
  | (l,x,r) => conode (unfold f l) x (unfold f r)
  end.

Definition cotree_bf {A: Type} (t: cotree A) : colist A :=
  bf_acc [t].

CoFixpoint cotree_bf_acc {A: Type} (ts: list (cotree A)) : colist A :=
  match ts with
  | nil       => absurd_set
  | cons t ts =>
    match t with
    | conode l x r => cocons x (bf_acc (l :: r :: ts))
    end
  end.

 
