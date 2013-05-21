Inductive tree {A: Type} :=
  | leaf : tree A
  | node : tree A -> A -> tree A -> tree A.

Fixpoint fold {A B: Type} (f: (B*A*B) -> B) (e: B) (t: tree A) : B :=
  match t with
  | leaf       => e
  | node l x r => f (fold f e l, x, fold f e r)
  end.
  
Fixpoint bf_acc {A: Type} (ts: list (tree A)) : list A :=
  match ts with
  | nil       => nil
  | cons t ts => admit
  end.

CoInductive colist {A: Type} :=
  | cocons : A -> colist A -> colist A.

CoInductive cotree {A: Type} :=
  | conode : cotree A -> A -> cotree A -> cotree A.

CoFixpoint unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
  match f e with
  | (l,x,r) => conode (unfold f l) x (unfold f r)
  end.

Definition bf {A: Type} (t: cotree A) : colist A :=
  bf_acc [t].

CoFixpoint bf_acc {A: Type} (ts: list (cotree A)) : colist A :=
  match ts with
  | nil       => absurd_set
  | cons t ts =>
    match t with
    | conode l x r => cocons x (bf_acc (l :: r :: ts))
    end
  end.

 
