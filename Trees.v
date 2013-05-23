Require Import List.

Inductive tree (A: Type) :=
  | leaf : tree A
  | node : tree A -> A -> tree A -> tree A.

Fixpoint tree_fold {A B: Type} (f: (B*A*B) -> B) (e: B) (t: tree A) : B :=
  match t with
  | leaf       => e
  | node l x r => f (tree_fold f e l, x, tree_fold f e r)
  end.

CoInductive colist (A: Type) :=
  | cocons : A -> colist A -> colist A.

CoFixpoint colist_unfold {A B: Type} (f: B -> (A*B)) (e: B) : colist A :=
  match f e with
  | (x,xs) => cocons _ x (colist_unfold f xs)
  end.

Fixpoint colist_take {A: Type} (n: nat) (xs: colist A) : list A :=
  match n with
    | O => nil
    | S n =>
      match xs with
        | cocons x xs => cons x (colist_take n xs)
      end
  end.

CoInductive cotree (A: Type) :=
  | conode : cotree A -> A -> cotree A -> cotree A.

CoFixpoint cotree_unfold {A B: Type} (f: B -> (B*A*B)) (e: B) : cotree A :=
  match f e with
  | (l,x,r) => conode _ (cotree_unfold f l) x (cotree_unfold f r)
  end.

CoFixpoint cotree_bf_acc {A: Type} (ts: list (cotree A)) : ts<>nil -> colist A.
  refine (match ts as xs return xs<>nil -> colist A with
    | nil =>
      fun h => _
    | cons t ts =>
      fun h  => 
        match t with
          | conode l x r => cocons _ x (cotree_bf_acc _ (ts ++ (cons l (cons r nil))) _)
        end
  end).
  exfalso; apply h; reflexivity.
  apply not_eq_sym; apply app_cons_not_nil.
Defined.

Definition cotree_bf {A: Type} (t: cotree A) : colist A.
  refine (cotree_bf_acc (t :: nil) _).
  apply not_eq_sym; apply nil_cons.
Defined.

(** **** CoTrees of Rational Numbers *)

Require Import NArith.
Require Import QArith.

(** **** The Calkin-Wilf Tree *)

Definition calkin_wilf_step (q:positive*positive) : (positive*positive)*Q*(positive*positive) :=
  match q with
    | (m,n) => ((m,(m + n)%positive),Qmake (Zpos m) n,((m + n)%positive,n))
  end.

Definition calkin_wilf_tree : cotree Q := cotree_unfold calkin_wilf_step (1,1)%positive.

Definition calkin_wilf_list : colist Q := cotree_bf calkin_wilf_tree.

Eval compute in colist_take 10 calkin_wilf_list.

(** **** The Stern-Brocot Tree *)

Definition N_pos (n:N) : n<>N0 -> positive.
  refine (match n as n' return n'<>N0 -> positive with
            | N0     => fun h => _
            | Npos p => fun h => p
          end).
  exfalso; apply h; reflexivity.
Defined.

Definition stern_brocot_step (q:(N*N)*(N*N)) : ((N*N)*(N*N))*Q*((N*N)*(N*N)).
Admitted.

Definition stern_brocot_tree : cotree Q := cotree_unfold stern_brocot_step ((0,1),(1,0))%N.

Definition stern_brocot_list : colist Q := cotree_bf stern_brocot_tree.
