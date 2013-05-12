
Module Maybe.

  Inductive Maybe (A : Type) :=
  | Just    : A -> Maybe A
  | Nothing : Maybe A.
  
  Definition map (A B : Type) (f : A -> B) (m : Maybe A) : Maybe B :=
    match m with
      | Just a  => Just _ (f a)
      | Nothing => Nothing _
    end.

  Definition apply (A B : Type) (f : A -> Maybe B) (m : Maybe A) : Maybe B :=
    match m with
      | Just a  =>
        match f a with
          | Just a' => Just _ a'
          | Nothing => Nothing _
        end
      | Nothing => Nothing _
    end.

  Definition append (A : Type) (m1 m2 : Maybe A) : Maybe A :=
    match m1 with
      | Just  _ => m1
      | Nothing => m2
    end.

  Notation "f <$> a" := (map   _ _ f a) (at level 80, right associativity).
  Notation "f <*> a" := (apply _ _ f a) (at level 80, right associativity).
  Notation "a <|> b" := (append  _ a b) (at level 80, right associativity).

End Maybe.
