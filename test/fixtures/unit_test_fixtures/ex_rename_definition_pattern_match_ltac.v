Definition Foo A B C := A \/ B \/ C.

Ltac silly :=
  match goal with
    | |- Foo _ _ _ =>  unfold Foo
    | _ =>  idtac
  end.
