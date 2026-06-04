Definition Bar A B C := A \/ B \/ C.

Ltac silly := match goal with
              | |- Bar _ _ _ => unfold Bar
              | _ => idtac
              end.
