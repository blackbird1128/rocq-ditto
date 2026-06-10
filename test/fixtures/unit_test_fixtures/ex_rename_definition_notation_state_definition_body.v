Definition F := nat.

Definition Foo : F := 0.

Definition EqF (x y : F) := x = y.

Section LocalNotation.

Declare Scope FScope.

Infix "=F=" := EqF (at level 70) : FScope.

Open Scope FScope.

Definition state_printer_definition_body : Prop := Foo =F= 0.

End LocalNotation.
