Definition F := nat.

Definition Bar : F := 0.

Definition EqF (x y : F) := x = y.

Section LocalNotation.

Declare Scope FScope.

Infix "=F=" := EqF (at level 70) : FScope.

Open Scope FScope.

Definition state_printer_definition_type : Bar =F= 0 := eq_refl.

End LocalNotation.
