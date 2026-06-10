Definition F := nat.

Definition EqF (x y : F) := x = y.

Section LocalNotation.

Declare Scope FScope.

Infix "=F=" := EqF (at level 70) : FScope.

Open Scope FScope.

Definition Foo : 0 =F= 0 := eq_refl.

End LocalNotation.
