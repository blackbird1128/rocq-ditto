Definition F := nat.

Definition Bar : F := 0.

Definition EqF (x y : F) := x = y.

Section LocalNotation.

Declare Scope FScope.

Infix "=F=" := EqF (at level 70) : FScope.

Open Scope FScope.

Lemma state_printer_assert : True.
Proof.
  assert (Bar =F= 0) by reflexivity.
  exact I.
Qed.

End LocalNotation.
