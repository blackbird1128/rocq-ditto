
Ltac t x := exists x; reflexivity.
Goal exists n, n=0.

Info 0 t 1||t 0.
Qed.
