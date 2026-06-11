Class intuitionistic_Tarski_neutral_dimensionless := {
 ITpoint : Type;
 IBet : ITpoint -> ITpoint -> ITpoint -> Prop;
 ICong : ITpoint -> ITpoint -> ITpoint -> ITpoint -> Prop;
 IT A B C := ~ (A <> B /\ B <> C /\ ~ IBet A B C);
 ICol A B C :=  ~ (~ IT C A B /\ ~ IT A C B /\ ~ IT A B C);
}.
