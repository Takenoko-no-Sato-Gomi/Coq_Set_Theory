Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.
Require Export Set_Theory_Group.
Require Export Set_Theory_Ring.



(*可換環*)
Theorem Comutive_Ring_Law_3:forall f g R I:Set,Comutive_Ring f g R/\Ring_Left_Ideal f g R I->Ring_Semi_Ideal f g R I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.

apply H0.
split.

apply H1.
split.

intros.
rewrite -> (Comutive_Ring_Law_2 f g R x a).
apply H2.
apply H4.
split.
apply H.
destruct H4.
split.
apply H0.
apply H5.
apply H4.
split.

apply H2.

apply H3.
Qed.

Theorem Comutive_Ring_Law_4:forall f g R I:Set,Comutive_Ring f g R/\Ring_Right_Ideal f g R I->Ring_Semi_Ideal f g R I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.

apply H0.
split.

apply H1.
split.

apply H2.
split.

intros.
rewrite -> (Comutive_Ring_Law_2 f g R a x).
apply H2.
apply H4.
split.
apply H.
destruct H4.
split.
apply H4.
apply H0.
apply H5.

apply H3.
Qed.

Theorem Comutive_Ring_Law_5:forall f g R I:Set,Comutive_Ring f g R/\Ring_Semi_Ideal f g R I->Comutive_Ring (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
intros.
destruct H1.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
rewrite -> H3.
rewrite -> H4.
rewrite -> (Quotient_Ring_Law_3 f g R I x0 x1).
rewrite -> (Quotient_Ring_Law_3 f g R I x1 x0).
rewrite -> (Comutive_Ring_Law_2 f g R x0 x1).
split.
split.
apply H.
split.
apply H1.
apply H2.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H2.
apply H1.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
Qed.



Definition Prime_Ideal(f g R I:Set):=Ring_Semi_Ideal f g R I/\(forall x1 x2:Set,x1 ∈ R/\x2 ∈ R/\Operation g x1 x2 ∈ I->(x1 ∈ I\/x2 ∈ I)).

Theorem Prime_Ideal_Law_1:forall f g R I:Set,Prime_Ideal f g R I->Ring_Semi_Ideal f g R I.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Prime_Ideal_Law_2:forall f g R I x1 x2:Set,Prime_Ideal f g R I/\x1 ∈ R/\x2 ∈ R/\Operation g x1 x2 ∈ I->(x1 ∈ I\/x2 ∈ I).
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
Qed.

Theorem Prime_Ideal_Law_3:forall f g R I:Set,Comutive_Ring f g R/\Prime_Ideal f g R I->Integral_Domain (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
destruct H0.
split.
apply (Comutive_Ring_Law_5 f g R I).
split.
apply H.
apply H0.
intros.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct (Law_of_Excluded_Middle (x0 ∈ I)).

left.
rewrite -> H3.
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I x0).
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
apply H4.

right.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H2.
apply H3.
intros.
destruct H5.
apply Quotient_Set_Law_1 in H5.
destruct H5.
destruct H5.
rewrite -> H3.
rewrite -> H7.
rewrite -> (Quotient_Ring_Law_3 f g R I x0 x2).
rewrite -> (Quotient_Ring_Law_3 f g R I x2 x0).
rewrite -> H7 in H6.
assert (~Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x0 x2)=Identify_Element (Group_Quotient_Operation f R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
intro.
apply H6.
assert (x0 ∈ I\/x2 ∈ I).
apply H1.
split.
apply H2.
split.
apply H5.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f I) I (Operation g x0 x2)).
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
split.
apply H2.
apply H5.
apply H8.
destruct H9.
destruct H4.
apply H9.
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I x2).
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
apply H9.
split.
apply H8.
rewrite -> (Comutive_Ring_Law_2 f g R x2 x0).
apply H8.
split.
apply H.
split.
apply H5.
apply H2.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H5.
apply H2.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H2.
apply H5.
Qed.

Definition Maximal_Ideal(f g R I:Set):=Prime_Ideal f g R I/\(forall J:Set,Prime_Ideal f g R J/\I ⊂ J->I=J).















