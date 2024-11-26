Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.
Require Export Set_Theory_Group.



(*環*)
Definition Ring(f g R:Set):=Abel_Group f R/\Monoid g R/\(forall x1 x2 x3:Set,x1 ∈ R/\x2 ∈ R/\x3 ∈ R->Operation g x1 (Operation f x2 x3)=Operation f (Operation g x1 x2) (Operation g x1 x3))/\(forall x1 x2 x3:Set,x1 ∈ R/\x2 ∈ R/\x3 ∈ R->Operation g (Operation f x1 x2) x3=Operation f (Operation g x1 x3) (Operation g x2 x3)).

Definition Zero_Ring(f g R:Set):=Ring f g R/\(forall x:Set,x ∈ R->x=Identify_Element f R).

Theorem Ring_Law_1:forall f g R:Set,Ring f g R->Abel_Group f R.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Ring_Law_2:forall f g R:Set,Ring f g R->Monoid g R.
Proof.
intros.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Ring_Law_3:forall f g R x1 x2 x3:Set,Ring f g R/\x1 ∈ R/\x2 ∈ R/\x3 ∈ R->Operation g x1 (Operation f x2 x3)=Operation f (Operation g x1 x2) (Operation g x1 x3).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Ring_Law_4:forall f g R x1 x2 x3:Set,Ring f g R/\x1 ∈ R/\x2 ∈ R/\x3 ∈ R->Operation g (Operation f x1 x2) x3=Operation f (Operation g x1 x3) (Operation g x2 x3).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H3.
apply H0.
Qed.

Theorem Ring_Law_5:forall f g R x:Set,Ring f g R/\x ∈ R->Operation g x (Identify_Element f R)=Identify_Element f R.
Proof.
intros.
destruct H.
rewrite <- (Group_Law_10 f R (Identify_Element g R)).
rewrite -> (Ring_Law_3 f g R x (Identify_Element g R) (Reverse_Element f R (Identify_Element g R))).
rewrite -> (Monoid_Law_6 g R).
rewrite -> (Group_Law_10 f R (Identify_Element g R)).
apply (Group_Law_13 f R (Operation g x (Identify_Element g R)) (Operation f x (Operation g x (Reverse_Element f R (Identify_Element g R)))) (Identify_Element f R)).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
rewrite -> (Group_Law_6 f R (Operation g x (Identify_Element g R))).
rewrite -> (Monoid_Law_6 g R x).
assert (Operation f x (Operation g x (Reverse_Element f R (Identify_Element g R)))=Operation f (Operation g x (Identify_Element g R))(Operation g x (Reverse_Element f R (Identify_Element g R)))).
rewrite -> (Monoid_Law_6 g R x).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
rewrite -> H1.
clear H1.
rewrite <- (Ring_Law_3 f g R x (Identify_Element g R) (Reverse_Element f R (Identify_Element g R))).
rewrite -> (Group_Law_10 f R (Identify_Element g R)).
assert (Operation f (Operation g x (Identify_Element f R)) x=Operation f (Operation g x (Identify_Element f R)) (Operation g x (Identify_Element g R))).
rewrite -> (Monoid_Law_6 g R x).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
rewrite -> H1.
clear H1.
rewrite <- (Ring_Law_3 f g R x (Identify_Element f R) (Identify_Element g R)).
rewrite -> (Group_Law_6 f R (Identify_Element g R)).
apply Monoid_Law_6.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H.
split.
apply H0.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H.
split.
apply H0.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply H.
split.
apply H0.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
Qed.

Theorem Ring_Law_6:forall f g R x:Set,Ring f g R/\x ∈ R->Operation g (Identify_Element f R) x=Identify_Element f R.
Proof.
intros.
destruct H.
rewrite <- (Group_Law_10 f R (Identify_Element g R)).
rewrite -> (Ring_Law_4 f g R (Identify_Element g R) (Reverse_Element f R (Identify_Element g R)) x).
rewrite -> (Group_Law_10 f R (Identify_Element g R)).
apply (Group_Law_13 f R (Operation g (Identify_Element g R) x) (Operation f (Operation g (Identify_Element g R) x) (Operation g (Reverse_Element f R (Identify_Element g R)) x)) (Identify_Element f R)).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_4.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_4.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
rewrite <- (Group_Law_3 f R (Operation g (Identify_Element g R) x) (Operation g (Reverse_Element f R (Identify_Element g R)) x) (Operation g (Identify_Element g R) x)).
rewrite <- (Ring_Law_4 f g R (Reverse_Element f R (Identify_Element g R)) (Identify_Element g R) x).
rewrite -> (Group_Law_11 f R (Identify_Element g R)).
rewrite <- (Ring_Law_4 f g R (Identify_Element g R) (Identify_Element f R) x).
rewrite -> (Group_Law_5 f R (Identify_Element g R)).
rewrite -> (Monoid_Law_7 g R x).
symmetry.
apply (Group_Law_6 f R x).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H0.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
Qed.

Theorem Ring_Law_7:forall f g R x y:Set,Ring f g R/\x ∈ R/\y ∈ R->Operation g (Reverse_Element f R x) y=Reverse_Element f R (Operation g x y).
Proof.
intros.
apply (Group_Law_13 f R (Operation g x y) (Operation g (Reverse_Element f R x) y) (Reverse_Element f R (Operation g x y))).
destruct H.
destruct H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H0.
apply H1.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
rewrite -> (Group_Law_11 f R (Operation g x y)).
rewrite <- (Ring_Law_4 f g R (Reverse_Element f R x) x y).
rewrite -> (Group_Law_11 f R x).
apply Ring_Law_6.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H0.
split.
apply H0.
apply H1.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Ring_Law_8:forall f g R x y:Set,Ring f g R/\x ∈ R/\y ∈ R->Operation g x (Reverse_Element f R y)=Reverse_Element f R (Operation g x y).
Proof.
intros.
destruct H.
destruct H0.
apply (Group_Law_13 f R (Operation g x y) (Operation g x (Reverse_Element f R y)) (Reverse_Element f R (Operation g x y))).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H1.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
rewrite -> (Group_Law_11 f R (Operation g x y)).
rewrite <- (Ring_Law_3 f g R x (Reverse_Element f R y) y).
rewrite -> (Group_Law_11 f R y).
apply Ring_Law_5.
split.
apply H.
apply H0.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply H0.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H1.
apply H1.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Ring_Law_9:forall f g R:Set,Ring f g R/\Identify_Element f R=Identify_Element g R->Zero_Ring f g R.
Proof.
intros.
destruct H.
split.
apply H.
intros.
rewrite <- (Monoid_Law_6 g R x).
rewrite <- H0.
apply (Ring_Law_5 f g R x).
split.
apply H.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
Qed.

Theorem Ring_Law_10:forall f g R:Set,Zero_Ring f g R->Identify_Element f R=Identify_Element g R.
Proof.
intros.
destruct H.
symmetry.
apply H0.
apply (Monoid_Law_5 g R).
apply (Ring_Law_2 f g R).
apply H.
Qed.



(*可換環*)
Definition Comutive_Ring(f g R:Set):=Ring f g R/\forall x y:Set,x ∈ R/\y ∈ R->Operation g x y=Operation g y x.

Theorem Comutive_Ring_Law_1:forall f g R:Set,Comutive_Ring f g R->Ring f g R.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Comutive_Ring_Law_2:forall f g R x y:Set,Comutive_Ring f g R/\x ∈ R/\y ∈ R->Operation g x y=Operation g y x.
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
Qed.



(*零因子*)
Definition Ring_zero_divisor_element(f g R x:Set):=x ∈ R/\exists x0:Set,x0 ∈ R/\~x0=Identify_Element f R/\(Operation g x x0=Identify_Element f R\/Operation g x0 x=Identify_Element f R).

Definition Ring_non_zero_divisor_element(f g R x:Set):=x ∈ R/\forall x0:Set,x0 ∈ R/\~x0=Identify_Element f R->(~Operation g x x0=Identify_Element f R)/\(~Operation g x0 x=Identify_Element f R).



(*整域*)
Definition Integral_Domain(f g R:Set):=Comutive_Ring f g R/\forall x:Set,x ∈ R->(x=Identify_Element f R\/Ring_non_zero_divisor_element f g R x).

Theorem Integral_Domain_Law_1:forall f g R:Set,Integral_Domain f g R->Comutive_Ring f g R.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Integral_Domain_Law_2:forall f g R x y:Set,Integral_Domain f g R/\x ∈ R/\y ∈ R/\Operation g x y=Identify_Element f R->(x=Identify_Element f R\/y=Identify_Element f R).
Proof.
intros.
destruct H.
destruct H.
destruct H0.
destruct H2.
assert (x ∈ R).
apply H0.
assert (y ∈ R).
apply H2.
apply H1 in H4.
apply H1 in H5.
destruct H4.
left.
apply H4.
destruct H5.
right.
apply H5.
destruct H4.
assert (forall x0:Set,x0 ∈ R/\Operation g x x0=Identify_Element f R/\Operation g x0 x=Identify_Element f R->x0=Identify_Element f R).
intros.
destruct (Law_of_Excluded_Middle (x0=Identify_Element f R)).
apply H8.
destruct H7.
assert (x0 ∈ R/\~(x0=Identify_Element f R)).
split.
apply H7.
apply H8.
apply H6 in H10.
destruct H10.
destruct H10.
destruct H9.
apply H9.
assert (y ∈ R/\Operation g x y=Identify_Element f R/\Operation g y x=Identify_Element f R).
split.
apply H2.
split.
apply H3.
rewrite -> (Comutive_Ring_Law_2 f g R y x).
apply H3.
split.
apply H.
split.
apply H2.
apply H0.
apply H7 in H8.
right.
apply H8.
Qed.



(*単元*)
Definition Ring_invertible_element(f g R x:Set):=x ∈ R/\exists x0:Set,x0 ∈ R/\Operation g x x0=Identify_Element g R/\Operation g x0 x=Identify_Element g R.

Definition Ring_non_vertible_element(f g R x:Set):=x ∈ R/\forall x0:Set,x0 ∈ R->(~Operation g x x0=Identify_Element g R)/\(~Operation g x0 x=Identify_Element g R).

Definition Ring_invertible_Set(f g R:Set):=Prop_Set (fun a=>Ring_invertible_element f g R a).

Theorem Ring_invertible_Set_Law_1:forall f g R a:Set,a ∈ Ring_invertible_Set f g R<->Ring_invertible_element f g R a.
Proof.
intros.
apply Prop_Set_Law_1.
exists R.
intros.
destruct H.
apply H.
Qed.

Theorem Ring_invertible_Set_Law_2:forall f g R:Set,Ring f g R->Group (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R).
Proof.
intros.

assert (Binary_Operation (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R)).
apply (Restriction_Binary_Operation_Law_1 g R (Ring_invertible_Set f g R)).
split.
destruct H.
destruct H0.
destruct H0.
apply H0.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
apply H0.
intros.
destruct H0.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
destruct H2.
destruct H2.
destruct H3.
apply Ring_invertible_Set_Law_1 in H1.
destruct H1.
destruct H5.
destruct H5.
destruct H6.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
exists (Operation g x0 x).
split.
apply (Monoid_Law_1 g R x0 x).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H5.
apply H2.
split.
rewrite -> (Monoid_Law_2 g R (Operation g x1 x2) x0 x).
rewrite <- (Monoid_Law_2 g R x1 x2 x0).
rewrite -> H6.
rewrite -> (Monoid_Law_6 g R x1).
apply H3.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
split.
apply H1.
apply H5.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
split.
apply H5.
apply H2.
rewrite -> (Monoid_Law_2 g R (Operation g x0 x) x1 x2).
rewrite <- (Monoid_Law_2 g R x0 x x1).
rewrite -> H4.
rewrite -> (Monoid_Law_6 g R x0).
apply H7.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H5.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H5.
split.
apply H2.
apply H0.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H5.
apply H2.
split.
apply H0.
apply H1.

assert (Monoid (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R)).
split.
apply H0.
split.
intro.
intros.
destruct H1.
destruct H2.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x2 x3).
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x1 (Operation g x2 x3)).
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x1 x2).
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) (Operation g x1 x2) x3).
destruct H.
destruct H4.
destruct H4.
destruct H6.
apply H6.
split.
apply Ring_invertible_Set_Law_1 in H1.
destruct H1.
apply H1.
split.
apply Ring_invertible_Set_Law_1 in H2.
destruct H2.
apply H2.
apply Ring_invertible_Set_Law_1 in H3.
destruct H3.
apply H3.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
rewrite <- (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x1 x2).
unfold Operation.
apply (Map_Law_2 (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Double_Direct_Product_Set (Ring_invertible_Set f g R) (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R) (Ordered_Set x1 x2)).
split.
apply H0.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H1.
apply H2.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
apply H1.
apply H2.
apply H3.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
apply H1.
apply H2.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
apply H1.
rewrite <- (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x2 x3).
unfold Operation.
apply (Map_Law_2 (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Double_Direct_Product_Set (Ring_invertible_Set f g R) (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R) (Ordered_Set x2 x3)).
split.
apply H0.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H2.
apply H3.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
apply H2.
apply H3.
split.
destruct H.
destruct H4.
destruct H4.
apply H4.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H4.
destruct H4.
apply H4.
split.
apply H2.
apply H3.

exists (Identify_Element g R).
split.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
intros.
apply Ring_invertible_Set_Law_1 in H1.
destruct H1.
split.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x (Identify_Element g R)).
apply (Monoid_Law_6 g R x).
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
destruct H.
destruct H3.
destruct H3.
apply H3.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H3.
destruct H3.
apply H3.
split.
apply Ring_invertible_Set_Law_1.
split.
apply H1.
apply H2.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) (Identify_Element g R) x).
apply (Monoid_Law_7 g R x).
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
destruct H.
destruct H3.
destruct H3.
apply H3.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H3.
destruct H3.
apply H3.
split.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply Ring_invertible_Set_Law_1.
split.
apply H1.
apply H2.
split.
apply H0.
split.
destruct H1.
destruct H2.
apply H2.
split.
destruct H1.
destruct H2.
apply H3.

intros.
apply Ring_invertible_Set_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
destruct H4.
exists x0.
split.
apply Ring_invertible_Set_Law_1.
split.
apply H3.
exists x.
split.
apply H2.
split.
apply H5.
apply H4.
split.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x x0).
rewrite -> H4.
apply (Monoid_Law_8 (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R) (Identify_Element g R)).
split.
apply H1.
split.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
intros.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) y (Identify_Element g R)).
apply (Monoid_Law_6 g R y).
split.
apply (Ring_Law_2 f g R).
apply H.
apply Ring_invertible_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
destruct H.
destruct H7.
destruct H7.
apply H7.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H7.
destruct H7.
apply H7.
split.
apply H6.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
destruct H.
destruct H6.
destruct H6.
apply H6.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Ring_invertible_Set_Law_1.
split.
apply H2.
exists x0.
split.
apply H3.
split.
apply H4.
apply H5.
apply Ring_invertible_Set_Law_1.
split.
apply H3.
exists x.
split.
apply H2.
split.
apply H5.
apply H4.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) x0 x).
rewrite -> H5.
apply (Monoid_Law_8 (Restriction_Binary_Operation g (Ring_invertible_Set f g R)) (Ring_invertible_Set f g R) (Identify_Element g R)).
split.
apply H1.
split.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
intros.
rewrite -> (Restriction_Binary_Operation_Law_2 g R (Ring_invertible_Set f g R) y (Identify_Element g R)).
apply (Monoid_Law_6 g R y).
split.
apply (Ring_Law_2 f g R).
apply H.
apply Ring_invertible_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
destruct H.
destruct H7.
destruct H7.
apply H7.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H7.
destruct H7.
apply H7.
split.
apply H6.
apply Ring_invertible_Set_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> (Monoid_Law_6 g R (Identify_Element g R)).
split.
split.
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
destruct H.
destruct H6.
destruct H6.
apply H6.
split.
intro.
intro.
apply Ring_invertible_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Ring_invertible_Set_Law_1.
split.
apply H3.
exists x.
split.
apply H2.
split.
apply H5.
apply H4.
apply Ring_invertible_Set_Law_1.
split.
apply H2.
exists x0.
split.
apply H3.
split.
apply H4.
apply H5.
Qed.

Theorem Ring_invertible_Set_Law_3:forall f g R x:Set,Ring f g R/\x ∈ (Ring_invertible_Set f g R)->(Reverse_Element g R x) ∈ R.
Proof.
intros.
destruct H.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
destruct H1.
destruct H1.
destruct H2.

assert ((Reverse_Element g R x) ∈ R/\(Operation g x (Reverse_Element g R x))=(Identify_Element g R)/\(Operation g (Reverse_Element g R x) x)=(Identify_Element g R)).
apply (Well_Defined_1 (fun x'=>x' ∈ R/\(Operation g x x')=(Identify_Element g R)/\(Operation g x' x)=(Identify_Element g R))).
exists x0.
split.
split.
apply H1.
split.
apply H2.
apply H3.
intros.
destruct H4.
destruct H5.
rewrite <- (Monoid_Law_6 g R x0).
rewrite <- H5.
rewrite -> (Monoid_Law_2 g R x0 x x').
rewrite -> H3.
apply (Monoid_Law_7 g R x').
split.
apply (Ring_Law_2 f g R).
apply H.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H0.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
destruct H4.
destruct H5.

apply H4.
Qed.


Theorem Ring_invertible_Set_Law_4:forall f g R x:Set,Ring f g R/\x ∈ (Ring_invertible_Set f g R)->Operation g x (Reverse_Element g R x)=Identify_Element g R.
Proof.
intros.
destruct H.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
destruct H1.
destruct H1.
destruct H2.

assert ((Reverse_Element g R x) ∈ R/\(Operation g x (Reverse_Element g R x))=(Identify_Element g R)/\(Operation g (Reverse_Element g R x) x)=(Identify_Element g R)).
apply (Well_Defined_1 (fun x'=>x' ∈ R/\(Operation g x x')=(Identify_Element g R)/\(Operation g x' x)=(Identify_Element g R))).
exists x0.
split.
split.
apply H1.
split.
apply H2.
apply H3.
intros.
destruct H4.
destruct H5.
rewrite <- (Monoid_Law_6 g R x0).
rewrite <- H5.
rewrite -> (Monoid_Law_2 g R x0 x x').
rewrite -> H3.
apply (Monoid_Law_7 g R x').
split.
apply (Ring_Law_2 f g R).
apply H.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H0.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
destruct H4.
destruct H5.

apply H5.
Qed.

Theorem Ring_invertible_Set_Law_5:forall f g R x:Set,Ring f g R/\x ∈ (Ring_invertible_Set f g R)->Operation g (Reverse_Element g R x) x=Identify_Element g R.
Proof.
intros.
destruct H.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
destruct H1.
destruct H1.
destruct H2.

assert ((Reverse_Element g R x) ∈ R/\(Operation g x (Reverse_Element g R x))=(Identify_Element g R)/\(Operation g (Reverse_Element g R x) x)=(Identify_Element g R)).
apply (Well_Defined_1 (fun x'=>x' ∈ R/\(Operation g x x')=(Identify_Element g R)/\(Operation g x' x)=(Identify_Element g R))).
exists x0.
split.
split.
apply H1.
split.
apply H2.
apply H3.
intros.
destruct H4.
destruct H5.
rewrite <- (Monoid_Law_6 g R x0).
rewrite <- H5.
rewrite -> (Monoid_Law_2 g R x0 x x').
rewrite -> H3.
apply (Monoid_Law_7 g R x').
split.
apply (Ring_Law_2 f g R).
apply H.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H0.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
destruct H4.
destruct H5.

apply H6.
Qed.

Theorem Ring_invertible_Set_Law_6:forall f g R x:Set,Ring f g R/\x ∈ (Ring_invertible_Set f g R)->Ring_non_zero_divisor_element f g R x.
Proof.
intros.
destruct H.
apply Ring_invertible_Set_Law_1 in H0.
destruct H0.
destruct H1.
destruct H1.
destruct H2.
split.
apply H0.
intros.
destruct H4.
split.
intro.
apply H5.
rewrite <- (Monoid_Law_7 g R x1).
rewrite <- H3.
rewrite <- (Monoid_Law_2 g R x0 x x1).
rewrite -> H6.
apply (Ring_Law_5 f g R x0).
split.
apply H.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H0.
apply H4.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H4.
intro.
apply H5.
rewrite <- (Monoid_Law_6 g R x1).
rewrite <- H2.
rewrite -> (Monoid_Law_2 g R x1 x x0).
rewrite -> H6.
apply (Ring_Law_6 f g R x0).
split.
apply H.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H4.
split.
apply H0.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H4.
Qed.



(*体*)
Definition Field(f g F:Set):=Comutive_Ring f g F/\(forall x:Set,x ∈ F->(x=Identify_Element f F\/Ring_invertible_element f g F x)).

Theorem Field_Law_1:forall f g F:Set,Field f g F->Comutive_Ring f g F.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Field_Law_2:forall f g F x:Set,Field f g F/\x ∈ F->(x=Identify_Element f F\/Ring_invertible_element f g F x).
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
Qed.

Theorem Field_Law_3:forall f g F:Set,Field f g F->Integral_Domain f g F.
Proof.
intros.
destruct H.
split.
apply H.
intros.
apply H0 in H1.
destruct H1.
left.
apply H1.
right.
apply (Ring_invertible_Set_Law_6 f g F x).
split.
apply Comutive_Ring_Law_1.
apply H.
apply Ring_invertible_Set_Law_1.
apply H1.
Qed.



(*部分環*)
Definition Sub_Ring(f g R f0 g0 R0:Set):=Ring f g R/\Ring f0 g0 R0/\R0 ⊂ R/\f0=Restriction_Binary_Operation f R0/\g0=Restriction_Binary_Operation g R0/\Identify_Element g R=Identify_Element g0 R0.

Theorem Sub_Ring_Law_1:forall f g R f0 g0 R0:Set,Sub_Ring f g R f0 g0 R0->Sub_Group f R f0 R0.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
split.

apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.

apply Abel_Group_Law_1.
apply (Ring_Law_1 f0 g0 R0).
apply H0.

split.
apply H1.

apply H2.
Qed.

Theorem Sub_Ring_Law_2:forall f g R f0 g0 R0 x1 x2:Set,Sub_Ring f g R f0 g0 R0/\x1 ∈ R0/\x2 ∈ R0->Operation g0 x1 x2=Operation g x1 x2.
Proof.
intros.
destruct H.
destruct H0.
destruct H.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
rewrite -> H5.
unfold Operation.
unfold Restriction_Binary_Operation.
apply (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x2)).
split.
destruct H.
destruct H7.
destruct H7.
apply H7.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H7.
apply Double_Direct_Product_Set_Law_1.
destruct H7.
destruct H7.
destruct H7.
destruct H8.
exists x.
exists x0.
split.
apply H7.
split.
apply H3.
apply H8.
apply H3.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H0.
apply H1.
Qed.

Theorem Sub_Ring_Law_3:forall f g R R0:Set,Sub_Ring f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0<->Ring f g R/\R0 ⊂ R/\(forall x y:Set,x ∈ R0/\y ∈ R0->(Operation f x (Reverse_Element f R y)) ∈ R0)/\(forall x y:Set,x ∈ R0/\y ∈ R0->(Operation g x y) ∈ R0)/\(Identify_Element g R) ∈ R0.
Proof.
intros.
split.

intros.
assert (Sub_Ring f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
split.
apply H0.
split.
apply H2.
split.
intros.
destruct H6.
rewrite <- (Sub_Group_Law_1 f R (Restriction_Binary_Operation f R0) R0 x (Reverse_Element f R y)).
rewrite -> (Sub_Group_Law_3 f R (Restriction_Binary_Operation f R0) R0 y).
apply Group_Law_2.
split.
apply H1.
split.
apply H6.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H1.
apply H7.
split.
apply (Sub_Ring_Law_1 f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H.
apply H7.
split.
apply (Sub_Ring_Law_1 f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H.
split.
apply H6.
rewrite -> (Sub_Group_Law_3 f R (Restriction_Binary_Operation f R0) R0 y).
apply Group_Law_9.
split.
apply (Sub_Ring_Law_1 f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H.
apply H7.
split.
apply (Sub_Ring_Law_1 f g R (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H.
apply H7.
split.
intros.
destruct H6.
unfold Operation.
rewrite <- (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x y)).
apply (Monoid_Law_1 (Restriction_Map g (Double_Direct_Product_Set R0 R0)) R0 x y).
split.
apply (Ring_Law_2 (Restriction_Binary_Operation f R0) (Restriction_Map g (Double_Direct_Product_Set R0 R0)) R0).
apply H.
split.
apply H6.
apply H7.
split.
destruct H0.
destruct H8.
destruct H8.
apply H8.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H8.
apply Double_Direct_Product_Set_Law_1.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
exists x0.
exists x1.
split.
apply H8.
split.
apply H2.
apply H9.
apply H2.
apply H10.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists y.
split.
split.
split.
apply H6.
apply H7.
rewrite -> H5.
apply Monoid_Law_5.
apply (Ring_Law_2 (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
apply H1.

intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
assert (Sub_Group f R (Restriction_Binary_Operation f R0) R0).
apply Sub_Group_Law_4.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
split.
apply H1.
apply Empty_Set_Law_1.
exists (Identify_Element g R).
apply H3.
assert (Sub_Group f R (Restriction_Binary_Operation f R0) R0).
apply H4.
destruct H5.
destruct H6.
destruct H7.
split.
apply H.

assert (Ring (Restriction_Binary_Operation f R0) (Restriction_Binary_Operation g R0) R0).
split.
split.
apply H6.
intros.
destruct H9.
rewrite -> (Sub_Group_Law_1 f R (Restriction_Binary_Operation f R0) R0 x y).
rewrite -> (Sub_Group_Law_1 f R (Restriction_Binary_Operation f R0) R0 y x).
apply (Abel_Group_Law_4 f R x y).
split.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
apply H9.
apply H0.
apply H10.
split.
apply H4.
split.
apply H10.
apply H9.
split.
apply H4.
split.
apply H9.
apply H10.

split.
split.
apply (Map_Law_5 (Restriction_Binary_Operation g R0) (Double_Direct_Product_Set R0 R0) R R0).
split.
apply (Restriction_Map_Law_2 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R).
split.
destruct H.
destruct H9.
destruct H9.
apply H9.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H9.
apply Double_Direct_Product_Set_Law_1.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
exists x.
exists x0.
split.
apply H9.
split.
apply H0.
apply H10.
apply H0.
apply H11.
split.
apply H0.
intros.
apply Double_Direct_Product_Set_Law_1 in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R x).
rewrite <- H9.
unfold Operation in H2.
apply H2.
split.
apply H10.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x2.
exists x3.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
apply H9.
split.
apply H10.
apply H11.
split.
intro.
intros.
destruct H9.
destruct H10.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x2 x3)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x2)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 (Culculateion_Map g (Ordered_Set x2 x3)))).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set (Culculateion_Map g (Ordered_Set x1 x2)) x3)).
assert (Culculateion_Map g (Ordered_Set x1 (Culculateion_Map g (Ordered_Set x2 x3)))=Operation g x1 (Operation g x2 x3)).
unfold Operation.
split.
rewrite -> H12.
clear H12.
assert (Culculateion_Map g (Ordered_Set (Culculateion_Map g (Ordered_Set x1 x2)) x3)=Operation g (Operation g x1 x2) x3).
unfold Operation.
split.
rewrite -> H12.
clear H12.
rewrite -> (Monoid_Law_2 g R x1 x2 x3).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H9.
split.
apply H0.
apply H10.
apply H0.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map g (Ordered_Set x1 x2)).
exists x3.
split.
split.
split.
assert (Culculateion_Map g (Ordered_Set x1 x2)=Operation g x1 x2).
unfold Operation.
split.
rewrite -> H12.
apply H2.
split.
apply H9.
apply H10.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists (Culculateion_Map g (Ordered_Set x2 x3)).
split.
split.
split.
apply H9.
assert (Culculateion_Map g (Ordered_Set x2 x3)=Operation g x2 x3).
unfold Operation.
split.
rewrite -> H12.
apply H2.
split.
apply H10.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H9.
apply H10.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H10.
apply H11.
exists (Identify_Element g R).
split.
apply H3.
intros.
split.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x (Identify_Element g R))).
assert (Culculateion_Map g (Ordered_Set x (Identify_Element g R))=Operation g x (Identify_Element g R)).
unfold Operation.
split.
rewrite -> H10.
rewrite -> (Monoid_Law_6 g R x).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H9.
split.
destruct H.
destruct H10.
destruct H10.
apply H10.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H10.
apply Double_Direct_Product_Set_Law_1.
destruct H10.
destruct H10.
destruct H10.
destruct H11.
exists x0.
exists x1.
split.
apply H10.
split.
apply H0.
apply H11.
apply H0.
apply H12.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists (Identify_Element g R).
split.
split.
split.
apply H9.
apply H3.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set (Identify_Element g R) x)).
assert (Culculateion_Map g (Ordered_Set (Identify_Element g R) x)=Operation g (Identify_Element g R) x).
unfold Operation.
split.
rewrite -> H10.
rewrite -> (Monoid_Law_7 g R x).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H9.
split.
destruct H.
destruct H10.
destruct H10.
apply H10.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H10.
apply Double_Direct_Product_Set_Law_1.
destruct H10.
destruct H10.
destruct H10.
destruct H11.
exists x0.
exists x1.
split.
apply H10.
split.
apply H0.
apply H11.
apply H0.
apply H12.
apply Double_Direct_Product_Set_Law_1.
exists (Identify_Element g R).
exists x.
split.
split.
split.
apply H3.
apply H9.
split.

intros.
destruct H9.
destruct H10.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x2 x3)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 (Culculateion_Map f (Ordered_Set x2 x3)))).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x2)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x3)).
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set (Culculateion_Map g (Ordered_Set x1 x2)) (Culculateion_Map g (Ordered_Set x1 x3)))).
apply (Ring_Law_3 f g R x1 x2 x3).
split.
apply H.
split.
apply H0.
apply H9.
split.
apply H0.
apply H10.
apply H0.
apply H11.
split.
destruct H.
destruct H.
destruct H.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map g (Ordered_Set x1 x2)).
exists (Culculateion_Map g (Ordered_Set x1 x3)).
split.
split.
split.
assert (Culculateion_Map g (Ordered_Set x1 x2)=Operation g x1 x2).
unfold Operation.
split.
rewrite -> H12.
apply H2.
split.
apply H9.
apply H10.
assert (Culculateion_Map g (Ordered_Set x1 x3)=Operation g x1 x3).
unfold Operation.
split.
rewrite -> H12.
apply H2.
split.
apply H9.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x3.
split.
split.
split.
apply H9.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H9.
apply H10.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists (Culculateion_Map f (Ordered_Set x2 x3)).
split.
split.
split.
apply H9.
assert (Culculateion_Map f (Ordered_Set x2 x3)=Operation f x2 x3).
unfold Operation.
split.
rewrite -> H12.
unfold Operation.
rewrite <- (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x2 x3)).
apply (Map_Law_2 (Restriction_Map f (Double_Direct_Product_Set R0 R0)) (Double_Direct_Product_Set R0 R0) R0 (Ordered_Set x2 x3)).
split.
destruct H6.
apply H6.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H10.
apply H11.
split.
destruct H5.
apply H5.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H13.
apply Double_Direct_Product_Set_Law_1.
destruct H13.
destruct H13.
destruct H13.
destruct H14.
exists x.
exists x0.
split.
apply H13.
split.
apply H0.
apply H14.
apply H0.
apply H15.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H10.
apply H11.
split.
destruct H5.
apply H5.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H10.
apply H11.

intros.
destruct H9.
destruct H10.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x2)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set (Culculateion_Map f (Ordered_Set x1 x2)) x3)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x3)).
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x2 x3)).
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set (Culculateion_Map g (Ordered_Set x1 x3)) (Culculateion_Map g (Ordered_Set x2 x3)))).
apply (Ring_Law_4 f g R x1 x2 x3).
split.
apply H.
split.
apply H0.
apply H9.
split.
apply H0.
apply H10.
apply H0.
apply H11.
split.
destruct H5.
apply H5.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map g (Ordered_Set x1 x3)).
exists (Culculateion_Map g (Ordered_Set x2 x3)).
split.
split.
split.
unfold Operation in H2.
apply H2.
split.
apply H9.
apply H11.
unfold Operation in H2.
apply H2.
split.
apply H10.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H10.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x3.
split.
split.
split.
apply H9.
apply H11.
split.
destruct H.
destruct H12.
destruct H12.
apply H12.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map f (Ordered_Set x1 x2)).
exists x3.
split.
split.
split.
rewrite <- (Restriction_Map_Law_3 f (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set x1 x2)).
apply (Map_Law_2 (Restriction_Map f (Double_Direct_Product_Set R0 R0)) (Double_Direct_Product_Set R0 R0) R0 (Ordered_Set x1 x2)).
split.
destruct H6.
apply H6.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H9.
apply H10.
split.
destruct H5.
apply H5.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H9.
apply H10.
apply H11.
split.
destruct H5.
apply H5.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H12.
apply Double_Direct_Product_Set_Law_1.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
exists x.
exists x0.
split.
apply H12.
split.
apply H0.
apply H13.
apply H0.
apply H14.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H9.
apply H10.
split.

apply H9.
split.
apply H7.
split.
split.
split.
split.
apply (Monoid_Law_8 (Restriction_Binary_Operation g R0) R0 (Identify_Element g R)).
split.
destruct H9.
destruct H10.
apply H10.
split.
apply H3.
intros.
unfold Operation.
unfold Restriction_Binary_Operation.
rewrite -> (Restriction_Map_Law_3 g (Double_Direct_Product_Set R R) (Double_Direct_Product_Set R0 R0) R (Ordered_Set y (Identify_Element g R))).
assert (Culculateion_Map g (Ordered_Set y (Identify_Element g R))=Operation g y (Identify_Element g R)).
unfold Operation.
split.
rewrite -> H11.
apply (Monoid_Law_6 g R y).
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H10.
split.
destruct H.
destruct H11.
destruct H11.
apply H11.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H11.
apply Double_Direct_Product_Set_Law_1.
destruct H11.
destruct H11.
destruct H11.
destruct H12.
exists x.
exists x0.
split.
apply H11.
split.
apply H0.
apply H12.
apply H0.
apply H13.
apply Double_Direct_Product_Set_Law_1.
exists y.
exists (Identify_Element g R).
split.
split.
split.
apply H10.
apply H3.
Qed.



(*イデアル*)
Definition Ring_Left_Ideal(f g R I:Set):=I ⊂ R/\(forall x y:Set,x ∈ I/\y ∈ I->(Operation f x y) ∈ I)/\(forall a x:Set,a ∈ R/\x ∈ I->(Operation g a x) ∈ I)/\~I=∅.

Theorem Ring_Left_Ideal_Law_1:forall f g R I x:Set,Ring_Left_Ideal f g R I/\x ∈ I->x ∈ R.
Proof.
intros.
destruct H.
destruct H.
apply H.
apply H0.
Qed.

Theorem Ring_Left_Ideal_Law_2:forall f g R I x y:Set,Ring_Left_Ideal f g R I/\x ∈ I/\y ∈ I->(Operation f x y) ∈ I.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Ring_Left_Ideal_Law_3:forall f g R I a x:Set,Ring_Left_Ideal f g R I/\a ∈ R/\x ∈ I->(Operation g a x) ∈ I.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Ring_Left_Ideal_Law_4:forall f g R I:Set,Ring_Left_Ideal f g R I->~I=∅.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply H2.
Qed.

Theorem Ring_Left_Ideal_Law_5:forall f g R I:Set,Ring f g R/\Ring_Left_Ideal f g R I->(Identify_Element f R) ∈ I.
Proof.
intros.
destruct H.
assert (~I=∅).
apply (Ring_Left_Ideal_Law_4 f g R I).
apply H0.
apply Empty_Set_Law_1 in H1.
destruct H1.
rewrite <- (Group_Law_10 f R x).
apply (Ring_Left_Ideal_Law_2 f g R I x (Reverse_Element f R x)).
split.
apply H0.
split.
apply H1.
rewrite <- (Monoid_Law_7 g R x).
rewrite <- (Ring_Law_7 f g R (Identify_Element g R) x).
apply (Ring_Left_Ideal_Law_3 f g R I (Reverse_Element f R (Identify_Element g R)) x).
split.
apply H0.
split.
apply (Group_Law_9 f R (Identify_Element g R)).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply (Ring_Left_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
apply (Ring_Left_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply (Ring_Left_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
Qed.

Theorem Ring_Left_Ideal_Law_6:forall f g R I:Set,Ring f g R/\Ring_Left_Ideal f g R I->Normal_Sub_Group f R (Restriction_Binary_Operation f I) I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Abel_Group_Law_3.
split.
apply (Ring_Law_1 f g R).
apply H.
apply Sub_Group_Law_4.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
split.
intros.
destruct H4.
apply H1.
split.
apply H4.
rewrite <- (Monoid_Law_7 g R (Reverse_Element f R x2)).
rewrite -> (Ring_Law_8 f g R (Identify_Element g R) x2).
rewrite <- (Ring_Law_7 f g R (Identify_Element g R) x2).
apply H2.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H5.
split.
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H5.
split.
apply H.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H5.
split.
apply (Ring_Law_2 f g R).
apply H.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H0.
apply H5.
apply H3.
Qed.

Theorem Ring_Left_Ideal_Law_7:forall f g R I:Set,Ring f g R/\Ring_Left_Ideal f g R I/\(Identify_Element g R) ∈ I->R=I.
Proof.
intros.
destruct H.
destruct H0.
assert (Ring_Left_Ideal f g R I).
apply H0.
destruct H2.
destruct H3.
destruct H4.
apply Theorem_of_Extensionality.
intros.
split.
intro.
rewrite <- (Monoid_Law_6 g R z).
apply H4.
split.
apply H6.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H6.
apply H2.
Qed.

Theorem Ring_Left_Ideal_Law_8:forall f g R X:Set,Ring f g R/\(forall I:Set,I ∈ X->Ring_Left_Ideal f g R I)/\~X=∅->Ring_Left_Ideal f g R (Meet_Set X).
Proof.
intros.
destruct H.
destruct H0.
split.

intro.
intro.
assert (~X=∅).
apply H1.
apply Empty_Set_Law_1 in H3.
destruct H3.
apply (Ring_Left_Ideal_Law_1 f g R x z).
split.
apply H0.
apply H3.
apply (Meet_Set_Law_2 X x z).
split.
apply H2.
apply H3.
split.

intro.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Left_Ideal_Law_2 f g R A x y).
split.
apply H0.
apply H4.
split.
apply (Meet_Set_Law_2 X A x).
split.
apply H2.
apply H4.
apply (Meet_Set_Law_2 X A y).
split.
apply H3.
apply H4.

split.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Left_Ideal_Law_3 f g R A a x).
split.
apply H0.
apply H4.
split.
apply H2.
apply (Meet_Set_Law_2 X A x).
split.
apply H3.
apply H4.
apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Meet_Set_Law_3.
split.
apply H1.
intros.
apply (Ring_Left_Ideal_Law_5 f g R A).
split.
apply H.
apply H0.
apply H2.
Qed.

Theorem Ring_Left_Ideal_Law_9:forall f g R I J:Set,Ring f g R/\Ring_Left_Ideal f g R I/\Ring_Left_Ideal f g R J->Ring_Left_Ideal f g R (I ∩ J).
Proof.
intros.
destruct H.
destruct H0.
apply Ring_Left_Ideal_Law_8.
split.
apply H.
split.
intros.
apply Pair_Set_Law_1 in H2.
destruct H2.
rewrite -> H2.
apply H0.
rewrite -> H2.
apply H1.
apply Pair_Set_Law_4.
Qed.



Definition Ring_Left_Principal_Ideal(f g R x:Set):=Prop_Set (fun a=>a ∈ R/\exists y:Set,y ∈ R/\a=Operation g y x).

Theorem Ring_Left_Principal_Ideal_Law_1:forall f g R x a:Set,a ∈ (Ring_Left_Principal_Ideal f g R x)<->a ∈ R/\exists y:Set,y ∈ R/\a=Operation g y x.
Proof.
intros.
apply Prop_Set_Law_1.
exists R.
intros.
destruct H.
apply H.
Qed.

Theorem Ring_Left_Principal_Ideal_Law_2:forall f g R x:Set,Ring f g R/\x ∈ R->Ring_Left_Ideal f g R (Ring_Left_Principal_Ideal f g R x).
Proof.
intros.
destruct H.
split.

intro.
intro.
apply Ring_Left_Principal_Ideal_Law_1 in H1.
destruct H1.
apply H1.
split.

intros.
destruct H1.
apply Ring_Left_Principal_Ideal_Law_1 in H1.
destruct H1.
destruct H3.
destruct H3.
apply Ring_Left_Principal_Ideal_Law_1 in H2.
destruct H2.
destruct H5.
destruct H5.
rewrite -> H4.
rewrite -> H6.
rewrite <- (Ring_Law_4 f g R x1 x2 x).
apply Ring_Left_Principal_Ideal_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H3.
apply H5.
apply H0.
exists (Operation f x1 x2).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H3.
apply H5.
split.
split.
apply H.
split.
apply H3.
split.
apply H5.
apply H0.

split.
intros.
destruct H1.
apply Ring_Left_Principal_Ideal_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
apply Ring_Left_Principal_Ideal_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
exists (Operation g a x1).
split.
apply (Monoid_Law_1 g R a x1).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H3.
rewrite -> H4.
apply (Monoid_Law_2 g R a x1 x).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H3.
apply H0.

apply Empty_Set_Law_1.
exists x.
apply Ring_Left_Principal_Ideal_Law_1.
split.
apply H0.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
symmetry.
apply Monoid_Law_7.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
Qed.




Definition Ring_Left_Ideal_Sum(f R I J:Set):=Prop_Set (fun a=>exists x y:Set,a ∈ R/\a=Operation f x y/\x ∈ I/\y ∈ J).

Theorem Ring_Left_Ideal_Sum_Law_1:forall f R I J a:Set,a ∈ (Ring_Left_Ideal_Sum f R I J)<->exists x y:Set,a ∈ R/\a=Operation f x y/\x ∈ I/\y ∈ J.
Proof.
intros.
apply Prop_Set_Law_1.
exists R.
intros.
destruct H.
destruct H.
destruct H.
apply H.
Qed.

Theorem Ring_Left_Ideal_Sum_Law_2:forall f g R I J:Set,Ring f g R/\Ring_Left_Ideal f g R I/\Ring_Left_Ideal f g R J->Ring_Left_Ideal f g R (Ring_Left_Ideal_Sum f R I J).
Proof.
intros.
destruct H.
destruct H0.
split.

intro.
intro.
apply Ring_Left_Ideal_Sum_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
apply H2.
split.

intros.
destruct H2.
apply Ring_Left_Ideal_Sum_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
destruct H5.
apply Ring_Left_Ideal_Sum_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H7.
destruct H8.
apply Ring_Left_Ideal_Sum_Law_1.
exists (Operation f x0 x2).
exists (Operation f x1 x3).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H2.
apply H3.
split.
rewrite -> H4.
rewrite -> H7.
rewrite -> (Group_Law_3 f R (Operation f x0 x1) x2 x3).
rewrite <- (Group_Law_3 f R x0 x1 x2).
rewrite -> (Abel_Group_Law_4 f R x1 x2).
rewrite -> (Group_Law_3 f R x0 x2 x1).
rewrite -> (Group_Law_3 f R (Operation f x0 x2) x1 x3).
split.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
apply (Ring_Left_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Left_Ideal_Law_1 f g R J x3).
split.
apply H1.
apply H9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
split.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Left_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
split.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Left_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
apply (Ring_Left_Ideal_Law_1 f g R J x3).
split.
apply H1.
apply H9.
split.
apply (Ring_Left_Ideal_Law_2 f g R I x0 x2).
split.
apply H0.
split.
apply H5.
apply H8.
apply (Ring_Left_Ideal_Law_2 f g R J x1 x3).
split.
apply H1.
split.
apply H6.
apply H9.

split.
intros.
destruct H2.
apply Ring_Left_Ideal_Sum_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
destruct H5.
apply Ring_Left_Ideal_Sum_Law_1.
exists (Operation g a x0).
exists (Operation g a x1).
split.
apply (Monoid_Law_1 g R a x).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
rewrite -> H4.
apply (Ring_Law_3 f g R a x0 x1).
split.
apply H.
split.
apply H2.
split.
apply (Ring_Left_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
apply (Ring_Left_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
split.
apply (Ring_Left_Ideal_Law_3 f g R I a x0).
split.
apply H0.
split.
apply H2.
apply H5.
apply (Ring_Left_Ideal_Law_3 f g R J a x1).
split.
apply H1.
split.
apply H2.
apply H6.

apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Ring_Left_Ideal_Sum_Law_1.
exists (Identify_Element f R).
exists (Identify_Element f R).
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
symmetry.
apply (Group_Law_5 f R (Identify_Element f R)).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Left_Ideal_Law_5 f g R I).
split.
apply H.
apply H0.
apply (Ring_Left_Ideal_Law_5 f g R J).
split.
apply H.
apply H1.
Qed.



Definition Ring_Right_Ideal(f g R I:Set):=I ⊂ R/\(forall x y:Set,x ∈ I/\y ∈ I->(Operation f x y) ∈ I)/\(forall a x:Set,a ∈ R/\x ∈ I->(Operation g x a) ∈ I)/\~I=∅.

Theorem Ring_Right_Ideal_Law_1:forall f g R I x:Set,Ring_Right_Ideal f g R I/\x ∈ I->x ∈ R.
Proof.
intros.
destruct H.
destruct H.
apply H.
apply H0.
Qed.

Theorem Ring_Right_Ideal_Law_2:forall f g R I x y:Set,Ring_Right_Ideal f g R I/\x ∈ I/\y ∈ I->(Operation f x y) ∈ I.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Ring_Right_Ideal_Law_3:forall f g R I a x:Set,Ring_Right_Ideal f g R I/\a ∈ R/\x ∈ I->(Operation g x a) ∈ I.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Ring_Right_Ideal_Law_4:forall f g R I:Set,Ring_Right_Ideal f g R I->~I=∅.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply H2.
Qed.

Theorem Ring_Right_Ideal_Law_5:forall f g R I:Set,Ring f g R/\Ring_Right_Ideal f g R I->(Identify_Element f R) ∈ I.
Proof.
intros.
destruct H.
assert (~I=∅).
apply (Ring_Right_Ideal_Law_4 f g R I).
apply H0.
apply Empty_Set_Law_1 in H1.
destruct H1.
rewrite <- (Group_Law_10 f R x).
apply (Ring_Right_Ideal_Law_2 f g R I x (Reverse_Element f R x)).
split.
apply H0.
split.
apply H1.
rewrite <- (Monoid_Law_6 g R x).
rewrite <- (Ring_Law_8 f g R x (Identify_Element g R)).
apply (Ring_Right_Ideal_Law_3 f g R I (Reverse_Element f R (Identify_Element g R)) x).
split.
apply H0.
split.
apply (Group_Law_9 f R (Identify_Element g R)).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Ring_Law_2 f g R).
apply H.
apply (Ring_Right_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply (Ring_Right_Ideal_Law_1 f g R I x).
split.
apply H0.
apply H1.
Qed.

Theorem Ring_Right_Ideal_Law_6:forall f g R I:Set,Ring f g R/\Ring_Right_Ideal f g R I->Normal_Sub_Group f R (Restriction_Binary_Operation f I) I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Abel_Group_Law_3.
split.
apply (Ring_Law_1 f g R).
apply H.
apply Sub_Group_Law_4.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
split.
intros.
destruct H4.
apply H1.
split.
apply H4.
rewrite <- (Monoid_Law_6 g R x2).
rewrite <- (Ring_Law_8 f g R x2 (Identify_Element g R)).
apply H2.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H5.
split.
apply H.
split.
apply H0.
apply H5.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
apply H5.
apply H3.
Qed.

Theorem Ring_Right_Ideal_Law_7:forall f g R I:Set,Ring f g R/\Ring_Right_Ideal f g R I/\(Identify_Element g R) ∈ I->R=I.
Proof.
intros.
destruct H.
destruct H0.
assert (Ring_Right_Ideal f g R I).
apply H0.
destruct H2.
destruct H3.
destruct H4.
apply Theorem_of_Extensionality.
intros.
split.
intro.
rewrite <- (Monoid_Law_7 g R z).
apply H4.
split.
apply H6.
apply H1.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H6.
apply H2.
Qed.

Theorem Ring_Right_Ideal_Law_8:forall f g R X:Set,Ring f g R/\(forall I:Set,I ∈ X->Ring_Right_Ideal f g R I)/\~X=∅->Ring_Right_Ideal f g R (Meet_Set X).
Proof.
intros.
destruct H.
destruct H0.
split.

intro.
intro.
assert (~X=∅).
apply H1.
apply Empty_Set_Law_1 in H3.
destruct H3.
apply (Ring_Right_Ideal_Law_1 f g R x z).
split.
apply H0.
apply H3.
apply (Meet_Set_Law_2 X x z).
split.
apply H2.
apply H3.
split.

intro.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Right_Ideal_Law_2 f g R A x y).
split.
apply H0.
apply H4.
split.
apply (Meet_Set_Law_2 X A x).
split.
apply H2.
apply H4.
apply (Meet_Set_Law_2 X A y).
split.
apply H3.
apply H4.

split.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Right_Ideal_Law_3 f g R A a x).
split.
apply H0.
apply H4.
split.
apply H2.
apply (Meet_Set_Law_2 X A x).
split.
apply H3.
apply H4.

apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Meet_Set_Law_3.
split.
apply H1.
intros.
apply (Ring_Right_Ideal_Law_5 f g R A).
split.
apply H.
apply H0.
apply H2.
Qed.

Theorem Ring_Right_Ideal_Law_9:forall f g R I J:Set,Ring f g R/\Ring_Right_Ideal f g R I/\Ring_Right_Ideal f g R J->Ring_Right_Ideal f g R (I ∩ J).
Proof.
intros.
destruct H.
destruct H0.
apply Ring_Right_Ideal_Law_8.
split.
apply H.
split.
intros.
apply Pair_Set_Law_1 in H2.
destruct H2.
rewrite -> H2.
apply H0.
rewrite -> H2.
apply H1.
apply Pair_Set_Law_4.
Qed.



Definition Ring_Right_Principal_Ideal(f g R x:Set):=Prop_Set (fun a=>a ∈ R/\exists y:Set,y ∈ R/\a=Operation g x y).

Theorem Ring_Right_Principal_Ideal_Law_1:forall f g R x a:Set,a ∈ (Ring_Right_Principal_Ideal f g R x)<->a ∈ R/\exists y:Set,y ∈ R/\a=Operation g x y.
Proof.
intros.
apply Prop_Set_Law_1.
exists R.
intros.
destruct H.
apply H.
Qed.

Theorem Ring_Right_Principal_Ideal_Law_2:forall f g R x:Set,Ring f g R/\x ∈ R->Ring_Right_Ideal f g R (Ring_Right_Principal_Ideal f g R x).
Proof.
intros.
destruct H.
split.

intro.
intro.
apply Ring_Right_Principal_Ideal_Law_1 in H1.
destruct H1.
apply H1.
split.

intros.
destruct H1.
apply Ring_Right_Principal_Ideal_Law_1 in H1.
destruct H1.
destruct H3.
destruct H3.
apply Ring_Right_Principal_Ideal_Law_1 in H2.
destruct H2.
destruct H5.
destruct H5.
rewrite -> H4.
rewrite -> H6.
rewrite <- (Ring_Law_3 f g R x x1 x2).
apply Ring_Right_Principal_Ideal_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H3.
apply H5.
exists (Operation f x1 x2).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H3.
apply H5.
split.
split.
apply H.
split.
apply H0.
split.
apply H3.
apply H5.

split.
intros.
destruct H1.
apply Ring_Right_Principal_Ideal_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
apply Ring_Right_Principal_Ideal_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H1.
exists (Operation g x1 a).
split.
apply (Monoid_Law_1 g R x1 a).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H3.
apply H1.
rewrite -> H4.
symmetry.
apply (Monoid_Law_2 g R x x1 a).
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
split.
apply H3.
apply H1.

apply Empty_Set_Law_1.
exists x.
apply Ring_Right_Principal_Ideal_Law_1.
split.
apply H0.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
symmetry.
apply Monoid_Law_6.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H0.
Qed.



Definition Ring_Right_Ideal_Sum(f R I J:Set):=Prop_Set (fun a=>exists x y:Set,a ∈ R/\a=Operation f x y/\x ∈ I/\y ∈ J).

Theorem Ring_Right_Ideal_Sum_Law_1:forall f R I J a:Set,a ∈ (Ring_Right_Ideal_Sum f R I J)<->exists x y:Set,a ∈ R/\a=Operation f x y/\x ∈ I/\y ∈ J.
Proof.
intros.
apply Prop_Set_Law_1.
exists R.
intros.
destruct H.
destruct H.
destruct H.
apply H.
Qed.

Theorem Ring_Right_Ideal_Sum_Law_2:forall f g R I J:Set,Ring f g R/\Ring_Right_Ideal f g R I/\Ring_Right_Ideal f g R J->Ring_Right_Ideal f g R (Ring_Right_Ideal_Sum f R I J).
Proof.
intros.
destruct H.
destruct H0.
split.

intro.
intro.
apply Ring_Right_Ideal_Sum_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
apply H2.
split.

intros.
destruct H2.
apply Ring_Right_Ideal_Sum_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
destruct H5.
apply Ring_Right_Ideal_Sum_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H7.
destruct H8.
apply Ring_Right_Ideal_Sum_Law_1.
exists (Operation f x0 x2).
exists (Operation f x1 x3).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H2.
apply H3.
split.
rewrite -> H4.
rewrite -> H7.
rewrite -> (Group_Law_3 f R (Operation f x0 x1) x2 x3).
rewrite <- (Group_Law_3 f R x0 x1 x2).
rewrite -> (Abel_Group_Law_4 f R x1 x2).
rewrite -> (Group_Law_3 f R x0 x2 x1).
rewrite -> (Group_Law_3 f R (Operation f x0 x2) x1 x3).
split.
split.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
apply (Ring_Right_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Right_Ideal_Law_1 f g R J x3).
split.
apply H1.
apply H9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
split.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Right_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
split.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply (Ring_Right_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x2).
split.
apply H0.
apply H8.
apply (Ring_Right_Ideal_Law_1 f g R J x3).
split.
apply H1.
apply H9.
split.
apply (Ring_Right_Ideal_Law_2 f g R I x0 x2).
split.
apply H0.
split.
apply H5.
apply H8.
apply (Ring_Right_Ideal_Law_2 f g R J x1 x3).
split.
apply H1.
split.
apply H6.
apply H9.

split.
intros.
destruct H2.
apply Ring_Right_Ideal_Sum_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
destruct H5.
apply Ring_Right_Ideal_Sum_Law_1.
exists (Operation g x0 a).
exists (Operation g x1 a).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H3.
apply H2.
split.
rewrite -> H4.
apply (Ring_Law_4 f g R x0 x1 a).
split.
apply H.
split.
apply (Ring_Right_Ideal_Law_1 f g R I x0).
split.
apply H0.
apply H5.
split.
apply (Ring_Right_Ideal_Law_1 f g R J x1).
split.
apply H1.
apply H6.
apply H2.
split.
apply (Ring_Right_Ideal_Law_3 f g R I a x0).
split.
apply H0.
split.
apply H2.
apply H5.
apply (Ring_Right_Ideal_Law_3 f g R J a x1).
split.
apply H1.
split.
apply H2.
apply H6.

apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Ring_Right_Ideal_Sum_Law_1.
exists (Identify_Element f R).
exists (Identify_Element f R).
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
rewrite -> (Group_Law_5 f R (Identify_Element f R)).
split.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Right_Ideal_Law_5 f g R I).
split.
apply H.
apply H0.
apply (Ring_Right_Ideal_Law_5 f g R J).
split.
apply H.
apply H1.
Qed.



Definition Ring_Semi_Ideal(f g R I:Set):=I ⊂ R/\(forall x y:Set,x ∈ I/\y ∈ I->(Operation f x y) ∈ I)/\(forall a x:Set,a ∈ R/\x ∈ I->(Operation g x a) ∈ I)/\(forall a x:Set,a ∈ R/\x ∈ I->(Operation g a x) ∈ I)/\~I=∅.

Theorem Ring_Semi_Ideal_Law_1:forall f g R I:Set,Ring_Semi_Ideal f g R I->Ring_Left_Ideal f g R I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.
apply H.
split.
apply H0.
split.
apply H2.
apply H3.
Qed.

Theorem Ring_Semi_Ideal_Law_2:forall f g R I:Set,Ring_Semi_Ideal f g R I->Ring_Right_Ideal f g R I.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H3.
Qed.

Theorem Ring_Semi_Ideal_Law_3:forall f g R I x:Set,Ring_Semi_Ideal f g R I/\x ∈ I->x ∈ R.
Proof.
intros.
destruct H.
apply (Ring_Left_Ideal_Law_1 f g R I).
split.
apply Ring_Semi_Ideal_Law_1.
apply H.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_4:forall f g R I x y:Set,Ring_Semi_Ideal f g R I/\x ∈ I/\y ∈ I->(Operation f x y) ∈ I.
Proof.
intros.
destruct H.
apply (Ring_Left_Ideal_Law_2 f g R I).
split.
apply Ring_Semi_Ideal_Law_1.
apply H.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_5:forall f g R I a x:Set,Ring_Semi_Ideal f g R I/\a ∈ R/\x ∈ I->(Operation g a x) ∈ I.
Proof.
intros.
destruct H.
apply (Ring_Left_Ideal_Law_3 f g R I).
split.
apply Ring_Semi_Ideal_Law_1.
apply H.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_6:forall f g R I a x:Set,Ring_Semi_Ideal f g R I/\a ∈ R/\x ∈ I->(Operation g x a) ∈ I.
Proof.
intros.
destruct H.
apply (Ring_Right_Ideal_Law_3 f g R I).
split.
apply Ring_Semi_Ideal_Law_2.
apply H.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_7:forall f g R I:Set,Ring_Semi_Ideal f g R I->~I=∅.
Proof.
intros.
apply (Ring_Left_Ideal_Law_4 f g R I).
apply Ring_Semi_Ideal_Law_1.
apply H.
Qed.

Theorem Ring_Semi_Ideal_Law_8:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->(Identify_Element f R) ∈ I.
Proof.
intros.
destruct H.
apply (Ring_Left_Ideal_Law_5 f g R I).
split.
apply H.
apply Ring_Semi_Ideal_Law_1.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_9:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Normal_Sub_Group f R (Restriction_Binary_Operation f I) I.
Proof.
intros.
destruct H.
apply (Ring_Left_Ideal_Law_6 f g R I).
split.
apply H.
apply Ring_Semi_Ideal_Law_1.
apply H0.
Qed.

Theorem Ring_Semi_Ideal_Law_10:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\(Identify_Element g R) ∈ I->R=I.
Proof.
intros.
destruct H.
destruct H0.
apply (Ring_Left_Ideal_Law_7 f g R I).
split.
apply H.
split.
apply Ring_Semi_Ideal_Law_1.
apply H0.
apply H1.
Qed.

Theorem Ring_Semi_Ideal_Law_11:forall f g R X:Set,Ring f g R/\(forall I:Set,I ∈ X->Ring_Semi_Ideal f g R I)/\~X=∅->Ring_Semi_Ideal f g R (Meet_Set X).
Proof.
intros.
destruct H.
destruct H0.
split.

intro.
intro.
assert (~X=∅).
apply H1.
apply Empty_Set_Law_1 in H3.
destruct H3.
apply (Ring_Semi_Ideal_Law_3 f g R x z).
split.
apply H0.
apply H3.
apply (Meet_Set_Law_2 X x z).
split.
apply H2.
apply H3.
split.

intro.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Semi_Ideal_Law_4 f g R A x y).
split.
apply H0.
apply H4.
split.
apply (Meet_Set_Law_2 X A x).
split.
apply H2.
apply H4.
apply (Meet_Set_Law_2 X A y).
split.
apply H3.
apply H4.
split.

intro.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Semi_Ideal_Law_6 f g R A a x).
split.
apply H0.
apply H4.
split.
apply H2.
apply (Meet_Set_Law_2 X A x).
split.
apply H3.
apply H4.
split.

intro.
intros.
destruct H2.
apply Meet_Set_Law_3.
split.
intro.
apply H1.
apply H4.
intros.
apply (Ring_Semi_Ideal_Law_5 f g R A a x).
split.
apply H0.
apply H4.
split.
apply H2.
apply (Meet_Set_Law_2 X A x).
split.
apply H3.
apply H4.

apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Meet_Set_Law_3.
split.
apply H1.
intros.
apply (Ring_Semi_Ideal_Law_8 f g R A).
split.
apply H.
apply H0.
apply H2.
Qed.

Theorem Ring_Semi_Ideal_Law_12:forall f g R I J:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\Ring_Semi_Ideal f g R J->Ring_Semi_Ideal f g R (I ∩ J).
Proof.
intros.
destruct H.
destruct H0.
apply Ring_Semi_Ideal_Law_11.
split.
apply H.
split.
intros.
apply Pair_Set_Law_1 in H2.
destruct H2.
rewrite -> H2.
apply H0.
rewrite -> H2.
apply H1.
apply Pair_Set_Law_4.
Qed.



Definition Ring_Quotient_Operation(f g R I:Set):=Prop_Set (fun a=>exists x1 x2:Set,a=Ordered_Set (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x2)) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x1 x2))/\x1 ∈ R/\x2 ∈ R/\(Operation g x1 x2) ∈ R).

Theorem Quotient_Ring_Law_1:forall f g R I a:Set,a ∈ (Ring_Quotient_Operation f g R I)<->(exists x1 x2:Set,a=Ordered_Set (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x2)) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x1 x2))/\x1 ∈ R/\x2 ∈ R/\(Operation g x1 x2) ∈ R).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set (Double_Direct_Product_Set (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Quotient_Set (Left_Equivalenc_Relation f R I) R)) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
rewrite -> H.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1)).
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x0 x1)).
split.
split.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0).
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H0.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists (Operation g x0 x1).
split.
apply H2.
split.
Qed.

Theorem Quotient_Ring_Law_2:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Binary_Operation (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.

intros.
apply Quotient_Ring_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
exists (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f R I) R x) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0)).
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x x0)).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x).
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H2.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H3.
split.
split.
apply Quotient_Set_Law_1.
exists (Operation g x x0).
split.
apply H4.
split.
apply H1.

intros.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x2 x3)).
split.
split.
apply Quotient_Ring_Law_1.
exists x2.
exists x3.
rewrite <- H4.
rewrite <- H5.
rewrite -> H1.
split.
split.
split.
apply H2.
split.
apply H3.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
apply Quotient_Set_Law_1.
exists (Operation g x2 x3).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.

intros.
destruct H6.
apply Quotient_Ring_Law_1 in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H8.
destruct H9.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H11.
rewrite <- H1 in H6.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H11 in H7.
apply (Equivalence_Class_Law_5 (Left_Equivalenc_Relation f R I) (Operation g x2 x3) (Operation g x4 x5) R).
split.
apply (Left_Equivalenc_Relation_Law_2 f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply H10.
apply Left_Equivalenc_Relation_Law_1.
exists (Operation g x2 x3).
exists (Operation g x4 x5).
split.
split.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply H10.
assert (Relation_Prop (Left_Equivalenc_Relation f R I) x2 x4).
apply (Equivalence_Class_Law_4 (Left_Equivalenc_Relation f R I) x2 x4 R).
split.
apply (Left_Equivalenc_Relation_Law_2 f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H2.
split.
apply H8.
rewrite <- H4.
apply H6.
apply Left_Equivalenc_Relation_Law_1 in H13.
destruct H13.
destruct H13.
destruct H13.
destruct H14.
destruct H15.
apply Ordered_Set_Law_2 in H13.
destruct H13.
rewrite <- H13 in H16.
rewrite <- H17 in H16.
clear H13.
clear H17.
clear H14.
clear H15.
assert (Relation_Prop (Left_Equivalenc_Relation f R I) x3 x5).
apply (Equivalence_Class_Law_4 (Left_Equivalenc_Relation f R I) x3 x5 R).
split.
apply (Left_Equivalenc_Relation_Law_2 f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H3.
split.
apply H9.
rewrite <- H5.
apply H12.
apply Left_Equivalenc_Relation_Law_1 in H13.
destruct H13.
destruct H13.
destruct H13.
destruct H14.
destruct H15.
apply Ordered_Set_Law_2 in H13.
destruct H13.
rewrite <- H13 in H17.
rewrite <- H18 in H17.
clear H13.
clear H18.
clear H14.
clear H15.
rewrite <- (Group_Law_6 f R x4).
rewrite <- (Group_Law_10 f R x2).
rewrite <- (Group_Law_3 f R x2 (Reverse_Element f R x2) x4).
rewrite <- (Group_Law_6 f R x5).
rewrite <- (Group_Law_10 f R x3).
rewrite <- (Group_Law_3 f R x3 (Reverse_Element f R x3) x5).
rewrite -> (Ring_Law_3 f g R (Operation f x2 (Operation f (Reverse_Element f R x2) x4)) x3 (Operation f (Reverse_Element f R x3) x5)).
rewrite -> (Ring_Law_4 f g R x2 (Operation f (Reverse_Element f R x2) x4) x3).
rewrite -> (Ring_Law_4 f g R x2 (Operation f (Reverse_Element f R x2) x4) (Operation f (Reverse_Element f R x3) x5)).
rewrite -> (Group_Law_3 f R (Reverse_Element f R (Operation g x2 x3)) (Operation f (Operation g x2 x3) (Operation g (Operation f (Reverse_Element f R x2) x4) x3)) (Operation f (Operation g x2 (Operation f (Reverse_Element f R x3) x5)) (Operation g (Operation f (Reverse_Element f R x2) x4) (Operation f (Reverse_Element f R x3) x5)))).
rewrite -> (Group_Law_3 f R (Reverse_Element f R (Operation g x2 x3)) (Operation g x2 x3) (Operation g (Operation f (Reverse_Element f R x2) x4) x3)).
rewrite -> (Group_Law_11 f R (Operation g x2 x3)).
apply (Ring_Semi_Ideal_Law_4 f g R I).
split.
apply H0.
split.
apply (Ring_Semi_Ideal_Law_4 f g R I).
split.
apply H0.
split.
apply  (Ring_Semi_Ideal_Law_8 f g R I).
split.
apply H.
apply H0.
apply (Ring_Semi_Ideal_Law_6 f g R I).
split.
apply H0.
split.
apply H3.
apply H16.
apply (Ring_Semi_Ideal_Law_4 f g R I).
split.
apply H0.
split.
apply (Ring_Semi_Ideal_Law_5 f g R I).
split.
apply H0.
split.
apply H2.
apply H17.
apply (Ring_Semi_Ideal_Law_5 f g R I).
split.
apply H0.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
apply H17.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply (Ring_Semi_Ideal_Law_6 f g R I).
split.
apply H0.
split.
apply H3.
apply H16.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
apply H3.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply (Ring_Semi_Ideal_Law_5 f g R I).
split.
apply H0.
split.
apply H2.
apply H17.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply (Ring_Semi_Ideal_Law_5 f g R I).
split.
apply H0.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
apply H17.
split.
apply H.
split.
apply H2.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H17.
split.
apply H.
split.
apply H2.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
apply H3.
split.
apply H.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H2.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H16.
split.
apply H3.
apply (Ring_Semi_Ideal_Law_3 f g R I).
split.
apply H0.
apply H17.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H3.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H3.
apply H9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H3.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H2.
split.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H2.
apply H8.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
apply H8.
Qed.

Theorem Quotient_Ring_Law_3:forall f g R I x1 x2:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\x1 ∈ R/\x2 ∈ R->Operation (Ring_Quotient_Operation f g R I) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x2)=Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x1 x2).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
symmetry.
apply (Map_Law_3 (Ring_Quotient_Operation f g R I) (Double_Direct_Product_Set (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Quotient_Set (Left_Equivalenc_Relation f R I) R)) (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1) (Equivalence_Class (Left_Equivalenc_Relation f R I) R x2)) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x1 x2))).
split.

apply Quotient_Ring_Law_2.
split.
apply H.
apply H0.
split.

apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x1).
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x2).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x2.
split.
apply H2.
split.
split.

apply Quotient_Set_Law_1.
exists (Operation g x1 x2).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
split.

apply Quotient_Ring_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H1.
split.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
Qed.

Theorem Quotient_Ring_Law_4:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Ring (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.

split.
apply (Quotient_Group_Law_3 f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_9 f g R I).
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
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I x0 x1).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I x1 x0).
rewrite -> (Abel_Group_Law_4 f R x0 x1).
split.
split.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H1.
apply H2.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H2.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
apply H2.
split.

split.
apply (Quotient_Ring_Law_2 f g R I).
split.
apply H.
apply H0.
split.
intro.
intros.
destruct H1.
destruct H2.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
rewrite -> H4.
rewrite -> H5.
rewrite -> H6.
rewrite -> (Quotient_Ring_Law_3 f g R I x0 x4).
rewrite -> (Quotient_Ring_Law_3 f g R I x (Operation g x0 x4)).
rewrite -> (Quotient_Ring_Law_3 f g R I x x0).
rewrite -> (Quotient_Ring_Law_3 f g R I (Operation g x x0) x4).
rewrite -> (Monoid_Law_2 g R x x0 x4).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply H2.
apply H3.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Identify_Element g R)).
split.
apply Quotient_Set_Law_1.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
intros.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
split.
rewrite -> H2.
rewrite -> (Quotient_Ring_Law_3 f g R I x0 (Identify_Element g R)).
rewrite -> (Monoid_Law_6 g R x0).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
rewrite -> H2.
rewrite -> (Quotient_Ring_Law_3 f g R I (Identify_Element g R) x0).
rewrite -> (Monoid_Law_7 g R x0).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply H0.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.

intros.
destruct H1.
destruct H2.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
rewrite -> H4.
rewrite -> H5.
rewrite -> H6.
rewrite -> (Quotient_Ring_Law_3 f g R I x x4).
rewrite -> (Quotient_Ring_Law_3 f g R I x x0).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I x0 x4).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I (Operation g x x0) (Operation g x x4)).
rewrite -> (Quotient_Ring_Law_3 f g R I x (Operation f x0 x4)).
rewrite -> (Ring_Law_3 f g R x x0 x4).
split.
split.
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H3.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H3.

intros.
destruct H1.
destruct H2.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
rewrite -> H4.
rewrite -> H5.
rewrite -> H6.
rewrite -> (Quotient_Ring_Law_3 f g R I x x4).
rewrite -> (Quotient_Ring_Law_3 f g R I x0 x4).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I x x0).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I (Operation g x x4) (Operation g x0 x4)).
rewrite -> (Quotient_Ring_Law_3 f g R I (Operation f x x0) x4).
rewrite -> (Ring_Law_4 f g R x x0 x4).
split.
split.
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H1.
apply H2.
apply H3.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H3.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H2.
apply H3.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
apply H2.
split.
apply H.
split.
apply H0.
split.
apply H2.
apply H3.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H3.
Qed.

Theorem Quotient_Ring_Law_5:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Equivalence_Class (Left_Equivalenc_Relation f R I) R (Identify_Element g R)=Identify_Element (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
apply (Monoid_Law_8 (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Identify_Element g R))).
split.
apply (Ring_Law_2 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
split.
apply Quotient_Set_Law_1.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
intros.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
rewrite -> H2.
rewrite -> (Quotient_Ring_Law_3 f g R I x (Identify_Element g R)).
rewrite -> (Monoid_Law_6 g R x).
split.
split.
apply (Ring_Law_2 f g R).
apply H.
apply H1.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
Qed.



(*環準同型*)
Definition Ring_homomorphism(h f1 g1 R1 f2 g2 R2:Set):=Ring f1 g1 R1/\Ring f2 g2 R2/\Map h R1 R2/\(forall x y:Set,(x ∈ R1/\y ∈ R1)->Operation f2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation f1 x y))/\(forall x y:Set,(x ∈ R1/\y ∈ R1)->Operation g2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation g1 x y))/\(Identify_Element g2 R2)=Culculateion_Map h (Identify_Element g1 R1).

Theorem Ring_homomorphism_Law_1:forall h f1 g1 R1 f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2->Group_homomorphism h f1 R1 f2 R2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
split.

apply (Ring_Law_1 f1 g1 R1).
apply H.
split.

apply (Ring_Law_1 f2 g2 R2).
apply H0.
split.

apply H1.

intros.
apply H2.
apply H5.
Qed.

Theorem Ring_homomorphism_Law_2:forall f g R:Set,Ring f g R->Ring_homomorphism (Identify_Map R) f g R f g R.
Proof.
intros.
split.

apply H.
split.

apply H.
split.

apply Identify_Map_Law_4.
split.

intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 R x).
rewrite <- (Identify_Map_Law_3 R y).
rewrite <- (Identify_Map_Law_3 R (Operation f x y)).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.
split.

intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 R x).
rewrite <- (Identify_Map_Law_3 R y).
rewrite <- (Identify_Map_Law_3 R (Operation g x y)).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.

rewrite <- (Identify_Map_Law_3 R (Identify_Element g R)).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
Qed.

Theorem Ring_homomorphism_Law_3:forall h1 h2 f1 g1 R1 f2 g2 R2 f3 g3 R3:Set,Ring_homomorphism h1 f1 g1 R1 f2 g2 R2/\Ring_homomorphism h2 f2 g2 R2 f3 g3 R3->Ring_homomorphism (Composite_Map h1 h2) f1 g1 R1 f3 g3 R3.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H0.
destruct H6.
destruct H7.
destruct H8.
destruct H9.
split.

apply H.
split.
apply H6.
split.
apply (Composite_Map_Law_1 h1 h2 R1 R2 R3).
split.
apply H2.
apply H7.
split.

intros.
destruct H11.
rewrite <- (Composite_Map_Law_2 h1 h2 x R1 R2 R3).
rewrite <- (Composite_Map_Law_2 h1 h2 y R1 R2 R3).
rewrite <- (Composite_Map_Law_2 h1 h2 (Operation f1 x y) R1 R2 R3).
rewrite -> (H8 (Culculateion_Map h1 x) (Culculateion_Map h1 y)).
rewrite -> (H3 x y).
split.
split.
apply H11.
apply H12.
split.
apply (Map_Law_2 h1 R1 R2 x).
split.
apply H2.
apply H11.
apply (Map_Law_2 h1 R1 R2 y).
split.
apply H2.
apply H12.
split.
apply H2.
split.
apply H7.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H.
split.
apply H11.
apply H12.
split.
apply H2.
split.
apply H7.
apply H12.
split.
apply H2.
split.
apply H7.
apply H11.
split.

intros.
destruct H11.
rewrite <- (Composite_Map_Law_2 h1 h2 x R1 R2 R3).
rewrite <- (Composite_Map_Law_2 h1 h2 y R1 R2 R3).
rewrite <- (Composite_Map_Law_2 h1 h2 (Operation g1 x y) R1 R2 R3).
rewrite -> (H9 (Culculateion_Map h1 x) (Culculateion_Map h1 y)).
rewrite -> (H4 x y).
split.
split.
apply H11.
apply H12.
split.
apply (Map_Law_2 h1 R1 R2 x).
split.
apply H2.
apply H11.
apply (Map_Law_2 h1 R1 R2 y).
split.
apply H2.
apply H12.
split.
apply H2.
split.
apply H7.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H.
split.
apply H11.
apply H12.
split.
apply H2.
split.
apply H7.
apply H12.
split.
apply H2.
split.
apply H7.
apply H11.

rewrite <- (Composite_Map_Law_2 h1 h2 (Identify_Element g1 R1) R1 R2 R3).
rewrite <- H5.
rewrite <- H10.
split.
split.
apply H2.
split.
apply H7.
apply Monoid_Law_4.
apply (Ring_Law_2 f1 g1 R1).
apply H.
Qed.

Theorem Ring_homomorphism_Law_4:forall h f1 g1 R1 f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2->Sub_Ring f2 g2 R2 (Restriction_Binary_Operation f2 (Map_Image h R1 R2)) (Restriction_Binary_Operation g2 (Map_Image h R1 R2)) (Map_Image h R1 R2).
Proof.
intros.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
apply (Sub_Ring_Law_3 f2 g2 R2 (Map_Image h R1 R2)).
split.

apply H1.
split.

intro.
intro.
apply Map_Image_Law_1 in H6.
destruct H6.
apply H6.
split.

intros.
destruct H6.
apply Map_Image_Law_1 in H6.
destruct H6.
destruct H8.
destruct H8.
apply Map_Image_Law_1 in H7.
destruct H7.
destruct H10.
destruct H10.
apply Map_Image_Law_1.
split.
rewrite -> H9.
rewrite -> H11.
rewrite <- (Group_homomorphism_Law_4 h f1 R1 f2 R2 x1).
rewrite -> (H3 x0 (Reverse_Element f1 R1 x1)).
apply (Map_Law_2 h R1 R2 (Operation f1 x0 (Reverse_Element f1 R1 x1))).
split.
apply H2.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
split.
apply H8.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
apply H10.
split.
apply H8.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
apply H10.
split.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
apply H10.
exists (Operation f1 x0 (Reverse_Element f1 R1 x1)).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
split.
apply H8.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
apply H10.
rewrite -> H9.
rewrite -> H11.
rewrite <- (Group_homomorphism_Law_4 h f1 R1 f2 R2).
apply H3.
split.
apply H8.
apply Group_Law_9.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
apply H10.
split.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
apply H10.
split.

intros.
destruct H6.
apply Map_Image_Law_1 in H6.
destruct H6.
destruct H8.
destruct H8.
apply Map_Image_Law_1 in H7.
destruct H7.
destruct H10.
destruct H10.
rewrite -> H9.
rewrite -> H11.
apply Map_Image_Law_1.
split.
rewrite -> H4.
apply (Map_Law_2 h R1 R2 (Operation g1 x0 x1)).
split.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H8.
apply H10.
split.
apply H8.
apply H10.
exists (Operation g1 x0 x1).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H8.
apply H10.
apply H4.
split.
apply H8.
apply H10.

apply Map_Image_Law_1.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f2 g2 R2).
apply H1.
exists (Identify_Element g1 R1).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
apply H5.
Qed.

Theorem Ring_homomorphism_Law_5:forall h f1 g1 R1 f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2->Ring (Restriction_Binary_Operation f2 (Map_Image h R1 R2)) (Restriction_Binary_Operation g2 (Map_Image h R1 R2)) (Map_Image h R1 R2).
Proof.
intros.
apply Ring_homomorphism_Law_4 in H.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Ring_homomorphism_Law_6:forall h f1 g1 R1 f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2->Ring_Semi_Ideal f1 g1 R1 (Map_Kernel h R1 f2 R2).
Proof.
intros.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
split.

intro.
intro.
apply Map_Kernel_Law_1 in H6.
destruct H6.
apply H6.
split.

intros.
destruct H6.
apply Map_Kernel_Law_1 in H6.
destruct H6.
apply Map_Kernel_Law_1 in H7.
destruct H7.
apply Map_Kernel_Law_1.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
split.
apply H6.
apply H7.
rewrite <- H3.
rewrite <- H8.
rewrite <- H9.
symmetry.
apply Group_Law_6.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H1.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H1.
split.
apply H6.
apply H7.
split.

intros.
destruct H6.
apply Map_Kernel_Law_1 in H7.
destruct H7.
apply Map_Kernel_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H7.
apply H6.
rewrite <- H4.
rewrite <- H8.
symmetry.
apply (Ring_Law_6 f2 g2 R2 (Culculateion_Map h a)).
split.
apply H1.
apply (Map_Law_2 h R1 R2 a).
split.
apply H2.
apply H6.
split.
apply H7.
apply H6.
split.

intros.
destruct H6.
apply Map_Kernel_Law_1 in H7.
destruct H7.
apply Map_Kernel_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H6.
apply H7.
rewrite <- H4.
rewrite <- H8.
symmetry.
apply (Ring_Law_5 f2 g2 R2 (Culculateion_Map h a)).
split.
apply H1.
apply (Map_Law_2 h R1 R2 a).
split.
apply H2.
apply H6.
split.
apply H6.
apply H7.

apply Empty_Set_Law_1.
exists (Identify_Element f1 R1).
apply Map_Kernel_Law_1.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H0.
symmetry.
apply Group_homomorphism_Law_3.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.

Theorem Ring_homomorphism_Law_7:forall h f1 g1 R1 I f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Left_Ideal f1 g1 R1 I/\Surjective_Map h R1 R2->Ring_Left_Ideal f2 g2 R2 (Sub_Set_Map_Image h R1 R2 I).
Proof. 
intros.
destruct H.
destruct H0.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
split.

intro.
intro.
apply Sub_Set_Map_Image_Law_1 in H8.
destruct H8.
apply H8.

split.
intros.
destruct H8.
apply Sub_Set_Map_Image_Law_1 in H8.
destruct H8.
destruct H10.
destruct H10.
apply Sub_Set_Map_Image_Law_1 in H9.
destruct H9.
destruct H12.
destruct H12.
apply Sub_Set_Map_Image_Law_1.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H3.
split.
apply H8.
apply H9.
exists (Operation f1 x0 x1).
split.
apply (Ring_Left_Ideal_Law_2 f1 g1 R1 I x0 x1).
split.
apply H0.
split.
apply H10.
apply H12.
rewrite -> H11.
rewrite -> H13.
apply H5.
split.
apply (Ring_Left_Ideal_Law_1 f1 g1 R1 I x0).
split.
apply H0.
apply H10.
apply (Ring_Left_Ideal_Law_1 f1 g1 R1 I x1).
split.
apply H0.
apply H12.
split.

intros.
destruct H8.
apply Sub_Set_Map_Image_Law_1 in H9.
destruct H9.
destruct H10.
destruct H10.
apply Sub_Set_Map_Image_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f2 g2 R2).
apply H3.
split.
apply H8.
apply H9.
rewrite -> H11.
destruct H1.
apply H12 in H8.
destruct H8.
destruct H8.
rewrite -> H13.
exists (Operation g1 x1 x0).
split.
apply (Ring_Left_Ideal_Law_3 f1 g1 R1 I x1 x0).
split.
apply H0.
split.
apply H8.
apply H10.
apply H6.
split.
apply H8.
apply (Ring_Left_Ideal_Law_1 f1 g1 R1 I x0).
split.
apply H0.
apply H10.

apply Empty_Set_Law_1.
exists (Identify_Element f2 R2).
apply Sub_Set_Map_Image_Law_1.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H3.
exists (Identify_Element f1 R1).
split.
apply (Ring_Left_Ideal_Law_5 f1 g1 R1 I).
split.
apply H2.
apply H0.
symmetry.
apply (Group_homomorphism_Law_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.

Theorem Ring_homomorphism_Law_8:forall h f1 g1 R1 I f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Right_Ideal f1 g1 R1 I/\Surjective_Map h R1 R2->Ring_Right_Ideal f2 g2 R2 (Sub_Set_Map_Image h R1 R2 I).
Proof. 
intros.
destruct H.
destruct H0.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
split.

intro.
intro.
apply Sub_Set_Map_Image_Law_1 in H8.
destruct H8.
apply H8.

split.
intros.
destruct H8.
apply Sub_Set_Map_Image_Law_1 in H8.
destruct H8.
destruct H10.
destruct H10.
apply Sub_Set_Map_Image_Law_1 in H9.
destruct H9.
destruct H12.
destruct H12.
apply Sub_Set_Map_Image_Law_1.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H3.
split.
apply H8.
apply H9.
exists (Operation f1 x0 x1).
split.
apply (Ring_Right_Ideal_Law_2 f1 g1 R1 I x0 x1).
split.
apply H0.
split.
apply H10.
apply H12.
rewrite -> H11.
rewrite -> H13.
apply H5.
split.
apply (Ring_Right_Ideal_Law_1 f1 g1 R1 I x0).
split.
apply H0.
apply H10.
apply (Ring_Right_Ideal_Law_1 f1 g1 R1 I x1).
split.
apply H0.
apply H12.
split.

intros.
destruct H8.
apply Sub_Set_Map_Image_Law_1 in H9.
destruct H9.
destruct H10.
destruct H10.
apply Sub_Set_Map_Image_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f2 g2 R2).
apply H3.
split.
apply H9.
apply H8.
rewrite -> H11.
destruct H1.
apply H12 in H8.
destruct H8.
destruct H8.
rewrite -> H13.
exists (Operation g1 x0 x1).
split.
apply (Ring_Right_Ideal_Law_3 f1 g1 R1 I x1 x0).
split.
apply H0.
split.
apply H8.
apply H10.
apply H6.
split.
apply (Ring_Right_Ideal_Law_1 f1 g1 R1 I x0).
split.
apply H0.
apply H10.
apply H8.

apply Empty_Set_Law_1.
exists (Identify_Element f2 R2).
apply Sub_Set_Map_Image_Law_1.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H3.
exists (Identify_Element f1 R1).
split.
apply (Ring_Right_Ideal_Law_5 f1 g1 R1 I).
split.
apply H2.
apply H0.
symmetry.
apply (Group_homomorphism_Law_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.

Theorem Ring_homomorphism_Law_9:forall h f1 g1 R1 I f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Semi_Ideal f1 g1 R1 I/\Surjective_Map h R1 R2->Ring_Semi_Ideal f2 g2 R2 (Sub_Set_Map_Image h R1 R2 I).
Proof.
intros.
destruct H.
destruct H0.

assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Left_Ideal f1 g1 R1 I/\Surjective_Map h R1 R2).
split.
apply H.
split.
apply Ring_Semi_Ideal_Law_1.
apply H0.
apply H1.
apply Ring_homomorphism_Law_7 in H2.
destruct H2.
destruct H3.
destruct H4.

assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Right_Ideal f1 g1 R1 I/\Surjective_Map h R1 R2).
split.
apply H.
split.
apply Ring_Semi_Ideal_Law_2.
apply H0.
apply H1.
apply Ring_homomorphism_Law_8 in H6.
destruct H6.
destruct H7.
destruct H8.
split.

apply H2.
split.
apply H3.
split.
apply H8.
split.
apply H4.
apply H5.
Qed.

Theorem Ring_homomorphism_Law_10:forall h f1 g1 R1 f2 g2 R2 I:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Left_Ideal f2 g2 R2 I->Ring_Left_Ideal f1 g1 R1 (Sub_Set_Map_Pull_Backe h R1 R2 I).
Proof. 
intros.
destruct H.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
split.

intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H7.
destruct H7.
apply H7.

split.
intros.
destruct H7.
apply Sub_Set_Map_Pull_Backe_Law_1 in H7.
destruct H7.
destruct H9.
destruct H9.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H11.
destruct H11.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H1.
split.
apply H7.
apply H8.
exists (Operation f2 x0 x1).
split.
apply (Ring_Left_Ideal_Law_2 f2 g2 R2 I x0 x1).
split.
apply H0.
split.
apply H9.
apply H11.
rewrite -> H10.
rewrite -> H12.
apply H4.
split.
apply H7.
apply H8.

split.
intros.
destruct H7.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H9.
destruct H9.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H1.
split.
apply H7.
apply H8.
exists (Operation g2 (Culculateion_Map h a) x0).
split.
apply (Ring_Left_Ideal_Law_3 f2 g2 R2 I (Culculateion_Map h a) x0).
split.
apply H0.
split.
apply (Map_Law_2 h R1 R2 a).
split.
apply H3.
apply H7.
apply H9.
rewrite -> H10.
apply H5.
split.
apply H7.
apply H8.

apply Empty_Set_Law_1.
exists (Identify_Element f1 R1).
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H1.
exists (Identify_Element f2 R2).
split.
apply (Ring_Left_Ideal_Law_5 f2 g2 R2 I).
split.
apply H2.
apply H0.
symmetry.
apply (Group_homomorphism_Law_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.

Theorem Ring_homomorphism_Law_11:forall h f1 g1 R1 f2 g2 R2 I:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Right_Ideal f2 g2 R2 I->Ring_Right_Ideal f1 g1 R1 (Sub_Set_Map_Pull_Backe h R1 R2 I).
Proof.
intros.
destruct H.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
split.

intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H7.
destruct H7.
apply H7.

split.
intros.
destruct H7.
apply Sub_Set_Map_Pull_Backe_Law_1 in H7.
destruct H7.
destruct H9.
destruct H9.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H11.
destruct H11.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H1.
split.
apply H7.
apply H8.
exists (Operation f2 x0 x1).
split.
apply (Ring_Right_Ideal_Law_2 f2 g2 R2 I x0 x1).
split.
apply H0.
split.
apply H9.
apply H11.
rewrite -> H10.
rewrite -> H12.
apply H4.
split.
apply H7.
apply H8.

split.
intros.
destruct H7.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H9.
destruct H9.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H1.
split.
apply H8.
apply H7.
exists (Operation g2 x0 (Culculateion_Map h a)).
split.
apply (Ring_Right_Ideal_Law_3 f2 g2 R2 I (Culculateion_Map h a) x0).
split.
apply H0.
split.
apply (Map_Law_2 h R1 R2 a).
split.
apply H3.
apply H7.
apply H9.
rewrite -> H10.
apply H5.
split.
apply H8.
apply H7.

apply Empty_Set_Law_1.
exists (Identify_Element f1 R1).
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H1.
exists (Identify_Element f2 R2).
split.
apply (Ring_Right_Ideal_Law_5 f2 g2 R2 I).
split.
apply H2.
apply H0.
symmetry.
apply (Group_homomorphism_Law_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.

Theorem Ring_homomorphism_Law_12:forall h f1 g1 R1 f2 g2 R2 I:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Semi_Ideal f2 g2 R2 I->Ring_Semi_Ideal f1 g1 R1 (Sub_Set_Map_Pull_Backe h R1 R2 I).
Proof.
intros.
destruct H.

assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Left_Ideal f2 g2 R2 I).
split.
apply H.
apply Ring_Semi_Ideal_Law_1.
apply H0.
apply Ring_homomorphism_Law_10 in H1.
destruct H1.
destruct H2.
destruct H3.

assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2/\Ring_Right_Ideal f2 g2 R2 I).
split.
apply H.
apply Ring_Semi_Ideal_Law_2.
apply H0.
apply Ring_homomorphism_Law_11 in H5.
destruct H5.
destruct H6.
destruct H7.
split.

apply H1.
split.
apply H2.
split.
apply H7.
split.
apply H3.
apply H4.
Qed.



(*環同型*)
Definition Ring_Isomorphism(h f1 g1 R1 f2 g2 R2:Set):=Ring f1 g1 R1/\Ring f2 g2 R2/\Bijective_Map h R1 R2/\(forall x y:Set,(x ∈ R1/\y ∈ R1)->Operation f2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation f1 x y))/\(forall x y:Set,(x ∈ R1/\y ∈ R1)->Operation g2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation g1 x y))/\(Identify_Element g2 R2)=Culculateion_Map h (Identify_Element g1 R1).

Theorem Ring_Isomorphism_Law_1:forall h f1 g1 R1 f2 g2 R2:Set,Ring_Isomorphism h f1 g1 R1 f2 g2 R2->Group_Isomorphism h f1 R1 f2 R2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
split.

apply Abel_Group_Law_1.
apply (Ring_Law_1 f1 g1 R1).
apply H.
split.

apply Abel_Group_Law_1.
apply (Ring_Law_1 f2 g2 R2).
apply H0.
split.

apply H1.
apply H2.
Qed.

Theorem Ring_Isomorphism_Law_2:forall h f1 g1 R1 f2 g2 R2:Set,Ring_Isomorphism h f1 g1 R1 f2 g2 R2->Ring_homomorphism h f1 g1 R1 f2 g2 R2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
split.
apply H.
split.
apply H0.
split.
destruct H1.
destruct H1.
apply H1.
split.
apply H2.
split.
apply H3.
apply H4.
Qed.

Theorem Ring_Isomorphism_Law_3:forall f g R:Set,Ring f g R->Ring_Isomorphism (Identify_Map R) f g R f g R.
Proof.
intros.
split.
apply H.
split.
apply H.
split.
apply Identify_Map_Law_2.
split.
intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 R x).
rewrite <- (Identify_Map_Law_3 R y).
rewrite <- (Identify_Map_Law_3 R (Operation f x y)).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.
split.
intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 R x).
rewrite <- (Identify_Map_Law_3 R y).
rewrite <- (Identify_Map_Law_3 R (Operation g x y)).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.
apply Identify_Map_Law_3.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
Qed.

Theorem Ring_Isomorphism_Law_4:forall h1 h2 f1 g1 R1 f2 g2 R2 f3 g3 R3:Set,Ring_Isomorphism h1 f1 g1 R1 f2 g2 R2/\Ring_Isomorphism h2 f2 g2 R2 f3 g3 R3->Ring_Isomorphism (Composite_Map h1 h2) f1 g1 R1 f3 g3 R3.
Proof.
intros.
destruct H.
assert (Ring_homomorphism (Composite_Map h1 h2) f1 g1 R1 f3 g3 R3).
apply (Ring_homomorphism_Law_3 h1 h2 f1 g1 R1 f2 g2 R2 f3 g3 R3).
split.
apply Ring_Isomorphism_Law_2.
apply H.
apply Ring_Isomorphism_Law_2.
apply H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
split.
apply H1.
split.
apply H2.
split.
apply (Composite_Map_Law_5 h1 h2 R1 R2 R3).
split.
destruct H.
destruct H7.
destruct H8.
apply H8.
destruct H0.
destruct H7.
destruct H8.
apply H8.
split.
apply H4.
split.
apply H5.
apply H6.
Qed.

Theorem Ring_Isomorphism_Law_5:forall h f1 g1 R1 f2 g2 R2:Set,Ring_Isomorphism h f1 g1 R1 f2 g2 R2->Ring_Isomorphism (Inverse_Map h R1 R2) f2 g2 R2 f1 g1 R1.
Proof.
intros.
assert (Ring_Isomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert (Group_Isomorphism (Inverse_Map h R1 R2) f2 R2 f1 R1).
apply (Group_Isomorphism_Law_4 h f1 R1 f2 R2).
apply (Ring_Isomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
destruct H6.
destruct H7.
destruct H8.
split.
apply H1.
split.
apply H0.
split.
apply H8.
split.
apply H9.
split.
intros.
destruct H10.
assert (Injective_Map h R1 R2).
destruct H2.
apply H12.
destruct H12.
apply H13.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply (Map_Law_2 (Inverse_Map h R1 R2) R2 R1 x).
split.
apply Inverse_Map_Law_2.
apply H2.
apply H10.
apply (Map_Law_2 (Inverse_Map h R1 R2) R2 R1 y).
split.
apply Inverse_Map_Law_2.
apply H2.
apply H11.
split.
apply (Map_Law_2 (Inverse_Map h R1 R2) R2 R1 (Operation g2 x y)).
split.
apply Inverse_Map_Law_2.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f2 g2 R2).
apply H1.
split.
apply H10.
apply H11.
rewrite <- H4.
rewrite -> (Composite_Map_Law_2 (Inverse_Map h R1 R2) h x R2 R1 R2).
rewrite -> (Composite_Map_Law_2 (Inverse_Map h R1 R2) h y R2 R1 R2).
rewrite -> (Composite_Map_Law_2 (Inverse_Map h R1 R2) h (Operation g2 x y) R2 R1 R2).
rewrite <- (Inverse_Map_Law_5 h R1 R2).
rewrite <- (Identify_Map_Law_3 R2 x).
rewrite <- (Identify_Map_Law_3 R2 y).
rewrite <- (Identify_Map_Law_3 R2 (Operation g2 x y)).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f2 g2 R2).
apply H.
split.
apply H10.
apply H11.
apply H11.
apply H10.
apply H2.
split.
apply Inverse_Map_Law_2.
apply H2.
split.
destruct H2.
destruct H2.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f2 g2 R2).
apply H1.
split.
apply H10.
apply H11.
split.
apply H8.
split.
apply H12.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H2.
split.
apply H12.
apply H10.
split.
apply (Map_Law_2 (Inverse_Map h R1 R2) R2 R1 x).
split.
apply Inverse_Map_Law_2.
apply H2.
apply H10.
apply (Map_Law_2 (Inverse_Map h R1 R2) R2 R1 y).
split.
apply Inverse_Map_Law_2.
apply H2.
apply H11.
rewrite -> H5.
rewrite -> (Composite_Map_Law_2 h (Inverse_Map h R1 R2) (Identify_Element g1 R1) R1 R2 R1).
rewrite <- (Inverse_Map_Law_4 h R1 R2).
apply (Identify_Map_Law_3 R1 (Identify_Element g1 R1)).
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
apply H2.
split.
destruct H2.
destruct H2.
apply H2.
split.
apply Inverse_Map_Law_2.
apply H2.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
Qed.



(*環準同型定理*)
Theorem Fundamental_Homomorphism_Theorem_2:forall h f1 g1 R1 f2 g2 R2:Set,Ring_homomorphism h f1 g1 R1 f2 g2 R2->Ring_Isomorphism (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Group_Quotient_Operation f1 R1 (Map_Kernel h R1 f2 R2)) (Ring_Quotient_Operation f1 g1 R1 (Map_Kernel h R1 f2 R2)) (Quotient_Set (Left_Equivalenc_Relation f1 R1 (Map_Kernel h R1 f2 R2)) R1) (Restriction_Binary_Operation f2 (Map_Image h R1 R2)) (Restriction_Binary_Operation g2 (Map_Image h R1 R2)) (Map_Image h R1 R2).
Proof.
intros.
assert (Ring_homomorphism h f1 g1 R1 f2 g2 R2).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert (Group_Isomorphism (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Group_Quotient_Operation f1 R1 (Map_Kernel h R1 f2 R2)) (Left_Quotient_Group f1 R1 (Map_Kernel h R1 f2 R2)) (Restriction_Binary_Operation f2 (Map_Image h R1 R2)) (Map_Image h R1 R2)).
apply Fundamental_Homomorphism_Theorem_1.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
destruct H6.
destruct H7.
destruct H8.
split.

apply (Quotient_Ring_Law_4 f1 g1 R1 (Map_Kernel h R1 f2 R2)).
split.
apply H0.
apply (Ring_homomorphism_Law_6 h f1 g1 R1 f2 g2 R2).
apply H.
split.

apply (Ring_homomorphism_Law_5 h f1 g1 R1 f2 g2 R2).
apply H.
split.

apply H8.
split.

apply H9.
split.

intros.
destruct H10.
apply Quotient_Set_Law_1 in H10.
destruct H10.
destruct H10.
apply Quotient_Set_Law_1 in H11.
destruct H11.
destruct H11.
rewrite -> H12.
rewrite -> H13.
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Left_Quotient_Group f1 R1 (Map_Kernel h R1 f2 R2)) (Map_Image h R1 R2) (Equivalence_Class (Left_Equivalenc_Relation f1 R1 (Map_Kernel h R1 f2 R2)) R1 x0) (Culculateion_Map h x0)).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Left_Quotient_Group f1 R1 (Map_Kernel h R1 f2 R2)) (Map_Image h R1 R2) (Equivalence_Class (Left_Equivalenc_Relation f1 R1 (Map_Kernel h R1 f2 R2)) R1 x1) (Culculateion_Map h x1)).
assert (Operation (Restriction_Binary_Operation g2 (Map_Image h R1 R2)) (Culculateion_Map h x0) (Culculateion_Map h x1)=Operation g2 (Culculateion_Map h x0) (Culculateion_Map h x1)).
unfold Operation.
unfold Restriction_Binary_Operation.
apply (Restriction_Map_Law_3 g2 (Double_Direct_Product_Set R2 R2) (Double_Direct_Product_Set (Map_Image h R1 R2) (Map_Image h R1 R2)) R2 (Ordered_Set (Culculateion_Map h x0) (Culculateion_Map h x1))).
split.
destruct H1.
destruct H14.
destruct H14.
apply H14.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H14.
apply Double_Direct_Product_Set_Law_1.
destruct H14.
destruct H14.
destruct H14.
destruct H15.
exists x2.
exists x3.
split.
apply H14.
split.
apply Map_Image_Law_1 in H15.
destruct H15.
apply H15.
apply Map_Image_Law_1 in H16.
destruct H16.
apply H16.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map h x0).
exists (Culculateion_Map h x1).
split.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 x0).
split.
apply H2.
apply H10.
exists x0.
split.
apply H10.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 x1).
split.
apply H2.
apply H11.
exists x1.
split.
apply H11.
split.
rewrite -> H14.
clear H14.
rewrite -> (Quotient_Ring_Law_3 f1 g1 R1 (Map_Kernel h R1 f2 R2) x0 x1).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Left_Quotient_Group f1 R1 (Map_Kernel h R1 f2 R2)) (Map_Image h R1 R2) (Equivalence_Class (Left_Equivalenc_Relation f1 R1 (Map_Kernel h R1 f2 R2)) R1 (Operation g1 x0 x1)) (Culculateion_Map h (Operation g1 x0 x1))).
apply H4.
split.
apply H10.
apply H11.
split.
apply (Fundamental_Homomorphism_Lemma_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
split.
apply Quotient_Set_Law_1.
exists (Operation g1 x0 x1).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H10.
apply H11.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 (Operation g1 x0 x1)).
split.
apply H2.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H10.
apply H11.
exists (Operation g1 x0 x1).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H10.
apply H11.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
exists (Operation g1 x0 x1).
split.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H10.
apply H11.
split.
apply H0.
split.
apply (Ring_homomorphism_Law_6 h f1 g1 R1 f2 g2 R2).
apply H.
split.
apply H10.
apply H11.
split.
apply (Fundamental_Homomorphism_Lemma_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H11.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 x1).
split.
apply H2.
apply H11.
exists x1.
split.
apply H11.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
exists x1.
split.
split.
apply H11.
split.
apply (Fundamental_Homomorphism_Lemma_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H10.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 x0).
split.
apply H2.
apply H10.
exists x0.
split.
apply H10.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
exists x0.
split.
split.
apply H10.

rewrite <- (Quotient_Ring_Law_5 f1 g1 R1 (Map_Kernel h R1 f2 R2)).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 R1 f2 R2) (Left_Quotient_Group f1 R1 (Map_Kernel h R1 f2 R2)) (Map_Image h R1 R2) (Equivalence_Class (Left_Equivalenc_Relation f1 R1 (Map_Kernel h R1 f2 R2)) R1 (Identify_Element g1 R1)) (Culculateion_Map h (Identify_Element g1 R1))).
rewrite <- H5.
assert (Sub_Ring f2 g2 R2 (Restriction_Binary_Operation f2 (Map_Image h R1 R2)) (Restriction_Binary_Operation g2 (Map_Image h R1 R2)) (Map_Image h R1 R2)).
apply (Ring_homomorphism_Law_4 h f1 g1 R1 f2 g2 R2).
apply H.
destruct H10.
destruct H11.
destruct H12.
destruct H13.
destruct H14.
symmetry.
apply H15.
split.
apply (Fundamental_Homomorphism_Lemma_3 h f1 R1 f2 R2).
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
split.
apply Quotient_Set_Law_1.
exists (Identify_Element g1 R1).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h R1 R2 (Identify_Element g1 R1)).
split.
apply H2.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
exists (Identify_Element g1 R1).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply Fundamental_Homomorphism_Lemma_2.
split. 
apply (Ring_homomorphism_Law_1 h f1 g1 R1 f2 g2 R2).
apply H.
exists (Identify_Element g1 R1).
split.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f1 g1 R1).
apply H0.
split.
apply H0.
apply (Ring_homomorphism_Law_6 h f1 g1 R1 f2 g2 R2).
apply H.
Qed.



Definition Quotient_Ring_Map(f R I:Set):=Prop_Set (fun a=>exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x)).

Theorem Quotient_Ring_Map_Law_1:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\a ∈ (Quotient_Ring_Map f R I)->exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x).
Proof.
intros.
destruct H.
destruct H0.
apply (Prop_Set_Law_1 (fun a=>exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
exists (Double_Direct_Product_Set R (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
intros.
destruct H2.
destruct H2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0).
split.
symmetry.
apply H3.
split.
apply H2.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H2.
split.
apply H1.
Qed.

Theorem Quotient_Ring_Map_Law_2:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\(exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))->a ∈ (Quotient_Ring_Map f R I).
Proof.
intros.
destruct H.
destruct H0.
apply (Prop_Set_Law_1 (fun a=>exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
exists (Double_Direct_Product_Set R (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
intros.
destruct H2.
destruct H2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0).
split.
symmetry.
apply H3.
split.
apply H2.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H2.
split.
apply H1.
Qed.

Theorem Quotient_Ring_Map_Law_3:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Map (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.

intros.
assert (exists x:Set,x ∈ R/\a=Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x)).
apply (Quotient_Ring_Map_Law_1 f g R I a).
split.
apply H.
split.
apply H0.
apply H1.
destruct H2.
destruct H2.
exists x.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x).
split.
apply H2.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H2.
split.
apply H3.

intros.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R x).
split.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
split.
apply H.
split.
apply H0.
exists x.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H1.
split.
intros.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
assert (exists x0:Set,x0 ∈ R/\Ordered_Set x x'=Ordered_Set x0 (Equivalence_Class (Left_Equivalenc_Relation f R I) R x0)).
apply (Quotient_Ring_Map_Law_1 f g R I (Ordered_Set x x')).
split.
apply H.
split.
apply H0.
apply H2.
destruct H5.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H7.
rewrite -> H6.
split.
Qed.

Theorem Quotient_Ring_Map_Law_4:forall f g R I x:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\x ∈ R->Equivalence_Class (Left_Equivalenc_Relation f R I) R x=Culculateion_Map (Quotient_Ring_Map f R I) x.
Proof.
intros.
destruct H.
destruct H0.
apply (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x)).
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H1.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
split.
apply H.
split.
apply H0.
exists x.
split.
apply H1.
split.
Qed.

Theorem Quotient_Ring_Map_Law_5:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Ring_homomorphism (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.

apply H.
split.

apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
split.

apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.

intros.
destruct H1.
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x)).
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) y (Equivalence_Class (Left_Equivalenc_Relation f R I) R y)).
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Operation f x y) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation f x y))).
rewrite -> (Quotient_Group_Law_4 f R (Restriction_Binary_Operation f I) I x y).
split.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
apply H2.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H1.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Operation f x y).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H1.
apply H2.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set (Operation f x y) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation f x y)))).
split.
apply H.
split.
apply H0.
exists (Operation f x y).
split.
apply Group_Law_2.
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply H.
split.
apply H1.
apply H2.
split.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply H2.
split.
apply Quotient_Set_Law_1.
exists y.
split.
apply H2.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set y (Equivalence_Class (Left_Equivalenc_Relation f R I) R y))).
split.
apply H.
split.
apply H0.
exists y.
split.
apply H2.
split.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H1.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
split.
apply H.
split.
apply H0.
exists x.
split.
apply H1.
split.
split.

intros.
destruct H1.
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x)).
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) y (Equivalence_Class (Left_Equivalenc_Relation f R I) R y)).
rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Operation g x y) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x y))).
apply (Quotient_Ring_Law_3 f g R I x y).
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Operation g x y).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set (Operation g x y) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Operation g x y)))).
split.
apply H.
split.
apply H0.
exists (Operation g x y).
split.
apply Monoid_Law_1.
split.
apply (Ring_Law_2 f g R).
apply H.
split.
apply H1.
apply H2.
split.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply H2.
split.
apply Quotient_Set_Law_1.
exists y.
split.
apply H2.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set y (Equivalence_Class (Left_Equivalenc_Relation f R I) R y))).
split.
apply H.
split.
apply H0.
exists y.
split.
apply H2.
split.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H1.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set x (Equivalence_Class (Left_Equivalenc_Relation f R I) R x))).
split.
apply H.
split.
apply H0.
exists x.
split.
apply H1.
split.

rewrite <- (Map_Law_3 (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Identify_Element g R) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Identify_Element g R))).
symmetry.
apply Quotient_Ring_Law_5.
split.
apply H.
apply H0.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply Quotient_Set_Law_1.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
apply (Quotient_Ring_Map_Law_2 f g R I (Ordered_Set (Identify_Element g R) (Equivalence_Class (Left_Equivalenc_Relation f R I) R (Identify_Element g R)))).
split.
apply H.
split.
apply H0.
exists (Identify_Element g R).
split.
apply Monoid_Law_5.
apply (Ring_Law_2 f g R).
apply H.
split.
Qed.

Theorem Quotient_Ring_Map_Law_6:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Surjective_Map (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R).
Proof.
intros.
destruct H.
split.
apply (Quotient_Ring_Map_Law_3 f g R I).
split.
apply H.
apply H0.

intros.
apply Quotient_Set_Law_1 in H1.
destruct H1.
exists x.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I x).
apply H1.
destruct H1.
split.
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Quotient_Ring_Map_Law_7:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\Ring_Semi_Ideal (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a->a=Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
Proof.
intros.
destruct H.
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.

intro.
assert (z ∈ Quotient_Set (Left_Equivalenc_Relation f R I) R).
apply (Ring_Semi_Ideal_Law_3 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a z).
split.
apply H1.
apply H2.
apply Sub_Set_Map_Image_Law_1.
split.
apply H3.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
exists x.
split.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H3.
exists z.
split.
apply H2.
rewrite -> H4.
apply (Quotient_Ring_Map_Law_4 f g R I x).
split.
apply H.
split.
apply H0.
apply H3.
rewrite -> H4.
apply (Quotient_Ring_Map_Law_4 f g R I x).
split.
apply H.
split.
apply H0.
apply H3.

intro.
apply Sub_Set_Map_Image_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Sub_Set_Map_Pull_Backe_Law_1 in H3.
destruct H3.
destruct H6.
destruct H6.
rewrite -> H4.
rewrite <- H7.
apply H6.
Qed.

Theorem Quotient_Ring_Map_Law_8:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\Ring_Semi_Ideal f g R a/\I ⊂ a->a=Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R a z).
split.
apply H1.
apply H3.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
apply Sub_Set_Map_Image_Law_1.
split.
apply Quotient_Set_Law_1.
exists z.
split.
apply (Ring_Semi_Ideal_Law_3 f g R a z).
split.
apply H1.
apply H3.
symmetry.
apply (Quotient_Ring_Map_Law_4 f g R I z).
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R a z).
split.
apply H1.
apply H3.
exists z.
split.
apply H3.
split.
split.

intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H3.
destruct H3.
destruct H4.
destruct H4.
apply Sub_Set_Map_Image_Law_1 in H4.
destruct H4.
destruct H6.
destruct H6.
apply Quotient_Set_Law_1 in H4.
destruct H4.
destruct H4.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I x0) in H7.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z) in H5.
rewrite <- (Group_Law_6 f R z).
rewrite <- (Group_Law_10 f R x0).
rewrite <- (Group_Law_3 f R x0 (Reverse_Element f R x0) z).
assert (Relation_Prop (Left_Equivalenc_Relation f R I) x0 z).
apply (Equivalence_Class_Law_4 (Left_Equivalenc_Relation f R I) x0 z R).
split.
apply (Left_Equivalenc_Relation_Law_2 f R (Restriction_Binary_Operation f I) I).
assert (Normal_Sub_Group f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
destruct H9.
apply H9.
split.
apply (Ring_Semi_Ideal_Law_3 f g R a x0).
split.
apply H1.
apply H6.
split.
apply H3.
rewrite <- H7.
apply H5.
apply Left_Equivalenc_Relation_Law_1 in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
destruct H11.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite <- H9 in H12.
rewrite <- H13 in H12.
apply (Ring_Semi_Ideal_Law_4 f g R a x0 (Operation f (Reverse_Element f R x0) z)).
split.
apply H1.
split.
apply H6.
apply H2.
apply H12.
split.
apply (Abel_Group_Law_1 f R).
apply (Ring_Law_1 f g R).
apply H.
split.
apply (Ring_Semi_Ideal_Law_3 f g R a x0).
split.
apply H1.
apply H6.
split.
apply (Group_Law_9 f R x0).
split.
apply H.
apply (Ring_Semi_Ideal_Law_3 f g R a x0).
split.
apply H1.
apply H6.
apply H3.
split.
apply (Abel_Group_Law_1 f R).
apply (Ring_Law_1 f g R).
apply H.
apply (Ring_Semi_Ideal_Law_3 f g R a x0).
split.
apply H1.
apply H6.
split.
apply (Abel_Group_Law_1 f R).
apply (Ring_Law_1 f g R).
apply H.
apply H3.
split.
apply H.
split.
apply H0.
apply H3.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R a x0).
split.
apply H1.
apply H6.
Qed.



Definition Semi_Ideal_Set(f g R:Set):=Prop_Set (fun I=>Ring_Semi_Ideal f g R I).

Theorem Semi_Ideal_Set_Law_1:forall f g R a:Set,a ∈ Semi_Ideal_Set f g R<->Ring_Semi_Ideal f g R a.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set R).
intros.
destruct H.
apply Power_Set_Law_1.
apply H.
Qed.



Definition Semi_Ideal_Set_1(f g R I:Set):=Prop_Set (fun J=>Ring_Semi_Ideal f g R J/\I ⊂ J).

Theorem Semi_Ideal_Set_1_Law_1:forall f g R I a:Set,a ∈ Semi_Ideal_Set_1 f g R I<->Ring_Semi_Ideal f g R a/\I ⊂ a.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set R).
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
apply H.
Qed.



Definition Qutioent_Ideal_Map(f g R I:Set):=Prop_Set (fun a=>exists J:Set,Ring_Semi_Ideal f g R J/\I ⊂J/\a=Ordered_Set J (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) J)).

Theorem Qutioent_Ideal_Map_Law_1:forall f g R I a:Set,a ∈ Qutioent_Ideal_Map f g R I<->exists J:Set,Ring_Semi_Ideal f g R J/\I ⊂J/\a=Ordered_Set J (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) J).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set (Power_Set R) (Power_Set (Power_Set R))).
intros.
destruct H.
destruct H.
destruct H0.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x0).
split.
symmetry.
apply H1.
split.
apply Power_Set_Law_1.
destruct H.
apply H.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
apply Sub_Set_Map_Image_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
rewrite -> H5.
intro.
intro.
apply Equivalence_Class_Law_1 in H6.
destruct H6.
apply H6.
Qed.

Theorem Qutioent_Ideal_Map_Law_2:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Map (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
Proof.
intros.
destruct H.
split.

intros.
apply Qutioent_Ideal_Map_Law_1 in H1.
destruct H1.
destruct H1.
destruct H2.
exists x.
exists (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x).
split.
apply Semi_Ideal_Set_1_Law_1.
split.
apply H1.
apply H2.
split.
apply Semi_Ideal_Set_Law_1.
apply (Ring_homomorphism_Law_9 (Quotient_Ring_Map f R I) f g R x (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
apply (Quotient_Ring_Map_Law_6 f g R I).
split.
apply H.
apply H0.
apply H3.

intros.
apply Semi_Ideal_Set_1_Law_1 in H1.
destruct H1.
exists (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) x).
split.
split.
apply Qutioent_Ideal_Map_Law_1.
exists x.
split.
apply H1.
split.
apply H2.
split.
apply Semi_Ideal_Set_Law_1.
apply (Ring_homomorphism_Law_9 (Quotient_Ring_Map f R I) f g R x (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
split.
apply H1.
apply (Quotient_Ring_Map_Law_6 f g R I).
split.
apply H.
apply H0.
intros.
destruct H3.
apply Qutioent_Ideal_Map_Law_1 in H3.
destruct H3.
destruct H3.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H6.
symmetry.
apply H7.
Qed.

Theorem Qutioent_Ideal_Map_Law_3:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\a ∈ (Semi_Ideal_Set_1 f g R I)->Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a=Culculateion_Map (Qutioent_Ideal_Map f g R I) a.
Proof.
intros.
destruct H.
destruct H0.
apply (Map_Law_3 (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)) a (Sub_Set_Map_Image (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a)).
split.
apply Qutioent_Ideal_Map_Law_2.
split.
apply H.
apply H0.
split.
apply H1.
split.
apply Semi_Ideal_Set_Law_1.
apply (Ring_homomorphism_Law_9 (Quotient_Ring_Map f R I) f g R a (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
split.
apply Semi_Ideal_Set_1_Law_1 in H1.
destruct H1.
apply H1.
apply (Quotient_Ring_Map_Law_6 f g R I).
split.
apply H.
apply H0.
apply Qutioent_Ideal_Map_Law_1.
exists a.
apply Semi_Ideal_Set_1_Law_1 in H1.
destruct H1.
split.
apply H1.
split.
apply H2.
split.
Qed.

Theorem Qutioent_Ideal_Map_Law_4:forall f g R I:Set,Ring f g R/\Ring_Semi_Ideal f g R I->Bijective_Map (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
Proof.
intros.
destruct H.
split.

split.
apply Qutioent_Ideal_Map_Law_2.
split.
apply H.
apply H0.
intros.
apply Semi_Ideal_Set_Law_1 in H1.
exists (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_1 f g R I).
apply H0.
apply H2.
exists (Equivalence_Class (Left_Equivalenc_Relation f R I) R z).
split.
apply (Quotient_Group_Law_7 (Group_Quotient_Operation f R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Restriction_Binary_Operation (Group_Quotient_Operation f R I) y) y (Equivalence_Class (Left_Equivalenc_Relation f R I) R z)).
split.
apply (Ring_Semi_Ideal_Law_9 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply Quotient_Set_Law_1.
exists z.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I).
apply (Quotient_Group_Law_5 (Group_Quotient_Operation f R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) (Restriction_Binary_Operation (Group_Quotient_Operation f R I) y) y).
apply (Ring_Semi_Ideal_Law_9 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
apply (Quotient_Ring_Map_Law_4 f g R I z).
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) y)). 
apply (Quotient_Ring_Map_Law_7 f g R I y).
split.
apply H.
split.
apply H0.
apply H1.
split.
apply H.
split.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z).
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I).
apply (Ring_Semi_Ideal_Law_8 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) y).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.

split.
apply Qutioent_Ideal_Map_Law_2.
split.
apply H.
apply H0.
intros.
destruct H1.
destruct H2.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I x1) in H3.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I x2) in H3.
apply Semi_Ideal_Set_1_Law_1 in H1.
destruct H1.
apply Semi_Ideal_Set_1_Law_1 in H2.
destruct H2.
rewrite -> (Quotient_Ring_Map_Law_8 f g R I x1).
rewrite -> (Quotient_Ring_Map_Law_8 f g R I x2).
rewrite -> H3.
split.
split.
apply H.
split.
apply H0.
split.
apply H2.
apply H5.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H4.
split.
apply H.
split.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Qutioent_Ideal_Map_Law_5:forall f g R I a:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\a ∈ (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R))->Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a=Culculateion_Map (Inverse_Map (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R))) a.
Proof.
intros.
destruct H.
destruct H0.
apply Semi_Ideal_Set_Law_1 in H1.
rewrite -> (Quotient_Ring_Map_Law_7 f g R I a).
rewrite -> (Qutioent_Ideal_Map_Law_3 f g R I (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a)).
rewrite -> (Composite_Map_Law_2 (Qutioent_Ideal_Map f g R I) (Inverse_Map (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R))) (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)) (Semi_Ideal_Set_1 f g R I)).
rewrite <- (Inverse_Map_Law_4 (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R))).
rewrite <- (Identify_Map_Law_3 (Semi_Ideal_Set_1 f g R I) (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a)).
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I (Sub_Set_Map_Pull_Backe (Quotient_Ring_Map f R I) R (Quotient_Set (Left_Equivalenc_Relation f R I) R) a)).
rewrite <- (Quotient_Ring_Map_Law_7 f g R I a).
split.
split.
apply H.
split.
apply H0.
apply H1.
split.
apply H.
split.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z).
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I z).
apply (Ring_Semi_Ideal_Law_8 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
split.
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z).
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I z).
apply (Ring_Semi_Ideal_Law_8 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
split.
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.
apply (Qutioent_Ideal_Map_Law_4 f g R I).
split.
apply H.
apply H0.
split.
apply (Qutioent_Ideal_Map_Law_2 f g R I).
split.
apply H.
apply H0.
split.
apply (Inverse_Map_Law_2 (Qutioent_Ideal_Map f g R I) (Semi_Ideal_Set_1 f g R I) (Semi_Ideal_Set (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R))).
apply (Qutioent_Ideal_Map_Law_4 f g R I).
split.
apply H.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z).
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I z).
apply (Ring_Semi_Ideal_Law_8 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
split.
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.
split.
apply H.
split.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply (Ring_homomorphism_Law_12 (Quotient_Ring_Map f R I) f g R (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R I).
split.
apply H.
apply H0.
apply H1.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
exists (Culculateion_Map (Quotient_Ring_Map f R I) z).
split.
rewrite <- (Quotient_Ring_Map_Law_4 f g R I z).
rewrite -> (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f I) I z).
apply (Ring_Semi_Ideal_Law_8 (Group_Quotient_Operation f R I) (Ring_Quotient_Operation f g R I) (Quotient_Set (Left_Equivalenc_Relation f R I) R) a).
split.
apply (Quotient_Ring_Law_4 f g R I).
split.
apply H.
apply H0.
apply H1.
split.
apply (Ring_Semi_Ideal_Law_9 f g R I).
split.
apply H.
apply H0.
apply H2.
split.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H0.
apply H2.
split.
split.
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Qutioent_Ideal_Map_Law_6:forall f g R I a1 a2:Set,Ring f g R/\Ring_Semi_Ideal f g R I/\Ring_Semi_Ideal f g R a1/\Ring_Semi_Ideal f g R a2/\I ⊂ a1/\I ⊂ a2/\a1 ⊂ a2->(Culculateion_Map (Qutioent_Ideal_Map f g R I) a1) ⊂ (Culculateion_Map (Qutioent_Ideal_Map f g R I) a2).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
intro.
intro.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I a1) in H6.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R I a2).
apply Sub_Set_Map_Image_Law_1 in H6.
destruct H6.
destruct H7.
destruct H7.
apply Sub_Set_Map_Image_Law_1.
split.
apply H6.
exists x.
split.
apply H5.
apply H7.
apply H8.
split.
apply H.
split.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply H2.
apply H4.
split.
apply H.
split.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply H1.
apply H3.
Qed.