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



(*体*)
Theorem Field_Law_4:forall f g F I:Set,Field f g F/\Ring_Semi_Ideal f g F I/\~Zero_Ring f g F->(forall x:Set,x ∈ I->x=Identify_Element f F)\/(F=I).
Proof.
intros.
destruct H.
destruct H0.

destruct (Law_of_Excluded_Middle (exists x:Set,x ∈ I/\~x=Identify_Element f F)).
destruct H2.
destruct H2.
right.
apply (Ring_Semi_Ideal_Law_10 f g F I).
split.
apply H.
split.
apply H0.
assert (Field f g F/\x ∈ F).
split.
apply H.
apply (Ring_Semi_Ideal_Law_3 f g F I x).
split.
apply H0.
apply H2.
apply (Field_Law_2 f g F x) in H4.
destruct H4.
destruct H3.
apply H4.
apply Ring_invertible_Set_Law_1 in H4.
rewrite <- (Ring_invertible_Set_Law_4 f g F x).
apply (Ring_Semi_Ideal_Law_6 f g F I (Reverse_Element g F x) x).
split.
apply H0.
split.
apply (Ring_invertible_Set_Law_3 f g F x).
split.
apply H.
apply H4.
apply H2.
split.
apply H.
apply H4.

left.
intros.
assert (Field f g F/\x ∈ F).
split.
apply H.
apply (Ring_Semi_Ideal_Law_3 f g F I x).
split.
apply H0.
apply H3.
apply (Field_Law_2 f g F x) in H4.
destruct H4.
apply H4.
destruct H2.
exists x.
split.
apply H3.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
intro.
apply H1.
apply Ring_Law_9.
split.
apply Comutive_Ring_Law_1.
apply Field_Law_1.
apply H.
rewrite <- H5.
rewrite -> H7.
symmetry.
apply Ring_Law_6.
split.
apply Comutive_Ring_Law_1.
apply Field_Law_1.
apply H.
apply H4.
Qed.

Theorem Field_Law_5:forall f g F:Set,Comutive_Ring f g F/\(forall I:Set,Ring_Semi_Ideal f g F I->((forall x:Set,x ∈ I->x=Identify_Element f F)\/F=I))->Field f g F.
Proof.
intros.
destruct H.
split.
apply H.
intros.
assert (Ring_Semi_Ideal f g F (Ring_Left_Principal_Ideal f g F x)).
apply (Comutive_Ring_Law_3 f g F (Ring_Left_Principal_Ideal f g F x)).
split.
apply H.
apply (Ring_Left_Principal_Ideal_Law_2 f g F x).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H1.
apply H0 in H2.
destruct H2.
left.
apply H2.
apply Ring_Left_Principal_Ideal_Law_1.
split.
apply H1.
exists (Identify_Element g F).
split.
apply (Monoid_Law_4 g F).
apply (Ring_Law_2 f g F).
apply Comutive_Ring_Law_1.
apply H.
symmetry.
apply (Monoid_Law_7 g F x).
split.
apply (Ring_Law_2 f g F).
apply Comutive_Ring_Law_1.
apply H.
apply H1.
right.
split.
apply H1.
assert ((Identify_Element g F) ∈ Ring_Left_Principal_Ideal f g F x).
rewrite <- H2.
apply (Monoid_Law_4 g F).
apply (Ring_Law_2 f g F).
apply Comutive_Ring_Law_1.
apply H.
apply Ring_Left_Principal_Ideal_Law_1 in H3.
destruct H3.
destruct H4.
destruct H4.
exists x0.
split.
apply H4.
rewrite -> H5.
split.
apply (Comutive_Ring_Law_2 f g F x x0).
split.
apply H.
split.
apply H1.
apply H4.
split.
Qed.



(*素イデアル*)
Definition Prime_Ideal(f g R p:Set):=Ring_Semi_Ideal f g R p/\(forall x1 x2:Set,x1 ∈ R/\x2 ∈ R/\Operation g x1 x2 ∈ p->(x1 ∈ p\/x2 ∈ p))/\~p=R.

Theorem Prime_Ideal_Law_1:forall f g R p:Set,Prime_Ideal f g R p->Ring_Semi_Ideal f g R p.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Prime_Ideal_Law_2:forall f g R p x1 x2:Set,Prime_Ideal f g R p/\x1 ∈ R/\x2 ∈ R/\Operation g x1 x2 ∈ p->(x1 ∈ p\/x2 ∈ p).
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
Qed.

Theorem Prime_Ideal_Law_3:forall f g R p:Set,Prime_Ideal f g R p->~p=R.
Proof.
intros.
destruct H.
destruct H0.
apply H1.
Qed.

Theorem Prime_Ideal_Law_4:forall f g R p:Set,Comutive_Ring f g R/\Prime_Ideal f g R p->Integral_Domain (Group_Quotient_Operation f R p) (Ring_Quotient_Operation f g R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply (Comutive_Ring_Law_5 f g R p).
split.
apply H.
apply H0.
intros.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
destruct (Law_of_Excluded_Middle (x0 ∈ p)).

left.
rewrite -> H4.
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f p) p x0).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
apply H5.

right.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H3.
apply H4.
intros.
destruct H6.
apply Quotient_Set_Law_1 in H6.
destruct H6.
destruct H6.
rewrite -> H4.
rewrite -> H8.
rewrite -> (Quotient_Ring_Law_3 f g R p x0 x2).
rewrite -> (Quotient_Ring_Law_3 f g R p x2 x0).
rewrite -> H8 in H7.
assert (~Equivalence_Class (Left_Equivalenc_Relation f R p) R (Operation g x0 x2)=Identify_Element (Group_Quotient_Operation f R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R)).
intro.
apply H7.
assert (x0 ∈ p\/x2 ∈ p).
apply H1.
split.
apply H3.
split.
apply H6.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f p) p (Operation g x0 x2)).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
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
apply H3.
apply H6.
apply H9.
destruct H10.
destruct H5.
apply H10.
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f p) p x2).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
apply H10.
split.
apply H9.
rewrite -> (Comutive_Ring_Law_2 f g R x2 x0).
apply H9.
split.
apply H.
split.
apply H6.
apply H3.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H6.
apply H3.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H3.
apply H6.
Qed.

Theorem Prime_Ideal_Law_5:forall f g R p:Set,Comutive_Ring f g R/\Ring_Semi_Ideal f g R p/\Integral_Domain (Group_Quotient_Operation f R p) (Ring_Quotient_Operation f g R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R)/\~p=R->Prime_Ideal f g R p.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H0.
split.

intros.
destruct H3.
destruct H4.
assert (Integral_Domain (Group_Quotient_Operation f R p) (Ring_Quotient_Operation f g R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R)/\(Equivalence_Class (Left_Equivalenc_Relation f R p) R x1) ∈ (Quotient_Set (Left_Equivalenc_Relation f R p) R)/\(Equivalence_Class (Left_Equivalenc_Relation f R p) R x2) ∈ (Quotient_Set (Left_Equivalenc_Relation f R p) R)/\Operation (Ring_Quotient_Operation f g R p) (Equivalence_Class (Left_Equivalenc_Relation f R p) R x1) (Equivalence_Class (Left_Equivalenc_Relation f R p) R x2)=Identify_Element (Group_Quotient_Operation f R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R)).
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H3.
split.
split.
apply Quotient_Set_Law_1.
exists x2.
split.
apply H4.
split.
rewrite -> (Quotient_Ring_Law_3 f g R p x1 x2).
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f p) p (Operation g x1 x2)).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
apply H5.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H3.
apply H4.
apply (Integral_Domain_Law_2 (Group_Quotient_Operation f R p) (Ring_Quotient_Operation f g R p) (Quotient_Set (Left_Equivalenc_Relation f R p) R)) in H6.
destruct H6.

left.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f p) p x1).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply H3.
apply H6.

right.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f p) p x2).
split.
apply (Ring_Semi_Ideal_Law_9 f g R p).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply H4.
apply H6.

apply H2.
Qed.



(*極大イデアル*)
Definition Maximal_Ideal(f g R m:Set):=Ring_Semi_Ideal f g R m/\(forall I:Set,Ring_Semi_Ideal f g R I/\m ⊂ I->(I=m\/I=R))/\~m=R.

Theorem Maximal_Ideal_Law_1:forall f g R m:Set,Maximal_Ideal f g R m->Ring_Semi_Ideal f g R m.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Maximal_Ideal_Law_2:forall f g R m I:Set,Maximal_Ideal f g R m/\Ring_Semi_Ideal f g R I/\m ⊂ I->(I=m\/I=R).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Maximal_Ideal_Law_3:forall f g R m:Set,Maximal_Ideal f g R m->~m=R.
Proof.
intros.
destruct H.
destruct H0.
apply H1.
Qed.


Theorem Maximal_Ideal_Law_4:forall f g R m:Set,Comutive_Ring f g R/\Maximal_Ideal f g R m->Field (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R).
Proof.
intros.
destruct H.

apply (Field_Law_5 (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)).
split.
apply (Comutive_Ring_Law_5 f g R m).
split.
apply H.
apply H0.

intros.
assert (forall J_:Set,J_ ∈ Semi_Ideal_Set (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)->J_=(Culculateion_Map (Qutioent_Ideal_Map f g R m) m)\/J_=(Culculateion_Map (Qutioent_Ideal_Map f g R m) R)).
assert (Bijective_Map (Qutioent_Ideal_Map f g R m) (Semi_Ideal_Set_1 f g R m) (Semi_Ideal_Set (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R))).
apply (Qutioent_Ideal_Map_Law_4 f g R m).
split.
apply (Comutive_Ring_Law_1 f g R).
apply H.
apply H0.
assert (forall J:Set,J ∈ (Semi_Ideal_Set_1 f g R m)->(J=m\/J=R)).
intros.
apply (Semi_Ideal_Set_1_Law_1 f g R m) in H3.
apply (Maximal_Ideal_Law_2 f g R m J).
split.
apply H0.
apply H3.
intros.
destruct H2.
destruct H2.
apply H6 in H4.
destruct H4.
destruct H4.
apply H3 in H4.
destruct H4.
left.
rewrite -> H4 in H7.
apply H7.
right.
rewrite -> H4 in H7.
apply H7.

apply (Semi_Ideal_Set_Law_1 (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R) I) in H1.
apply H2 in H1.
destruct H1.

left.
intros.
rewrite -> H1 in H3.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R m m) in H3.
apply Sub_Set_Map_Image_Law_1 in H3.
destruct H3.
destruct H4.
destruct H4.
rewrite <- (Quotient_Ring_Map_Law_4 f g R m x0) in H5.
rewrite -> H5.
apply (Quotient_Group_Law_6 f R (Restriction_Binary_Operation f m) m x0).
split.
apply (Ring_Semi_Ideal_Law_9 f g R m).
split.
apply Comutive_Ring_Law_1.
apply H.
apply Maximal_Ideal_Law_1.
apply H0.
apply H4.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply Maximal_Ideal_Law_1.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R m x0).
split.
apply Maximal_Ideal_Law_1.
apply H0.
apply H4.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply Maximal_Ideal_Law_1.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
apply Maximal_Ideal_Law_1.
apply H0.
intro.
intro.
apply H4.

right.
rewrite -> H1.
rewrite <- (Qutioent_Ideal_Map_Law_3 f g R m R).
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Sub_Set_Map_Image_Law_1.
split.
apply H3.
apply Quotient_Set_Law_1 in H3.
destruct H3.
exists x.
rewrite <- (Quotient_Ring_Map_Law_4 f g R m x).
apply H3.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply Maximal_Ideal_Law_1.
apply H0.
destruct H3.
apply H3.
intro.
apply Sub_Set_Map_Image_Law_1 in H3.
destruct H3.
apply H3.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply Maximal_Ideal_Law_1.
apply H0.
apply Semi_Ideal_Set_1_Law_1.
split.
split.
intro.
intro.
apply H3.
split.
intros.
apply (Group_Law_2 f R x y).
split.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply Comutive_Ring_Law_1.
apply H.
apply H3.
split.
intros.
apply (Monoid_Law_1 g R x a).
split.
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
destruct H3.
split.
apply H4.
apply H3.
split.
intros.
apply (Monoid_Law_1 g R a x).
split.
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
apply H3.
apply Empty_Set_Law_1.
exists (Identify_Element f R).
apply Group_Law_4.
apply Abel_Group_Law_1.
apply (Ring_Law_1 f g R).
apply Comutive_Ring_Law_1.
apply H.
intro.
intro.
apply (Ring_Semi_Ideal_Law_3 f g R m z).
split.
apply Maximal_Ideal_Law_1.
apply H0.
apply H3.
Qed.

Theorem Maximal_Ideal_Law_5:forall f g R m:Set,Comutive_Ring f g R/\Ring_Semi_Ideal f g R m/\Field (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)/\~m=R->Maximal_Ideal f g R m.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

split.
apply H0.

split.
intros.
destruct H3.
assert (Field (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)/\Ring_Semi_Ideal (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R) (Sub_Set_Map_Image (Quotient_Ring_Map f R m) R (Quotient_Set (Left_Equivalenc_Relation f R m) R) I)/\~Zero_Ring (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)).
split.
apply H1.
split.
apply (Ring_homomorphism_Law_9 (Quotient_Ring_Map f R m) f g R I (Group_Quotient_Operation f R m) (Ring_Quotient_Operation f g R m) (Quotient_Set (Left_Equivalenc_Relation f R m) R)).
split.
apply (Quotient_Ring_Map_Law_5 f g R m).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply H3.
apply (Quotient_Ring_Map_Law_6 f g R m).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
intro.
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply (Ring_Semi_Ideal_Law_3 f g R m z).
split.
apply H0.
apply H6.
intro.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f m) m z).
split.
apply (Ring_Semi_Ideal_Law_9 f g R m).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply H6.
destruct H5.
apply H7.
apply Quotient_Set_Law_1.
exists z.
split.
apply H6.
split.
apply Field_Law_4 in H5.
destruct H5.

left.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply (Quotient_Group_Law_7 f R (Restriction_Binary_Operation f m) m z).
split.
apply (Ring_Semi_Ideal_Law_9 f g R m).
split.
apply Comutive_Ring_Law_1.
apply H.
apply H0.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H3.
apply H6.
apply H5.
apply Sub_Set_Map_Image_Law_1.
split.
apply Quotient_Set_Law_1.
exists z.
split.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H3.
apply H6.
split.
exists z.
split.
apply H6.
apply (Quotient_Ring_Map_Law_4 f g R m z).
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
apply (Ring_Semi_Ideal_Law_3 f g R I z).
split.
apply H3.
apply H6.
intro.
apply H4.
apply H6.

right.
symmetry.
apply (Ring_Semi_Ideal_Law_10 f g R I).
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H3.
rewrite -> (Quotient_Ring_Map_Law_8 f g R m I).
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Monoid_Law_5 g R).
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
exists (Culculateion_Map (Quotient_Ring_Map f R m) (Identify_Element g R)).
split.
rewrite <- H5.
rewrite <- (Quotient_Ring_Map_Law_4 f g R m).
apply Quotient_Set_Law_1.
exists (Identify_Element g R).
split.
apply (Monoid_Law_5 g R).
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
split.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
apply (Monoid_Law_5 g R).
apply (Ring_Law_2 f g R).
apply Comutive_Ring_Law_1.
apply H.
split.
split.
apply Comutive_Ring_Law_1.
apply H.
split.
apply H0.
split.
apply H3.
apply H4.

apply H2.
Qed.

Theorem Maximal_Ideal_Law_6:forall f g R m:Set,Comutive_Ring f g R/\Maximal_Ideal f g R m->Prime_Ideal f g R m.
Proof.
intros.
destruct H.
apply (Prime_Ideal_Law_5 f g R m).
split.
apply H.
split.
apply (Maximal_Ideal_Law_1 f g R m).
apply H0.
split.
apply Field_Law_3.
apply Maximal_Ideal_Law_4.
split.
apply H.
apply H0.
apply (Maximal_Ideal_Law_3 f g R m).
apply H0.
Qed.