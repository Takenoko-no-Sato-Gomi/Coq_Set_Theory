Require Export Coq_Basic.



(*二項演算*)
Definition Binary_Oparation(f X:Set):=Map f (Double_Direct_Product_Set X X) X.

Definition Oparation(f x1 x2:Set):=Culculateion_Map f (Ordered_Set x1 x2).

Axiom Binary_Oparation_Law_1:forall f X x1 x2:Set,(contain x1 X/\contain x2 X)->contain (Oparation f x1 x2) X.



(*群とモノイド*)

Definition Associative_Law(f X:Set):=(forall x1 x2 x3:Set,contain x1 X/\contain x2 X/\contain x3 X->(Oparation f x1 (Oparation f x2 x3))=(Oparation f (Oparation f x1 x2) x3)).

Definition Exists_of_Identify_Element(f X:Set):=(exists e:Set,contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x)).

Definition Identify_Element(f X:Set):=Well_Defined (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x)).

Definition Exists_of_Reverse_Element(f X:Set):=(exists e:Set,(contain e X/\(forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))/\(forall x:Set,contain x X->exists x':Set,contain x' X/\(Oparation f x x')=e/\(Oparation f x' x)=e))).

Definition Reverse_Element(f x X:Set):=Well_Defined (fun x'=>contain x' X/\(Oparation f x x')=(Identify_Element f X)/\(Oparation f x' x)=(Identify_Element f X)).



Definition Monoid(f X:Set):=Binary_Oparation f X/\Associative_Law f X/\Exists_of_Identify_Element f X.

Definition Group(f X:Set):=Binary_Oparation f X/\Associative_Law f X/\Exists_of_Reverse_Element f X.



Theorem Monoid_Law_1:forall f X:Set,Group f X->Monoid f X.
Proof.
intros.
split.
apply H.
split.
apply H.
destruct H.
destruct H0.
destruct H1.
exists x.
split.
apply H1.
apply H1.
Qed.

Theorem Monoid_Law_2:forall f X:Set,Monoid f X->exists! e:Set,contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
exists x.
split.
split.
apply H1.
intros.
split.
apply H1.
apply H2.
apply H1.
apply H2.
intros.
destruct H1.
apply H2 in H1.
destruct H2.
apply H3 in H2.
destruct H2.
destruct H1.
rewrite <- H1.
apply H5.
Qed.

Theorem Monoid_Law_3:forall f X:Set,Monoid f X->(forall x:Set,contain x X->(contain (Identify_Element f X) X/\Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
Proof.
intros.
assert (Monoid f X).
apply H.
destruct H.
destruct H2.
destruct H3.
destruct H3.
assert (contain x X).
apply H0.
apply H4 in H0.
destruct H0.
destruct H0.
split.
apply (Well_Defined_1 (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))).
apply Monoid_Law_2.
apply H1.
split.
apply (Well_Defined_1 (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))).
apply Monoid_Law_2.
apply H1.
assert (contain x X).
apply H5.
apply H4 in H5.
destruct H5.
rewrite -> H5.
apply H0.
apply (Well_Defined_1 (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))).
apply Monoid_Law_2.
apply H1.
assert (contain x X).
apply H5.
apply H4 in H5.
destruct H5.
rewrite -> H5.
apply H0.
Qed.



Theorem Group_Law_1:forall f X:Set,Group f X->forall x:Set,contain x X->exists! x':Set,contain x' X/\(Oparation f x x'=(Identify_Element f X)/\Oparation f x' x=(Identify_Element f X)).
Proof.
intros.
assert (Group f X).
apply H.
destruct H.
destruct H2.
destruct H3.
destruct H3.
destruct H4.
assert (contain x X).
apply H0.
apply H5 in H0.
destruct H0.
exists x1.
split.
split.
apply H0.
assert (forall x:Set,contain x X->(contain (Identify_Element f X) X/\Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
apply Monoid_Law_3.
apply Monoid_Law_1.
apply H1.
destruct H0.
destruct H8.
assert (Identify_Element f X=x0).
assert (forall x:Set,contain x X->(contain (Identify_Element f X) X/\Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
apply Monoid_Law_3.
apply Monoid_Law_1.
apply H1.
apply H10 in H3.
destruct H3.
destruct H11.
apply H4 in H3.
destruct H3.
rewrite <- H12.
rewrite -> H3.
split.
split.
rewrite -> H10.
apply H8.
rewrite -> H10.
apply H9.
intros.
destruct H0.
destruct H8.
destruct H7.
destruct H10.
assert (Identify_Element f X=x0).
assert (forall x:Set,contain x X->(contain (Identify_Element f X) X/\Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
apply Monoid_Law_3.
apply Monoid_Law_1.
apply H1.
apply H12 in H3.
destruct H3.
destruct H13.
apply H4 in H3.
destruct H3.
rewrite <- H15.
rewrite -> H13.
split.
assert (Oparation f x' (Oparation f x x1)=Oparation f x' (Oparation f x x')).
rewrite -> H8.
rewrite -> H10.
rewrite -> H12.
split.
assert (contain x' X/\contain x X/\contain x1 X).
split.
apply H7.
split.
apply H6.
apply H0.
apply H2 in H14.
assert (contain x' X/\contain x X/\contain x' X).
split.
apply H7.
split.
apply H6.
apply H7.
apply H2 in H15.
rewrite -> H11 in H14.
rewrite -> H11 in H15.
assert (forall x:Set,contain x X->(contain (Identify_Element f X) X/\Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
apply Monoid_Law_3.
apply Monoid_Law_1.
apply H1.
apply H16 in H0.
destruct H0.
destruct H17.
rewrite -> H18 in H14.
apply H16 in H7.
destruct H7.
destruct H19.
rewrite -> H20 in H15.
rewrite <- H15.
rewrite <- H14.
apply H13.
Qed.

Theorem Group_Law_4:forall f X:Set,Group f X->forall x:Set,contain x X->(Oparation f x (Reverse_Element f x X)=(Identify_Element f X)/\Oparation f (Reverse_Element f x X) x=(Identify_Element f X)).
Proof.
intros.
apply (Well_Defined_1 (fun x'=>contain x' X/\(Oparation f x x')=(Identify_Element f X)/\(Oparation f x' x)=(Identify_Element f X))).
apply Group_Law_1.
apply H.
apply H0.
Qed.














