Require Export Coq_Basic.



(*二項演算*)
Definition Binary_Oparation(f X:Set):=Map f (Double_Direct_Product_Set X X) X.

Definition Oparation(f x1 x2:Set):=Culculateion_Map f (Ordered_Set x1 x2).

Axiom Binary_Oparation_Law_1:forall f X x1 x2:Set,(contain x1 X/\contain x2 X)->contain (Oparation f x1 x2) X.



(*群*)

Definition Associative_Law(f X:Set):=(forall x1 x2 x3:Set,contain x1 X/\contain x2 X/\contain x3 X->(Oparation f x1 (Oparation f x2 x3))=(Oparation f (Oparation f x1 x2) x3)).

Definition Exists_of_Identify_Element(f X:Set):=(exists e:Set,contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x)).

Definition Identify_Element(f X:Set):=Well_Defined (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x)).

Definition Exists_of_Reverse_Element(f X:Set):=(exists e:Set,(contain e X/\(forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))/\(forall x:Set,contain x X->exists x':Set,contain x' X/\(Oparation f x x')=e/\(Oparation f x' x)=e))).

Definition Reverse_Element(f x X:Set):=Well_Defined (fun x'=>contain x' X/\(Oparation f x x')=(Identify_Element f X)/\(Oparation f x' x)=(Identify_Element f X)).

Definition Group(f X:Set):=Binary_Oparation f X/\Associative_Law f X/\Exists_of_Reverse_Element f X.

Theorem Group_Law_1:forall f X:Set,Group f X->exists! e:Set,contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H1.
destruct H2.
exists x.
split.
split.
apply H1.
intros.
split.
apply H2.
apply H4.
apply H2 in H4.
destruct H4.
apply H5.
intros.
destruct H4.
apply H5 in H1.
apply H2 in H4.
destruct H1.
destruct H4.
rewrite <- H1.
apply H7.
Qed.

Theorem Group_Law_2:forall f X:Set,Group f X->(forall x:Set,contain x X->(Oparation f x (Identify_Element f X)=x/\Oparation f (Identify_Element f X) x=x)).
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
destruct H0.
apply (Well_Defined_1 (fun e=>contain e X/\forall x:Set,contain x X->(Oparation f x e=x/\Oparation f e x=x))).
apply Group_Law_1.
apply H1.
apply H6.
Qed.

Theorem Group_Law_3:forall f x X:Set,Group f X/\contain x X->exists! x':Set,contain x' X/\(Oparation f x x'=(Identify_Element f X)/\Oparation f x' x=(Identify_Element f X)).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H2.
destruct H3.
apply H4 in H0.
destruct H0.
exists x1.
split.
split.
apply H0.
assert (Identify_Element f X=x0).

Qed.

Theorem Group_Law_4:forall f x X:Set,Group f X->(Oparation f x (Reverse_Element f x X)=(Identify_Element f X)/\Oparation f (Reverse_Element f x X) x=(Identify_Element f X)).
Proof.

Qed.











