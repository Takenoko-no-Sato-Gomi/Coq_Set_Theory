Require Export Coq_Basic.



(*開集合と閉集合*)
Definition Open_Set_Family(O X:Set):=(Sub_Set O (Power_Set X))/\(contain _0 O)/\(contain X O)/\(forall x y:Set,(contain x O/\contain y O)->contain (Pair_Meet_Set x y) O)/\(forall x:Set,(Sub_Set x O/\~x=_0)->contain (Union_Set x) O).

Definition Close_Set_Family(C X:Set):=(Sub_Set C (Power_Set X))/\(contain _0 C)/\(contain X C)/\(forall x y:Set,(contain x C/\contain y C)->contain (Pair_Union_Set x y) C)/\(forall x:Set,(Sub_Set x C/\~x=_0)->contain (Meet_Set x) C).

Theorem Topology_Law_1:forall O X:Set,(Open_Set_Family O X/\~O=_0)->(Close_Set_Family (Prop_Set (fun z=>exists x:Set,z=Complement_Set X x/\contain x O)) X).
Proof.
assert (forall O X w:Set,contain w (Prop_Set (fun z:Set=>exists x:Set,z=Complement_Set X x/\contain x O))<->(exists x:Set,w=Complement_Set X x/\contain x O)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H in H1.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply H1.

intros.
destruct H0.
unfold Open_Set_Family in H0.
destruct H0.
destruct H2.
destruct H3.
destruct H4.
unfold Close_Set_Family.

split.
intro.
intro.
apply H in H6.
destruct H6.
destruct H6.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H6 in H8.
apply Complement_Set_Law_1 in H8.
destruct H8.
apply H8.

split.
apply H.
exists X.
split.
rewrite -> Complement_Set_Law_2.
split.
apply H3.

split.
apply H.
exists _0.
split.
rewrite <- Complement_Set_Law_3.
split.
apply H2.

split.
intros.
apply H.
destruct H6.
apply H in H6.
apply H in H7.
destruct H6.
destruct H6.
destruct H7.
destruct H7.
exists (Pair_Meet_Set (Complement_Set X x) (Complement_Set X y)).
split.
rewrite <- De_Morgans_Law_2.
rewrite -> Complement_Set_Law_4.
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H10.
destruct H10.
rewrite -> H6 in H10.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
rewrite -> H7 in H10.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
apply H4.
split.
rewrite -> H6.
rewrite -> Complement_Set_Law_4.
apply H8.
apply Power_Set_Law_1.
apply H0.
apply H8.
rewrite -> H7.
rewrite -> Complement_Set_Law_4.
apply H9.
apply Power_Set_Law_1.
apply H0.
apply H9.

intros.
apply H.
destruct H6.
exists (Complement_Set X (Meet_Set x)).
split.
rewrite -> Complement_Set_Law_4.
split.
intro.
intro.
assert (forall A:Set,contain A x->contain z A).
apply Meet_Set_Law_1.
apply H7.
apply H8.
apply Empty_Set_Law_1 in H7.
destruct H7.
assert (contain x0 x).
apply H7.
assert (Sub_Set x (Power_Set X)).
intro.
intro.
apply H6 in H11.
apply H in H11.
destruct H11.
destruct H11.
rewrite -> H11.
apply Power_Set_Law_1.
intro.
intro.
apply Complement_Set_Law_1 in H13.
destruct H13.
apply H13.
apply H11 in H7.
apply Power_Set_Law_1 in H7.
apply H7.
apply H9.
apply H10.
rewrite -> De_Morgans_Law_4.
apply H5.
split.
intro.
intro.
apply H in H8.
destruct H8.
destruct H8.
apply H6 in H9.
apply H in H9.
destruct H9.
destruct H9.
rewrite -> H8.
rewrite -> H9.
rewrite -> Complement_Set_Law_4.
apply H10.
apply Power_Set_Law_1.
apply H0.
apply H10.
apply Empty_Set_Law_1 in H7.
apply Empty_Set_Law_1.
destruct H7.
exists (Complement_Set X x0).
apply H.
exists x0.
split.
split.
apply H7.
apply H7.
Qed.

Theorem Topology_Law_2:forall C X:Set,(Close_Set_Family C X/\~C=_0)->(Open_Set_Family (Prop_Set (fun z=>exists x:Set,z=Complement_Set X x/\contain x C)) X).
Proof.

assert (forall O X w:Set,contain w (Prop_Set (fun z:Set=>exists x:Set,z=Complement_Set X x/\contain x O))<->(exists x:Set,w=Complement_Set X x/\contain x O)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H in H1.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply H1.

intros.
destruct H0.
unfold Close_Set_Family in H0.
destruct H0.
destruct H2.
destruct H3.
destruct H4.
unfold Open_Set_Family.

split.
intro.
intro.
apply H in H6.
destruct H6.
destruct H6.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H6 in H8.
apply Complement_Set_Law_1 in H8.
destruct H8.
apply H8.

split.
apply H.
exists X.
split.
rewrite -> Complement_Set_Law_2.
split.
apply H3.

split.
apply H.
exists _0.
split.
rewrite <- Complement_Set_Law_3.
split.
apply H2.

split.
intros.
destruct H6.
apply H in H6.
destruct H6.
destruct H6.
apply H in H7.
destruct H7.
destruct H7.
apply H.
exists (Pair_Union_Set (Complement_Set X x) (Complement_Set X y)).
split.
rewrite <- De_Morgans_Law_1.
rewrite -> Complement_Set_Law_4.
split.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H10.
destruct H10.
rewrite -> H6 in H10.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
apply H4.
split.
rewrite -> H6.
rewrite -> Complement_Set_Law_4.
apply H8.
apply Power_Set_Law_1.
apply H0.
apply H8.
rewrite -> H7.
rewrite -> Complement_Set_Law_4.
apply H9.
apply Power_Set_Law_1.
apply H0.
apply H9.

intros.
destruct H6.
apply H.
exists (Complement_Set X (Union_Set x)).
split.
rewrite -> Complement_Set_Law_4.
split.
intro.
intro.
apply Union_Set_Law_1 in H8.
destruct H8.
destruct H8.
apply H6 in H8.
apply H in H8.
destruct H8.
destruct H8.
rewrite -> H8 in H9.
apply Complement_Set_Law_1 in H9.
destruct H9.
apply H9.
rewrite -> De_Morgans_Law_3.
apply H5.
split.
intro.
intro.
apply H in H8.
destruct H8.
destruct H8.
rewrite -> H8.
apply H6 in H9.
apply H in H9.
destruct H9.
destruct H9.
rewrite -> H9.
rewrite -> Complement_Set_Law_4.
apply H10.
apply Power_Set_Law_1.
apply H0.
apply H10.
apply Empty_Set_Law_1 in H7.
apply Empty_Set_Law_1.
destruct H7.
exists (Complement_Set X x0).
apply H.
exists x0.
split.
split.
apply H7.
apply H7.
Qed.



(*開基*)
Definition Open_Base(X O B:Set):=(Sub_Set B O)/\(forall o:Set,contain o O->exists B0:Set,Sub_Set B0 B/\Union_Set B0=o).

Theorem Open_Base_Law_1:forall X O B:Set,Open_Set_Family O X->(Open_Base X O B<->(Sub_Set B O/\forall x o:Set,(contain x o/\contain o O)->exists B0:Set,contain x B0/\Sub_Set B0 o/\contain B0 B)).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
unfold Open_Base.
split.
intro.
destruct H4.
split.
apply H4.
intros.
destruct H6.
apply H5 in H7.
destruct H7.
destruct H7.
rewrite <- H8 in H6.
apply Union_Set_Law_1 in H6.
destruct H6.
destruct H6.
exists x1.
split.
apply H9.
split.
intro.
intro.
rewrite <- H8.
apply Union_Set_Law_1.
exists x1.
split.
apply H6.
apply H10.
apply H7.
apply H6.

intro.
destruct H4.
split.
apply H4.
intros.
exists (Prop_Set (fun b=>exists x:Set,contain x b/\contain b B/\Sub_Set b o)).
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun b:Set=>exists x:Set,contain x b/\contain b B/\Sub_Set b o)) in H7.
destruct H7.
destruct H7.
apply H8.
exists B.
intros.
destruct H9.
destruct H9.
destruct H10.
apply H10.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1 in H7.
destruct H7.
destruct H7.
apply (Prop_Set_Law_1 (fun b:Set=>exists x:Set,contain x b/\contain b B/\Sub_Set b o)) in H7.
destruct H7.
destruct H7.
destruct H9.
apply H10.
apply H8.
exists B.
intros.
destruct H10.
destruct H10.
destruct H11.
apply H11.
intro.
apply Union_Set_Law_1.
assert (contain z o/\contain o O).
split.
apply H7.
apply H6.
apply H5 in H8.
destruct H8.
destruct H8.
exists x.
split.
apply (Prop_Set_Law_1 (fun b:Set=>exists x:Set,contain x b/\contain b B/\Sub_Set b o)).
exists B.
intros.
destruct H10.
destruct H10.
destruct H11.
apply H11.
destruct H9.
exists z.
split.
apply H8.
split.
apply H10.
apply H9.
apply H8.
Qed.

Theorem Open_Base_Law_2:forall X O B:Set,(Open_Set_Family O X/\Open_Base X O B)->(Union_Set B=X).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1 in H6.
destruct H6.
destruct H6.
apply H0 in H6.
apply H in H6.
apply Power_Set_Law_1 in H6.
apply H6.
apply H7.
intro.
apply H5 in H2.
destruct H2.
destruct H2.
rewrite <- H7 in H6.
apply Union_Set_Law_1.
apply Union_Set_Law_1 in H6.
destruct H6.
destruct H6.
exists x0.
split.
apply H2.
apply H6.
apply H8.
Qed.

Theorem Open_Base_Law_3:forall X O B:Set,(Open_Set_Family O X/\Open_Base X O B)->(forall b1 b2 p:Set,(contain b1 B/\contain b2 B/\contain p (Pair_Meet_Set b1 b2))->exists b:Set,contain b B/\contain p b/\Sub_Set b (Pair_Meet_Set b1 b2)).
Proof.
intro.
intro.
intro.
intro.
destruct H.
assert (Open_Base X O B).
apply H0.
destruct H.
destruct H2.
destruct H3.
destruct H4.
destruct H0.
intros.
destruct H7.
destruct H8.
assert (contain (Pair_Meet_Set b1 b2) O).
apply H4.
split.
apply H0.
apply H7.
apply H0.
apply H8.
apply H6 in H10.
destruct H10.
destruct H10.
apply Open_Base_Law_1 in H1.
destruct H1.
assert (contain p (Pair_Meet_Set b1 b2)/\contain (Pair_Meet_Set b1 b2) O).
split.
apply H9.
apply H4.
split.
apply H0.
apply H7.
apply H0.
apply H8.
apply H12 in H13.
destruct H13.
destruct H13.
destruct H14.
exists x0.
split.
apply H15.
split.
apply H13.
apply H14.
split.
apply H.
split.
apply H2.
split.
apply H3.
split.
apply H4.
apply H5.
Qed.



(*内部*)

Definition Interior_Set(x O:Set):=Union_Set (Prop_Set (fun y=>contain y O/\Sub_Set y x)).

Theorem Interior_Set_Law_1:forall x O X:Set,(Open_Set_Family O X/\Sub_Set x X)->(contain (Interior_Set x O) O).
Proof.
intros.
destruct H.
unfold Open_Set_Family in H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
apply H4.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun y :Set=>contain y O/\Sub_Set y x)) in H5.
destruct H5.
apply H5.
exists O.
intros.
destruct H7.
apply H7.
apply Empty_Set_Law_1.
exists _0.
apply Prop_Set_Law_1.
exists O.
intros.
destruct H5.
apply H5.
split.
apply H1.
intro.
intro.
destruct (Definition_of_Empty_Set z).
apply H5.
Qed.

Theorem Interior_Set_Law_2:forall x O X:Set,(Open_Set_Family O X/\Sub_Set x X)->(Sub_Set (Interior_Set x O) x).
Proof.
intros.
destruct H.
unfold Open_Set_Family in H.
destruct H.
destruct H1. 
destruct H2.
destruct H3.
unfold Interior_Set.
intro.
intro.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply (Prop_Set_Law_1 (fun y :Set=>contain y O/\Sub_Set y x)) in H5.
destruct H5.
apply H7.
apply H6.
exists O.
intros.
destruct H8.
apply H8.
Qed.

Theorem Interior_Set_Law_3:forall x O X:Set,(Open_Set_Family O X/\Sub_Set x X)->(contain x O<->x=Interior_Set x O).
Proof.
intros.
destruct H.
unfold Open_Set_Family in H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
split.
intro.
apply Axiom_of_Extensionality.
intro.
split.
intro.
unfold Interior_Set.
apply Union_Set_Law_1.
exists x.
split.
apply Prop_Set_Law_1.
exists O.
intros.
destruct H7.
apply H7.
split.
apply H5.
intro.
intro.
apply H7.
apply H6.
intro.
apply (Interior_Set_Law_2 x O X) in H6.
apply H6.
split.
unfold Open_Set_Family.
split.
apply H.
split.
apply H1.
split.
apply H2.
split.
apply H3.
apply H4.
apply H0.

intro.
rewrite -> H5.
apply H4.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun y:Set=>contain y O/\Sub_Set y x)) in H6.
destruct H6.
apply H6.
exists O.
intro.
intro.
destruct H8.
apply H8.
apply Empty_Set_Law_1.
exists x.
apply Prop_Set_Law_1.
exists O.
intros.
destruct H6.
apply H6.
split.
rewrite -> H5.
apply (Interior_Set_Law_1 x O X).
split.
unfold Open_Set_Family.
split.
apply H.
split.
apply H1.
split.
apply H2.
split.
apply H3.
apply H4.
apply H0.
intro.
intro.
apply H6.
Qed.



(*閉包*)
Definition Closure_Set(x C:Set):=Meet_Set (Prop_Set (fun y=>contain y C/\Sub_Set x y)).

Theorem Closure_Set_Law_1:forall x C X:Set,(Close_Set_Family C X/\Sub_Set x X)->(contain (Closure_Set x C) C).
Proof.
intros.
destruct H.
unfold Close_Set_Family in H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
apply H4.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun y :Set=>contain y C/\Sub_Set x y)) in H5.
destruct H5.
apply H5.
exists C.
intros.
destruct H7.
apply H7.
apply Empty_Set_Law_1.
exists X.
apply (Prop_Set_Law_1 (fun y :Set=>contain y C/\Sub_Set x y)).
exists C.
intros.
destruct H5.
apply H5.
split.
apply H2.
apply H0.
Qed.

Theorem Closure_Set_Law_2:forall x C X:Set,(Close_Set_Family C X/\Sub_Set x X)->(Sub_Set x (Closure_Set x C)).
Proof.
intros.
destruct H.
unfold Close_Set_Family in H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
intro.
intro.
unfold Closure_Set.
apply Meet_Set_Law_1.
apply Empty_Set_Law_1.
exists X.
apply Prop_Set_Law_1.
exists C.
intros.
destruct H6.
apply H6.
split.
apply H2.
apply H0.
intros.
apply (Prop_Set_Law_1 (fun y :Set=>contain y C/\Sub_Set x y)) in H6.
destruct H6.
apply H7.
apply H5.
exists C.
intros.
destruct H8.
apply H8.
Qed.

Theorem Closure_Set_Law_3:forall x C X:Set,(Close_Set_Family C X/\Sub_Set x X)->(contain x C<->x=Closure_Set x C).
Proof.
intros.
destruct H.
unfold Close_Set_Family in H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
split.
intro.
apply Axiom_of_Extensionality.
intro.
split.
intro.
unfold Closure_Set.
apply Meet_Set_Law_1.
apply Empty_Set_Law_1.
exists x.
apply Prop_Set_Law_1.
exists C.
intros.
destruct H7.
apply H7.
split.
apply H5.
intro.
intro.
apply H7.
intros.
apply (Prop_Set_Law_1 (fun y:Set=>contain y C/\Sub_Set x y)) in H7.
destruct H7.
apply H8.
apply H6.
exists C.
intros.
destruct H9.
apply H9.
intro.
unfold Closure_Set in H6.
assert (forall A:Set,contain A (Prop_Set (fun y:Set=>contain y C/\Sub_Set x y))->contain z A).
apply Meet_Set_Law_1.
apply Empty_Set_Law_1.
exists x.
apply (Prop_Set_Law_1 (fun y:Set=>contain y C/\Sub_Set x y)).
exists C.
intros.
destruct H7.
apply H7.
split.
apply H5.
intro.
intro.
apply H7.
apply H6.
apply H7.
apply (Prop_Set_Law_1 (fun y:Set=>contain y C/\Sub_Set x y)).
exists C.
intros.
destruct H8.
apply H8.
split.
apply H5.
intro.
intro.
apply H8.

intro.
rewrite -> H5.
apply H4.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun y:Set=>contain y C/\Sub_Set x y)) in H6.
destruct H6.
apply H6.
apply H7 in H6.
exists C.
intros.
destruct H8.
apply H8.
exists C.
intros.
destruct H8.
apply H8.
apply Empty_Set_Law_1.
exists X.
apply (Prop_Set_Law_1 (fun y:Set=>contain y C/\Sub_Set x y)).
exists C.
intros.
destruct H6.
apply H6.
split.
apply H2.
apply H0.
Qed.



(*相対位相*)
Definition Sub_Set_Open_Set_Family(O Y X:Set):=Prop_Set (fun o_y=>exists o:Set,contain o O/\(o_y=Pair_Meet_Set Y o)).

Theorem Sub_Set_Open_Set_Family_Law_1:forall O X Y:Set,(Open_Set_Family O X/\Sub_Set Y X)->(Open_Set_Family (Sub_Set_Open_Set_Family O Y X) Y).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.

assert (forall z:Set,contain z (Prop_Set (fun o_y=>exists o:Set,contain o O/\(o_y=Pair_Meet_Set Y o)))<->exists o:Set,contain o O/\(z=Pair_Meet_Set Y o)).
intro.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply H0.
destruct H5.
destruct H5.
rewrite -> H7 in H6.
apply Pair_Meet_Set_Law_1 in H6.
destruct H6.
apply H6.

split.
intro.
intro.
apply H5 in H6.
destruct H6.
destruct H6.
rewrite -> H7.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H8.
destruct H8.
apply H8.

split.
apply H5.
exists _0.
split.
apply H1.
apply Theorem_of_Extensionality.
intro.
split.
intro.
destruct (Definition_of_Empty_Set z).
apply H6.
intro.
apply Pair_Meet_Set_Law_1 in H6.
destruct H6.
apply H7.

split.
apply H5.
exists X.
split.
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1.
split.
apply H6.
apply H0.
apply H6.
intro.
apply Pair_Meet_Set_Law_1 in H6.
destruct H6.
apply H6.

split.
intros.
apply H5.
destruct H6.
apply H5 in H6.
apply H5 in H7.
destruct H6.
destruct H6.
destruct H7.
destruct H7.
exists (Pair_Meet_Set x0 x1).
split.
apply H3.
split.
apply H6.
apply H7.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1 in H10.
apply Pair_Meet_Set_Law_1.
destruct H10.
split.
rewrite -> H8 in H10.
apply Pair_Meet_Set_Law_1 in H10.
destruct H10.
apply H10.
apply Pair_Meet_Set_Law_1.
rewrite -> H8 in H10.
rewrite -> H9 in H11.
apply Pair_Meet_Set_Law_1 in H10.
apply Pair_Meet_Set_Law_1 in H11.
destruct H10.
destruct H11.
split.
apply H12.
apply H13.
intro.
apply Pair_Meet_Set_Law_1 in H10.
apply Pair_Meet_Set_Law_1.
destruct H10.
apply Pair_Meet_Set_Law_1 in H11.
destruct H11.
rewrite -> H8.
rewrite -> H9.
split.
apply Pair_Meet_Set_Law_1.
split.
apply H10.
apply H11.
apply Pair_Meet_Set_Law_1.
split.
apply H10.
apply H12.

intros.
apply H5.

Qed.









