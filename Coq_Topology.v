Require Export Coq_Basic.



(*開集合と閉集合*)
Definition Open_Set_Family(O X:Set):=(O ⊂ (Power_Set X))/\(∅ ∈ O)/\(X ∈ O)/\(forall x y:Set,(x ∈ O/\y ∈ O)->(x ∩ y) ∈ O)/\(forall x:Set,(x ⊂ O/\~x=∅)->(Union_Set x) ∈ O).

Definition Close_Set_Family(C X:Set):=(C ⊂ (Power_Set X))/\(∅ ∈ C)/\(X ∈ C)/\(forall x y:Set,(x ∈ C/\y ∈ C)->(x ∪ y) ∈ C)/\(forall x:Set,(x ⊂ C/\~x=∅)->(Meet_Set x) ∈ C).

Theorem Topology_Law_1:forall O X:Set,(Open_Set_Family O X/\~O=∅)->(Close_Set_Family (Prop_Set (fun z=>exists x:Set,z=Complement_Set X x/\x ∈ O)) X).
Proof.
assert (forall O X w:Set,w ∈ (Prop_Set (fun z:Set=>exists x:Set,z=Complement_Set X x/\x ∈ O))<->(exists x:Set,w=Complement_Set X x/\x ∈ O)).
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
exists (∅).
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
exists ((Complement_Set X x) ∩ (Complement_Set X y)).
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
assert (forall A:Set,A ∈ x->z ∈ A).
apply Meet_Set_Law_1.
apply H7.
apply H8.
apply Empty_Set_Law_1 in H7.
destruct H7.
assert (x0 ∈ x).
apply H7.
assert (x ⊂ (Power_Set X)).
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

Theorem Topology_Law_2:forall C X:Set,(Close_Set_Family C X/\~C=∅)->(Open_Set_Family (Prop_Set (fun z=>exists x:Set,z=Complement_Set X x/\x ∈ C)) X).
Proof.

assert (forall O X w:Set,w ∈ (Prop_Set (fun z:Set=>exists x:Set,z=Complement_Set X x/\x ∈ O))<->(exists x:Set,w=Complement_Set X x/\x ∈ O)).
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
exists (∅).
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
exists ((Complement_Set X x) ∪ (Complement_Set X y)).
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
Definition Open_Base(X O B:Set):=(B ⊂ O)/\(forall U:Set,U ∈ O->exists B0:Set,B0 ⊂ B/\Union_Set B0=U).

Definition Generating_Open_Bsse(X B:Set):=(Prop_Set (fun U=>exists b:Set,b ⊂ B/\U=Union_Set b)).

Theorem Open_Base_Law_1:forall X O B:Set,Open_Base X O B<->((B ⊂ O)/\(forall U:Set,forall x:Set,(U ∈ O/\x ∈ U)->(exists b:Set,b ∈ B/\x ∈ b/\b ⊂ U))).
Proof.
intros.
split.

intros.
split.
destruct H.
apply H.
destruct H.
intros.
destruct H1.
apply H0 in H1.
destruct H1.
destruct H1.
rewrite <- H3 in H2.
apply Union_Set_Law_1 in H2.
destruct H2.
destruct H2.
exists x1.
split.
apply H1.
apply H2.
split.
apply H4.
intro.
intro.
rewrite <- H3.
apply Union_Set_Law_1.
exists x1.
split.
apply H2.
apply H5.

intros.
split.
destruct H.
apply H.
destruct H.
intros.
exists (Prop_Set (fun b=>b ∈ B/\b ⊂ U)).
assert (forall a:Set,a ∈ (Prop_Set (fun b=>b ∈ B/\b ⊂ U))<->a ∈ B/\a ⊂ U).
intro.
apply Prop_Set_Law_1.
exists B.
intros.
destruct H2.
apply H2.
split.
intro.
intro.
apply H2 in H3.
destruct H3.
apply H3.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1 in H3.
destruct H3.
destruct H3.
apply  H2 in H3.
destruct H3.
apply H5.
apply H4.
intro.
apply Union_Set_Law_1.
assert (U ∈ O/\z ∈ U).
split.
apply H1.
apply H3.
apply H0 in H4.
destruct H4.
destruct H4.
destruct H5.
exists x.
split.
apply H2.
split.
apply H4.
apply H6.
apply H5.
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

Theorem Open_Base_Law_3:forall X O B:Set,(Open_Set_Family O X/\Open_Base X O B)->(forall b1 b2 p:Set,(b1 ∈ B/\b2 ∈ B/\p ∈ (b1 ∩ b2))->exists b:Set,b ∈ B/\p ∈ b/\b ⊂ (b1 ∩ b2)).
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
assert ((b1 ∩ b2) ∈ O).
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
assert ((b1 ∩ b2) ∈ O/\p ∈ (b1 ∩ b2)).
split.
apply H4.
split.
apply H0.
apply H7.
apply H0.
apply H8.
apply H9.
apply H12 in H13.
destruct H13.
destruct H13.
destruct H14.
exists x0.
split.
apply H13.
split.
apply H14.
apply H15.
Qed.

Theorem Open_Base_Law_4:forall X B:Set,((Union_Set B=X)/\(forall b1 b2 p:Set,(b1 ∈ B/\b2 ∈ B/\p ∈ (b1 ∩ b2))->exists b:Set,b ∈ B/\p ∈ b/\b ⊂ (b1 ∩ b2)))->Open_Base X (Generating_Open_Bsse X B) B.
Proof.
intros.
destruct H.
assert (forall a:Set,a ∈ (Generating_Open_Bsse X B)<->exists b:Set,b ⊂ B/\a=Union_Set b).
intro.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
apply Power_Set_Law_1.
intro.
intro.
rewrite <- H.
destruct H1.
destruct H1.
rewrite -> H3 in H2.
apply Union_Set_Law_1.
apply Union_Set_Law_1 in H2.
destruct H2.
destruct H2.
exists x1.
split.
apply H1.
apply H2.
apply H4.
split.

intro.
intro.
apply H1.
exists (Single_Set z).
split.
intro.
intro.
apply Single_Set_Law_1 in H3.
rewrite -> H3.
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1.
exists z.
split.
apply Single_Set_Law_1.
split.
apply H3.
intro.
apply Union_Set_Law_1 in H3.
destruct H3.
destruct H3.
apply Single_Set_Law_1 in H3.
rewrite <- H3.
apply H4.

intros.
apply H1 in H2.
destruct H2.
destruct H2.
exists x.
split.
apply H2.
rewrite -> H3.
split.
Qed.

Theorem Open_Base_Law_5:forall X B:Set,((Union_Set B=X)/\(forall b1 b2 p:Set,(b1 ∈ B/\b2 ∈ B/\p ∈ (b1 ∩ b2))->exists b:Set,b ∈ B/\p ∈ b/\b ⊂ (b1 ∩ b2)))->Open_Set_Family (Generating_Open_Bsse X B) X.
Proof.
intros.
destruct H.
assert (forall a:Set,a ∈ (Generating_Open_Bsse X B)<->exists b:Set,b ⊂ B/\a=Union_Set b).
intro.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
apply Power_Set_Law_1.
intro.
intro.
rewrite <- H.
destruct H1.
destruct H1.
rewrite -> H3 in H2.
apply Union_Set_Law_1.
apply Union_Set_Law_1 in H2.
destruct H2.
destruct H2.
exists x1.
split.
apply H1.
apply H2.
apply H4.
split.

intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply H1 in H2.
destruct H2.
destruct H2.
rewrite <- H.
rewrite -> H4 in H3.
apply Union_Set_Law_1.
apply Union_Set_Law_1 in H3.
destruct H3.
destruct H3.
exists x0.
split.
apply H2.
apply H3.
apply H5.
split.

apply H1.
exists (∅).
split.
intro.
intro.
destruct (Definition_of_Empty_Set z).
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
destruct (Definition_of_Empty_Set z).
apply H2.
intro.
apply Union_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct (Definition_of_Empty_Set x).
apply H2.
split.

apply H1.
exists B.
split.
intro.
intro.
apply H2.
rewrite -> H.
split.
split.

intros.
destruct H2.
apply H1 in H2.
apply H1 in H3.
destruct H2.
destruct H2.
destruct H3.
destruct H3.
apply H1.
exists (Prop_Set (fun b0=>b0 ∈ B/\exists b1 b2:Set,b1 ∈ x0/\b2 ∈ x1/\b0 ⊂ (b1 ∩ b2))).
assert (forall a:Set,a ∈ (Prop_Set (fun b0=>b0 ∈ B/\exists b1 b2:Set,b1 ∈ x0/\b2 ∈ x1/\b0 ⊂ (b1 ∩ b2)))<->a ∈ B/\exists b1 b2:Set,b1 ∈ x0/\b2 ∈ x1/\a ⊂ (b1 ∩ b2)).
intro.
apply Prop_Set_Law_1.
exists B.
intros.
destruct H6.
apply H6.
split.
intro.
intro.
apply H6 in H7.
destruct H7.
apply H7.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1.
apply Pair_Meet_Set_Law_1 in H7.
destruct H7.
rewrite -> H4 in H7.
rewrite -> H5 in H8.
apply Union_Set_Law_1 in H7.
apply Union_Set_Law_1 in H8.
destruct H7.
destruct H7.
destruct H8.
destruct H8.
assert (x2 ∈ B/\x3 ∈ B/\z ∈ (x2 ∩ x3)).
split.
apply H2.
apply H7.
split.
apply H3.
apply H8.
apply Pair_Meet_Set_Law_1.
split.
apply H9.
apply H10.
apply H0 in H11.
destruct H11.
destruct H11.
destruct H12.
exists x4.
split.
apply H6.
split.
apply H11.
exists x2.
exists x3.
split.
apply H7.
split.
apply H8.
apply H13.
apply H12.
intro.
apply Union_Set_Law_1 in H7.
destruct H7.
destruct H7.
apply Pair_Meet_Set_Law_1.
apply H6 in H7.
destruct H7.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
apply H11 in H8.
apply Pair_Meet_Set_Law_1 in H8.
destruct H8.
split.
rewrite -> H4.
apply Union_Set_Law_1.
exists x3.
split.
apply H9.
apply H8.
rewrite -> H5.
apply Union_Set_Law_1.
exists x4.
split.
apply H10.
apply H12.

intros.
destruct H2.
apply H1.
exists (Union_Set (Prop_Set (fun b=>exists a:Set,b ⊂ B/\a=Union_Set b/\a ∈ B))).
assert (forall A:Set,A ∈ (Prop_Set (fun b=>exists a:Set,b ⊂ B/\a=Union_Set b/\a ∈ B))<->exists a:Set,A ⊂ B/\a=Union_Set A/\a ∈ B).
intro.
apply Prop_Set_Law_1.
exists (Power_Set B).
intros.
destruct H4.
destruct H4.
apply  Power_Set_Law_1.
apply H4.
split.
intro.
intro.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply H4 in H5.
destruct H5.
destruct H5.
apply H5.
apply H6.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply H2 in H5.
apply H1 in H5.
destruct H5.
destruct H5.
rewrite -> H7 in H6.
apply Union_Set_Law_1 in H6.
destruct H6.
destruct H6.


Qed.



(*内部*)
Definition Interior_Set(x O:Set):=Union_Set (Prop_Set (fun y=>y ∈ O/\y ⊂ x)).

Theorem Interior_Set_Law_1:forall x O X:Set,(Open_Set_Family O X/\x ⊂ X)->((Interior_Set x O) ∈ O).
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
apply (Prop_Set_Law_1 (fun y :Set=>y ∈ O/\y ⊂ x)) in H5.
destruct H5.
apply H5.
exists O.
intros.
destruct H7.
apply H7.
apply Empty_Set_Law_1.
exists (∅).
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

Theorem Interior_Set_Law_2:forall x O X:Set,(Open_Set_Family O X/\x ⊂ X)->((Interior_Set x O) ⊂ x).
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
apply (Prop_Set_Law_1 (fun y :Set=>y ∈ O/\y ⊂ x)) in H5.
destruct H5.
apply H7.
apply H6.
exists O.
intros.
destruct H8.
apply H8.
Qed.

Theorem Interior_Set_Law_3:forall x O X:Set,(Open_Set_Family O X/\x ⊂ X)->(x ∈ O<->x=Interior_Set x O).
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
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ O/\y ⊂ x)) in H6.
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
Definition Closure_Set(x C:Set):=Meet_Set (Prop_Set (fun y=>y ∈ C/\x ⊂ y)).

Theorem Closure_Set_Law_1:forall x C X:Set,(Close_Set_Family C X/\x ⊂ X)->((Closure_Set x C) ∈ C).
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
apply (Prop_Set_Law_1 (fun y :Set=>y ∈ C/\x ⊂ y)) in H5.
destruct H5.
apply H5.
exists C.
intros.
destruct H7.
apply H7.
apply Empty_Set_Law_1.
exists X.
apply (Prop_Set_Law_1 (fun y :Set=>y ∈ C/\x ⊂ y)).
exists C.
intros.
destruct H5.
apply H5.
split.
apply H2.
apply H0.
Qed.

Theorem Closure_Set_Law_2:forall x C X:Set,(Close_Set_Family C X/\x ⊂ X)->(x ⊂ (Closure_Set x C)).
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
apply (Prop_Set_Law_1 (fun y :Set=>y ∈ C/\x ⊂ y)) in H6.
destruct H6.
apply H7.
apply H5.
exists C.
intros.
destruct H8.
apply H8.
Qed.

Theorem Closure_Set_Law_3:forall x C X:Set,(Close_Set_Family C X/\x ⊂ X)->(x ∈ C<->x=Closure_Set x C).
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
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ C/\x ⊂ y)) in H7.
destruct H7.
apply H8.
apply H6.
exists C.
intros.
destruct H9.
apply H9.
intro.
unfold Closure_Set in H6.
assert (forall A:Set,A ∈ (Prop_Set (fun y:Set=>y ∈ C/\x ⊂ y))->z ∈ A).
apply Meet_Set_Law_1.
apply Empty_Set_Law_1.
exists x.
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ C/\x ⊂ y)).
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
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ C/\x ⊂ y)).
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
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ C/\x ⊂ y)) in H6.
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
apply (Prop_Set_Law_1 (fun y:Set=>y ∈ C/\x ⊂ y)).
exists C.
intros.
destruct H6.
apply H6.
split.
apply H2.
apply H0.
Qed.



(*連結空間*)
Definition Connected_Space(O X:Set):=Open_Set_Family O X/\(~(exists A B:Set,~A=∅/\~B=∅/\A ∈ O/\B ∈ O/\Pair_Union_Set A B=X/\A ∩ B=∅)).

Theorem Connected_Space_Law_1:forall O X:Set,Connected_Space O X<->Open_Set_Family O X/\(~exists A B:Set,~A=∅/\~B=∅/\A ∈ O/\B ∈ O/\(Complement_Set X A) ∪ (Complement_Set X B)=X/\(Complement_Set X A) ∩ (Complement_Set X B)=∅).
Proof.
intros.
split.

intros.
split.
destruct H.
apply H.
destruct H.
intro.
destruct H0.
destruct H1.
destruct H0.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
exists x.
exists x0.
split.
apply H0.
split.
apply H1.
split.
apply H2.
split.
apply H3.
split.
assert ((Complement_Set X (x ∪ x0))=(Complement_Set X X)).
rewrite -> Complement_Set_Law_2.
rewrite -> De_Morgans_Law_2.
apply H5.
assert ((Complement_Set X (Complement_Set X (x ∪ x0)))=(Complement_Set X (Complement_Set X X))).
rewrite -> H6.
split.
rewrite -> Complement_Set_Law_2 in H7.
rewrite <- Complement_Set_Law_3 in H7.
rewrite <- H7.
symmetry.
apply Complement_Set_Law_4.
intro.
intro.
apply Pair_Union_Set_Law_1 in H8.
destruct H8.
destruct H.
apply H in H2.
apply Power_Set_Law_1 in H2.
apply H2.
apply H8.
destruct H.
apply H in H3.
apply Power_Set_Law_1 in H3.
apply H3.
apply H8.
assert ((Complement_Set X (x ∩ x0))=X).
rewrite <- De_Morgans_Law_1 in H4.
apply H4.
assert (Complement_Set X ((Complement_Set X x) ∪ (Complement_Set X x0))=∅).
rewrite <- (Complement_Set_Law_2 X).
rewrite -> H4.
split.
rewrite <- H7.
rewrite <- De_Morgans_Law_1.
symmetry.
apply Complement_Set_Law_4.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H8.
destruct H8.
destruct H.
apply H in H2.
apply Power_Set_Law_1 in H2.
apply H2 in H8.
apply H8.

split.
destruct H.
apply H.
intro.
destruct H.
destruct H1.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
exists x.
exists x0.
split.
apply H0.
split.
apply H1.
split.
apply H2.
split.
apply H3.
split.
rewrite <- De_Morgans_Law_1.
rewrite -> H5.
symmetry.
apply Complement_Set_Law_3.
rewrite <- De_Morgans_Law_2.
rewrite -> H4.
apply Complement_Set_Law_2.
Qed.

Theorem  Connected_Space_Law_2:forall O X:Set,Connected_Space O X<->Open_Set_Family O X/\(forall x:Set,(x ∈ O/\(Complement_Set X x) ∈ O)->(x=∅\/x=X)).
Proof.
intros.
split.

intro.
destruct H.
split.
apply H.
intros.
assert (forall A B:Set,~(~A=∅/\~B=∅/\A ∈ O/\B ∈ O/\A ∪ B=X/\A ∩ B=∅)).
intro.
apply Prop_Law_4.
intro.
apply H0.
destruct H2.
exists A.
exists x0.
apply H2.
specialize (H2 x).
specialize (H2 ((Complement_Set X x))).
assert (~(~x=∅/\~Complement_Set X x=∅)).
intro.
destruct H2.
destruct H3.
split.
apply H2.
split.
apply H3.
destruct H1.
split.
apply H1.
split.
apply H4.
split.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Union_Set_Law_1 in H5.
destruct H5.
destruct H.
apply H in H1.
apply Power_Set_Law_1 in H1.
apply H1.
apply H5.
apply Complement_Set_Law_1 in H5.
destruct H5.
apply H5.
intro.
apply Pair_Union_Set_Law_1.
destruct (Law_of_Excluded_Middle (z ∈ x)).
left.
apply H6.
right.
apply Complement_Set_Law_1.
split.
apply H5.
apply H6.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1 in H5.
destruct H5.
apply Complement_Set_Law_1 in H6.
destruct H6.
destruct H7.
apply H5.
intro.
destruct (Definition_of_Empty_Set z).
apply H5.
apply Prop_Law_7 in H3.
destruct H3.
left.
apply Prop_Law_3.
apply H3.
right.
destruct H1.
destruct H.
apply H in H1.
apply Power_Set_Law_1 in H1.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply H1.
apply H6.
intro.
apply Prop_Law_3 in H3.
destruct (Law_of_Excluded_Middle (z ∈ x)).
apply H7.
destruct (Definition_of_Empty_Set z).
rewrite <- H3.
apply Complement_Set_Law_1.
split.
apply H6.
apply H7.

split.
destruct H.
apply H.
destruct H.
intro.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
assert (x ∈ O/\(Complement_Set X x) ∈ O).
split.
apply H3.
assert ((Complement_Set X x)=x0).
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H7.
destruct H7.
rewrite <- H5 in H7.
apply Pair_Union_Set_Law_1 in H7.
destruct H7.
destruct H8.
apply H7.
apply H7.
intro.
apply Complement_Set_Law_1.
split.
rewrite <- H5.
apply Pair_Union_Set_Law_1.
right.
apply H7.
intro.
destruct (Definition_of_Empty_Set z).
rewrite <- H6.
apply Pair_Meet_Set_Law_1.
split.
apply H8.
apply H7.
rewrite -> H7.
apply H4.
apply H0 in H7.
destruct H7.
destruct H1.
apply H7.
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
rewrite <- H6.
apply Pair_Meet_Set_Law_1.
split.
rewrite -> H7.
destruct H.
apply H in H4.
apply Power_Set_Law_1 in H4.
apply H4.
apply H8.
apply H8.
intro.
destruct (Definition_of_Empty_Set z).
apply H8.
Qed.



(*相対位相*)
Definition Sub_Set_Open_Set_Family(O Y X:Set):=Prop_Set (fun o_y=>exists o:Set,o ∈ O/\(o_y=Y ∩ o)).

Theorem Sub_Set_Open_Set_Family_Law_1:forall O X Y:Set,(Open_Set_Family O X/\Y ⊂ X)->(Open_Set_Family (Sub_Set_Open_Set_Family O Y X) Y).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.

assert (forall z:Set,z ∈ (Prop_Set (fun o_y=>exists o:Set,o ∈ O/\(o_y=Y ∩ o)))<->exists o:Set,o ∈ O/\(z=Y ∩ o)).
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
exists (∅).
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
exists (x0 ∩ x1).
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
destruct H6.
exists (Union_Set (Prop_Set (fun a=>exists U:Set,U=Y ∩ a/\U ∈ x/\a ∈ O))).
assert (forall A:Set,A ∈ (Prop_Set (fun a=>exists U:Set,U=Y ∩ a/\U ∈ x/\a ∈ O))<->exists U:Set,U=Y ∩ A/\U ∈ x/\A ∈ O).
intros.
apply Prop_Set_Law_1.
exists O.
intros.
destruct H8.
destruct H8.
destruct H9.
apply H10.
split.
apply H4.
split.
intro.
intro.
apply H8 in H9.
destruct H9.
destruct H9.
destruct H10.
apply H11.
apply Empty_Set_Law_1.
apply Empty_Set_Law_1 in H7.
destruct H7.
assert (x0 ∈ x).
apply H7.
apply H6 in H7.
apply H5 in H7.
destruct H7.
destruct H7.
exists x1.
apply H8.
exists x0.
split.
apply H10.
split.
apply H9.
apply H7.


apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1.
apply Union_Set_Law_1 in H9.
destruct H9.
destruct H9.
split.
apply H6 in H9.
apply H5 in H9.
destruct H9.
destruct H9.
rewrite -> H11 in H10.
apply Pair_Meet_Set_Law_1 in H10.
destruct H10.
apply H10.
apply Union_Set_Law_1.
assert (x0 ∈ x).
apply H9.
apply H6 in H9.
apply H5 in H9.
destruct H9.
destruct H9.
exists x1.
split.
apply H8.
exists x0.
split.
apply H12.
split.
apply H11.
apply H9.
rewrite -> H12 in H10.
apply Pair_Meet_Set_Law_1 in H10.
destruct H10.
apply H13.
intros.
apply Union_Set_Law_1.
apply Pair_Meet_Set_Law_1 in H9.
destruct H9.
apply Union_Set_Law_1 in H10.
destruct H10.
destruct H10.
apply H8 in H10.
destruct H10.
destruct H10.
destruct H12.
exists x1.
split.
apply H12.
rewrite -> H10.
apply Pair_Meet_Set_Law_1.
split.
apply H9.
apply H11.
Qed.





