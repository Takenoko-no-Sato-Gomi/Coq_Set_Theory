Require Export Set_Theory_Basic.
Require Export Set_Theory_Map.



(*開集合系、閉集合系*)
Definition Open_Set_Family(O X:Set):=(O ⊂ (Power_Set X))/\(∅ ∈ O)/\(X ∈ O)/\(forall x y:Set,(x ∈ O/\y ∈ O)->(x ∩ y) ∈ O)/\(forall x:Set,(x ⊂ O/\~x=∅)->(Union_Set x) ∈ O).

Definition Close_Set_Family(C X:Set):=(C ⊂ (Power_Set X))/\(∅ ∈ C)/\(X ∈ C)/\(forall x y:Set,(x ∈ C/\y ∈ C)->(x ∪ y) ∈ C)/\(forall x:Set,(x ⊂ C/\~x=∅)->(Meet_Set x) ∈ C).



Theorem Open_Set_Family_Law_1:forall A O X:Set,Open_Set_Family O X/\A ∈ O->A ⊂ X.
Proof.
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
apply H.
apply H0.
Qed.

Theorem Open_Set_Family_Law_2:forall O X:Set,Open_Set_Family O X->∅ ∈ O.
Proof.
intros.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Open_Set_Family_Law_3:forall O X:Set,Open_Set_Family O X->X ∈ O.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply H1.
Qed.

Theorem Open_Set_Family_Law_4:forall O X A1 A2:Set,Open_Set_Family O X/\A1 ∈ O/\A2 ∈ O->(A1 ∩ A2) ∈ O.
Proof.
intros.
destruct H.
destruct H0.
destruct H.
destruct H2.
destruct H3.
destruct H4.
apply H4.
split.
apply H0.
apply H1.
Qed.

Theorem Open_Set_Family_Law_5:forall O X A0:Set,Open_Set_Family O X/\A0 ⊂ O/\~A0=∅->(Union_Set A0) ∈ O.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
apply H4.
apply H0.
Qed.



Theorem Close_Set_Family_Law_1:forall A C X:Set,Close_Set_Family C X/\A ∈ C->A ⊂ X.
Proof.
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
apply H.
apply H0.
Qed.

Theorem Close_Set_Family_Law_2:forall C X:Set,Close_Set_Family C X->∅ ∈ C.
Proof.
intros.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Close_Set_Family_Law_3:forall C X:Set,Close_Set_Family C X->X ∈ C.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply H1.
Qed.

Theorem Close_Set_Family_Law_4:forall C X A1 A2:Set,Close_Set_Family C X/\A1 ∈ C/\A2 ∈ C->(A1 ∪ A2) ∈ C.
Proof.
intros.
destruct H.
destruct H0.
destruct H.
destruct H2.
destruct H3.
destruct H4.
apply H4.
split.
apply H0.
apply H1.
Qed.

Theorem Close_Set_Family_Law_5:forall C X A0:Set,Close_Set_Family C X/\A0 ⊂ C/\~A0=∅->(Meet_Set A0) ∈ C.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
apply H4.
apply H0.
Qed.



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



(*開基、生成された開集合系*)
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
exists (Union_Set (Prop_Set (fun B0=>B0 ⊂ B/\exists a:Set,a ∈ x/\a=Union_Set B0))).
assert (forall A:Set,A ∈ (Prop_Set (fun B0=>B0 ⊂ B/\exists a:Set,a ∈ x/\a=Union_Set B0))<->A ⊂ B/\exists a:Set,a ∈ x/\a=Union_Set A).
intro.
apply Prop_Set_Law_1.
exists (Power_Set B).
intros.
destruct H4.
apply Power_Set_Law_1.
apply H4.
split.
intro.
intro.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply H4 in H5.
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
assert (x0 ∈ x).
apply H5.
apply H2 in H5.
apply H1 in H5.
destruct H5.
destruct H5.
rewrite -> H8 in H6.
apply Union_Set_Law_1 in H6.
destruct H6.
destruct H6.
exists x2.
split.
apply Union_Set_Law_1.
exists x1.
split.
apply H4.
split.
apply H5.
exists x0.
split.
apply H7.
apply H8.
apply H6.
apply H9.
intros.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply Union_Set_Law_1 in H5.
destruct H5.
destruct H5.
apply H4 in H5.
destruct H5.
destruct H8.
destruct H8.
apply Union_Set_Law_1.
exists x2.
split.
apply H8.
rewrite -> H9.
apply Union_Set_Law_1.
exists x0.
split.
apply H7.
apply H6.
Qed.



(*内部*)
Definition Interior_Set(A O X:Set):=Union_Set (Prop_Set (fun y=>y ∈ O/\y ⊂ A)).

Theorem Interior_Set_Law_1:forall A O X x:Set,x ∈ (Interior_Set A O X)<->exists A0:Set,A0 ∈ O/\A0 ⊂ A/\x ∈ A0.
Proof.
intros.
split.

intro.
apply Union_Set_Law_1 in H.
destruct H.
destruct H.
apply (Prop_Set_Law_1 (fun y=>y ∈ O/\y ⊂ A)) in H.
exists x0.
destruct H.
split.
apply H.
split.
apply H1.
apply H0.
exists O.
intros.
destruct H2.
apply H2.

intros.
destruct H.
destruct H.
destruct H0.
apply Union_Set_Law_1.
exists x0.
split.
apply (Prop_Set_Law_1 (fun y=>y ∈ O/\y ⊂ A)).
exists O.
intros.
destruct H2.
apply H2.
split.
apply H.
apply H0.
apply H1.
Qed.

Theorem Interior_Set_Law_2:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->((Interior_Set A O X) ∈ O).
Proof.
intros.
destruct H.
apply (Open_Set_Family_Law_5 O X (Prop_Set (fun y=>y ∈ O/\y ⊂ A))).
split.
apply H.
intros.
split.
intros.
intro.
intro.
apply (Prop_Set_Law_1 (fun y : Set => y ∈ O /\ y ⊂ A)).
exists O.
intros.
destruct H2.
apply H2.
apply (Prop_Set_Law_1 (fun y : Set => y ∈ O /\ y ⊂ A)).
exists O.
intros.
destruct H2.
apply H2.
apply (Prop_Set_Law_1 (fun y : Set => y ∈ O /\ y ⊂ A)).
exists O.
intros.
destruct H2.
apply H2.
apply H1.
intro.
apply (Definition_of_Empty_Set (∅)).
rewrite <- H1.
apply (Prop_Set_Law_1 (fun y : Set => y ∈ O /\ y ⊂ A)).
exists O.
intros.
destruct H2.
apply H2.
rewrite -> H1.
split.
apply (Open_Set_Family_Law_2 O X).
apply H.
intro.
intro.
destruct (Definition_of_Empty_Set z).
apply H2.
Qed.

Theorem Interior_Set_Law_3:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->((Interior_Set A O X) ⊂ A).
Proof.
intros.
destruct H.
intro.
intro.
apply Interior_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H2.
apply H2.
apply H3.
Qed.

Theorem  Interior_Set_Law_4:forall A O X:Set,(Open_Set_Family O X/\A ∈ O)->A=Interior_Set A O X.
Proof.
intros.
destruct H.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Interior_Set_Law_1.
exists A.
split.
apply H0.
split.
intro.
intro.
apply H2.
apply H1.
intro.
apply (Interior_Set_Law_3 A O X).
split.
apply H.
apply (Open_Set_Family_Law_1 A O X).
split.
apply H.
apply H0.
apply H1.
Qed.

Theorem Interior_Set_Law_5:forall A O X:Set,(Open_Set_Family O X/\A=Interior_Set A O X/\A ⊂ X)->A ∈ O.
Proof.
intros.
destruct H.
destruct H0.
rewrite -> H0.
apply Interior_Set_Law_2.
split.
apply H.
apply H1.
Qed.

Theorem Interior_Set_Law_6:forall O X:Set,Open_Set_Family O X->(Interior_Set X O X)=X.
Proof.
intros.
apply Theorem_of_Extensionality.
intros.
split.

intro.
apply (Interior_Set_Law_3 X O X).
split.
apply H.
intro.
intro.
apply H1.
apply H0.

intro.
apply Interior_Set_Law_1.
exists X.
split.
apply Open_Set_Family_Law_3.
apply H.
split.
intro.
intro.
apply H1.
apply H0.
Qed.

Theorem Interior_Set_Law_7:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->(Interior_Set (Interior_Set A O X) O X)=(Interior_Set A O X).
Proof.
intros.
destruct H.
rewrite <- (Interior_Set_Law_4 (Interior_Set A O X) O X).
split.
split.
apply H.
apply Interior_Set_Law_2.
split.
apply H.
apply H0.
Qed.

Theorem Interior_Set_Law_8:forall A B O X:Set,(Open_Set_Family O X/\A ⊂ X/\B ⊂ X)->Interior_Set (A ∩ B) O X=(Interior_Set A O X) ∩ (Interior_Set B O X).
Proof.
intros.
destruct H.
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Pair_Meet_Set_Law_1.
apply Interior_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct H3.
split.
apply Interior_Set_Law_1.
exists x.
split.
apply H2.
split.
intro.
intro.
apply H3 in H5.
apply Pair_Meet_Set_Law_1 in H5.
destruct H5.
apply H5.
apply H4.
apply Interior_Set_Law_1.
exists x.
split.
apply H2.
split.
intro.
intro.
apply H3 in H5.
apply Pair_Meet_Set_Law_1 in H5.
destruct H5.
apply H6.
apply H4.

intro.
apply Interior_Set_Law_1.
apply Pair_Meet_Set_Law_1 in H2.
destruct H2.
apply Interior_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct H4.
apply Interior_Set_Law_1 in H3.
destruct H3.
destruct H3.
destruct H6.
exists (x ∩ x0).
split.
apply (Open_Set_Family_Law_4 O X x x0).
split.
apply H.
split.
apply H2.
apply H3.
split.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H8.
apply Pair_Meet_Set_Law_1.
destruct H8.
split.
apply H4.
apply H8.
apply H6.
apply H9.
apply Pair_Meet_Set_Law_1.
split.
apply H5.
apply H7.
Qed.



(*閉包*)
Definition Closure_Set(A O X:Set):=Meet_Set (Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)).

Theorem Closure_Set_Law_1:forall A O X x A0:Set,Open_Set_Family O X/\A ⊂ X/\x ∈ (Closure_Set A O X)/\A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O->x ∈ A0.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.

assert (~∅=(Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
intro.
apply (Definition_of_Empty_Set X).
rewrite -> H5.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H6.
destruct H7.
apply Power_Set_Law_1.
apply H7.
split.
intro.
intro.
apply H3.
apply H2.
apply H6.
split.
intro.
intro.
apply H6.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.

apply (Meet_Set_Law_2 (Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) A0 x).
split.
apply H1.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H6.
destruct H7.
apply Power_Set_Law_1.
apply H7.
split.
apply H2.
split.
apply H3.
apply H4.
Qed.

Theorem Closure_Set_Law_2:forall A O X x:Set,Open_Set_Family O X/\A ⊂ X/\(forall A0:Set,A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O->x ∈ A0)->x ∈ (Closure_Set A O X).
Proof.
intros.
destruct H.
destruct H0.

assert (~∅=(Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
intro.
apply (Definition_of_Empty_Set X).
rewrite -> H2.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H3.
destruct H4.
apply Power_Set_Law_1.
apply H4.
split.
apply H0.
split.
intro.
intro.
apply H3.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.

apply Meet_Set_Law_3.
split.
intro.
apply H2.
symmetry.
apply H3.
intros.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) in H3.
apply H1.
apply H3.
exists (Power_Set X).
intros.
destruct H5.
destruct H6.
apply Power_Set_Law_1.
apply H6.
Qed.

Theorem Closure_Set_Law_3:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->(Complement_Set X (Closure_Set A O X) ∈ O).
Proof.
intros.
destruct H.

assert (~∅=(Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
intro.
apply (Definition_of_Empty_Set X).
rewrite -> H1.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H2.
destruct H3.
apply Power_Set_Law_1.
apply H3.
split.
apply H0.
split.
intro.
intro.
apply H2.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.

unfold Closure_Set.
rewrite -> (De_Morgans_Law_4 (Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) X).
apply (Open_Set_Family_Law_5 O X (Prop_Set (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)))).
split.
apply H.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))) in H2.
destruct H2.
destruct H2.
rewrite -> H2.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) in H3.
destruct H3.
destruct H4.
apply H5.
exists (Power_Set X).
intros.
destruct H5.
destruct H6.
apply Power_Set_Law_1.
apply H6.
exists (Power_Set X).
intros.
destruct H4.
destruct H4.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) in H5.
destruct H5.
destruct H6.
apply Power_Set_Law_1.
rewrite -> H4.
intro.
intro.
apply Complement_Set_Law_1 in H8.
destruct H8.
apply H8.
exists (Power_Set X).
intros.
destruct H7.
destruct H8.
apply Power_Set_Law_1.
apply H8.

intro.
apply (Definition_of_Empty_Set (∅)).
rewrite <- H2.
apply (Prop_Set_Law_1 (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
exists (Power_Set X).
intros.
destruct H3.
destruct H3.
rewrite -> H3.
apply Power_Set_Law_1.
intro.
intro.
apply Complement_Set_Law_1 in H5.
destruct H5.
apply H5.
rewrite -> H2.
exists X.
split.
rewrite -> Complement_Set_Law_2.
split.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H3.
destruct H4.
apply Power_Set_Law_1.
apply H4.
split.
apply H0.
split.
intro.
intro.
apply H3.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
intro.
apply H1.
symmetry.
apply H2.
Qed.

Theorem Closure_Set_Law_4:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->(A ⊂ (Closure_Set A O X)).
Proof.
intros.
destruct H.
intro.
intro.
apply (Closure_Set_Law_2 A O X z).
split.
apply H.
split.
apply H0.
intros.
destruct H2.
destruct H3.
apply H2.
apply H1.
Qed.

Theorem  Closure_Set_Law_5:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X/\(Complement_Set X A) ∈ O)->A=Closure_Set A O X.
Proof.
intros.
destruct H.
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Closure_Set_Law_4.
split.
apply H.
apply H0.
apply H2.

intro.
apply (Closure_Set_Law_1 A O X z A).
split.
apply H.
split.
apply H0.
split.
apply H2.
split.
intro.
intro.
apply H3.
split.
apply H0.
apply H1.
Qed.

Theorem Closure_Set_Law_6:forall A O X:Set,(Open_Set_Family O X/\A=Closure_Set A O X/\A ⊂ X)->(Complement_Set X A) ∈ O.
Proof.
intros.
destruct H.
destruct H0.

assert (~∅=(Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
intro.
apply (Definition_of_Empty_Set X).
rewrite -> H2.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H3.
destruct H4.
apply Power_Set_Law_1.
apply H4.
split.
apply H1.
split.
intro.
intro.
apply H3.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.

rewrite -> H0.
unfold Closure_Set.
rewrite -> (De_Morgans_Law_4 (Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) X).
apply (Open_Set_Family_Law_5 O X (Prop_Set (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)))).
split.
apply H.
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))) in H3.
destruct H3.
destruct H3.
rewrite -> H3.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) in H4.
destruct H4.
destruct H5.
apply H6.
exists (Power_Set X).
intros.
destruct H6.
destruct H7.
apply Power_Set_Law_1.
apply H7.
exists (Power_Set X).
intros.
destruct H5.
destruct H5.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)) in H6.
destruct H6.
destruct H7.
apply Power_Set_Law_1.
rewrite -> H5.
intro.
intro.
apply Complement_Set_Law_1 in H9.
destruct H9.
apply H9.
exists (Power_Set X).
intros.
destruct H8.
destruct H9.
apply Power_Set_Law_1.
apply H9.

intro.
apply (Definition_of_Empty_Set (∅)).
rewrite <- H3.
apply (Prop_Set_Law_1 (fun x=>exists y:Set,x=Complement_Set X y/\y ∈ Prop_Set (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O))).
exists (Power_Set X).
intros.
destruct H4.
destruct H4.
rewrite -> H4.
apply Power_Set_Law_1.
intro.
intro.
apply Complement_Set_Law_1 in H6.
destruct H6.
apply H6.
exists X.
rewrite -> H3.
split.
rewrite -> Complement_Set_Law_2.
split.
apply (Prop_Set_Law_1 (fun A0=>A ⊂ A0/\A0 ⊂ X/\Complement_Set X A0 ∈ O)).
exists (Power_Set X).
intros.
destruct H4.
destruct H5.
apply Power_Set_Law_1.
apply H5.
split.
apply H1.
split.
intro.
intro.
apply H4.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
intro.
apply H2.
symmetry.
apply H3.
Qed.

Theorem Closure_Set_Law_7:forall O X:Set,(Open_Set_Family O X)->Closure_Set (∅) O X=(∅).
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply (Closure_Set_Law_1 (∅) O X z (∅)).
split.
apply H.
split.
intro.
intro.
destruct (Definition_of_Empty_Set z0).
apply H1.
split.
apply H0.
split.
intro.
intro.
apply H1.
split.
intro.
intro.
destruct (Definition_of_Empty_Set z0).
apply H1.
rewrite <- Complement_Set_Law_3.
apply Open_Set_Family_Law_3.
apply H.

intro.
destruct (Definition_of_Empty_Set z).
apply H0.
Qed.

Theorem Closure_Set_Law_8:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->(Closure_Set (Closure_Set A O X) O X)=(Closure_Set A O X).
Proof.
intros.
destruct H.
rewrite <- (Closure_Set_Law_5 (Closure_Set A O X) O X).
split.
split.
apply H.
split.
intro.
intro.
apply (Closure_Set_Law_1 A O X z X).
split.
apply H.
split.
apply H0.
split.
apply H1.
split.
apply H0.
split.
intro.
intro.
apply H2.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
apply Closure_Set_Law_3.
split.
apply H.
apply H0.
Qed.

Theorem Closure_Set_Law_9:forall A B O X:Set,(Open_Set_Family O X/\A ⊂ X/\B ⊂ X)->Closure_Set (A ∪ B) O X=(Closure_Set A O X) ∪ (Closure_Set B O X).
Proof.
intros.
apply Theorem_of_Extensionality.
intros.
destruct H.
destruct H0.
split.

intro.
apply (Closure_Set_Law_1 (A ∪ B) O X z (Closure_Set A O X ∪ Closure_Set B O X)).
split.
apply H.
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H3.
destruct H3.
apply H0.
apply H3.
apply H1.
apply H3.
split.
apply H2.
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H3.
apply Pair_Union_Set_Law_1.
destruct H3.
left.
apply (Closure_Set_Law_4 A O X).
split.
apply H.
apply H0.
apply H3.
right.
apply (Closure_Set_Law_4 B O X).
split.
apply H.
apply H1.
apply H3.
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H3.
destruct H3.
apply (Closure_Set_Law_1 A O X z0 X).
split.
apply H.
split.
apply H0.
split.
apply H3.
split.
apply H0.
split.
intro.
intro.
apply H4.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
apply (Closure_Set_Law_1 B O X z0 X).
split.
apply H.
split.
apply H1.
split.
apply H3.
split.
apply H1.
split.
intro.
intro.
apply H4.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
rewrite -> (De_Morgans_Law_2 (Closure_Set A O X) (Closure_Set B O X) X).
apply (Open_Set_Family_Law_4 O X (Complement_Set X (Closure_Set A O X)) (Complement_Set X (Closure_Set B O X))).
split.
apply H.
split.
apply (Closure_Set_Law_3 A O X).
split.
apply H.
apply H0.
apply (Closure_Set_Law_3 B O X).
split.
apply H.
apply H1.

intro.
apply Pair_Union_Set_Law_1 in H2.
apply (Closure_Set_Law_2 (A ∪ B) O X z).
split.
apply H.
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H3.
destruct H3.
apply H0.
apply H3.
apply H1.
apply H3.
intros.
destruct H3.
destruct H4.
destruct H2.
apply (Closure_Set_Law_1 A O X z A0).
split.
apply H.
split.
apply H0.
split.
apply H2.
split.
intro.
intro.
apply H3.
apply Pair_Union_Set_Law_1.
left.
apply H6.
split.
intro.
intro.
apply H4.
apply H6.
apply H5.
apply (Closure_Set_Law_1 B O X z A0).
split.
apply H.
split.
apply H1.
split.
apply H2.
split.
intro.
intro.
apply H3.
apply Pair_Union_Set_Law_1.
right.
apply H6.
split.
apply H4.
apply H5.
Qed.



(*境界*)
Definition Border_Set(A O X:Set):=Complement_Set (Closure_Set A O X) (Interior_Set A O X).

Theorem Border_Set_Law_1:forall A O X x:Set,x ∈ (Border_Set A O X)<->x ∈ (Closure_Set A O X)/\~x ∈(Interior_Set A O X).
Proof.
intros.
split.
intro.

apply Complement_Set_Law_1 in H.
apply H.

intro.
apply Complement_Set_Law_1.
apply H.
Qed.

Theorem Border_Set_Law_2:forall A O X:Set,(Open_Set_Family O X/\A ⊂ X)->(Complement_Set X (Border_Set A O X) ∈ O).
Proof.
intros.
destruct H.

assert ((Border_Set A O X)=((Closure_Set A O X) ∩ (Complement_Set X (Interior_Set A O X)))).
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1.
apply Complement_Set_Law_1 in H1.
destruct H1.
split.
apply H1.
apply Complement_Set_Law_1.
split.
apply (Closure_Set_Law_1 A O X z X).
split.
apply H.
split.
apply H0.
split.
apply H1.
split.
apply H0.
split.
intro.
intro.
apply H3.
rewrite -> Complement_Set_Law_2.
apply (Open_Set_Family_Law_2 O X).
apply H.
apply H2.
intro.
apply Pair_Meet_Set_Law_1 in H1.
destruct H1.
apply Complement_Set_Law_1 in H2.
destruct H2.
apply Border_Set_Law_1.
split.
apply H1.
apply H3.

rewrite -> H1.
rewrite -> De_Morgans_Law_1.
rewrite -> Complement_Set_Law_4.
apply (Open_Set_Family_Law_5 O X (Pair_Set (Complement_Set X (Closure_Set A O X)) (Interior_Set A O X))).
split.
apply H.
split.
intro.
intro.
apply Pair_Set_Law_1 in H2.
destruct H2.
rewrite -> H2.
apply Closure_Set_Law_3.
split.
apply H.
apply H0.
rewrite -> H2.
apply Interior_Set_Law_2.
split.
apply H.
apply H0.
intro.
apply (Definition_of_Empty_Set (Complement_Set X (Closure_Set A O X))).
rewrite <- H2.
apply Pair_Set_Law_1.
left.
split.
intro.
intro.
apply H0.
apply (Interior_Set_Law_3 A O X).
split.
apply H.
apply H0.
apply H2.
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
Definition Sub_Set_Space(O Y X:Set):=Prop_Set (fun o_y=>exists o:Set,o ∈ O/\(o_y=Y ∩ o)).

Theorem Sub_Set_Space_Law_1:forall O X Y:Set,(Open_Set_Family O X/\Y ⊂ X)->(Open_Set_Family (Sub_Set_Space O Y X) Y).
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



(*連続写像*)
Definition Continuous_Map(f O1 X1 O2 X2:Set):=Map f X1 X2/\Open_Set_Family O1 X1/\Open_Set_Family O2 X2/\(forall U:Set,U ∈ O2->(Sub_Set_Map_Pull_Backe f X1 X2 U) ∈ O1).

Theorem Continuous_Map_Law_1:forall X O:Set,Open_Set_Family O X->Continuous_Map (Identify_Map X) O X O X.
Proof.
intros.
split.
apply Identify_Map_Law_4.
split.
apply H.
split.
apply H.
intros.

assert (Sub_Set_Map_Pull_Backe (Identify_Map X) X X U=U).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H1.
destruct H1.
destruct H2.
destruct H2.
rewrite -> H3 in H2.
rewrite <- (Identify_Map_Law_3 X z) in H2.
apply H2.
apply H1.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H1.
exists (Culculateion_Map (Identify_Map X) z).
split.
rewrite <- (Identify_Map_Law_3 X z).
apply H1.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H1.
split.

rewrite -> H1.
apply H0.
Qed.

Theorem Continuous_Map_Law_2:forall f1 f2 O1 X1 O2 X2 O3 X3:Set,Continuous_Map f1 O1 X1 O2 X2/\Continuous_Map f2 O2 X2 O3 X3->Continuous_Map (Composite_Map f1 f2) O1 X1 O3 X3.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H0.
destruct H4.
destruct H5.
split.
apply (Composite_Map_Law_1 f1 f2 X1 X2 X3).
split.
apply H.
apply H0.
split.
apply H1.
split.
apply H5.
intros.

assert (Sub_Set_Map_Pull_Backe (Composite_Map f1 f2) X1 X3 U=Sub_Set_Map_Pull_Backe f1 X1 X2 (Sub_Set_Map_Pull_Backe f2 X2 X3 U)).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H9.
destruct H9.
rewrite <- (Composite_Map_Law_2 f1 f2 z X1 X2 X3) in H10.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H8.
exists (Culculateion_Map f1 z).
split.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Map_Law_2 f1 X1 X2 z).
split.
apply H.
apply H8.
exists (Culculateion_Map f2 (Culculateion_Map f1 z)).
split.
rewrite <- H10.
apply H9.
split.
split.
split.
apply H.
split.
apply H0.
apply H8.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H9.
destruct H9.
apply Sub_Set_Map_Pull_Backe_Law_1 in H9.
destruct H9.
destruct H11.
destruct H11.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H8.
exists x0.
split.
apply H11.
rewrite <- (Composite_Map_Law_2 f1 f2 z X1 X2 X3).
rewrite <- H10.
apply H12.
split.
apply H.
split.
apply H0.
apply H8.
rewrite -> H8.
apply H3.
apply H6.
apply H7.
Qed.

Theorem Continuous_Map_Law_3:forall f O1 X1 O2 X2 U:Set,Continuous_Map f O1 X1 O2 X2/\(Complement_Set X2 U) ∈ O2->(Complement_Set X1 (Sub_Set_Map_Pull_Backe f X1 X2 U)) ∈ O1.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.

assert (Complement_Set X1 (Sub_Set_Map_Pull_Backe f X1 X2 U)=Sub_Set_Map_Pull_Backe f X1 X2 (Complement_Set X2 U)).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H4.
destruct H4.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H4.
exists (Culculateion_Map f z).
split.
apply Complement_Set_Law_1.
split.
apply (Map_Law_2 f X1 X2 z).
split.
apply H.
apply H4.
intro.
apply H5.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H4.
exists (Culculateion_Map f z).
split.
apply H6.
split.
split.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H4.
destruct H4.
destruct H5.
destruct H5.
apply Complement_Set_Law_1 in H5.
destruct H5.
apply Complement_Set_Law_1.
split.
apply H4.
intro.
apply H7.
apply Sub_Set_Map_Pull_Backe_Law_1 in H8.
destruct H8.
destruct H9.
destruct H9.
rewrite -> H6.
rewrite <- H10.
apply H9.

rewrite -> H4.
apply H3.
apply H0.
Qed.

Theorem Continuous_Map_Law_4:forall f O1 X1 O2 X2:Set,Map f X1 X2/\Open_Set_Family O1 X1/\Open_Set_Family O2 X2/\(forall U:Set,(Complement_Set X2 U) ∈ O2->(Complement_Set X1 (Sub_Set_Map_Pull_Backe f X1 X2 U)) ∈ O1)->Continuous_Map f O1 X1 O2 X2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H.
split.
apply H0.
split.
apply H1.

intros.
assert (Complement_Set X1 (Complement_Set X1 (Sub_Set_Map_Pull_Backe f X1 X2 U))=Complement_Set X1 (Sub_Set_Map_Pull_Backe f X1 X2 (Complement_Set X2 U))).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H4.
destruct H4.
apply Complement_Set_Law_1.
split.
apply H4.
intro.
apply H5.
apply Sub_Set_Map_Pull_Backe_Law_1 in H6.
destruct H6.
destruct H7.
destruct H7.
apply Complement_Set_Law_1 in H7.
destruct H7.
apply Complement_Set_Law_1.
split.
apply H4.
intro.
apply H9.
apply Sub_Set_Map_Pull_Backe_Law_1 in H10.
destruct H10.
destruct H11.
destruct H11.
rewrite -> H8.
rewrite <- H12.
apply H11.
intro.
apply Complement_Set_Law_1 in H4.
destruct H4.
apply Complement_Set_Law_1.
split.
apply H4.
intro.
apply H5.
apply Complement_Set_Law_1 in H6.
destruct H6.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H6.
exists (Culculateion_Map f z).
split.
apply Complement_Set_Law_1.
split.
apply (Map_Law_2 f X1 X2 z).
split.
apply H.
apply H4.
intro.
apply H7.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply H4.
exists (Culculateion_Map f z).
split.
apply H8.
split.
split.

rewrite <- (Complement_Set_Law_4 (Sub_Set_Map_Pull_Backe f X1 X2 U) X1).
rewrite -> H4.
apply H2.
rewrite -> (Complement_Set_Law_4 U X2).
apply H3.
apply (Open_Set_Family_Law_1 U O2 X2).
split.
apply H1.
apply H3.
intro.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H5.
destruct H5.
apply H5.
Qed.



Definition Homeomorphic_Map(f O1 X1 O2 X2:Set):=Bijective_Map f X1 X2/\Continuous_Map f O1 X1 O2 X2/\Continuous_Map (Inverse_Map f X1 X2) O2 X2 O1 X1.

Theorem Homeomorphic_Map_Law_1:forall X O:Set,Open_Set_Family O X->Homeomorphic_Map (Identify_Map X) O X O X.
Proof.
intros.
split.
apply Identify_Map_Law_2.
split.
apply Continuous_Map_Law_1.
apply H.
split.
apply Inverse_Map_Law_6.
apply Identify_Map_Law_2.
split.
apply H.
split.
apply H.
intros.

assert (Sub_Set_Map_Pull_Backe (Inverse_Map (Identify_Map X) X X) X X U=U).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1 in H1.
destruct H1.
destruct H2.
destruct H2.
assert (Culculateion_Map (Inverse_Map (Identify_Map X) X X) z=z).
assert (Culculateion_Map (Identify_Map X) x=Culculateion_Map (Identify_Map X) (Culculateion_Map (Inverse_Map (Identify_Map X) X X) z)).
rewrite <- H3.
split.
rewrite -> (Composite_Map_Law_2 (Inverse_Map (Identify_Map X) X X) (Identify_Map X) z X X X) in H4.
rewrite <- (Inverse_Map_Law_5 (Identify_Map X) X X) in H4.
rewrite <- (Identify_Map_Law_3 X x) in H4.
rewrite <- (Identify_Map_Law_3 X z) in H4.
rewrite <- H3.
apply H4.
apply H1.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H2.
apply Identify_Map_Law_2.
split.
apply Inverse_Map_Law_2.
apply Identify_Map_Law_2.
split.
apply Identify_Map_Law_4.
apply H1.
rewrite <- H4.
rewrite <- H3.
apply H2.
intro.
apply Sub_Set_Map_Pull_Backe_Law_1.
split.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H1.
exists (Culculateion_Map (Inverse_Map (Identify_Map X) X X) z).
split.
assert (Culculateion_Map (Inverse_Map (Identify_Map X) X X) z=).
assert (Culculateion_Map (Identify_Map X) z=Culculateion_Map (Identify_Map X) (Culculateion_Map (Inverse_Map (Identify_Map X) X X) z)).
rewrite -> (Composite_Map_Law_2 (Inverse_Map (Identify_Map X) X X) (Identify_Map X) z X X X).
rewrite <- (Inverse_Map_Law_5 (Identify_Map X) X X).
rewrite  <- (Identify_Map_Law_3 X z).
split.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H1.
apply Identify_Map_Law_2.
split.
apply Inverse_Map_Law_2.
apply Identify_Map_Law_2.
split.
apply Identify_Map_Law_4.
apply (Open_Set_Family_Law_1 U O X).
split.
apply H.
apply H0.
apply H1.
apply 
Qed.

Theorem Homeomorphic_Map_Law_2:forall f1 f2 O1 X1 O2 X2 O3 X3:Set,Homeomorphic_Map f1 O1 X1 O2 X2/\Homeomorphic_Map f2 O2 X2 O3 X3->Homeomorphic_Map (Composite_Map f1 f2) O1 X1 O3 X3.
Proof.

Qed.














