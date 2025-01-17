Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.



(*超限帰納法*)
Theorem Transfinite_Induction_1:forall p:Set->Prop,forall f X x:Set,(Well_Oredered_Relation f X/\(forall a:Set,a ∈ X/\(forall x0:Set,(x0∈ X/\Relation_Prop f x0 a/\~x0=a)->p x0)->p a)/\x ∈ X)->p x.
Proof.
intros.
destruct H.
destruct H0.

assert (forall a:Set,(a ∈ X->((Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) ⊂ (Prop_Set (fun x=>x ∈ X/\p x))))<->(forall x:Set,(a ∈ X/\x ∈ X/\Relation_Prop f x a/\~x=a)->p x)).
split.
intros.
destruct H3.
destruct H4.
apply H2 in H3.
assert (x0 ∈ (Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a))).
apply Prop_Set_Law_1.
exists X.
intros.
destruct H6.
apply H6.
split.
apply H4.
apply H5.
apply H3 in H6.
apply (Prop_Set_Law_1 (fun x=>x ∈ X/\p x)) in H6.
destruct H6.
apply H7.
exists X.
intros.
destruct H8.
apply H8.
intros.
intro.
intro.
apply (Prop_Set_Law_1 (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) in H4.
destruct H4.
assert (z ∈ X).
apply H4.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H7.
apply H7.
split.
apply H6.
apply H2.
split.
apply H3.
split.
apply H6.
apply H5.
exists X.
intros.
destruct H6.
apply H6.

assert (forall a:Set,(a ∈ X->( (Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) ⊂ (Prop_Set (fun x=>x ∈ X/\p x))))<->(a ∈ X->((Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) ∩ (Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x)))=∅))).
split.
intros.
apply Prop_Law_3.
intro.
apply Empty_Set_Law_1 in H5.
destruct H5.
apply Pair_Meet_Set_Law_1 in H5.
destruct H5.
apply Complement_Set_Law_1 in H6.
destruct H6.
apply H7.
apply H3 in H4.
apply H4 in H5.
apply H5.
intros.
intro.
intro.
apply H3 in H4.
apply Prop_Law_1 in H4.
assert (forall x:Set,~x ∈ ((Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) ∩ (Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x))))).
apply Prop_Law_4.
intro.
apply H4.
apply Empty_Set_Law_1.
apply H6.
specialize (H6 z).
assert ((~z ∈ (Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)))\/(~z ∈ (Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x))))).
apply Prop_Law_7.
intro.
apply H6.
apply Pair_Meet_Set_Law_1.
apply H7.
destruct H7.
destruct H7.
apply H5.
assert ((~z ∈ X)\/(~~z ∈ (Prop_Set (fun x=>x ∈ X/\p x)))).
apply Prop_Law_7.
intro.
apply H7.
apply Complement_Set_Law_1.
apply H8.
destruct H8.
apply (Prop_Set_Law_1 (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) in H5.
destruct H5.
destruct H8.
apply H5.
exists X.
intros.
destruct H10.
apply H10.
apply Prop_Law_3.
apply H8.

apply H0.
split.
apply H1.
intros.
destruct H4.
assert (X=(Prop_Set (fun x=>x ∈ X/\p x))).
assert (Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x))=∅).
apply Prop_Law_3.
intro.
assert ((Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x))) ⊂ X/\~(Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x)))=∅).
split.
intro.
intro.
apply Complement_Set_Law_1 in H7.
destruct H7.
apply H7.
apply H6.
destruct H.
apply H8 in H7.
destruct H7.
destruct H7.
apply Complement_Set_Law_1 in H7.
destruct H7.
assert ((~x1 ∈ X)\/(~p x1)).
apply Prop_Law_7.
intro.
apply H10.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H12.
apply H12.
apply H11.
destruct H11.
apply H11.
apply H7.
apply H11.
assert (x1 ∈ X->((Prop_Set (fun x=>x ∈ X/\Relation_Prop f x x1/\~x=x1)) ∩ (Complement_Set X (Prop_Set (fun x=>x ∈ X/\p x))))=∅).
intro.
apply Prop_Law_3.
intro.
apply Empty_Set_Law_1 in H13.
destruct H13.
apply Pair_Meet_Set_Law_1 in H13.
destruct H13.
apply (Prop_Set_Law_1 (fun x=>x ∈ X/\Relation_Prop f x x1/\~x=x1)) in H13.
destruct H13.
destruct H15.
apply H16.
destruct H.
destruct H.
destruct H18.
destruct H19.
apply H20.
split.
apply H15.
apply H9.
apply H14.
exists X.
intros.
destruct H16.
apply H16.
apply H0.
split.
apply H7.
assert (forall x:Set,x1 ∈ X/\x ∈ X/\Relation_Prop f x x1/\~x=x1->p x).
apply H2.
apply H3.
apply H12.
intros.
apply H13.
split.
apply H7.
apply H14.
assert (X=Prop_Set (fun a=>a ∈ X/\p a)).
apply Theorem_of_Extensionality.
intro.
split.
intro.
destruct (Law_of_Excluded_Middle (z ∈ Prop_Set (fun a=>a ∈ X/\p a))).
apply H8.
destruct (Definition_of_Empty_Set z).
rewrite <- H6.
apply Complement_Set_Law_1.
split.
apply H7.
apply H8.
intro.
apply (Prop_Set_Law_1 (fun a=>a ∈ X/\p a)).
exists X.
intros.
destruct H8.
apply H8.
apply H7.
apply H7.
rewrite ->H6 in H4.
apply (Prop_Set_Law_1 (fun a=>a ∈ X/\p a)) in H4.
destruct H4.
apply H7.
exists X.
intros.
destruct H8.
apply H8.
Qed.

Theorem Transfinite_Induction_2:forall p:Set->Prop,forall f X x:Set,(Narrow_Well_Oredered_Relation f X/\(forall a:Set,(a ∈ X/\forall x0:Set,(x0 ∈ X/\Relation_Prop f x0 a->p x0))->p a)/\x ∈ X)->p x.
Proof.
intros.
destruct H.
destruct H0.
apply (Transfinite_Induction_1 p (Prop_Set (fun a=>a ∈ f\/(exists x0:Set,x0 ∈ X/\a=(Ordered_Set x0 x0)))) X x).
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
intros.
destruct H2.
apply H0.
split.
apply H2.
intros.
destruct H4.
apply H3.
split.
apply H4.
split.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set X X).
intros.
destruct H6.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
symmetry.
apply H6.
apply H8.
apply Double_Direct_Product_Set_Law_1.
destruct H6.
destruct H6.
exists x2.
exists x2.
split.
symmetry.
apply H7.
split.
apply H6.
apply H6.
left.
apply H5.
intro.
destruct H.
destruct H7.
destruct H8.
destruct H9.
apply (H9 x0).
apply H4.
rewrite <- H6 in H5.
apply H5.
apply H1.
Qed.



(*順序準同型*)
Definition Ordered_Relation_homomorphism(M f X g Y:Set):=Ordered_Relation f X/\Ordered_Relation g Y/\Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->((Relation_Prop f x1 x2)<->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Ordered_Relation_homomorphs_Law_1:forall f X:Set,Ordered_Relation f X->Ordered_Relation_homomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

split.
destruct (Identify_Map_Law_2 X).
destruct H0.
apply H0.
intros.
destruct H0.
apply (Identify_Map_Law_3 X) in H0.
apply (Identify_Map_Law_3 X) in H1.
rewrite <- H0.
rewrite <- H1.
split.
intro.
apply H2.
intro.
destruct H0.
apply H2.
Qed.

Theorem Ordered_Relation_homomorphism_Law_2:forall M1 M2 f X g Y h Z:Set,Ordered_Relation_homomorphism M1 f X g Y/\Ordered_Relation_homomorphism M2 g Y h Z->Ordered_Relation_homomorphism (Composite_Map M1 M2) f X h Z.
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
apply H.

split.
apply H4.
split.
apply (Composite_Map_Law_1 M1 M2 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map M1 x1) ∈ Y/\(Culculateion_Map M1 x2) ∈ Y).
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H10.
apply H8.
apply H11.
intro.
apply H8.
apply H10.
apply H11.
split.
apply H2.
split.
apply H5.
apply H9.
split.
apply H2.
split.
apply H5.
apply H7.
Qed.



(*順序同型*)
Definition Ordered_Relation_Isomorphism(M f X g Y:Set):=Ordered_Relation f X/\Ordered_Relation g Y/\Bijective_Map M X Y/\forall x1 x2:Set,x1 ∈ X/\x2 ∈ X->(Relation_Prop f x1 x2<->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Ordered_Relation_Isomorphism_Law_1:forall f X:Set,Ordered_Relation f X->Ordered_Relation_Isomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

split.
apply (Identify_Map_Law_2 X).
intros.
destruct H0.
apply (Identify_Map_Law_3 X) in H0.
apply (Identify_Map_Law_3 X) in H1.
rewrite <- H0.
rewrite <- H1.
split.
intro.
apply H2.
intro.
apply H2.
Qed.

Theorem Ordered_Relation_Isomorphism_Law_2:forall M1 M2 f X g Y h Z:Set,Ordered_Relation_Isomorphism M1 f X g Y/\Ordered_Relation_Isomorphism M2 g Y h Z->Ordered_Relation_Isomorphism (Composite_Map M1 M2) f X h Z.
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
apply H.
split.
apply H4.

split.
apply (Composite_Map_Law_5 M1 M2 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map M1 x1) ∈ Y/\(Culculateion_Map M1 x2) ∈ Y).
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H10.
apply H8.
apply H11.
intro.
apply H8.
apply H10.
apply H11.
split.
apply H2.
split.
apply H5.
apply H9.
split.
apply H2.
split.
apply H5.
apply H7.
Qed.

Theorem Ordered_Relation_Isomorphism_Law_3:forall M f X g Y:Set,Ordered_Relation_Isomorphism M f X g Y->Ordered_Relation_Isomorphism (Inverse_Map M X Y) g Y f X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H0.
split.
apply H.
split.
apply Inverse_Map_Law_6.
apply H1.

intros.
destruct H3.
assert  ((Culculateion_Map (Inverse_Map M X Y) x1) ∈ X/\(Culculateion_Map (Inverse_Map M X Y) x2) ∈ X).
split.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x1).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x2).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H4.
apply H2 in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x1 Y X Y) in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x2 Y X Y) in H5.
rewrite <- (Inverse_Map_Law_5 M X Y) in H5.
rewrite <- (Identify_Map_Law_3 Y x1) in H5.
rewrite <- (Identify_Map_Law_3 Y x2) in H5.
split.
intro.
apply H5.
apply H6.
intro.
apply H5.
apply H6.
apply H4.
apply H3.
apply H1.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H3.
Qed.



(*整列準同型*)
Definition Well_Oredered_Relation_homomorphism(M f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->(Relation_Prop f x1 x2<->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Well_Oredered_Relation_homomorphism_Law_1:forall f X:Set,Well_Oredered_Relation f X->Well_Oredered_Relation_homomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

split.
apply (Identify_Map_Law_2 X).
intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 X x1).
rewrite <- (Identify_Map_Law_3 X x2).
split.
intro.
apply H2.
intro.
apply H2.
apply H1.
apply H0.
Qed.

Theorem Well_Oredered_Relation_homomorphism_Law_2:forall M1 f X M2 g Y M3 h Z:Set,Well_Oredered_Relation_homomorphism M1 f X g Y/\Well_Oredered_Relation_homomorphism M2 g Y h Z->Well_Oredered_Relation_homomorphism (Composite_Map M1 M2) f X h Z.
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
apply H.

split.
apply H4.
split.
apply (Composite_Map_Law_1 M1 M2 X Y Z).
split.
apply H2.
apply H5.

intros.
destruct H7.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H6.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
apply H3.
split.
apply H7.
apply H8.
apply H9.
intro.
apply H3.
split.
apply H7.
apply H8.
apply H6.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
apply H9.
split.
apply H2.
split.
apply H5.
apply H8.
split.
apply H2.
split.
apply H5.
apply H7.
Qed.

Theorem Well_Oredered_Relation_homomorphism_Law_3:forall f X x1 x2:Set,(Well_Oredered_Relation f X/\x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->Well_Oredered_Relation_homomorphism (Identify_Map ((Predecessor_Set f X x1))) (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

split.
apply (Restriction_Relation_Law_8 f X (Predecessor_Set f X x1)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply H3.
apply H.

split.
apply (Restriction_Relation_Law_8 f X (Predecessor_Set f X x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply H3.
apply H.

assert (Map (Identify_Map ((Predecessor_Set f X x1))) (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
apply (Map_Law_5 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
apply Identify_Map_Law_4.
intros.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
rewrite <- (Identify_Map_Law_3 (Predecessor_Set f X x1) x).
apply Predecessor_Set_Law_1.
split.
apply H3.
apply (Ordered_Relation_Law_3 f X x x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H4.
apply H2.
apply Predecessor_Set_Law_1.
split.
apply H3.
apply H4.

split.
apply H3.
intros.
destruct H4.
rewrite <- (Map_Law_3 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0 x0).
rewrite <- (Map_Law_3 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3 x3).
assert (x0 ∈ Predecessor_Set f X x2).
apply Predecessor_Set_Law_1 in H4.
destruct H4.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Ordered_Relation_Law_3 f X x0 x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H6.
apply H2.
assert (x3 ∈ Predecessor_Set f X x2).
apply Predecessor_Set_Law_1 in H5.
destruct H5.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply (Ordered_Relation_Law_3 f X x3 x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H7.
apply H2.
split.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H6.
split.
apply H7.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H4.
split.
apply H5.
apply H8.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H4.
split.
apply H5.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H6.
split.
apply H7.
apply H8.

split.
apply H3.
split.
apply H5.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H5.
destruct H5.
split.
apply H5.
apply (Ordered_Relation_Law_3 f X x3 x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H6.
apply H2.
apply Identify_Map_Law_1.
exists x3.
split.
apply H5.
split.
split.
apply H3.
split.
apply H4.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
split.
apply H4.
apply (Ordered_Relation_Law_3 f X x0 x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H6.
apply H2.
apply Identify_Map_Law_1.
exists x0.
split.
apply H4.
split.
Qed.

Theorem Well_Oredered_Relation_homomorphism_Law_4:forall M f X x:Set,Well_Oredered_Relation_homomorphism M f X f X/\Injective_Map M X X/\x ∈ X->Relation_Prop f x (Culculateion_Map M x).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H0.

apply (Transfinite_Induction_1 (fun a=>Relation_Prop f a (Culculateion_Map M a)) f X x).
split.
apply H.
split.
intros.
destruct H5.
destruct (Law_of_Excluded_Middle (Relation_Prop f a (Culculateion_Map M a))).
apply H7.

assert (Relation_Prop f (Culculateion_Map M a) a).
assert (Totaly_Ordered_Relation f X/\(Culculateion_Map M a) ∈ X/\a ∈ X).
split.
destruct H.
apply H.
split.
apply (Map_Law_2 M X X a).
split.
apply H2.
apply H5.
apply H5.
apply (Totaly_Ordered_Relation_Law_2) in H8.
destruct H8.
apply H8.
destruct H7.
apply H8.

assert(~a=(Culculateion_Map M a)).
intro.
destruct H7.
rewrite <- H9.
apply (Ordered_Relation_Law_2 f X a).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H5.

assert (~Culculateion_Map M a=Culculateion_Map M (Culculateion_Map M a)).
intro.
apply H9.
destruct H0.
apply H11.
split.
apply H5.
split.
apply (Map_Law_2 M X X a).
split.
apply H2.
apply H5.
apply H10.

destruct H10.
apply (Ordered_Relation_Law_4 f X (Culculateion_Map M a) (Culculateion_Map M (Culculateion_Map M a))).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H6.
split.
apply (Map_Law_2 M X X a).
split.
apply H2.
apply H5.
split.
apply H8.
intro.
apply H9.
symmetry.
apply H10.
apply (H3 (Culculateion_Map M a) a).
split.
apply (Map_Law_2 M X X a).
split.
apply H2.
apply H5.
apply H5.
apply H8.
apply H4.
Qed.



(*整列準同型*)
Definition Well_Oredered_Relation_Isomorphism(M f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\Bijective_Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->((Relation_Prop f x1 x2)<->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Well_Oredered_Relation_Isomorphism_Law_1:forall f X:Set,Well_Oredered_Relation f X->Well_Oredered_Relation_Isomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

split.
apply (Identify_Map_Law_2 X).
intros.
destruct H0.
apply (Identify_Map_Law_3 X) in H0.
apply (Identify_Map_Law_3 X) in H1.
rewrite <- H0.
rewrite <- H1.
split.
intro.
apply H2.
intro.
apply H2.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_2:forall M1 M2 f X g Y h Z:Set,Well_Oredered_Relation_Isomorphism M1 f X g Y/\Well_Oredered_Relation_Isomorphism M2 g Y h Z->Well_Oredered_Relation_Isomorphism (Composite_Map M1 M2) f X h Z.
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
apply H.
split.
apply H4.

split.
apply (Composite_Map_Law_5 M1 M2 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map M1 x1) ∈ Y/\(Culculateion_Map M1 x2) ∈ Y).
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H10.
apply H8.
apply H11.
intro.
apply H8.
apply H10.
apply H11.
split.
apply H2.
split.
apply H5.
apply H9.
split.
apply H2.
split.
apply H5.
apply H7.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_3:forall M f X g Y:Set,Well_Oredered_Relation_Isomorphism M f X g Y->Well_Oredered_Relation_Isomorphism (Inverse_Map M X Y) g Y f X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H0.
split.
apply H.
split.
apply Inverse_Map_Law_6.
apply H1.

intros.
destruct H3.
assert ((Culculateion_Map (Inverse_Map M X Y) x1) ∈ X/\(Culculateion_Map (Inverse_Map M X Y) x2) ∈ X).
split.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x1).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x2).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H4.
apply H2 in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x1 Y X Y) in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x2 Y X Y) in H5.
rewrite <- (Inverse_Map_Law_5 M X Y) in H5.
rewrite <- (Identify_Map_Law_3 Y x1) in H5.
rewrite <- (Identify_Map_Law_3 Y x2) in H5.
split.
intro.
apply H5.
apply H6.
intro.
apply H5.
apply H6.
apply H4.
apply H3.
apply H1.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H3.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_4:forall M f X:Set,Well_Oredered_Relation_Isomorphism M f X f X->Identify_Map X=M.
Proof.
intros.
assert (Well_Oredered_Relation_Isomorphism M f X f X).
apply H.
destruct H0.
destruct H1.
destruct H2.

apply (Map_Law_4 (Identify_Map X) M X X).
split.
apply Identify_Map_Law_4.
split.
apply H2.
intros.
rewrite <- (Identify_Map_Law_3 X x).
apply (Ordered_Relation_Law_4 f X x (Culculateion_Map M x)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Well_Oredered_Relation_homomorphism_Law_4 M f X x).
split.
split.
apply H.
split.
apply H.
split.
destruct H2.
destruct H2.
apply H2.
apply H3.
split.
destruct H2.
apply H5.
apply H4.
assert (Well_Oredered_Relation_Isomorphism (Inverse_Map M X X) f X f X).
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H.
assert (Well_Oredered_Relation_Isomorphism (Inverse_Map M X X) f X f X).
apply H5.
destruct H6.
destruct H6.
destruct H7.
destruct H9.
apply H10.
split.
apply (Map_Law_2 M X X x).
split.
destruct H2.
destruct H2.
apply H2.
apply H4.
apply H4.
rewrite -> (Composite_Map_Law_2 M (Inverse_Map M X X) x X X X).
rewrite <- (Inverse_Map_Law_4 M X X).
rewrite <- (Identify_Map_Law_3 X x).
apply (Well_Oredered_Relation_homomorphism_Law_4 (Inverse_Map M X X) f X x).
split.
split.
apply H.
split.
apply H.
split.
destruct H9.
destruct H9.
apply H9.
apply H10.
split.
destruct H9.
apply H11.
apply H4.
apply H4.
apply H2.
split.
destruct H2.
destruct H2.
apply H2.
split.
destruct H9.
destruct H9.
apply H9.
apply H4.
apply H4.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_5:forall M1 M2 f X g Y:Set,Well_Oredered_Relation_Isomorphism M1 f X g Y/\Well_Oredered_Relation_Isomorphism M2 f X g Y->M1=M2.
Proof.
intros.
destruct H.
assert (Well_Oredered_Relation_Isomorphism M1 f X g Y).
apply H.
destruct H1.
destruct H2.
destruct H3.
assert (Well_Oredered_Relation_Isomorphism M2 f X g Y).
apply H0.
destruct H5.
destruct H6.
destruct H7.
apply (Map_Law_4 M1 M2 X Y).
split.
destruct H3.
destruct H3.
apply H3.
split.
destruct H7.
destruct H7.
apply H7.
intros.
rewrite -> (Identify_Map_Law_3 X x).
rewrite -> (Inverse_Map_Law_4 M2 X Y).
rewrite <- (Composite_Map_Law_2 M2 (Inverse_Map M2 X Y) x X Y X).
rewrite -> (Composite_Map_Law_2 (Inverse_Map M2 X Y) M1 (Culculateion_Map M2 x) Y X Y).
rewrite -> (Composite_Map_Law_2 (Inverse_Map M2 X Y) M2 (Culculateion_Map M2 x) Y X Y).
rewrite <- (Inverse_Map_Law_5 M2 X Y).
rewrite <- (Well_Oredered_Relation_Isomorphism_Law_4 (Composite_Map (Inverse_Map M2 X Y) M1) g Y).
split.
apply (Well_Oredered_Relation_Isomorphism_Law_2 (Inverse_Map M2 X Y) M1 g Y f X g Y).
split.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H0.
apply H.
apply H7.
split.
apply Inverse_Map_Law_6.
apply H7.
split.
destruct H7.
destruct H7.
apply H7.
apply (Map_Law_2 M2 X Y x).
split.
destruct H7.
destruct H7.
apply H7.
apply H9.
split.
apply Inverse_Map_Law_2.
apply H7.
split.
destruct H3.
destruct H3.
apply H3.
apply (Map_Law_2 M2 X Y x).
split.
destruct H7.
destruct H7.
apply H7.
apply H9.
split.
destruct H7.
destruct H7.
apply H7.
split.
apply Inverse_Map_Law_2.
apply H7.
apply H9.
apply H7.
apply H9.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_6:forall M f X x1 x2:Set,(Well_Oredered_Relation f X/\x1 ∈ X/\x2 ∈ X/\Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2))->x1=x2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
assert (Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2)).
apply H2.

apply (Ordered_Relation_Law_4 f X x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.

assert (forall a1 a2:Set,a1 ∈ X/\a2 ∈ X/\(exists M0:Set,Well_Oredered_Relation_Isomorphism M0 (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation f (Predecessor_Set f X a2)) (Predecessor_Set f X a2))->Relation_Prop f a1 a2).
intros.
destruct H4.
destruct H5.
destruct H6.

destruct (Law_of_Excluded_Middle (Relation_Prop f a1 a2)).
apply H7.
assert (Relation_Prop f a2 a1).
assert (Totaly_Ordered_Relation f X/\a2 ∈ X/\a1 ∈ X).
split.
destruct H.
apply H.
split.
apply H5.
apply H4.
apply Totaly_Ordered_Relation_Law_2 in H8.
destruct H8.
apply H8.
destruct H7.
apply H8.
assert (~a1=a2).
intro.
apply H7.
rewrite -> H9 in H8.
rewrite -> H9.
apply H8.
apply (Ordered_Relation_Law_3 f X a1 (Culculateion_Map x a1) a2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X a1) a1 (Culculateion_Map x a1)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply H10.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Ordered_Relation_Law_2 f X a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H4.
split.
assert (Culculateion_Map x a1 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2)).
split.
destruct H6.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Ordered_Relation_Law_2 f X a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H4.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x a1) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H11.
apply H8.
apply (Well_Oredered_Relation_homomorphism_Law_4 x (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) a1).
split.
destruct H6.
destruct H10.
destruct H11.
split.
apply H6.
split.
apply H6.
split.
apply (Map_Law_5 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) (Predecessor_Set f X a1)).
split.
destruct H11.
destruct H11.
apply H11.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map x x0 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2)).
split.
destruct H11.
destruct H11.
apply H11.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
assert (Culculateion_Map x x0 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2)).
split.
destruct H11.
destruct H11.
apply H11.
apply H13.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x0) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H16.
apply H8.
intros.
assert (x0 ∈ Predecessor_Set f X a1/\x3 ∈ Predecessor_Set f X a1).
apply H13.
apply H12 in H13.
destruct H14.
split.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X a1) (Culculateion_Map x x0) (Culculateion_Map x x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply H17.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x x0 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x0).
split.
destruct H11.
destruct H11.
apply H11.
apply H14.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
split.
apply H17.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x0) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H18.
apply H8.
split.
assert (Culculateion_Map x x3 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x3).
split.
destruct H11.
destruct H11.
apply H11.
apply H15.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x3) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H18.
apply H8.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X a2) (Culculateion_Map x x0) (Culculateion_Map x x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply H17.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x0).
split.
destruct H11.
destruct H11.
apply H11.
apply H14.
split.
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x3).
split.
destruct H11.
destruct H11.
apply H11.
apply H15.
apply (H12 x0 x3).
split.
apply H14.
apply H15.
apply H16.
intro.
apply (H12 x0 x3).
split.
apply H14.
apply H15.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X a2) (Culculateion_Map x x0) (Culculateion_Map x x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply H17.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x0).
split.
destruct H11.
destruct H11.
apply H11.
apply H14.
split.
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x3).
split.
destruct H11.
destruct H11.
apply H11.
apply H15.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X a1) (Culculateion_Map x x0) (Culculateion_Map x x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply H17.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
assert (Culculateion_Map x x0 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x0).
split.
destruct H11.
destruct H11.
apply H11.
apply H14.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x0) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H18.
apply H8.
split.
assert (Culculateion_Map x x3 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x3).
split.
destruct H11.
destruct H11.
apply H11.
apply H15.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x3) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H18.
apply H8.
apply H16.
split.
destruct H6.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
split.
apply (Map_Law_5 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) (Predecessor_Set f X a1)).
split.
apply H13.
intros.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
assert (Culculateion_Map x x0 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) x0).
split.
apply H13.
apply Predecessor_Set_Law_1.
split.
apply H15.
apply H16.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map x x0) a2 a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H18.
apply H8.
destruct H13.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Ordered_Relation_Law_2 f X a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H4.
assert (Culculateion_Map x a1 ∈ Predecessor_Set f X a2).
apply (Map_Law_2 x (Predecessor_Set f X a1) (Predecessor_Set f X a2) a1).
split.
destruct H6.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Ordered_Relation_Law_2 f X a1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H4.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply H11.

split.
apply H4.
split.
apply H0.
split.
apply H1.
exists M.
apply H3.
apply H4.
split.
apply H1.
split.
apply H0.
exists (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H3.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_7:forall f X g Y:Set,(Well_Oredered_Relation f X/\Well_Oredered_Relation g Y)->((exists M x0:Set,x0 ∈ X/\Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set_1 f X x0)) (Predecessor_Set_1 f X x0) g Y)\/(exists M:Set,Well_Oredered_Relation_Isomorphism M f X g Y)\/(exists M y0:Set,y0 ∈ Y/\Well_Oredered_Relation_Isomorphism M f X (Restriction_Relation g (Predecessor_Set_1 g Y y0)) (Predecessor_Set_1 g Y y0))).
Proof.
intros.
destruct H.

assert (forall a:Set,a ∈ (Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))<->exists x y:Set,x ∈ X/\y ∈ Y/\a=Ordered_Set x y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set (Pair_Union_Set X Y))).
intros.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
rewrite -> H3.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Ordered_Set_Law_1 in H5.
destruct H5.
rewrite -> H5 in H6.
apply Pair_Set_Law_1 in H6.
destruct H6.
rewrite -> H6.
apply Pair_Union_Set_Law_1.
left.
apply H1.
rewrite -> H6.
apply Pair_Union_Set_Law_1.
right.
apply H2.
rewrite -> H5 in H6.
apply Single_Set_Law_1 in H6.
rewrite -> H6.
apply Pair_Union_Set_Law_1.
right.
apply H2.
assert (exists h:Set,h=(Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))).
exists (Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y))).
split.
destruct H2.
rewrite <- H2 in H1.
clear H2.

assert (forall a:Set,a ∈ (Prop_Set (fun x=>exists y:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))<->exists y:Set,a ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X a)) (Predecessor_Set f X a) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)).
intros.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H2.
destruct H2.
apply H2.
assert (exists h:Set,h=(Prop_Set (fun x=>exists y:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))).
exists (Prop_Set (fun x=>exists y:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y))).
split.
destruct H3.
rewrite <- H3 in H2.
clear H3.

assert (forall a:Set,a ∈ (Prop_Set (fun y=>exists x:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))<->exists x:Set,x ∈ X/\a ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y a)) (Predecessor_Set g Y a)).
intros.
apply Prop_Set_Law_1.
exists Y.
intros.
destruct H3.
destruct H3.
destruct H4.
apply H4.
assert (exists h:Set,h=(Prop_Set (fun y=>exists x:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))).
exists (Prop_Set (fun y=>exists x:Set,x ∈ X/\y ∈ Y/\exists M:Set,Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y))).
split.
destruct H4.
rewrite <- H4 in H3.
clear H4.

assert (Map x x0 x1).
split.
intros.
apply H1 in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
destruct H6.
exists x2.
exists x3.
split.
apply H2.
exists x3.
split.
apply H4.
split.
apply H5.
apply H7.
split.
apply H3.
exists x2.
split.
apply H4.
split.
apply H5.
apply H7.
apply H6.
intros.
apply H2 in H4.
destruct H4.
destruct H4.
destruct H5.
exists x3.
split.
split.
apply H1.
exists x2.
exists x3.
split.
apply H4.
split.
apply H5.
split.
split.
apply H6.
apply H3.
exists x2.
split.
apply H4.
split.
apply H5.
apply H6.
intros.
destruct H7.
apply H1 in H7.
destruct H7.
destruct H7.
destruct H7.
destruct H9.
destruct H10.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite <- H10 in H7.
rewrite <- H12 in H9.
rewrite <- H10 in H11.
rewrite <- H12 in H11.
clear H10.
clear H12.
apply H3 in H8.
destruct H8.
destruct H8.
destruct H10.
clear H10.
destruct H6.
destruct H11.
apply (Well_Oredered_Relation_Isomorphism_Law_6 (Composite_Map (Inverse_Map x7 (Predecessor_Set f X x2) (Predecessor_Set g Y x3)) x8) g Y x3 x').
split.
apply H0.
split.
apply H5.
split.
apply H9.
apply (Well_Oredered_Relation_Isomorphism_Law_2 (Inverse_Map x7 (Predecessor_Set f X x2) (Predecessor_Set g Y x3)) x8 (Restriction_Relation g (Predecessor_Set g Y x3)) (Predecessor_Set g Y x3) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Restriction_Relation g (Predecessor_Set g Y x')) (Predecessor_Set g Y x')).
split.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H6.
apply H10.

assert (x0⊂X).
intro.
intro.
apply H2 in H5.
destruct H5.
destruct H5.
apply H5.

assert (x1⊂Y).
intro.
intro.
apply H3 in H6.
destruct H6.
destruct H6.
destruct H7.
apply H7.

assert (Well_Oredered_Relation_Isomorphism x (Restriction_Relation f x0) x0 (Restriction_Relation g x1) x1).
split.
apply (Restriction_Relation_Law_8 f X x0).
split.
apply H5.
apply H.
split.
apply (Restriction_Relation_Law_8 g Y x1).
split.
apply H6.
apply H0.
assert (Bijective_Map x x0 x1).
split.
split.
apply H4.
intros.
apply H3 in H7.
destruct H7.
destruct H7.
destruct H8.
exists x2.
split.
apply H2.
exists y.
split.
apply H7.
split.
apply H8.
apply H9.
apply (Map_Law_3 x x0 x1 x2 y).
split.
apply H4.
split.
apply H2.
exists y.
split.
apply H7.
split.
apply H8.
apply H9.
split.
apply H3.
exists x2.
split.
apply H7.
split.
apply H8.
apply H9.
apply H1.
exists x2.
exists y.
split.
apply H7.
split.
apply H8.
split.
split.
apply H9.
split.
apply H4.
intros.
destruct H7.
destruct H8.
assert (Ordered_Set x2 (Culculateion_Map x x2) ∈ x).
apply (Map_Law_1 x x0 x1 x2).
split.
apply H4.
apply H7.
apply H1 in H10.
destruct H10.
destruct H10.
destruct H10.
destruct H11.
destruct H12.
destruct H13.
assert (Ordered_Set x3 (Culculateion_Map x x3) ∈ x).
apply (Map_Law_1 x x0 x1 x3).
split.
apply H4.
apply H8.
apply H1 in H14.
destruct H14.
destruct H14.
destruct H14.
destruct H15.
destruct H16.
destruct H17.
apply Ordered_Set_Law_2 in H12.
destruct H12.
rewrite <- H12 in H13.
rewrite <- H18 in H13.
apply Ordered_Set_Law_2 in H16.
destruct H16.
rewrite <- H16 in H17.
rewrite <- H19 in H17.
apply (Well_Oredered_Relation_Isomorphism_Law_6 (Composite_Map x6 (Inverse_Map x9 (Predecessor_Set f X x3) (Predecessor_Set g Y (Culculateion_Map x x3)))) f X x2 x3).
split.
apply H.
split.
rewrite -> H12.
apply H10.
split.
rewrite -> H16.
apply H14.
apply (Well_Oredered_Relation_Isomorphism_Law_2 x6 (Inverse_Map x9 (Predecessor_Set f X x3) (Predecessor_Set g Y (Culculateion_Map x x3))) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Restriction_Relation f (Predecessor_Set f X x3)) (Predecessor_Set f X x3)).
split.
apply H13.
rewrite -> H9.
apply (Well_Oredered_Relation_Isomorphism_Law_3 x9 (Restriction_Relation f (Predecessor_Set f X x3)) (Predecessor_Set f X x3) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H17.
intros.
split.
apply H7.
intros.
split.
destruct H8.
intro.
apply (Restriction_Relation_Law_3 g Y x1 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
split.
apply (Map_Law_2 x x0 x1 x3).
split.
apply H4.
apply H9.
assert (Relation_Prop f x2 x3).
apply (Restriction_Relation_Law_4 f X x0 x2 x3).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H8.
split.
apply H9.
apply H10.
clear H10.
assert (x3 ∈ x0).
apply H9.
apply H2 in H10.
destruct H10.
destruct H10.
destruct H12.
destruct H13.
assert (Culculateion_Map x5 x2 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
destruct H13.
destruct H14.
destruct H15.
destruct H15.
destruct H15.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
assert (Culculateion_Map x5 x2=Culculateion_Map x x2).
assert (x2 ∈ x0).
apply H8.
apply H2 in H16.
destruct H16.
destruct H16.
destruct H17.
destruct H18.
assert (Well_Oredered_Relation_Isomorphism (Restriction_Map x5 (Predecessor_Set f X x2)) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x5 x2))) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
destruct H13.
destruct H19.
destruct H20.
split.
apply (Restriction_Relation_Law_8 f X (Predecessor_Set f X x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H22.
apply H.
split.
apply (Restriction_Relation_Law_8 g Y (Predecessor_Set g Y (Culculateion_Map x5 x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H22.
apply H0.
assert (Bijective_Map (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
split.
split.
apply (Map_Law_5 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H24.
apply H11.
apply H22.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x8) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x8).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x8 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
split.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H23.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H24.
apply H11.
apply H22.
intros.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
destruct H20.
destruct H20.
assert (y ∈ Predecessor_Set g Y x4).
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H15.
apply H25 in H26.
destruct H26.
destruct H26.
exists x8.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x8 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
split.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x8) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H27.
apply H22.
assert (Culculateion_Map x5 x8 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x8).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H30.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
rewrite <- H27.
apply H23.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
apply H27.
split.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H30.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x8 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
split.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x8) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x8).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
rewrite <- H27.
apply H23.
split.
apply (Map_Law_5 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H24.
apply H11.
apply H22.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x8) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x8).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x8 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
apply H11.
split.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply H11.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H23.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H24.
apply H11.
apply H22.
intros.
destruct H20.
destruct H23.
destruct H22.
destruct H25.
apply H24.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
split.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x9 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x9).
apply H26.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H28.
apply H11.
apply H25.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H28.
apply H11.
apply H22.
intros.
split.
apply H22.
intros.
destruct H23.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x5 x2)) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply H23.
split.
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x4) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8 ∈ Predecessor_Set g Y (Culculateion_Map x5 x2)).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H26.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 g Y (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H15.
split.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9 ∈ Predecessor_Set g Y (Culculateion_Map x5 x2)).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9) (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H15.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x9).
apply H21.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x9 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
split.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x9 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
split.
apply H24.
apply H25.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
apply H24.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
apply H23.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H23.
split.
apply H24.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
split.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x9 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x8 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x9 x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H11.
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x8).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x3) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x9).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8 ∈ (Predecessor_Set g Y (Culculateion_Map x5 x2))).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply H23.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H15.
split.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9 ∈ (Predecessor_Set g Y (Culculateion_Map x5 x2))).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply Predecessor_Set_Law_1.
split.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
apply (Ordered_Relation_Law_3 g Y (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9) (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H27.
apply H15.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x5 x2)) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x8) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply H23.
split.
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply H25.
split.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
apply H24.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z x2 x3).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H11.
apply H23.
rewrite -> (Well_Oredered_Relation_Isomorphism_Law_6 (Composite_Map (Inverse_Map (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2))) x7) g Y (Culculateion_Map x5 x2) x6).
apply (Map_Law_3 x x0 x1 x2 x6).
split.
apply H4.
split.
apply H8.
split.
apply H3.
exists x2.
split.
apply H16.
split.
apply H17.
exists x7.
apply H18.
apply H1.
exists x2.
exists x6.
split.
apply H16.
split.
apply H17.
split.
split.
exists x7.
apply H18.
split.
apply H0.
split.
apply H14.
split.
apply H17.
apply (Well_Oredered_Relation_Isomorphism_Law_2 (Inverse_Map (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2))) x7 (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x5 x2))) (Predecessor_Set g Y (Culculateion_Map x5 x2)) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Restriction_Relation g (Predecessor_Set g Y x6)) (Predecessor_Set g Y x6)).
split.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H19.
apply H18.
rewrite <- H16.
assert (x4=Culculateion_Map x x3).
apply (Map_Law_3 x x0 x1 x3 x4).
split.
apply H4.
split.
apply H9.
split.
apply H3.
exists x3.
split.
apply H10.
split.
apply H12.
exists x5.
apply H13.
apply H1.
exists x3.
exists x4.
split.
apply H10.
split.
apply H12.
split.
split.
exists x5.
apply H13.
rewrite <- H17.
assert (Culculateion_Map x5 x2 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 x5 (Predecessor_Set f X x3) (Predecessor_Set g Y x4) x2).
split.
destruct H13.
destruct H18.
destruct H19.
destruct H19.
destruct H19.
apply H19.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H18.
destruct H18.
apply H19.
destruct H8.
intro.
rewrite -> (Identify_Map_Law_3 x0 x2).
rewrite -> (Identify_Map_Law_3 x0 x3).
rewrite -> (Inverse_Map_Law_4 x x0 x1).
rewrite <- (Composite_Map_Law_2 x (Inverse_Map x x0 x1) x2 x0 x1 x0).
rewrite <- (Composite_Map_Law_2 x (Inverse_Map x x0 x1) x3 x0 x1 x0).
apply (Restriction_Relation_Law_3 f X x0 (Culculateion_Map (Inverse_Map x x0 x1) (Culculateion_Map x x2)) (Culculateion_Map (Inverse_Map x x0 x1) (Culculateion_Map x x3))).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x x0 x1) x1 x0 (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H7.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
split.
apply (Map_Law_2 (Inverse_Map x x0 x1) x1 x0 (Culculateion_Map x x3)).
split.
apply Inverse_Map_Law_2.
apply H7.
apply (Map_Law_2 x x0 x1 x3).
split.
apply H4.
apply H9.
assert (Relation_Prop g (Culculateion_Map x x2) (Culculateion_Map x x3)).
apply (Restriction_Relation_Law_4 g Y x1 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
split.
apply (Map_Law_2 x x0 x1 x3).
split.
apply H4.
apply H9.
apply H10.
clear H10.
assert (Culculateion_Map x x3∈ x1).
apply (Map_Law_2 x x0 x1 x3).
split.
apply H4.
apply H9.
apply H3 in H10.
destruct H10.
destruct H10.
destruct H12.
destruct H13.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2) ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
destruct H13.
destruct H14.
destruct H15.
apply Inverse_Map_Law_2.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H14.
destruct H14.







assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)=Culculateion_Map (Inverse_Map x x0 x1) (Culculateion_Map x x2)).
assert (Culculateion_Map x x3 ∈ x1).
apply (Map_Law_2 x x0 x1 x3).
split.
apply H4.
apply H9.
apply H3 in H16.
destruct H16.
destruct H16.
destruct H17.
destruct H18.
assert (Well_Oredered_Relation_Isomorphism (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Restriction_Relation f (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
destruct H13.
destruct H19.
destruct H20.
split.
apply (Restriction_Relation_Law_8 g Y (Predecessor_Set g Y (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H22.
apply H0.
split.
apply (Restriction_Relation_Law_8 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H22.
apply H.
assert (Bijective_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
split.





apply (Map_Law_5 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
apply (Restriction_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
split.
apply (Restriction_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H24.
apply H11.
apply H22.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
rewrite -> (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
split.
apply H24.
apply H25.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8)) (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) ∈ (Predecessor_Set g Y (Culculateion_Map x x3))).
apply (Map_Law_2 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8)).
split.
destruct H20.
destruct H20.
apply H20.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
split.
apply H24.
apply H25.
split.
apply Predecessor_Set_Law_1.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H23.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H24.
apply H11.
apply H22.
assert (Bijective_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H20.
apply Inverse_Map_Law_6 in H22.
destruct H22.
destruct H22.
intros.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
assert (y ∈ Predecessor_Set f X x4).
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X y (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H26.
apply H15.
apply H24 in H27.
destruct H27.
destruct H27.
exists x8.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x8 (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
rewrite -> (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H21.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite <- H28.
apply H26.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
rewrite -> H28.
symmetry.
apply (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply Predecessor_Set_Law_1.
split.
apply H30.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H31.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x8 (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
rewrite -> (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H21.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite <- H28.
apply H26.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply (Map_Law_5 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
apply (Restriction_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
split.
apply (Restriction_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H24.
apply H11.
apply H22.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
rewrite -> (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4)).
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H21.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
split.
apply H24.
apply H25.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8)) (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x5 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) ∈ (Predecessor_Set g Y (Culculateion_Map x x3))).
apply (Map_Law_2 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8)).
split.
destruct H20.
destruct H20.
apply H20.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
split.
apply H24.
apply H25.
split.
apply Predecessor_Set_Law_1.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply H23.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H24.
apply H11.
apply H22.
assert (Bijective_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H20.
apply Inverse_Map_Law_6 in H22.
intros.
destruct H23.
destruct H24.
destruct H22.
destruct H26.
apply H27.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
split.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
rewrite <- (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
rewrite <- (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x9).
apply H25.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H29.
apply H11.
apply H24.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H29.
apply H11.
apply H23.
intros.
split.
apply H22.
intros.
destruct H23.
split.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8) (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply H23.
split.
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8) (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
assert (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8 ∈ Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) x8).
split.
destruct H22.
destruct H22.
apply H22.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H26.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H28.
apply H15.
split.
assert (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x9 ∈ Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
apply (Map_Law_2 (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) x9).
split.
destruct H22.
destruct H22.
apply H22.
apply H24.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) x9) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H27.
apply H15.
rewrite -> (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
rewrite -> (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x9).
apply H21.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
split.
apply H27.
apply H28.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x9).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9(Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x9 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x9).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
split.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x x2)) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
split.
apply H24.
apply H25.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply H24.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply H23.
intro.
assert (Relation_Prop (Restriction_Relation f (Predecessor_Set f X x4)) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x9)).
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x9).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x9)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8 ∈ (Predecessor_Set f X x4)).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x8) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2) ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
split.
apply H28.
apply H29.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2) ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
split.
apply H28.
apply H29.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x8 (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x9 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x9).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H26.
apply H11.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x9) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H21.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x9).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Culculateion_Map x x2)).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x9 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 (Culculateion_Map x x2) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x9).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) (Culculateion_Map x x2)).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x9 (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
split.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
apply H20.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply (Map_Law_2 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
rewrite <- (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x8).
rewrite <- (Restriction_Map_Law_3 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X x4) x9).
apply H25.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply H24.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y z (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply H23.
apply H21 in H26.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x x2)) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply H27.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H23.
split.
apply H24.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x x3)) x8 x9).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply H27.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
split.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x8).
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y (Culculateion_Map x x3)) x9).
rewrite -> (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x8 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) x5 x9 (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))).
apply H26.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
split.
apply Inverse_Map_Law_2.
apply H20.
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H27.
apply H11.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x8).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 g Y x8 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Predecessor_Set f X x4) x9).
split.
apply Inverse_Map_Law_2.
apply H20.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 g Y x9 (Culculateion_Map x x2) (Culculateion_Map x x3)).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H28.
apply H11.
assert (Ordered_Set x2 (Culculateion_Map x x2) ∈ x).
apply (Map_Law_1 x x0 x1 x2).
split.
apply H4.
apply H8.
apply H1 in H20.
destruct H20.
destruct H20.
destruct H20.
destruct H21.
destruct H22.
apply Ordered_Set_Law_2 in H22.
destruct H22.
destruct H23.
rewrite <- H22 in H23.
rewrite <- H24 in H23.
rewrite -> (Composite_Map_Law_2 x (Inverse_Map x x0 x1) x2 x0 x1 x0).
rewrite <- (Inverse_Map_Law_4 x x0 x1).
rewrite <- (Identify_Map_Law_3 x0 x2).
apply (Well_Oredered_Relation_Isomorphism_Law_6 (Composite_Map (Inverse_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))) (Inverse_Map x10 (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x x2)))) f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)) x2).
split.
apply H.
split.
apply H14.
split.
apply H5.
apply H8.
apply (Well_Oredered_Relation_Isomorphism_Law_2 (Inverse_Map (Restriction_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))) (Inverse_Map x10 (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x x2))) (Restriction_Relation f (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2))) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x x2))) (Predecessor_Set g Y (Culculateion_Map x x2)) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2)).
split.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H19.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H23.
apply H8.
apply H7.
split.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H7.
apply H8.
rewrite <- H16.
assert (Culculateion_Map (Inverse_Map x x0 x1) (Culculateion_Map x x3)=x4).
rewrite -> (Composite_Map_Law_2 x (Inverse_Map x x0 x1) x3 x0 x1 x0).
rewrite <- (Inverse_Map_Law_4 x x0 x1).
rewrite <- (Identify_Map_Law_3 x0 x3).
assert (Ordered_Set x3 (Culculateion_Map x x3) ∈ x).
apply (Map_Law_1 x x0 x1 x3).
split.
apply H4.
apply H9.
apply H1 in H17.
destruct H17.
destruct H17.
destruct H17.
destruct H18.
destruct H19.
destruct H20.
apply Ordered_Set_Law_2 in H19.
destruct H19.
rewrite <- H19 in H20.
rewrite <- H21 in H20.
apply (Well_Oredered_Relation_Isomorphism_Law_6 (Composite_Map x8 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3)))) f X x3 x4).
split.
apply H.
split.
rewrite -> H19.
apply H17.
split.
apply H10.
apply (Well_Oredered_Relation_Isomorphism_Law_2 x8 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Restriction_Relation f (Predecessor_Set f X x3)) (Predecessor_Set f X x3) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x x3))) (Predecessor_Set g Y (Culculateion_Map x x3)) (Restriction_Relation f (Predecessor_Set f X x4)) (Predecessor_Set f X x4)).
split.
apply H20.
apply Well_Oredered_Relation_Isomorphism_Law_3.
apply H13.
apply H9.
apply H7.
split.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H7.
apply H9.
rewrite -> H17.
apply H15.
split.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H7.
apply H9.
split.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H7.
apply H8.
apply H7.
apply H9.
apply H8.

destruct (Law_of_Excluded_Middle (x0=X)).
destruct (Law_of_Excluded_Middle (x1=Y)).
right.
left.
exists x.
rewrite <- H8.
rewrite <- H9.
assert (Restriction_Relation f x0=f).
apply Axiom_of_Extensionality.
intro.
split.
intro.
assert (Relation (Restriction_Relation f x0) x0).
apply (Restriction_Relation_Law_2 f X x0).
split.
apply H5.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
assert (z ∈ Restriction_Relation f x0).
apply H10.
apply H11 in H10.
destruct H10.
destruct H10.
destruct H10.
destruct H13.
rewrite -> H10.
rewrite -> H10 in H12.
apply (Restriction_Relation_Law_4 f X x0 x2 x3).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H13.
split.
apply H14.
apply H12.
intro.
assert (Relation f X).
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
assert (z ∈ f).
apply H10.
apply H11 in H10.
destruct H10.
destruct H10.
destruct H10.
destruct H13.
rewrite -> H10.
apply (Restriction_Relation_Law_3 f X x0 x2 x3).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
rewrite -> H8.
apply H13.
split.
rewrite -> H8.
apply H14.
rewrite -> H10 in H12.
apply H12.
rewrite <- H10.
assert (Restriction_Relation g x1=g).
apply Axiom_of_Extensionality.
intro.
split.
intro.
assert (Relation (Restriction_Relation g x1) x1).
apply (Restriction_Relation_Law_2 g Y x1).
split.
apply H6.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
assert (z ∈ Restriction_Relation g x1).
apply H11.
apply H12 in H11.
destruct H11.
destruct H11.
destruct H11.
destruct H14.
rewrite -> H11 in H13.
rewrite -> H11.
apply (Restriction_Relation_Law_4 g Y x1 x2 x3).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
apply H14.
split.
apply H15.
apply H13.
intro.
assert (Relation g Y).
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
assert (z ∈ g).
apply H11.
apply H12 in H11.
destruct H11.
destruct H11.
destruct H11.
destruct H14.
rewrite -> H11 in H13.
rewrite -> H11.
apply (Restriction_Relation_Law_3 g Y x1 x2 x3).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H0.
apply H0.
split.
rewrite -> H9.
apply H14.
split.
rewrite -> H9.
apply H15.
apply H13.
rewrite <- H11.
apply H7.

right.
right.
assert (Well_Oredered_Relation g Y/\(Complement_Set Y x1) ⊂ Y/\~(Complement_Set Y x1)=∅).
split.
apply H0.
split.
intro.
intro.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
intro.
apply H9.
apply Axiom_of_Extensionality.
intro.
split.
apply H6.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x1)).
apply H12.
destruct (Definition_of_Empty_Set z).
rewrite <- H10.
apply Complement_Set_Law_1.
split.
apply H11.
apply H12.
apply Well_Oredered_Relation_Law_6 in H10.
destruct H10.
destruct H10.
apply Complement_Set_Law_1 in H10.
destruct H10.
exists x.
exists x2.
split.
apply H10.
split.
apply H.
split.
apply (Predecessor_Set_1_Law_2 g Y x2).
split.
apply H10.
apply H0.
assert (Predecessor_Set_1 g Y x2=x1).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Predecessor_Set_1_Law_1 in H13.
destruct H13.
destruct H14.
apply H3.
destruct (Law_of_Excluded_Middle (z ∈ x1)).
apply H3 in H16.
destruct H16.
exists x3.
apply H16.
destruct H15.
apply (Ordered_Relation_Law_4 g Y z x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H14.
apply H11.
apply Complement_Set_Law_1.
split.
apply H13.
apply H16.
intro.
apply Predecessor_Set_1_Law_1.
split.
apply H6.
apply H13.
split.
destruct (Law_of_Excluded_Middle (Relation_Prop g x2 z)).
destruct H12.
apply H3.
apply H3 in H13.
destruct H13.
destruct H12.
destruct H13.
destruct H15.
destruct H15.
destruct H16.
destruct H17.
exists (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2).
assert (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2 ∈ Predecessor_Set f X x3).
apply (Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x3) x2).
split.
apply Inverse_Map_Law_6.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H10.
exists (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))).
split.
apply Predecessor_Set_Law_2.
split.
apply H19.
apply H.
split.
apply Predecessor_Set_Law_2.
split.
apply H10.
apply H0.
split.
assert (Map (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y x2)).
apply (Map_Law_5 (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) (Predecessor_Set g Y x2)).
split.
apply (Restriction_Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z)).
split.
destruct H17.
destruct H17.
apply H17.
intro.
intro.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
intros.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
apply Predecessor_Set_Law_1.
split.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H22.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z)).
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H22.
apply (Ordered_Relation_Law_3 g Y (Culculateion_Map (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) x5) x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply H0.
split.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H22.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z)).
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply (H18 x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H22.
split.
apply (Inverse_Map_Law_6 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H22.
apply H14.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) (Culculateion_Map (Restriction_Map x4 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2))) x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply H0.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
split.
apply H23.
apply H24.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply H23.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H22.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H22.
split.
apply Inverse_Map_Law_2.
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H22.
split.
split.
apply H21.
intros.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
destruct H17.
destruct H17.
assert (y ∈ Predecessor_Set g Y z).
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y y x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H23.
apply H14.
apply H25 in H26.
destruct H26.
destruct H26.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
exists x5.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
rewrite <- H27.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y y x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H23.
apply H14.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite <- H27.
apply H23.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
split.
apply H17.
apply H25.
apply H24.
split.
apply Inverse_Map_Law_2.
split.
split.
apply H17.
apply H25.
apply H24.
split.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> H27.
symmetry.
apply (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
split.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
rewrite <- H27.
split.
apply H22.
apply (Ordered_Relation_Law_3 g Y y x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H23.
apply H14.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite <- H27.
apply H23.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
split.
apply H17.
apply H25.
apply H24.
split.
apply Inverse_Map_Law_2.
split.
split.
apply H17.
apply H25.
apply H24.
split.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
apply H21.
intros.
destruct H17.
destruct H23.
destruct H22.
destruct H25.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply H24.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H28.
apply H20.
rewrite <- (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
rewrite <- (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x6).
apply H26.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply H28.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H27.
intros.
destruct H21.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x5).
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X x3) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) (Predecessor_Set g Y z) x6).
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x2) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H23.
split.
apply Inverse_Map_Law_6.
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x4 x6 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x6).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
split.
apply H26.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x6) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H24.
split.
apply Inverse_Map_Law_6.
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x6).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H23.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H24.
apply H25.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H23.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H24.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x3) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x6).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x2) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x5).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x5) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply (Ordered_Relation_Law_3 f X x5 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H23.
split.
apply Inverse_Map_Law_6.
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x4 x6 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z) x6).
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
split.
apply H26.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x4 x6) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x2).
rewrite -> (Inverse_Map_Law_5 x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x4 x2 (Predecessor_Set g Y z) (Predecessor_Set f X x3) (Predecessor_Set g Y z)).
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x3) x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H19.
apply H20.
apply H24.
split.
apply Inverse_Map_Law_6.
apply H17.
split.
destruct H17.
destruct H17.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H14.
apply H25.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H24.
split.
destruct H17.
destruct H17.
apply H17.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x4 (Predecessor_Set f X x3) (Predecessor_Set g Y z)) x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H21.
apply H23.
destruct (Law_of_Excluded_Middle (Relation_Prop g z x2)).
apply H15.
assert (Totaly_Ordered_Relation g Y/\x2 ∈ Y/\z∈ Y).
split.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H10.
apply H6.
apply H13.
apply Totaly_Ordered_Relation_Law_2 in H16.
destruct H16.
destruct H14.
apply H16.
destruct H15.
apply H16.
intro.
apply H12.
rewrite <- H14.
apply H13.
split.
rewrite <- H8.
rewrite -> H13.
destruct H7.
destruct H14.
destruct H15.
apply H15.
intros.
destruct H7.
destruct H15.
destruct H16.
destruct H14.
assert (x3 ∈ x0/\x4 ∈ x0).
rewrite -> H8.
split.
apply H14.
apply H18.
apply H17 in H19.
split.
intro.
rewrite -> H13.
apply H19.
apply (Restriction_Relation_Law_3 f X x0 x3 x4).
split.
apply H5.
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
rewrite -> H8.
apply H14.
split.
rewrite -> H8.
apply H18.
apply H20.
intro.
apply (Restriction_Relation_Law_4 f X x0 x3 x4).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
rewrite -> H8.
apply H14.
split.
rewrite -> H8.
apply H18.
apply H19.
rewrite <- H13.
apply H20.

destruct (Law_of_Excluded_Middle (x1=Y)).
left.
assert (Well_Oredered_Relation f X/\(Complement_Set X x0) ⊂ X/\~(Complement_Set X x0)=∅).
split.
apply H.
split.
intro.
intro.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
intro.
apply H8.
apply Axiom_of_Extensionality.
intro.
split.
apply H5.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x0)).
apply H12.
destruct (Definition_of_Empty_Set z).
rewrite <- H10.
apply Complement_Set_Law_1.
split.
apply H11.
apply H12.
apply Well_Oredered_Relation_Law_6 in H10.
destruct H10.
destruct H10.
apply Complement_Set_Law_1 in H10.
destruct H10.
exists x.
exists x2.
split.
apply H10.
assert (Predecessor_Set_1 f X x2=x0).
apply Axiom_of_Extensionality.
intros.
split.
intro.
apply Predecessor_Set_1_Law_1 in H13.
destruct H13.
destruct H14.
destruct(Law_of_Excluded_Middle (z ∈ x0)).
apply H16.
destruct H15.
apply (Ordered_Relation_Law_4 f X z x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H14.
apply H11.
apply Complement_Set_Law_1.
split.
apply H13.
apply H16.
intro.
apply Predecessor_Set_1_Law_1.
split.
apply H5.
apply H13.
split.
destruct(Law_of_Excluded_Middle (Relation_Prop f z x2)).
apply H14.
assert (Relation_Prop f x2 z).
assert (Totaly_Ordered_Relation f X/\z ∈ X/\x2 ∈ X).
split.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H5.
apply H13.
apply H10.
apply Totaly_Ordered_Relation_Law_2 in H15.
destruct H15.
destruct H14.
apply H15.
apply H15.
destruct H12.
apply H2 in H13.
destruct H13.
destruct H12.
destruct H13.
destruct H16.
apply H2.
exists (Culculateion_Map x4 x2).
split.
apply H10.
assert (Culculateion_Map x4 x2 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3)).
split.
destruct H16.
destruct H17.
destruct H18.
destruct H18.
destruct H18.
apply H18.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply Predecessor_Set_Law_1 in H17.
destruct H17.
split.
apply H17.
exists (Restriction_Map x4 (Predecessor_Set f X x2)).
destruct H16.
destruct H19.
destruct H20.
split.
apply Predecessor_Set_Law_2.
split.
apply H10.
apply H.
split.
apply Predecessor_Set_Law_2.
split.
apply H17.
apply H0.
split.
assert (Map (Restriction_Map x4 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x4 x2))).
apply (Map_Law_5 (Restriction_Map x4 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) (Predecessor_Set g Y (Culculateion_Map x4 x2))).
split.
apply (Restriction_Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H15.
intros.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x5).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H15.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply H25.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x5 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H23.
apply H15.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H23.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H23.
split.
split.
apply H22.
destruct H20.
destruct H20.
intros.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
assert (y ∈ Predecessor_Set g Y x3).
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
apply H24 in H27.
destruct H27.
destruct H27.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
exists x5.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x5 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H28.
apply H25.
rewrite <- H28.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H28.
apply H25.
rewrite <- H28.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H28.
apply H25.
rewrite <- H28.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H28.
apply H25.
rewrite <- H28.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
rewrite <- H28.
apply H25.
rewrite <- H28.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x4 x2) x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
rewrite <- H28.
apply H26.
rewrite -> H28.
symmetry.
apply (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
split.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply Predecessor_Set_Law_1.
split.
apply H30.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x5 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x5).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x2).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
rewrite <- H28.
apply H26.
split.
apply H22.
destruct H20.
destruct H23.
intros.
destruct H25.
destruct H26.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H24.
split.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H28.
apply H15.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H29.
apply H15.
rewrite <- (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
rewrite <- (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x6).
apply H27.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply Predecessor_Set_Law_1.
split.
apply H30.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H29.
split.
apply H23.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply Predecessor_Set_Law_1.
split.
apply H30.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply H28.
intros.
destruct H22.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
rewrite -> (Restriction_Map_Law_3 x4 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x6).
assert (x5 ∈ Predecessor_Set f X x2).
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H24.
assert (x5 ∈ Predecessor_Set f X z).
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H15.
assert (x6 ∈ Predecessor_Set f X x2).
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H25.
assert (x6 ∈ Predecessor_Set f X z).
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H15.
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x5).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply (Ordered_Relation_Law_3 f X x5 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H24.
apply H15.
assert (Culculateion_Map x4 x5 ∈ Predecessor_Set g Y (Culculateion_Map x4 x2)).
apply Predecessor_Set_Law_1.
split.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H31.
destruct H31.
apply H31.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H30.
split.
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x2).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H21.
split.
apply H27.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x5 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H31.
destruct H31.
apply H31.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H24.
assert (Culculateion_Map x4 x6 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 x4 (Predecessor_Set f X z) (Predecessor_Set g Y x3) x6).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H15.
assert (Culculateion_Map x4 x6 ∈ Predecessor_Set g Y (Culculateion_Map x4 x2)).
apply Predecessor_Set_Law_1.
split.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply H32.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x6) (Culculateion_Map x4 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H33.
destruct H33.
apply H33.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H32.
split.
apply Predecessor_Set_Law_1.
split.
apply H17.
apply H18.
apply H21.
split.
apply H29.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x6 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H33.
destruct H33.
apply H33.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H15.
apply H25.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x4 x2)) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H31.
split.
apply H33.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H30.
split.
apply H32.
apply H21.
split.
apply H27.
apply H29.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
split.
apply H29.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
split.
apply H28.
apply H34.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
split.
apply H28.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x5 x6).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
split.
apply H29.
apply H21.
split.
apply H27.
apply H29.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H30.
split.
apply H32.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x4 x2)) (Culculateion_Map x4 x5) (Culculateion_Map x4 x6)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply H35.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H31.
split.
apply H33.
apply H34.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H25.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H22.
apply H24.
intro.
apply H12.
rewrite <- H14.
apply H13.
rewrite -> H13.
assert (Restriction_Relation g x1=g).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Restriction_Relation_Law_1 in H14.
destruct H14.
destruct H15.
destruct H15.
destruct H15.
destruct H16.
apply H14.
intro.
apply Restriction_Relation_Law_1.
split.
apply H14.
assert (Relation g Y).
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H15 in H14.
destruct H14.
destruct H14.
destruct H14.
destruct H16.
rewrite -> H9.
exists x3.
exists x4.
split.
apply H16.
split.
apply H17.
apply H14.
rewrite <- H14.
rewrite <- H9.
apply H7.

assert (Well_Oredered_Relation f X/\(Complement_Set X x0) ⊂ X/\~(Complement_Set X x0)=∅).
split.
apply H.
split.
intro.
intro.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply H10.
intro.
apply H8.
apply Axiom_of_Extensionality.
intro.
split.
apply H5.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x0)).
apply H12.
destruct (Definition_of_Empty_Set z).
rewrite <- H10.
apply Complement_Set_Law_1.
split.
apply H11.
apply H12.
apply Well_Oredered_Relation_Law_6 in H10.
assert (Well_Oredered_Relation g Y/\(Complement_Set Y x1) ⊂ Y/\~(Complement_Set Y x1)=∅).
split.
apply H0.
split.
intro.
intro.
apply Complement_Set_Law_1 in H11.
destruct H11.
apply H11.
intro.
apply H9.
apply Axiom_of_Extensionality.
intro.
split.
apply H6.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x1)).
apply H13.
destruct (Definition_of_Empty_Set z).
rewrite <- H11.
apply Complement_Set_Law_1.
split.
apply H12.
apply H13.
apply Well_Oredered_Relation_Law_6 in H11.
destruct H10.
destruct H10.
destruct H11.
destruct H11.
apply Complement_Set_Law_1 in H10.
destruct H10.
apply Complement_Set_Law_1 in H11.
destruct H11.
assert (Predecessor_Set_1 f X x2=x0).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Predecessor_Set_1_Law_1 in H16.
destruct H16.
destruct H17.
destruct (Law_of_Excluded_Middle (z ∈ x0)).
apply H19.
destruct H18.
apply (Ordered_Relation_Law_4 f X z x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H17.
apply H12.
apply Complement_Set_Law_1.
split.
apply H16.
apply H19.
intro.
apply Predecessor_Set_1_Law_1.
split.
apply H5.
apply H16.
split.
assert (Totaly_Ordered_Relation f X/\z ∈ X/\x2 ∈ X).
split.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H5.
apply H16.
apply H10.
apply Totaly_Ordered_Relation_Law_2 in H17.
destruct H17.
apply H17.
destruct H14.
apply H2 in H16.
destruct H16.
destruct H14.
destruct H16.
destruct H18.
destruct H18.
destruct H19.
destruct H20.
apply H2.
exists (Culculateion_Map x5 x2).
split.
apply H10.
assert (Culculateion_Map x5 x2 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x2).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
split.
apply H22.
exists (Restriction_Map x5 (Predecessor_Set f X x2)).
split.
apply Predecessor_Set_Law_2.
split.
apply H10.
apply H.
split.
apply Predecessor_Set_Law_2.
split.
apply H22.
apply H0.
assert (Bijective_Map (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
assert (Map (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
apply (Map_Law_5 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
split.
destruct H20.
destruct H20.
apply H20.
intro.
intro.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H17.
intros.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4)).
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map x5 x6 ∈ Predecessor_Set g Y x4).
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x6).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H17.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x6) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x6).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H17.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x2).
split.
destruct H20.
destruct H20.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x6 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H25.
apply H17.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply H25.
split.
destruct H20.
destruct H20.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H24.
apply H25.
split.
split.
apply H24.
intros.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
destruct H20.
destruct H20.
assert (y ∈ Predecessor_Set g Y x4).
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H23.
apply H28 in H29.
destruct H29.
destruct H29.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
exists x6.
split.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x6 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply H32.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply H31.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply H31.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x6) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply H32.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
rewrite <- H30.
split.
apply H25.
apply (Ordered_Relation_Law_3 g Y y (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H26.
apply H23.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x2).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
rewrite <- H30.
apply H26.
rewrite -> H30.
symmetry.
apply (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x6).
split.
apply H20.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply Predecessor_Set_Law_1.
split.
apply H32.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H33.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x6 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply H32.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply H31.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply H21.
split.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply H31.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map x5 x6) (Culculateion_Map x5 x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply H32.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x6).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H29.
apply H31.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X z) (Predecessor_Set g Y x4) x2).
split.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H17.
rewrite <- H30.
apply H26.
split.
apply H24.
destruct H20.
destruct H25.
intros.
destruct H27.
destruct H28.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H26.
split.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X x6 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H17.
split.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply (Ordered_Relation_Law_3 f X x7 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H17.
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x6).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x7).
apply H29.
split.
apply H25.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply Predecessor_Set_Law_1.
split.
apply H32.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H33.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply H31.
split.
apply H25.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply Predecessor_Set_Law_1.
split.
apply H32.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H33.
apply H17.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H30.
split.
apply H24.
intros.
destruct H25.
assert (x6 ∈ Predecessor_Set f X x2).
apply H25.
assert (x7 ∈ Predecessor_Set f X x2).
apply H26.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
assert (Predecessor_Set f X x2 ⊂ Predecessor_Set f X z).
intro.
intro.
apply Predecessor_Set_Law_1 in H31.
destruct H31.
apply Predecessor_Set_Law_1.
split.
apply H31.
apply (Ordered_Relation_Law_3 f X z0 x2 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H32.
apply H17.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x6 ∈ Predecessor_Set g Y (Culculateion_Map x5 x2)).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x6).
split.
destruct H24.
destruct H24.
apply H24.
apply H27.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x7 ∈ Predecessor_Set g Y (Culculateion_Map x5 x2)).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set g Y (Culculateion_Map x5 x2)) x7).
split.
destruct H24.
destruct H24.
apply H24.
apply H28.
assert (Predecessor_Set g Y (Culculateion_Map x5 x2) ⊂ Predecessor_Set g Y x4).
intro.
intro.
apply Predecessor_Set_Law_1 in H34.
destruct H34.
apply Predecessor_Set_Law_1.
split.
apply H34.
apply (Ordered_Relation_Law_3 g Y z0 (Culculateion_Map x5 x2) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H35.
apply H23.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y (Culculateion_Map x5 x2)) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H32.
split.
apply H33.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x4) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H34.
apply H32.
split.
apply H34.
apply H33.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x6).
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x7).
apply H21.
split.
apply H31.
apply H27.
apply H31.
apply H28.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X z) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H27.
split.
apply H31.
apply H28.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
split.
apply H28.
apply H35.
split.
destruct H20.
destruct H20.
apply H20.
split.
apply H31.
apply H28.
split.
destruct H20.
destruct H20.
apply H20.
split.
apply H31.
apply H27.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H27.
split.
apply H28.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X z) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H31.
apply H27.
split.
apply H31.
apply H28.
apply H21.
split.
apply H31.
apply H27.
apply H31.
apply H28.
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x6).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X z) (Predecessor_Set f X x2) (Predecessor_Set g Y x4) x7).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x4) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H34.
apply H32.
split.
apply H34.
apply H33.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y (Culculateion_Map x5 x2)) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X x2)) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H36.
destruct H36.
apply H36.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H32.
split.
apply H33.
apply H35.
split.
destruct H20.
destruct H20.
apply H20.
split.
apply H31.
apply H28.
split.
destruct H20.
destruct H20.
apply H20.
split.
apply H31.
apply H27.
intro.
apply H14.
rewrite <- H17.
apply H16.
assert (Predecessor_Set_1 g Y x3=x1).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Predecessor_Set_1_Law_1 in H17.
destruct H17.
destruct H18.
destruct (Law_of_Excluded_Middle (z ∈ x1)).
apply H20.
destruct H19.
apply (Ordered_Relation_Law_4 g Y z x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H18.
apply H13.
apply Complement_Set_Law_1.
split.
apply H17.
apply H20.
intro.
apply Predecessor_Set_1_Law_1.
split.
apply H6.
apply H17.
split.
assert (Totaly_Ordered_Relation g Y/\z ∈ Y/\x3 ∈ Y).
split.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H6.
apply H17.
apply H11.
apply Totaly_Ordered_Relation_Law_2 in H18.
destruct H18.
apply H18.
destruct H15.
apply H3 in H17.
destruct H17.
destruct H15.
destruct H17.
destruct H19.
destruct H19.
destruct H20.
destruct H21.
apply H3.
exists (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3).
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3 ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) x3).
split.
apply Inverse_Map_Law_2.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply Predecessor_Set_Law_1 in H23.
destruct H23.
split.
apply H23.
split.
apply H11.
exists (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))).
split.
apply Predecessor_Set_Law_2.
split.
apply H23.
apply H.
split.
apply Predecessor_Set_Law_2.
split.
apply H11.
apply H0.
assert (Bijective_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y x3)).
assert (Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y x3)).
apply (Map_Law_5 (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) (Predecessor_Set g Y x3)).
split.
apply (Restriction_Map_Law_2 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z)).
split.
apply H21.
intro.
intro.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H24.
intros.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
apply Predecessor_Set_Law_1.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x6).
split.
assert (Culculateion_Map x5 x6 ∈ Predecessor_Set g Y z).
apply (Map_Law_2 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z) x6).
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H24.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply H27.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map x5 x6) x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply H27.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z) x6).
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H24.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set g Y z) x3).
rewrite -> (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 x3 (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
apply H22.
split.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H24.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) x3).
split.
apply Inverse_Map_Law_2.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x4) x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply H27.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H26.
apply H24.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) x3).
split.
apply Inverse_Map_Law_2.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H26.
split.
apply Inverse_Map_Law_2.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
split.
destruct H21.
destruct H21.
apply H21.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H28.
apply H24.
apply Predecessor_Set_Law_1.
split.
apply H25.
apply H26.
split.
split.
apply H25.
intros.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
exists (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y).
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y)).
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) y).
split.
apply Inverse_Map_Law_2.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
split.
apply H28.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply H29.
split.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H24.
apply H22.
split.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply H29.
apply Predecessor_Set_Law_1.
split.
apply H23.
apply H24.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 y (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) y).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 x3 (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) x3).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) y x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H30.
destruct H30.
apply H30.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H27.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 y (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) y).
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply H21.
split.
apply Inverse_Map_Law_2.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
split.
destruct H21.
destruct H21.
apply H21.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply Predecessor_Set_Law_1.
split.
apply H28.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H29.
apply H24.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y ∈ Predecessor_Set f X x4).
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) y).
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) y) (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) y).
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) x3).
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H22.
split.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) y).
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply (Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) (Predecessor_Set g Y z) (Predecessor_Set f X x4) x3).
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 y (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) y).
rewrite -> (Composite_Map_Law_2 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x5 x3 (Predecessor_Set g Y z) (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Inverse_Map_Law_5 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set g Y z) x3).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) y x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H28.
destruct H28.
apply H28.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H27.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H18.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
split.
destruct H21.
destruct H21.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 g Y y x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H27.
apply H18.
split.
apply H25.
intros.
destruct H26.
destruct H27.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
rewrite -> (Identify_Map_Law_3 (Predecessor_Set f X x4) x6).
rewrite -> (Identify_Map_Law_3 (Predecessor_Set f X x4) x7).
rewrite -> (Inverse_Map_Law_4 x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)).
rewrite <- (Composite_Map_Law_2 x5 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x6 (Predecessor_Set f X x4) (Predecessor_Set g Y z) (Predecessor_Set f X x4)).
rewrite <- (Composite_Map_Law_2 x5 (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x7 (Predecessor_Set f X x4) (Predecessor_Set g Y z) (Predecessor_Set f X x4)).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x6).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x7).
rewrite -> H28.
split.
split.
destruct H21.
destruct H21.
apply H21.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H31.
destruct H31.
apply Predecessor_Set_Law_1.
split.
apply H31.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H32.
apply H24.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H30.
split.
destruct H21.
destruct H21.
apply H21.
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H31.
destruct H31.
apply Predecessor_Set_Law_1.
split.
apply H31.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H32.
apply H24.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H29.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X x7 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H24.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply Inverse_Map_Law_6.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H29.
apply H24.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H27.
apply (Ordered_Relation_Law_3 f X x7 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
apply H24.
apply Predecessor_Set_Law_1.
split.
apply H26.
apply (Ordered_Relation_Law_3 f X x6 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H29.
apply H24.
split.
apply H25.
intros.
destruct H26.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply Predecessor_Set_Law_1 in H27.
destruct H27.
assert (x6 ∈ Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)).
apply Predecessor_Set_Law_1.
split.
apply H26.
apply H28.
assert (x7 ∈ Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)).
apply Predecessor_Set_Law_1.
split.
apply H27.
apply H29.
assert (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) ⊂ Predecessor_Set f X x4).
intro.
intro.
apply Predecessor_Set_Law_1 in H32.
destruct H32.
apply Predecessor_Set_Law_1.
split.
apply H32.
apply (Ordered_Relation_Law_3 f X z0 (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3) x4).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H33.
apply H24.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x6 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y x3) x6).
split.
destruct H25.
destruct H25.
apply H25.
apply H30.
assert (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x7 ∈ Predecessor_Set g Y x3).
apply (Map_Law_2 (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y x3) x7).
split.
destruct H25.
destruct H25.
apply H25.
apply H31.
assert (Predecessor_Set g Y x3 ⊂ Predecessor_Set g Y z).
intro.
intro.
apply Predecessor_Set_Law_1 in H35.
destruct H35.
apply Predecessor_Set_Law_1.
split.
apply H35.
apply (Ordered_Relation_Law_3 g Y z0 x3 z).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H36.
apply H18.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H33.
split.
apply H34.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y z) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H35.
apply H33.
split.
apply H35.
apply H34.
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x6).
rewrite -> (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x7).
apply H22.
split.
apply H32.
apply H30.
apply H32.
apply H31.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x4) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H32.
apply H30.
split.
apply H32.
apply H31.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
split.
apply H31.
apply H36.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply H32.
apply H31.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply H32.
apply H30.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H30.
split.
apply H31.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x4) x6 x7).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H32.
apply H30.
split.
apply H32.
apply H31.
apply H22.
split.
apply H32.
apply H30.
apply H32.
apply H31.
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x6).
rewrite <- (Restriction_Map_Law_3 x5 (Predecessor_Set f X x4) (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3)) (Predecessor_Set g Y z) x7).
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y z) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H35.
apply H33.
split.
apply H35.
apply H34.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x6) (Culculateion_Map (Restriction_Map x5 (Predecessor_Set f X (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y z)) x3))) x7)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H37.
destruct H37.
apply H37.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply H33.
split.
apply H34.
apply H36.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply H32.
apply H31.
split.
destruct H21.
destruct H21.
apply H21.
split.
apply H32.
apply H30.
intro.
apply H15.
rewrite <- H18.
apply H17.
assert (~x2 ∈ x0).
apply H14.
destruct H18.
apply H2.
exists x3.
split.
apply H10.
split.
apply H11.
exists (Pair_Union_Set x (Single_Set (Ordered_Set x2 x3))).
split.
apply (Predecessor_Set_Law_2 f X x2).
split.
apply H10.
apply H.
split.
apply (Predecessor_Set_Law_2 g Y x3).
split.
apply H11.
apply H0.
assert (Bijective_Map (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3)).
assert (Map (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3)).
split.
intro.
intro.
apply Pair_Union_Set_Law_1 in H18.
destruct H18.
destruct H4.
apply H4 in H18.
destruct H18.
destruct H18.
destruct H18.
destruct H20.
exists x4.
exists x5.
split.
rewrite <- H16 in H18.
apply Predecessor_Set_1_Law_1 in H18.
destruct H18.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H18.
apply H22.
split.
rewrite <- H17 in H20.
apply Predecessor_Set_1_Law_1 in H20.
destruct H20.
destruct H22.
apply Predecessor_Set_Law_1.
split.
apply H20.
apply H22.
apply H21.
apply Single_Set_Law_1 in H18.
exists x2.
exists x3.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
apply H18.
intros.
apply Predecessor_Set_Law_1 in H18.
destruct H18.
destruct (Law_of_Excluded_Middle (x4=x2)).
exists x3.
split.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
rewrite -> H20.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
intros.
destruct H21.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
apply Pair_Union_Set_Law_1 in H21.
destruct H21.
destruct H4.
apply H4 in H21.
destruct H21.
destruct H21.
destruct H21.
destruct H25.
apply Ordered_Set_Law_2 in H26.
destruct H26.
destruct H14.
rewrite <- H20.
rewrite -> H26.
apply H21.
apply Single_Set_Law_1 in H21.
apply Ordered_Set_Law_2 in H21.
destruct H21.
symmetry.
apply H24.
exists (Culculateion_Map x x4).
split.
split.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 x x0 x1 x4).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
split.
apply H18.
split.
apply H19.
apply H20.
assert (Culculateion_Map x x4 ∈ x1).
apply (Map_Law_2 x x0 x1 x4).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
split.
apply H18.
split.
apply H19.
apply H20.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H21.
rewrite <- H17 in H21.
apply Predecessor_Set_1_Law_1 in H21.
destruct H21.
destruct H22.
apply H22.
intros.
destruct H21.
apply Pair_Union_Set_Law_1 in H21.
destruct H21.
apply Predecessor_Set_Law_1 in H22.
destruct H22.
symmetry.
assert (Ordered_Set x4 x' ∈ x).
apply H21.
assert (Map x x0 x1).
apply H4.
destruct H4.
apply H4 in H24.
destruct H24.
destruct H24.
destruct H24.
destruct H27.
apply Ordered_Set_Law_2 in H28.
destruct H28.
rewrite <- H28 in H24.
rewrite <- H29 in H27.
apply (Map_Law_3 x x0 x1 x4 x').
split.
apply H25.
split.
apply H24.
split.
apply H27.
apply H21.
apply Single_Set_Law_1 in H21.
apply Ordered_Set_Law_2 in H21.
destruct H21.
destruct H20.
apply H21.
assert (forall a:Set,a ∈ x0->Culculateion_Map (x ∪ Single_Set (Ordered_Set x2 x3)) a=Culculateion_Map x a).
intros.
symmetry.
apply (Map_Law_3 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) a (Culculateion_Map x a)).
split.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H19.
rewrite <- H16 in H19.
apply Predecessor_Set_1_Law_1 in H19.
destruct H19.
destruct H20.
apply H20.
split.
assert (Culculateion_Map x a ∈ x1).
apply (Map_Law_2 x x0 x1 a).
split.
apply H4.
apply H19.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H20.
rewrite <- H17 in H20.
apply Predecessor_Set_1_Law_1 in H20.
destruct H20.
destruct H21.
apply H21.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 x x0 x1 a).
split.
apply H4.
apply H19.
assert (Culculateion_Map (x ∪ Single_Set (Ordered_Set x2 x3)) x2=x3).
symmetry.
apply (Map_Law_3 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x2 x3).
split.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
split.
split.
apply H18.
intros.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
destruct (Law_of_Excluded_Middle (y=x3)).
exists x2.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
rewrite -> H23.
symmetry.
apply H20.
assert (y ∈ x1).
rewrite <- H17.
apply Predecessor_Set_1_Law_1.
split.
apply H21.
split.
apply H22.
apply H23.
assert (Bijective_Map x x0 x1).
destruct H7.
destruct H25.
destruct H26.
apply H26.
destruct H25.
destruct H25.
apply H27 in H24.
destruct H24.
destruct H24.
exists x4.
split.
apply Predecessor_Set_Law_1.
rewrite <- H16 in H24.
apply Predecessor_Set_1_Law_1 in H24.
destruct H24.
destruct H29.
split.
apply H24.
apply H29.
rewrite -> H28.
symmetry.
apply H19.
apply H24.
split.
apply H18.
intros.
assert (Bijective_Map x x0 x1).
destruct H7.
destruct H22.
destruct H23.
apply H23.
destruct H22.
destruct H23.
destruct H21.
destruct H25.
destruct (Law_of_Excluded_Middle (x4=x2)).
destruct (Law_of_Excluded_Middle (x5=x2)).
rewrite -> H27.
rewrite -> H28.
split.
rewrite -> H27 in H26.
rewrite -> H20 in H26.
rewrite -> H19 in H26.
destruct H15.
rewrite -> H26.
apply (Map_Law_2 x x0 x1 x5).
split.
apply H23.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
split.
apply H15.
split.
apply H25.
apply H28.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
split.
apply H25.
split.
apply H29.
apply H28.
destruct (Law_of_Excluded_Middle (x5=x2)).
rewrite -> H19 in H26.
rewrite -> H28 in H26.
rewrite -> H20 in H26.
destruct H15.
rewrite <- H26.
apply (Map_Law_2 x x0 x1 x4).
split.
apply H23.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
split.
apply H15.
split.
apply H21.
apply H27.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
split.
apply H21.
split.
apply H29.
apply H27.
apply H24.
assert (x4 ∈ x0).
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H21.
destruct H21.
split.
apply H21.
split.
apply H29.
apply H27.
assert (x5 ∈ x0).
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H25.
destruct H25.
split.
apply H25.
split.
apply H30.
apply H28.
split.
apply H29.
split.
apply H30.
rewrite <- (H19 x4).
rewrite <- (H19 x5).
apply H26.
apply H30.
apply H29.
split.
apply H18.
intros.
destruct H19.
assert (forall a:Set,a ∈ x0->Culculateion_Map (x ∪ Single_Set (Ordered_Set x2 x3)) a=Culculateion_Map x a).
intros.
symmetry.
apply (Map_Law_3 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) a (Culculateion_Map x a)).
split.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H21.
rewrite <- H16 in H21.
apply Predecessor_Set_1_Law_1 in H21.
destruct H21.
destruct H22.
apply H22.
split.
assert (Culculateion_Map x a ∈ x1).
apply (Map_Law_2 x x0 x1 a).
split.
apply H4.
apply H21.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H22.
rewrite <- H17 in H22.
apply Predecessor_Set_1_Law_1 in H22.
destruct H22.
destruct H23.
apply H23.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 x x0 x1 a).
split.
apply H4.
apply H21.
assert (Culculateion_Map (x ∪ Single_Set (Ordered_Set x2 x3)) x2=x3).
symmetry.
apply (Map_Law_3 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x2 x3).
split.
destruct H18.
destruct H18.
apply H18.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
destruct (Law_of_Excluded_Middle (x4=x2)).
destruct (Law_of_Excluded_Middle (x5=x2)).
rewrite -> H23.
rewrite -> H24.
rewrite -> H22.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) x3 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x2 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
rewrite -> H23.
rewrite -> H22.
rewrite -> H21.
split.
intro.
destruct H24.
apply (Ordered_Relation_Law_4 f X x5 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply H24.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x2 x5).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H24.
destruct H24.
apply H24.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
split.
apply H20.
apply H25.
intro.
assert (~x3=(Culculateion_Map x x5)).
intro.
destruct H15.
rewrite -> H26.
apply (Map_Law_2 x x0 x1 x5).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H15.
split.
apply H20.
apply H24.
destruct H26.
apply (Ordered_Relation_Law_4 g Y x3 (Culculateion_Map x x5)).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) x3 (Culculateion_Map x x5)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map x x5 ∈ x1).
apply (Map_Law_2 x x0 x1 x5).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H26.
apply H24.
rewrite <- H17 in H26.
apply Predecessor_Set_1_Law_1 in H26.
destruct H26.
destruct H27.
split.
apply H26.
apply H27.
apply H25.
assert (Culculateion_Map x x5 ∈ x1).
apply (Map_Law_2 x x0 x1 x5).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H26.
apply H24.
rewrite <- H17 in H26.
apply Predecessor_Set_1_Law_1 in H26.
destruct H26.
destruct H27.
apply H27.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H25.
apply H24.
destruct (Law_of_Excluded_Middle (x5=x2)).
rewrite -> H24.
rewrite -> H22.
rewrite -> H21.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x x4) x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
rewrite <- H21.
apply (Map_Law_2 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x4).
split.
destruct H18.
destruct H18.
apply H18.
apply H19.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H26.
apply H23.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply (Ordered_Relation_Law_2 g Y x3).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
apply H11.
assert (Culculateion_Map x x4 ∈ x1).
apply (Map_Law_2 x x0 x1 x4).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H26.
apply H23.
rewrite <- H17 in H26.
apply Predecessor_Set_1_Law_1 in H26.
destruct H26.
destruct H27.
apply H27.
intro.
rewrite <- H24.
rewrite -> H24.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x4 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H26.
destruct H26.
apply H26.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H19.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
apply H10.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply H26.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H25.
apply H23.
rewrite -> H21.
rewrite -> H21.
destruct H7.
destruct H25.
destruct H26.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x3) (Culculateion_Map x x4) (Culculateion_Map x x5)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
rewrite <- H21.
apply (Map_Law_2 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x4).
split.
destruct H18.
destruct H18.
apply H18.
apply H19.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H29.
apply H23.
split.
rewrite <- H21.
apply (Map_Law_2 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
split.
destruct H18.
destruct H18.
apply H18.
apply H20.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H29.
apply H24.
apply (Restriction_Relation_Law_4 g Y x1 (Culculateion_Map x x4) (Culculateion_Map x x5)).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x x0 x1 x4).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H29.
apply H23.
split.
apply (Map_Law_2 x x0 x1 x5).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H29.
apply H24.
apply H27.
split.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H29.
apply H23.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H29.
apply H24.
apply (Restriction_Relation_Law_3 f X x0 x4 x5).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H29.
apply H23.
split.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H29.
apply H24.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x4 x5).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H19.
split.
apply H20.
apply H28.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x4 x5).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
apply H19.
split.
apply H20.
apply (Restriction_Relation_Law_4 f X x0 x4 x5).
split.
apply H5.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H.
split.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H29.
apply H23.
split.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H29.
apply H24.
apply H27.
split.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
split.
apply H19.
split.
apply H29.
apply H23.
rewrite <- H16.
apply Predecessor_Set_1_Law_1.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
split.
apply H20.
split.
apply H29.
apply H24.
apply (Restriction_Relation_Law_3 g Y x1 (Culculateion_Map x x4) (Culculateion_Map x x5)).
split.
apply H6.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
apply (Map_Law_2 x x0 x1 x4).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H29.
apply H23.
split.
apply (Map_Law_2 x x0 x1 x5).
split.
apply H4.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H29.
apply H24.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x3) (Culculateion_Map x x4) (Culculateion_Map x x5)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H29.
destruct H29.
apply H29.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply H0.
split.
rewrite <- H21.
apply (Map_Law_2 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x4).
split.
destruct H18.
destruct H18.
apply H18.
apply H19.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H29.
apply H23.
split.
rewrite <- H21.
apply (Map_Law_2 (x ∪ Single_Set (Ordered_Set x2 x3)) (Predecessor_Set f X x2) (Predecessor_Set g Y x3) x5).
split.
destruct H18.
destruct H18.
apply H18.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_Law_1.
split.
apply H20.
apply H29.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H29.
apply H24.
apply H28.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H20.
destruct H20.
apply Predecessor_Set_1_Law_1.
split.
apply H20.
split.
apply H25.
apply H24.
rewrite <- H16.
apply Predecessor_Set_Law_1 in H19.
destruct H19.
apply Predecessor_Set_1_Law_1.
split.
apply H19.
split.
apply H25.
apply H23.
Qed.



(*狭義整列同型*)
Definition Narrow_Well_Oredered_Relation_homomorphism(M f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->((Relation_Prop f x1 x2)<->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Narrow_Well_Oredered_Relation_homomorphism_Law_1:forall f X:Set,Narrow_Well_Oredered_Relation f X->Narrow_Well_Oredered_Relation_homomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.
split.
apply (Identify_Map_Law_4 X).

intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 X x1).
rewrite <- (Identify_Map_Law_3 X x2).
split.
intro.
apply H2.
intro.
apply H2.
apply H1.
apply H0.
Qed.

Theorem Narrow_Well_Oredered_Relation_homomorphism_Law_2:forall M1 f X M2 g Y M3 h Z:Set,Narrow_Well_Oredered_Relation_homomorphism M1 f X g Y/\Narrow_Well_Oredered_Relation_homomorphism M2 g Y h Z->Narrow_Well_Oredered_Relation_homomorphism (Composite_Map M1 M2) f X h Z.
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
apply H.
split.
apply H4.
split.
apply (Composite_Map_Law_1 M1 M2 X Y Z).
split.
apply H2.
apply H5.
intros.
destruct H7.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H6.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
apply H3.
split.
apply H7.
apply H8.
apply H9.
intro.
apply H6 in H9.
apply H3 in H9.
apply H9.
split.
apply H7.
apply H8.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
split.
apply H2.
split.
apply H5.
apply H8.
split.
apply H2.
split.
apply H5.
apply H7.
Qed.

Theorem Narrow_Well_Oredered_Relation_homomorphism_Law_3:forall f X x1 x2:Set,(Narrow_Well_Oredered_Relation f X/\x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->Narrow_Well_Oredered_Relation_homomorphism (Identify_Map ((Predecessor_Set f X x1))) (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
split.

apply (Predecessor_Set_Law_3 f X x1).
split.
apply H0.
apply H.
split.

apply (Predecessor_Set_Law_3 f X x2).
split.
apply H1.
apply H.
split.

apply (Map_Law_5 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
apply Identify_Map_Law_4.
intros.
rewrite <- (Identify_Map_Law_3 (Predecessor_Set f X x1) x).
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply Predecessor_Set_Law_1.
split.
apply H3.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x x1 x2).
split.
apply H.
split.
apply H4.
apply H2.
apply H3.

intros.
destruct H3.
rewrite <- (Identify_Map_Law_3 (Predecessor_Set f X x1) x0).
rewrite <- (Identify_Map_Law_3 (Predecessor_Set f X x1) x3).
split.
intro.

apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply Predecessor_Set_Law_1.
split.
apply H3.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x0 x1 x2).
split.
apply H.
split.
apply H6.
apply H2.
split.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x3 x1 x2).
split.
apply H.
split.
apply H6.
apply H2.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply H3.
split.
apply H4.
apply H5.
intro.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply H3.
split.
apply H4.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply Predecessor_Set_Law_1.
split.
apply H3.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x0 x1 x2).
split.
apply H.
split.
apply H6.
apply H2.
split.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x3 x1 x2).
split.
apply H.
split.
apply H6.
apply H2.
apply H5.
apply H4.
apply H3.
Qed.

Theorem Narrow_Well_Oredered_Relation_homomorphism_Law_4:forall M f X x:Set,Narrow_Well_Oredered_Relation_homomorphism M f X f X/\Injective_Map M X X/\x ∈ X->Relation_Prop f x (Culculateion_Map M x)\/x=Culculateion_Map M x.
Proof.
intros.
destruct H.
destruct H0.
destruct H.
destruct H2.
destruct H3.

assert (Well_Oredered_Relation_homomorphism M (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X/\Injective_Map M X X/\x ∈ X).
split.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply H3.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H5.
apply H4 in H6.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H7.
apply Well_Oredered_Relation_Law_3.
destruct H7.
left.
apply H6.
apply H7.
destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
right.
exists (Culculateion_Map M x0).
split.
apply (Map_Law_2 M X X x0).
split.
apply H3.
apply H7.
rewrite -> H8.
rewrite -> H9.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H7.
apply Well_Oredered_Relation_Law_3.
destruct H7.
left.
apply H6.
apply H7.
right.
destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
assert (x1=x2).
destruct H0.
apply H10.
destruct H5.
split.
apply H5.
split.
apply H11.
rewrite -> H8.
rewrite -> H9.
split.
exists x1.
split.
destruct H5.
apply H5.
rewrite -> H10.
split.
split.
apply H0.
apply H1.
apply (Well_Oredered_Relation_homomorphism_Law_4 M (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x) in H5.
apply Well_Oredered_Relation_Law_3 in H5.
destruct H5.
left.
apply H5.
destruct H5.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
right.
rewrite -> H7.
rewrite -> H6.
split.
Qed.



Definition Narrow_Well_Oredered_Relation_Isomorphism(M f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\Bijective_Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X->(Relation_Prop f x1 x2<->Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_1:forall f X:Set,Narrow_Well_Oredered_Relation f X->Narrow_Well_Oredered_Relation_Isomorphism (Identify_Map X) f X f X.
Proof.
intros.
split.

apply H.
split.

apply H.
split.
apply Identify_Map_Law_2.

intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 X x1).
rewrite <- (Identify_Map_Law_3 X x2).
split.
intro.
apply H2.
intro.
apply H2.
apply H1.
apply H0.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_2:forall M1 M2 f X g Y h Z:Set,Narrow_Well_Oredered_Relation_Isomorphism M1 f X g Y/\Narrow_Well_Oredered_Relation_Isomorphism M2 g Y h Z->Narrow_Well_Oredered_Relation_Isomorphism (Composite_Map M1 M2) f X h Z.
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

apply H.
split.

apply H4.
split.

apply (Composite_Map_Law_5 M1 M2 X Y Z).
split.
apply H2.
apply H5.

intros.
destruct H7.
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
split.
intro.
apply H6.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
apply H3.
split.
apply H7.
apply H8.
apply H9.
intro.
apply H3.
split.
apply H7.
apply H8.
apply H6.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H8.
apply H9.
split.
destruct H2.
destruct H2.
apply H2.
split.
destruct H5.
destruct H5.
apply H5.
apply H8.
split.
destruct H2.
destruct H2.
apply H2.
split.
destruct H5.
destruct H5.
apply H5.
apply H7.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_3:forall M f X g Y:Set,Narrow_Well_Oredered_Relation_Isomorphism M f X g Y->Narrow_Well_Oredered_Relation_Isomorphism (Inverse_Map M X Y) g Y f X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

split.
apply H0.

split.
apply H.

split.
apply Inverse_Map_Law_6.
apply H1.

intros.
destruct H3.
split.
intro.
apply H2.
split.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x1).
split.
apply Inverse_Map_Law_6.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x2).
split.
apply Inverse_Map_Law_6.
apply H1.
apply H4.
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x1 Y X Y).
rewrite -> (Composite_Map_Law_2 (Inverse_Map M X Y) M x2 Y X Y).
rewrite <- (Inverse_Map_Law_5 M X Y).
rewrite <- (Identify_Map_Law_3 Y x1).
rewrite <- (Identify_Map_Law_3 Y x2).
apply H5.
apply H4.
apply H3.
apply H1.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H3.
intro.
rewrite -> (Identify_Map_Law_3 Y x1).
rewrite -> (Identify_Map_Law_3 Y x2).
rewrite -> (Inverse_Map_Law_5 M X Y).
rewrite <- (Composite_Map_Law_2 (Inverse_Map M X Y) M x1 Y X Y).
rewrite <- (Composite_Map_Law_2 (Inverse_Map M X Y) M x2 Y X Y).
apply H2.
split.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x1).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map M X Y) Y X x2).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H4.
apply H5.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H4.
split.
apply Inverse_Map_Law_2.
apply H1.
split.
destruct H1.
destruct H1.
apply H1.
apply H3.
apply H1.
apply H4.
apply H3.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_4:forall M f X:Set,Narrow_Well_Oredered_Relation_Isomorphism M f X f X->Identify_Map X=M.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

apply (Well_Oredered_Relation_Isomorphism_Law_4 M (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X).
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply H1.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H3.
destruct H3.
apply H2 in H4.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H6.
apply Well_Oredered_Relation_Law_3.
destruct H6.
left.
apply H4.
apply H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H7.
destruct H7.
right.
exists (Culculateion_Map M x).
split.
apply (Map_Law_2 M X X x).
split.
destruct H1.
destruct H1.
apply H1.
apply H6.
rewrite -> H7.
rewrite -> H8.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H6.
apply Well_Oredered_Relation_Law_3.
destruct H6.
left.
apply H4.
apply H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H7.
destruct H7.
right.
assert (x1=x2).
destruct H1.
destruct H9.
apply H10.
split.
apply H3.
split.
apply H5.
rewrite -> H7.
rewrite -> H8.
split.
exists x1.
split.
apply H3.
rewrite -> H9.
split.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_5:forall M1 M2 f X g Y:Set,Narrow_Well_Oredered_Relation_Isomorphism M1 f X g Y/\Narrow_Well_Oredered_Relation_Isomorphism M2 f X g Y->M1=M2.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H0.
destruct H4.
destruct H5.

apply (Well_Oredered_Relation_Isomorphism_Law_5 M1 M2 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y).
split.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Well_Oredered_Relation_Law_4.
apply H1.
split.
apply H2.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H10.
apply Well_Oredered_Relation_Law_3.
destruct H10.
left.
apply H8.
apply H10.
right.
destruct H10.
destruct H10.
apply Ordered_Set_Law_2 in H11.
destruct H11.
exists (Culculateion_Map M1 x).
split.
apply (Map_Law_2 M1 X Y x).
split.
destruct H2.
destruct H2.
apply H2.
apply H10.
rewrite -> H11.
rewrite -> H12.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H10.
apply Well_Oredered_Relation_Law_3.
destruct H10.
left.
apply H8.
apply H10.
destruct H10.
destruct H10.
apply Ordered_Set_Law_2 in H11.
destruct H11.
right.
exists x1.
split.
apply H7.
apply Ordered_Set_Law_2.
split.
split.
destruct H2.
destruct H13.
apply H14.
split.
apply H9.
split.
apply H7.
rewrite -> H11.
rewrite -> H12.
split.

split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Well_Oredered_Relation_Law_4.
apply H1.
split.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H6 in H8.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H9.
apply Well_Oredered_Relation_Law_3.
destruct H9.
left.
apply H8.
apply H9.
destruct H9.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
right.
exists (Culculateion_Map M2 x).
split.
apply (Map_Law_2 M2 X Y x).
split.
destruct H5.
destruct H5.
apply H5.
apply H9.
rewrite -> H10.
rewrite -> H11.
split.
intro.
apply Well_Oredered_Relation_Law_3 in H9.
apply Well_Oredered_Relation_Law_3.
destruct H9.
left.
apply H8.
apply H9.
destruct H9.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
right.
exists x1.
split.
destruct H7.
apply H7.
apply Ordered_Set_Law_2.
split.
split.
destruct H5.
destruct H12.
apply H13.
destruct H7.
split.
apply H14.
split.
apply H7.
rewrite -> H10.
rewrite -> H11.
split.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_6:forall M f X x1 x2:Set,(Narrow_Well_Oredered_Relation f X/\x1 ∈ X/\x2 ∈ X/\Narrow_Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2))->x1=x2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

apply (Well_Oredered_Relation_Isomorphism_Law_6 (M ∪ (Single_Set (Ordered_Set x1 x2))) (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x1 x2).
split.

apply Well_Oredered_Relation_Law_4.
apply H.

split.
apply H0.

split.
apply H1.

split.
apply (Predecessor_Set_Law_2 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x1).
split.
apply H0.
apply Well_Oredered_Relation_Law_4.
apply H.

split.
apply (Predecessor_Set_Law_2 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x2).
split.
apply H1.
apply Well_Oredered_Relation_Law_4.
apply H.

assert (Bijective_Map (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x2)).
assert (Map (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x2)).
destruct H2.
destruct H3.
destruct H4.
split.
intros.
apply Pair_Union_Set_Law_1 in H6.
destruct H6.
destruct H4.
destruct H4.
destruct H4.
apply H4 in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H10.
exists x.
exists x0.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply Well_Oredered_Relation_Law_3.
left.
apply H12.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply Well_Oredered_Relation_Law_3.
left.
apply H13.
apply H11.
apply Single_Set_Law_1 in H6.
exists x1.
exists x2.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply H6.
intros.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply Well_Oredered_Relation_Law_3 in H7.
destruct H7.
exists (Culculateion_Map M x).
split.
split.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x).
split.
destruct H4.
destruct H4.
apply H4.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H7.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map M x ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x).
split.
apply H4.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H7.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
split.
apply H8.
apply Well_Oredered_Relation_Law_3.
left.
apply H9.
intros.
destruct H8.
apply Pair_Union_Set_Law_1 in H8.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Well_Oredered_Relation_Law_3 in H10.
destruct H8.
symmetry.
apply (Map_Law_3 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x x').
split.
destruct H4.
destruct H4.
apply H4.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H7.
split.
destruct H4.
destruct H4.
destruct H4.
apply H4 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H14.
apply Ordered_Set_Law_2 in H15.
destruct H15.
rewrite -> H16.
apply H14.
apply H8.
apply Single_Set_Law_1 in H8.
apply Ordered_Set_Law_2 in H8.
destruct H8.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x).
split.
apply H.
apply H6.
rewrite <- H8 in H7.
apply H7.
destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
exists x2.
split.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
rewrite -> H8.
rewrite -> H9.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
intros.
destruct H10.
apply Pair_Union_Set_Law_1 in H10.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
destruct H10.
destruct H4.
destruct H4.
destruct H4.
apply H4 in H10.
destruct H10.
destruct H10.
destruct H10.
destruct H16.
apply Ordered_Set_Law_2 in H17.
destruct H17.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x0).
split.
apply H.
apply H7.
rewrite <- H17 in H19.
rewrite -> H9 in H19.
rewrite -> H8 in H19.
apply H19.
apply Single_Set_Law_1 in H10.
apply Ordered_Set_Law_2 in H10.
destruct H10.
symmetry.
apply H13.

destruct H2.
destruct H4.
destruct H5.
destruct H5.
split.
destruct H5.
split.
apply H3.
intros.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Well_Oredered_Relation_Law_3 in H10.
destruct H10.
assert (y ∈ Predecessor_Set f X x2).
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H10.
apply H8 in H11.
destruct H11.
destruct H11.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
exists x.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply Well_Oredered_Relation_Law_3.
left.
apply H13.
apply (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2)).
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply Well_Oredered_Relation_Law_3.
left.
apply H13.
split.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply Pair_Union_Set_Law_1.
left.
rewrite -> H12.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x).
split.
apply H5.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply H13.
destruct H10.
destruct H10.
apply Ordered_Set_Law_2 in H11.
destruct H11.
exists x1.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
rewrite -> H11.
rewrite <- H12.
apply (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2).
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.

destruct H7.
split.
apply H3.
intros.
destruct H9.
destruct H10.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Well_Oredered_Relation_Law_3 in H12.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply Well_Oredered_Relation_Law_3 in H13.
destruct H12.
destruct H13.
apply H8.
split.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
rewrite -> (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0 (Culculateion_Map M x0)).
rewrite -> (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3 (Culculateion_Map M x3)).
apply H11.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply Well_Oredered_Relation_Law_3.
left.
apply H13.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
split.
apply Predecessor_Set_Law_1.
split.
apply H14.
apply Well_Oredered_Relation_Law_3.
left.
apply H15.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H12.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
split.
apply H14.
apply Well_Oredered_Relation_Law_3.
left.
apply H15.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
destruct H7.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0 (Culculateion_Map M x0)) in H11.
destruct H13.
destruct H13.
apply Ordered_Set_Law_2 in H15.
destruct H15.
rewrite -> H15 in H11.
rewrite <- H16 in H11.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2) in H11.
assert (Ordered_Set x0 x2 ∈ M).
rewrite <- H11.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
split.
apply H7.
apply H14.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
apply H7 in H17.
destruct H17.
destruct H17.
destruct H17.
destruct H18.
apply Ordered_Set_Law_2 in H19.
destruct H19.
rewrite <- H20 in H18.
apply Predecessor_Set_Law_1 in H18.
destruct H18.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x2).
split.
apply H.
apply H1.
apply H21.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H12.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
split.
apply H7.
apply H14.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
split.
apply Predecessor_Set_Law_1.
split.
apply H15.
apply Well_Oredered_Relation_Law_3.
left.
apply H16.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
split.
apply H7.
apply H14.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply H12.
destruct H12.
destruct H12.
apply Ordered_Set_Law_2 in H14.
destruct H14.
rewrite -> H14 in H11.
rewrite <- H15 in H11.
destruct H13.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3 (Culculateion_Map M x3)) in H11.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2) in H11.
assert (Ordered_Set x3 x2 ∈ M).
rewrite -> H11.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
destruct H7.
apply H7 in H16.
destruct H16.
destruct H16.
destruct H16.
destruct H18.
apply Ordered_Set_Law_2 in H19.
destruct H19.
rewrite <- H20 in H18.
apply Predecessor_Set_Law_1 in H18.
destruct H18.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x2).
split.
apply H.
apply H18.
apply H21.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply Well_Oredered_Relation_Law_3.
left.
apply H13.
assert (Culculateion_Map M x3 ∈  Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
apply Predecessor_Set_Law_1 in H16.
destruct H16.
split.
apply Predecessor_Set_Law_1.
split.
apply H16.
apply Well_Oredered_Relation_Law_3.
left.
apply H17.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
apply H7.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply H13.
destruct H13.
destruct H13.
apply Ordered_Set_Law_2 in H16.
destruct H16.
rewrite -> H14.
rewrite <- H15.
rewrite -> H16.
rewrite <- H17.
split.
split.
apply H3.

intros.
destruct H4.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
apply Well_Oredered_Relation_Law_3 in H6.
apply Predecessor_Set_Law_1 in H5.
destruct H5.
apply Well_Oredered_Relation_Law_3 in H7.
destruct H6.
destruct H7.
split.
intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) (Culculateion_Map (M ∪ Single_Set (Ordered_Set x1 x2)) x0) (Culculateion_Map (M ∪ Single_Set (Ordered_Set x1 x2)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply (Map_Law_2 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0).
split.
destruct H3.
destruct H3.
apply H3.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
apply (Map_Law_2 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3).
split.
destruct H3.
destruct H3.
apply H3.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0 (Culculateion_Map M x0)).
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3 (Culculateion_Map M x3)).
apply Well_Oredered_Relation_Law_3.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) x0 x3).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
apply H8.
apply Well_Oredered_Relation_Law_3 in H9.
destruct H9.
left.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) (Culculateion_Map M x0) (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply H10.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
assert (Relation_Prop (Restriction_Relation f (Predecessor_Set f X x1)) x0 x3).
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply H10.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply H9.
destruct H2.
destruct H11.
destruct H12.
apply H13.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply H10.
right.
destruct H9.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H10.
rewrite -> H11.
exists (Culculateion_Map M x).
split.
assert (Culculateion_Map M x ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x).
split.
destruct H2.
destruct H12.
destruct H13.
destruct H13.
destruct H13.
apply H13.
apply Predecessor_Set_Law_1.
split.
apply H9.
rewrite <- H10.
apply H6.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
apply H12.
split.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
apply Predecessor_Set_Law_1.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.

intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
apply Well_Oredered_Relation_Law_3.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) (Culculateion_Map M x0) (Culculateion_Map M x3)).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) (Culculateion_Map M x0) (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H9.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
split.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
rewrite -> (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0 (Culculateion_Map M x0)).
rewrite -> (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3 (Culculateion_Map M x3)).
apply H8.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
split.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply Predecessor_Set_Law_1.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
apply H10.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Well_Oredered_Relation_Law_3 in H9.
destruct H9.
left.
destruct H2.
destruct H10.
destruct H11.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x1) x0 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply H13.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply H12.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) (Culculateion_Map M x0) (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply H13.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply H9.
right.
destruct H9.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
exists x0.
split.
apply H4.
apply Ordered_Set_Law_2.
split.
split.
destruct H2.
destruct H12.
destruct H13.
destruct H13.
destruct H15.
apply H16.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
rewrite -> H10.
rewrite -> H11.
split.

destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H8.
rewrite <- H9.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x0 (Culculateion_Map M x0)).
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2).
split.
intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) (Culculateion_Map M x0) x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H11.
destruct H12.
destruct H12.
destruct H12.
apply H12.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply Well_Oredered_Relation_Law_3.
left.
apply H12.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Well_Oredered_Relation_Law_3.
left.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H11.
destruct H12.
destruct H12.
apply H12.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H12.
intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) x0 x1).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply Well_Oredered_Relation_Law_3.
left.
apply H6.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
split.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply Well_Oredered_Relation_Law_3.
left.
apply H11.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0).
split.
destruct H2.
destruct H12.
destruct H13.
destruct H13.
destruct H13.
apply H13.
apply Predecessor_Set_Law_1.
split.
apply H4.
apply H6.

destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H8.
rewrite <- H9.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2).
destruct H7.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x3 (Culculateion_Map M x3)).
split.
intro.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) x1 x3).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) x1 x3).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
apply H10.
apply Well_Oredered_Relation_Law_3 in H11.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x1).
split.
apply H.
apply H0.
destruct H11.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x1 x3 x1).
split.
apply H.
split.
apply H11.
apply H7.
destruct H11.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
rewrite -> H13 in H7.
rewrite <- H12 in H7.
apply H7.

intro.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) x2 (Culculateion_Map M x3)).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x2 (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
split.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H11.
destruct H12.
destruct H12.
destruct H12.
apply H12.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply Predecessor_Set_Law_1.
split.
apply H11.
apply Well_Oredered_Relation_Law_3.
left.
apply H12.
apply H10.
apply Well_Oredered_Relation_Law_3 in H11.
destruct H11.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H12.
destruct H13.
destruct H13.
destruct H13.
apply H13.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x2).
split.
apply H.
apply H1.
apply (Narrow_Well_Oredered_Relation_Law_2 f X x2 (Culculateion_Map M x3) x2).
split.
apply H.
split.
apply H11.
apply H13.
destruct H11.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H14.
destruct H15.
destruct H15.
destruct H15.
apply H15.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
rewrite -> H13 in H15.
rewrite <- H12 in H15.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x2).
split.
apply H.
apply H1.
apply H15.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
split.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply Predecessor_Set_Law_1.
split.
apply H10.
apply Well_Oredered_Relation_Law_3.
left.
apply H11.
apply Pair_Union_Set_Law_1.
left.
apply (Map_Law_1 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3).
split.
destruct H2.
destruct H10.
destruct H11.
destruct H11.
destruct H11.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H5.
apply H7.

destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H10.
rewrite <- H11.
rewrite <- (Map_Law_3 (M ∪ Single_Set (Ordered_Set x1 x2)) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x1 x2).
split.
intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x2) x2 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply H13.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.

intro.
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X (Predecessor_Set (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=Ordered_Set x x))) X x1) x1 x1).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply H13.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
split.
destruct H3.
destruct H3.
apply H3.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply Well_Oredered_Relation_Law_3.
right.
exists x1.
split.
apply H0.
split.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply Well_Oredered_Relation_Law_3.
right.
exists x2.
split.
apply H1.
split.
apply Pair_Union_Set_Law_1.
right.
apply Single_Set_Law_1.
split.
Qed.

Theorem Narrow_Well_Oredered_Relation_Isomorphism_Law_7:forall f X g Y:Set,(Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y)->((exists M x0:Set,x0 ∈ X/\Narrow_Well_Oredered_Relation_Isomorphism M (Restriction_Relation f (Predecessor_Set f X x0)) (Predecessor_Set f X x0) g Y)\/(exists M:Set,Narrow_Well_Oredered_Relation_Isomorphism M f X g Y)\/(exists M y0:Set,y0 ∈ Y/\Narrow_Well_Oredered_Relation_Isomorphism M f X (Restriction_Relation g (Predecessor_Set g Y y0)) (Predecessor_Set g Y y0))).
Proof.
intros.
destruct H.
assert (Well_Oredered_Relation (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X/\Well_Oredered_Relation (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y).
split.
apply Well_Oredered_Relation_Law_4.
apply H.
apply Well_Oredered_Relation_Law_4.
apply H0.
apply (Well_Oredered_Relation_Isomorphism_Law_7 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y) in H1.

destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert (Predecessor_Set_1 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X x0=Predecessor_Set f X x0).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Predecessor_Set_1_Law_1 in H6.
destruct H6.
destruct H7.
apply Well_Oredered_Relation_Law_3 in H7.
destruct H7.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H7.
destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite -> H9 in H8.
rewrite <- H10 in H8.
destruct H8.
split.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply Predecessor_Set_1_Law_1.
split.
apply H6.
split.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
intro.
apply (Narrow_Well_Oredered_Relation_Law_4 f X z).
split.
apply H.
apply H6.
rewrite <- H8 in H7.
apply H7.
left.
exists x.
exists x0.
split.
apply H1.
split.
apply (Predecessor_Set_Law_3 f X x0).
split.
apply H1.
apply H.
split.
apply H0.
split.
rewrite <- H6.
apply H4.
intros.
assert (x1 ∈ Predecessor_Set f X x0/\x2 ∈ Predecessor_Set f X x0).
apply H7.
destruct H8.
split.
intro.
rewrite <- H6 in H7.
apply H5 in H7.
rewrite -> H6 in H7.
assert (Relation_Prop (Restriction_Relation (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) (Predecessor_Set f X x0)) x1 x2).
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X (Predecessor_Set f X x0) x1 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply H8.
split.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x0) x1 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply H8.
split.
apply H9.
apply H10.
apply H7 in H11.
apply Well_Oredered_Relation_Law_3 in H11.
destruct H11.
apply H11.
destruct H11.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x1).
split.
apply H.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply H8.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x0) x1 x1).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply H8.
split.
apply H8.
rewrite -> H6 in H4.
destruct H4.
destruct H14.
rewrite -> (H15 x2 x1) in H10.
apply H10.
split.
apply H9.
split.
apply H8.
rewrite -> H12.
apply H13.
intro.
rewrite <- H6 in H7.
apply H5 in H7.
rewrite -> H6 in H7.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) (Culculateion_Map x x1) (Culculateion_Map x x2)).
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply H7 in H11.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) x1 x2).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X (Predecessor_Set f X x0) x1 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
apply H12.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H.
split.
apply H8.
split.
apply H9.
apply H11.
apply Well_Oredered_Relation_Law_3 in H12.
destruct H12.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x0) x1 x2).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H13.
destruct H13.
apply H13.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H.
split.
apply H8.
split.
apply H9.
apply H12.
destruct H12.
destruct H12.
apply Ordered_Set_Law_2 in H13.
destruct H13.
destruct (Narrow_Well_Oredered_Relation_Law_4 g Y (Culculateion_Map x x3)).
split.
apply H0.
apply (Map_Law_2 x (Predecessor_Set f X x0) Y x3).
split.
rewrite <- H6.
destruct H4.
destruct H4.
apply H4.
rewrite <- H13.
apply H8.
rewrite -> H13 in H10.
rewrite -> H14 in H10.
apply H10.

destruct H1.
right.
left.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
exists x.
split.
apply H.
split.
apply H0.
split.
apply H3.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H5.
apply H4 in H6.
split.
intro.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) x1 x2).
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
apply H6 in H8.
apply Well_Oredered_Relation_Law_3 in H8.
destruct H8.
apply H8.
destruct H8.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x1).
split.
apply H.
destruct H5.
apply H5.
destruct H3.
destruct H11.
rewrite -> (H12 x2 x1) in H7.
apply H7.
destruct H5.
split.
apply H13.
split.
apply H5.
rewrite -> H9.
apply H10.
intro.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) (Culculateion_Map x x1) (Culculateion_Map x x2)).
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
apply H6 in H8.
apply Well_Oredered_Relation_Law_3 in H8.
destruct H8.
apply H8.
destruct H8.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
destruct (Narrow_Well_Oredered_Relation_Law_4 g Y (Culculateion_Map x x0)).
split.
apply H0.
apply (Map_Law_2 x X Y x0).
split.
destruct H3.
destruct H3.
apply H3.
apply H8.
rewrite -> H9 in H7.
rewrite -> H10 in H7.
apply H7.

destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert (Predecessor_Set_1 (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y x0=Predecessor_Set g Y x0).
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply Predecessor_Set_1_Law_1 in H6.
destruct H6.
destruct H7.
apply Well_Oredered_Relation_Law_3 in H7.
destruct H7.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H7.
destruct H7.
destruct H7.
apply Ordered_Set_Law_2 in H9.
destruct H9.
destruct H8.
rewrite -> H10.
apply H9.
intro.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply Predecessor_Set_1_Law_1.
split.
apply H6.
split.
apply Well_Oredered_Relation_Law_3.
left.
apply H7.
intro.
destruct (Narrow_Well_Oredered_Relation_Law_4 g Y z).
split.
apply H0.
apply H6.
rewrite <- H8 in H7.
apply H7.
right.
right.
rewrite -> H6 in H5.
rewrite -> H6 in H4.
exists x.
exists x0.
split.
apply H1.
split.
apply H.
split.
apply Predecessor_Set_Law_3.
split.
apply H1.
apply H0.
split.
apply H4.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
destruct H7.
apply H5 in H8.
split.
intro.
apply (Restriction_Relation_Law_3 g Y (Predecessor_Set g Y x0) (Culculateion_Map x x1) (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H0.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x1).
split.
destruct H4.
destruct H4.
apply H4.
apply H7.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x2).
split.
destruct H4.
destruct H4.
apply H4.
apply H9.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) x1 x2).
apply Well_Oredered_Relation_Law_3.
left.
apply H10.
apply H8 in H11.
assert (Relation_Prop (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) (Culculateion_Map x x1) (Culculateion_Map x x2)).
apply (Restriction_Relation_Law_4 (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y (Predecessor_Set g Y x0) (Culculateion_Map x x1) (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
apply H12.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H0.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x1).
split.
destruct H4.
destruct H4.
apply H4.
apply H7.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x2).
split.
destruct H4.
destruct H4.
apply H4.
apply H9.
apply H11.
apply Well_Oredered_Relation_Law_3 in H12.
destruct H12.
apply H12.
destruct H12.
destruct H12.
apply Ordered_Set_Law_2 in H13.
destruct H13.
destruct (Narrow_Well_Oredered_Relation_Law_4 f X x1).
split.
apply H.
apply H7.
destruct H4.
destruct H15.
rewrite -> (H16 x2 x1) in H10.
apply H10.
split.
apply H9.
split.
apply H7.
rewrite -> H13.
apply H14.
intro.
assert (Relation_Prop (Restriction_Relation (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) (Predecessor_Set g Y x0)) (Culculateion_Map x x1) (Culculateion_Map x x2)).
apply (Restriction_Relation_Law_3 (Prop_Set (fun a=>a ∈ g\/(exists x:Set,x ∈ Y/\a=(Ordered_Set x x)))) Y (Predecessor_Set g Y x0) (Culculateion_Map x x1) (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
apply Well_Oredered_Relation_Law_5.
apply Well_Oredered_Relation_Law_4.
apply H0.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x1).
split.
destruct H4.
destruct H4.
apply H4.
apply H7.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x2).
split.
destruct H4.
destruct H4.
apply H4.
apply H9.
apply Well_Oredered_Relation_Law_3.
left.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x0) (Culculateion_Map x x1) (Culculateion_Map x x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H0.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x1).
split.
destruct H4.
destruct H4.
apply H4.
apply H7.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x2).
split.
destruct H4.
destruct H4.
apply H4.
apply H9.
apply H10.
apply H8 in H11.
apply Well_Oredered_Relation_Law_3 in H11.
destruct H11.
apply H11.
destruct H11.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
destruct (Narrow_Well_Oredered_Relation_Law_4 g Y (Culculateion_Map x x3)).
split.
apply H0.
assert (Culculateion_Map x x3 ∈ Predecessor_Set g Y x0).
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x3).
split.
destruct H4.
destruct H4.
apply H4.
rewrite <- H12.
apply H7.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
rewrite -> H12 in H10.
rewrite -> H13 in H10.
apply (Restriction_Relation_Law_4 g Y (Predecessor_Set g Y x0) (Culculateion_Map x x3) (Culculateion_Map x x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Narrow_Well_Oredered_Relation_Law_1.
apply H0.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x3).
split.
destruct H4.
destruct H4.
apply H4.
apply H11.
split.
apply (Map_Law_2 x X (Predecessor_Set g Y x0) x3).
split.
destruct H4.
destruct H4.
apply H4.
apply H11.
apply H10.
Qed.