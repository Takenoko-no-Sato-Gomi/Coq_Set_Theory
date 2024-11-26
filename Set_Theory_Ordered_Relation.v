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
Definition Well_Oredered_Relation_homomorphism(M f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->(Relation_Prop f x1 x2->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

Definition Well_Oredered_Relation_Injective_homomorphism(M f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\Injective_Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->(Relation_Prop f x1 x2->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2))).

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
apply (Identify_Map_Law_3 X) in H0.
apply (Identify_Map_Law_3 X) in H2.
rewrite <- H0.
rewrite <- H2.
apply H1.
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
rewrite <- (Composite_Map_Law_2 M1 M2 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 M1 M2 x2 X Y Z).
apply H6.
destruct H7.
split.
apply (Map_Law_2 M1 X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 M1 X Y x2).
split.
apply H2.
apply H9.
apply H3.
apply H7.
apply H8.
destruct H7.
split.
apply H2.
split.
apply H5.
apply H9.
split.
apply H2.
split.
apply H5.
destruct H7.
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
split.
intros.
apply Identify_Map_Law_1 in H3.
destruct H3.
destruct H3.
exists x.
exists x.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
split.
apply H3.
destruct H.
destruct H.
destruct H.
destruct H8.
destruct H9.
apply (H9 x x1 x2).
split.
apply H5.
apply H2.
apply H4.
intros.
exists x.
split.
split.
apply Identify_Map_Law_1.
exists x.
split.
apply H3.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
split.
apply H3.
destruct H.
destruct H.
destruct H.
destruct H7.
destruct H8.
apply (H8 x x1 x2).
split.
apply H4.
apply H2.
intros.
destruct H4.
apply Identify_Map_Law_1 in H4.
destruct H4.
destruct H4.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H6.
rewrite -> H7.
split.

split.
apply H3.
intros.
destruct H4.
rewrite <- (Map_Law_3 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x2) x0 x0).
rewrite <- (Map_Law_3 (Identify_Map (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Predecessor_Set f X x2) x3 x3).
apply Restriction_Relation_Law_1.
apply Restriction_Relation_Law_1 in H5.
destruct H5.
split.
apply H5.
destruct H7.
exists x0.
exists x3.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
split.
apply H4.
destruct H.
destruct H.
destruct H.
destruct H11.
destruct H12.
apply (H12 x0 x1 x2).
split.
apply H8.
apply H2.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
split.
apply H6.
destruct H.
destruct H.
destruct H.
destruct H11.
destruct H12.
apply (H12 x3 x1 x2).
split.
apply H8.
apply H2.
split.
split.
apply H3.
split.
apply H6.
split.
apply Predecessor_Set_Law_1.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
split.
apply H6.
destruct H.
destruct H.
destruct H.
destruct H10.
destruct H11.
apply (H11 x3 x1 x2).
split.
apply H7.
apply H2.
apply Identify_Map_Law_1.
exists x3.
split.
apply H6.
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
destruct H.
destruct H.
destruct H.
destruct H10.
destruct H11.
apply (H11 x0 x1 x2).
split.
apply H7.
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
apply H3.
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
split.

destruct (Law_of_Excluded_Middle (Relation_Prop f x1 x2)).
apply H4.
assert (Relation_Prop f x2 x1).
assert (Totaly_Ordered_Relation f X/\x2 ∈ X/\x1 ∈ X).
split.
destruct H.
apply H.
split.
apply H1.
apply H0.
apply Totaly_Ordered_Relation_Law_2 in H5.
destruct H5.
apply H5.
destruct H4.
apply H5.
assert (~x1=x2).
intro.
apply H4.
rewrite -> H6 in H5.
rewrite -> H6.
apply H5.
apply (Ordered_Relation_Law_3 f X x1 (Culculateion_Map M x1) x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x1) x1 (Culculateion_Map M x1)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply H7.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply (Ordered_Relation_Law_2 f X x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H0.
split.
assert (Culculateion_Map M x1 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply (Ordered_Relation_Law_2 f X x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H0.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply Predecessor_Set_Law_1.
split.
apply H7.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map M x1) x2 x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H8.
apply H5.
apply (Well_Oredered_Relation_homomorphism_Law_4 M (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) x1).
split.
destruct H3.
destruct H7.
destruct H8.
split.
apply H3.
split.
apply H3.
split.
apply (Map_Law_5 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map M x ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H10.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
assert (Culculateion_Map M x ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H10.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map M x) x2 x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H13.
apply H5.
intros.
assert (x0 ∈ Predecessor_Set f X x1/\x3 ∈ Predecessor_Set f X x1).
apply H10.
apply H9 in H10.
apply H10 in H11.
destruct H12.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x1) (Culculateion_Map M x0) (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H12.
apply H14.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
apply H15.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map M x0) x2 x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
assert (Culculateion_Map M x0 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H12.
apply H14.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
apply H16.
apply H5.
split.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
assert (Culculateion_Map M x3 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map M x3) x2 x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H15.
apply H5.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) (Culculateion_Map M x0) (Culculateion_Map M x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H12.
split.
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply H10.
apply H9.
split.
apply H12.
apply H13.
apply H11.
split.
split.
apply (Map_Law_5 M (Predecessor_Set f X x1) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
apply H8.
intros.
assert (Culculateion_Map M x ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H3.
destruct H8.
destruct H9.
destruct H9.
destruct H9.
apply H9.
apply H7.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply Predecessor_Set_Law_1.
split.
apply H8.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map M x) x2 x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H9.
apply H5.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H10.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply (Ordered_Relation_Law_2 f X x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H0.
assert (Culculateion_Map M x1 ∈ Predecessor_Set f X x2).
apply (Map_Law_2 M (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H0.
apply (Ordered_Relation_Law_2 f X x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H0.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply H8.

apply Well_Oredered_Relation_Isomorphism_Law_3 in H3.
destruct (Law_of_Excluded_Middle (Relation_Prop f x2 x1)).
apply H4.
assert (Relation_Prop f x1 x2).
assert (Totaly_Ordered_Relation f X/\x2 ∈ X/\x1 ∈ X).
split.
destruct H.
apply H.
split.
apply H1.
apply H0.
apply Totaly_Ordered_Relation_Law_2 in H5.
destruct H5.
destruct H4.
apply H5.
apply H5.
assert (~x1=x2).
intro.
apply H4.
rewrite -> H6 in H5.
rewrite -> H6.
apply H5.
apply (Ordered_Relation_Law_3 f X x2 (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x2) x1).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x2) x2 (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x2)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply H7.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H1.
split.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x2 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
apply Inverse_Map_Law_2.
destruct H2.
destruct H7.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H1.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply Predecessor_Set_Law_1.
split.
apply H7.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x2) x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H8.
apply H5.

apply (Well_Oredered_Relation_homomorphism_Law_4 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) x2).
split.
destruct H3.
destruct H7.
destruct H8.
split.
apply H3.
split.
apply H3.
split.
apply (Map_Law_5 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H8.
destruct H8.
apply H8.
intros.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H10.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply H11.
assert ((Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x) ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H10.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply Predecessor_Set_Law_1 in H11.
destruct H11.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x) x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H13.
apply H5.
intros.
assert (x0 ∈ Predecessor_Set f X x2/\x3 ∈ Predecessor_Set f X x2).
apply H10.
apply H9 in H10.
apply H10 in H11.
destruct H12.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x2) (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x0) (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply Predecessor_Set_Law_1 in H12.
destruct H12.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x0 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H12.
apply H14.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
apply H15.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x0) x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x0 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H12.
apply H14.
apply Predecessor_Set_Law_1 in H15.
destruct H15.
apply H16.
apply H5.
split.
apply Predecessor_Set_Law_1.
split.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x3 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x3 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x3) x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H15.
apply H5.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x1) (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x0) (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x3)).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H14.
destruct H14.
apply H14.
split.
apply Ordered_Relation_Law_1.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H12.
split.
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H8.
destruct H8.
apply H8.
apply H13.
apply H10.
apply H9.
split.
apply H12.
apply H13.
apply H11.
split.
split.
apply (Map_Law_5 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1) (Predecessor_Set f X x2)).
split.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
apply H8.
intros.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H3.
destruct H8.
destruct H9.
destruct H9.
destruct H9.
apply H9.
apply H7.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply Predecessor_Set_Law_1.
split.
apply H8.
apply (Ordered_Relation_Law_3 f X (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x) x1 x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
split.
apply H9.
apply H5.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H10.
apply H11.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H1.
assert (Culculateion_Map (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) x2 ∈ Predecessor_Set f X x1).
apply (Map_Law_2 (Inverse_Map M (Predecessor_Set f X x1) (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Predecessor_Set f X x1)).
split.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
apply H8.
apply Predecessor_Set_Law_1.
split.
apply H1.
apply (Ordered_Relation_Law_2 f X x2).
split.
apply Totaly_Ordered_Relation_Law_1.
destruct H.
apply H.
apply H1.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
apply H8.
Qed.

Theorem Well_Oredered_Relation_Isomorphism_Law_7:forall f X g Y:Set,(Well_Oredered_Relation f X/\Well_Oredered_Relation g Y)->((exists M x0:Set,x0 ∈ X/\Well_Oredered_Relation_Isomorphism M (Restriction_Map f (Predecessor_Set f X x0)) (Predecessor_Set f X x0) g Y)\/exists M:Set,Well_Oredered_Relation_Isomorphism M f X g Y\/(exists M y0:Set,y0 ∈ Y/\Well_Oredered_Relation_Isomorphism M f X (Restriction_Map g (Predecessor_Set g Y y0)) (Predecessor_Set g Y y0))).
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
assert (Culculateion_Map (Inverse_Map x5 (Predecessor_Set f X x4) (Predecessor_Set g Y (Culculateion_Map x x3))) (Culculateion_Map x x2)=Culculateion_Map x (Culculateion_Map x x2)).
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




assert (Well_Oredered_Relation_Isomorphism (Restriction_Map x5 (Predecessor_Set f X x2)) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2) (Restriction_Relation g (Predecessor_Set g Y (Culculateion_Map x5 x2))) (Predecessor_Set g Y (Culculateion_Map x5 x2))).
destruct H13.
destruct H19.
destruct H20.
split.ghv
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
Qed.



(*狭義整列同型*)
Definition Narrow_Well_Oredered_Relation_homomorphism(M f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2)).

Definition Narrow_Well_Oredered_Relation_Isomorphism(M f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\Bijective_Map M X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->(Relation_Prop g (Culculateion_Map M x1) (Culculateion_Map M x2)).











