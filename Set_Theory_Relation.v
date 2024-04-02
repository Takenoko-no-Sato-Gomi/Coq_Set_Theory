Require Export Set_Theory_Basic.



(*関係*)
Definition Relation_Prop(f x y:Set):=(Ordered_Set x y) ∈ f.

Definition Relation(f X:Set):=forall a:Set,a ∈ f->exists x y:Set,a=Ordered_Set x y/\x ∈ X/\y ∈ X.

Theorem Relation_Law_1:forall f1 f2 X:Set,Relation f1 X/\Relation f2 X/\(forall x1 x2:Set,x1 ∈ X/\x2 ∈ X->(Relation_Prop f1 x1 x2<->Relation_Prop f2 x1 x2))->f1=f2.
Proof.
intros.
destruct H.
destruct H0.
apply Theorem_of_Extensionality.
intros.
split.

intro.
assert (z ∈ f1).
apply H2.
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
apply H1 in H4.
rewrite -> H2.
apply H4.
rewrite -> H2 in H3.
apply H3.

intro.
assert (z ∈ f2).
apply H2.
apply H0 in H2.
destruct H2.
destruct H2.
destruct H2.
apply H1 in H4.
rewrite -> H2.
apply H4.
rewrite -> H2 in H3.
apply H3.
Qed.



Definition Refrectiv_Law(f X:Set):=forall x:Set,x ∈ X->Relation_Prop f x x.

Definition Symmetric_Law(f X:Set):=forall x y:Set,Relation_Prop f x y->Relation_Prop f y x.

Definition Transitive_Law(f X:Set):=forall x y z:Set,(Relation_Prop f x y/\Relation_Prop f y z)->Relation_Prop f x z.

Definition Asymmetric_Law(f X:Set):=forall x y:Set,(Relation_Prop f x y/\Relation_Prop f y x)->x=y.

Definition Totaly_Odered_Law(f X:Set):=forall x y:Set,(x ∈ X/\y ∈ X)->(Relation_Prop f x y\/Relation_Prop f y x).



(*同値関係*)
Definition Equivalenc_Relation(f X:Set):=Relation f X/\Refrectiv_Law f X/\Symmetric_Law f X/\Transitive_Law f X.

Definition Equivalence_Class(f X x:Set):=Prop_Set (fun y=>y ∈ X/\Relation_Prop f x y).

Definition Quotient_Set(f X:Set):=Prop_Set (fun x'=>exists x:Set,x ∈ X/\x'=Equivalence_Class f X x).

Theorem Equivalence_Class_Law_1:forall f X x a:Set,a ∈ Prop_Set (fun y=>y ∈ X/\Relation_Prop f x y)<->a ∈ X/\Relation_Prop f x a.
Proof.
intros.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H.
apply H.
Qed.

Theorem Equivalence_Class_Law_2:forall f x y X:Set,(Equivalenc_Relation f X/\x ∈ (Equivalence_Class f X y))->(Relation_Prop f x y).
Proof.
intros.
destruct H.
apply Equivalence_Class_Law_1 in H0.
destruct H0.
destruct H.
destruct H2.
destruct H3.
apply H3.
apply H1.
Qed.

Theorem Equivalence_Class_Law_3:forall f x y X:Set,(Equivalenc_Relation f X/\Relation_Prop f x y)->(x ∈ (Equivalence_Class f X y)).
Proof.
intros.
destruct H.
destruct H.
apply Equivalence_Class_Law_1.
split.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
apply Ordered_Set_Law_2 in H0.
destruct H0.
destruct H2.
rewrite -> H0.
apply H2.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Quotient_Set_Law_1:forall f X A:Set,A ∈ (Prop_Set (fun x'=>exists x:Set,x ∈ X/\x'=Equivalence_Class f X x))<->exists x:Set,x ∈ X/\A=Equivalence_Class f X x.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
destruct H.
destruct H.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H0 in H1.
apply Equivalence_Class_Law_1 in H1.
destruct H1.
apply H1.
Qed.

Theorem Quotient_Set_Law_2:forall f X:Set,Equivalenc_Relation f X->(X=Union_Set (Quotient_Set f X)).
Proof.
intros.
apply Theorem_of_Extensionality.
intros.
split.

intro.
apply Union_Set_Law_1.
exists (Equivalence_Class f X z).
split.
apply Quotient_Set_Law_1.
exists z.
split.
apply H0.
split.
apply Equivalence_Class_Law_1.
split.
apply H0.
destruct H.
destruct H1.
apply H1.
apply H0.

intro.
apply Union_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
rewrite -> H2 in H1.
apply Equivalence_Class_Law_1 in H1.
destruct H1.
apply H1.
Qed.

Theorem Quotient_Set_Law_3:forall f x y X:Set,(Equivalenc_Relation f X/\x ∈ X/\y ∈ X/\~(Relation_Prop f x y)->(Equivalence_Class f X x) ∩ (Equivalence_Class f X y)=∅).
Proof.
intros.
apply Theorem_of_Extensionality.
intros.
split.
destruct H.
destruct H0.
destruct H1.

intro.
apply Pair_Meet_Set_Law_1 in H3.
destruct H3.
apply Equivalence_Class_Law_1 in H3.
apply Equivalence_Class_Law_1 in H4.
destruct H3.
destruct H4.
destruct H2.
destruct H.
destruct H2.
destruct H7.
apply (H8 x z y).
split.
apply H5.
apply H7.
apply H6.

intros.
destruct (Definition_of_Empty_Set z).
apply H0.
Qed.

Theorem Quotient_Set_Law_4:forall f x y X:Set,(Equivalenc_Relation f X/\x ∈ X/\y ∈ X/\(Equivalence_Class f X x)=(Equivalence_Class f X y))->Relation_Prop f x y.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.

apply (Equivalence_Class_Law_2 f x y X).
split.
apply H.
rewrite <- H2.
apply (Equivalence_Class_Law_3 f x x X).
split.
apply H.
destruct H.
destruct H3.
destruct H4.
apply H4.
apply H3.
apply H0.
Qed.



(*順序関係*)
Definition Ordered_Relation(f X:Set):=Relation f X/\Refrectiv_Law f X/\Transitive_Law f X/\Asymmetric_Law f X.

Definition Totaly_Ordered_Relation(f X:Set):=Ordered_Relation f X/\Totaly_Odered_Law f X.



Definition Upper_Bound(f X a:Set):=(forall x:Set,x ∈ X->Relation_Prop f x a).

Definition Maximal_Element(f X a:Set):=a ∈ X/\(forall x:Set,x ∈ X->~(Relation_Prop f a x/\~a=x)).

Definition Maximum_Element(f X a:Set):=a ∈ X/\(forall x:Set,x ∈ X->Relation_Prop f x a).



Definition Lower_Bound(f X a:Set):=(forall x:Set,x ∈ X->Relation_Prop f a x).

Definition Minimal_Element(f X a:Set):=a ∈ X/\(forall x:Set,x ∈ X->~(Relation_Prop f x a/\~a=x)).

Definition Minimum_Element(f X a:Set):=a ∈ X/\(forall x:Set,x ∈ X->Relation_Prop f a x).

Theorem Ordered_Relation_Law_1:forall f X a:Set,(Ordered_Relation f X/\Maximum_Element f X a)->(Maximal_Element f X a).
Proof.
intros.
split.
destruct H.
apply H0.
intro.
intro.
intro.
destruct H1.
apply H2.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H6.
split.
apply H1.
apply H3.
apply H0.
Qed.

Theorem Ordered_Relation_Law_2:forall f X a:Set,(Ordered_Relation f X/\Minimum_Element f X a)->(Minimal_Element f X a).
Proof.
intros.
split.
destruct H.
apply H0.
intro.
intro.
intro.
destruct H1.
apply H2.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H6.
split.
apply H3.
apply H0.
apply H1.
Qed.



(*整列順序*)
Definition Well_Oredered_Relation(f X:Set):=Totaly_Ordered_Relation f X/\(forall Y:Set,(Y ⊂ X/\~Y=∅)->exists a:Set,Minimum_Element f Y a).

(*狭義整列順序*)
Definition Narrow_Well_Oredered_Relation(f X:Set):=Relation f X/\Transitive_Law f X/\(forall x y:Set,(x ∈ X/\y ∈ X)->(Relation_Prop f x y\/x=y\/Relation_Prop f y x))/\(forall x:Set,x ∈ X->~Relation_Prop f x x)/\(forall Y:Set,(Y ⊂ X/\~Y=∅)->exists a:Set,a ∈ Y/\forall x:Set,(x ∈ Y/\~a=x)->Relation_Prop f a x).

Theorem Well_Oredered_Relation_Law_1:forall f X a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f/\(forall x:Set,~a=Ordered_Set x x)))<->a0 ∈ f/\(forall x:Set,~a0=Ordered_Set x x).
Proof.
intros.
apply Prop_Set_Law_1.
exists f.
intros.
destruct H.
apply H.
Qed.

Theorem Well_Oredered_Relation_Law_2:forall f X:Set,Well_Oredered_Relation f X->Narrow_Well_Oredered_Relation (Prop_Set (fun a=>a ∈ f/\(forall x:Set,~a=(Ordered_Set x x)))) X.
Proof.
intros.
destruct H.
destruct H.
destruct H.
destruct H2.
destruct H3.
assert (forall a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f/\(forall x:Set,~a=Ordered_Set x x)))<->a0 ∈ f/\(forall x:Set,~a0=Ordered_Set x x)).
intro.
apply (Prop_Set_Law_1 (fun a=>a ∈ f/\(forall x:Set,~a=Ordered_Set x x))).
exists f.
intros.
destruct H5.
apply H5.

split.
intro.
intro.
apply H5 in H6.
destruct H6.
apply H in H6.
destruct H6.
destruct H6.
exists x.
exists x0.
apply H6.
split.

intro.
intros.
destruct H6.
apply H5 in H6.
apply H5 in H7.
destruct H6.
destruct H7.
apply H5.
split.
apply (H3 x y z).
split.
apply H6.
apply H7.
intro.
intro.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H10 in H8.
rewrite -> H11 in H9.
assert (forall x1:Set,(~x0=x1)\/(~y=x1)).
intro.
apply Prop_Law_7.
intro.
apply Ordered_Set_Law_2 in H12.
apply (H8 x1).
apply H12.
assert ((~x0=x0)\/(~y=x0)).
apply H12.
destruct H13.
apply H13.
split.
rewrite -> H10 in H6.
rewrite -> H11 in H7.
apply H13.
apply H4.
split.
apply H7.
apply H6.
split.

intros.
apply H1 in H6.
destruct H6.
destruct (Law_of_Excluded_Middle (x=y)).
right.
left.
apply H7.
left.
apply H5.
split.
apply H6.
intros.
intro.
apply Ordered_Set_Law_2 in H8.
destruct H8.
apply H7.
rewrite -> H9.
apply H8.
destruct (Law_of_Excluded_Middle (x=y)).
right.
left.
apply H7.
right.
right.
apply H5.
split.
apply H6.
intros.
intro.
apply Ordered_Set_Law_2 in H8.
destruct H8.
apply H7.
rewrite -> H8.
apply H9.
split.

intros.
intro.
apply H5 in H7.
destruct H7.
apply (H8 x).
split.

intros.
apply H0 in H6.
destruct H6.
exists x.
destruct H6.
intros.
split.
apply H6.
intros.
apply H5.
split.
apply H7.
intros.
destruct H8.
apply H8.
intro.
intro.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
apply H10.
rewrite -> H11.
apply H9.
Qed.

Theorem Well_Oredered_Relation_Law_3:forall f X a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x))))<->a0 ∈ f\/(exists x:Set,x ∈ X/\a0=(Ordered_Set x x)).
Proof.
intros.
apply Prop_Set_Law_1.
exists (f ∪ (Prop_Set (fun a1=>exists x:Set,x ∈ X/\a1=Ordered_Set x x))).
intros.
destruct H.
apply Pair_Union_Set_Law_1.
left.
apply H.
apply Pair_Union_Set_Law_1.
destruct H.
right.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set X X).
intros.
destruct H.
destruct H0.
destruct H0.
rewrite -> H2.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x2.
split.
split.
split.
apply H0.
apply H0.
exists x0.
apply H.
Qed.

Theorem Well_Oredered_Relation_Law_4:forall f X:Set,Narrow_Well_Oredered_Relation f X->Well_Oredered_Relation (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
assert (forall a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x))))<->a0 ∈ f\/(exists x:Set,x ∈ X/\a0=(Ordered_Set x x))).
intro.
apply Prop_Set_Law_1.
exists (f ∪ (Prop_Set (fun a1=>exists x:Set,x ∈ X/\a1=Ordered_Set x x))).
intros.
destruct H4.
apply Pair_Union_Set_Law_1.
left.
apply H4.
apply Pair_Union_Set_Law_1.
destruct H4.
right.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set X X).
intros.
destruct H4.
destruct H5.
destruct H5.
rewrite -> H7.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x2.
split.
split.
split.
apply H5.
apply H5.
exists x0.
apply H4.
split.
split.
split.

intro.
intro.
apply H4 in H5.
destruct H5.
apply H in H5.
destruct H5.
destruct H5.
exists x.
exists x0.
apply H5.
destruct H5.
destruct H5.
exists x.
exists x.
split.
apply H6.
split.
apply H5.
apply H5.
split.

intro.
intro.
apply H4.
right.
exists x.
split.
apply H5.
split.
split.

intro.
intros.
destruct H5.
apply H4 in H5.
apply H4 in H6.
apply H4.
destruct H5.
destruct H6.
left.
apply (H0 x y z).
split.
apply H5.
apply H6.
destruct H6.
destruct H6.
left.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H8.
rewrite <- H7.
apply H5.
destruct H6.
destruct H5.
destruct H5.
left.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H7.
rewrite <- H8.
apply H6.
right.
destruct H5.
destruct H5.
destruct H6.
destruct H6.
exists x0.
split.
apply H5.
apply Ordered_Set_Law_2 in H7.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H7.
rewrite -> H10.
rewrite <- H8.
rewrite -> H9.
split.

intro.
intros.
destruct H5.
apply H4 in H5.
apply H4 in H6.
destruct H5.
destruct H6.
assert (~Relation_Prop f x x).
apply H2.
apply H in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H7.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite H5.
apply H7.
destruct H7.
apply (H0 x y x).
split.
apply H5.
apply H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H7.
apply H8.
destruct H5.
destruct H5.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H8.
apply H7.

intro.
intros.
assert (x ∈ X /\ y ∈ X).
apply H5.
apply H1 in H5.
destruct H5.
left.
apply H4.
left.
apply H5.
destruct H5.
left.
apply H4.
right.
exists x.
split.
destruct H6.
apply H6.
rewrite <- H5.
split.
right.
apply H4.
left.
apply H5.

intros.
assert (Y ⊂ X).
destruct H5.
apply H5.
apply H3 in H5.
destruct H5.
destruct H5.
exists x.
split.
apply H5.
intros.
apply H4.
destruct (Law_of_Excluded_Middle (x=x0)).
right.
exists x0.
split.
apply H6.
apply H8.
rewrite -> H9.
split.
left.
apply H7.
split.
apply H8.
apply H9.
Qed.



Definition Restriction_Relation(f X0:Set):=Prop_Set (fun a=>a ∈ f/\exists x y:Set,x ∈ X0/\y ∈ X0/\a=Ordered_Set x y).

Theorem Restriction_Relation_Law_1:forall f X0 a:Set,a ∈ (Restriction_Relation f X0)<->(a ∈ f/\exists x y:Set,x ∈ X0/\y ∈ X0/\a=Ordered_Set x y).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set X0)).
intros.
destruct H.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H2 in H3.
apply Ordered_Set_Law_1 in H3.
destruct H3.
rewrite -> H3 in H4.
apply Pair_Set_Law_1 in H4.
destruct H4.
rewrite -> H4.
apply H0.
rewrite -> H4.
apply H1.
rewrite -> H3 in H4.
apply Single_Set_Law_1 in H4.
rewrite -> H4.
apply H1.
Qed.

Theorem Restriction_Relation_Law_2:forall f X X0:Set,(X0 ⊂ X/\Relation f X)->Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
intro.
intro.
apply Restriction_Relation_Law_1 in H1.
destruct H1.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
apply H0 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H5.
exists x.
exists x0.
split.
apply H4.
split.
apply H2.
apply H3.
Qed.

Theorem Restriction_Relation_Law_3:forall f X X0 x y:Set,(X0 ⊂ X/\Relation f X/\x ∈ X0/\y ∈ X0/\Relation_Prop f x y)->Relation_Prop (Restriction_Relation f X0) x y.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Restriction_Relation_Law_1.
split.
apply H3.
exists x.
exists y.
split.
apply H1.
split.
apply H2.
split.
Qed.

Theorem Restriction_Relation_Law_4:forall f X X0 x y:Set,(X0 ⊂ X/\Relation f X/\x ∈ X0/\y ∈ X0/\Relation_Prop (Restriction_Relation f X0) x y)->Relation_Prop f x y.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Restriction_Relation_Law_1 in H3.
destruct H3.
apply H3.
Qed.

Theorem Restriction_Relation_Law_5:forall f X X0:Set,(X0 ⊂ X/\Equivalenc_Relation f X)->Equivalenc_Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.

split.
apply (Restriction_Relation_Law_2 f X X0).
split.
apply H.
apply H0.

split.
intro.
intros.
apply (Restriction_Relation_Law_3 f X X0 x x).
split.
apply H.
split.
apply H0.
split.
apply H4.
split.
apply H4.
apply H1.
apply H.
apply H4.

split.
intro.
intros.
apply (Restriction_Relation_Law_3 f X X0 y x).
split.
apply H.
split.
apply H0.
split.
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H7.
apply H6.
split.
apply H.
apply H0.
split.
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H4.
apply H5.
split.
apply H.
apply H0.
apply H2.
apply (Restriction_Relation_Law_4 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H4.
apply H5.
split.
apply H.
apply H0.
split.
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H7.
apply H6.
split.
apply H.
apply H0.
apply H4.

intro.
intros.
destruct H4.
assert (x ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H4.
apply H6.
split.
apply H.
apply H0.
assert (y ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H7.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H9.
apply H8.
split.
apply H.
apply H0.
assert (z ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H8.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H10.
apply H9.
split.
apply H.
apply H0.
apply (Restriction_Relation_Law_3 f X X0 x z).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H8.
apply (H3 x y z).
split.
apply (Restriction_Relation_Law_4 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H7.
apply H4.
apply (Restriction_Relation_Law_4 f X X0 y z).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H8.
apply H5.
Qed.

Theorem Restriction_Relation_Law_6:forall f X X0:Set,(X0 ⊂ X/\Ordered_Relation f X)->Ordered_Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.

split.
apply (Restriction_Relation_Law_2 f X X0).
split.
apply H.
apply H0.

split.
intro.
intro.
apply (Restriction_Relation_Law_3 f X X0 x x).
split.
apply H.
split.
apply H0.
split.
apply H4.
split.
apply H4.
apply H1.
apply H.
apply H4.

split.
intro.
intros.
destruct H4.
assert (x ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H4.
apply H6.
split.
apply H.
apply H0.
assert (y ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H7.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H9.
apply H8.
split.
apply H.
apply H0.
assert (z ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H8.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H10.
apply H9.
split.
apply H.
apply H0.
apply (Restriction_Relation_Law_3 f X X0 x z).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H8.
apply (H2 x y z).
split.
apply (Restriction_Relation_Law_4 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H7.
apply H4.
apply (Restriction_Relation_Law_4 f X X0 y z).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H8.
apply H5.

intro.
intros.
destruct H4.
assert (x ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H4.
apply H6.
split.
apply H.
apply H0.
assert (y ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H7.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H9.
apply H8.
split.
apply H.
apply H0.
apply H3.
split.
apply (Restriction_Relation_Law_4 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H7.
apply H4.
apply (Restriction_Relation_Law_4 f X X0 y x).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H6.
apply H5.
Qed.

Theorem Restriction_Relation_Law_7:forall f X X0:Set,(X0 ⊂ X/\Totaly_Ordered_Relation f X)->Totaly_Ordered_Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
destruct H0.
split.
apply (Restriction_Relation_Law_6 f X X0).
split.
apply H.
apply H0.

intro.
intros.
destruct H2.
assert (x ∈ X/\y ∈ X).
split.
apply H.
apply H2.
apply H.
apply H3.
apply H1 in H4.
destruct H4.
left.
apply (Restriction_Relation_Law_3 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H2.
split.
apply H3.
apply H4.
right.
apply (Restriction_Relation_Law_3 f X X0 y x).
split.
apply H.
split.
apply H0.
split.
apply H3.
split.
apply H2.
apply H4.
Qed.

Theorem Restriction_Relation_Law_8:forall f X X0:Set,(X0 ⊂ X/\Well_Oredered_Relation f X)->Well_Oredered_Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
destruct H0.
split.

apply (Restriction_Relation_Law_7 f X X0).
split.
apply H.
apply H0.

intros.
destruct H2.
assert (Y ⊂ X/\~Y=∅).
split.
intro.
intro.
apply H.
apply H2.
apply H4.
apply H3.
apply H1 in H4.
destruct H4.
destruct H4.
exists x.
split.
apply H4.
intros.
assert (x0 ∈ Y).
apply H6.
apply H5 in H6.
apply (Restriction_Relation_Law_3 f X X0 x x0).
split.
apply H.
split.
destruct H0.
destruct H0.
apply H0.
split.
apply H2.
apply H4.
split.
apply H2.
apply H7.
apply H6.
Qed.

Theorem Restriction_Relation_Law_9:forall f X X0:Set,(X0 ⊂ X/\Narrow_Well_Oredered_Relation f X)->Narrow_Well_Oredered_Relation (Restriction_Relation f X0) X0.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.

split.
apply (Restriction_Relation_Law_2 f X X0).
split.
apply H.
apply H0.

split.
intro.
intros.
destruct H5.
assert (x ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H7.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H5.
apply H7.
split.
apply H.
apply H0.
assert (y ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H8.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H10.
apply H9.
split.
apply H.
apply H0.
assert (z ∈ X0).
apply (Restriction_Relation_Law_2 f X X0) in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H9.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H11.
apply H10.
split.
apply H.
apply H0.
apply (Restriction_Relation_Law_3 f X X0 x z).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H9.
apply (H1 x y z).
split.
apply (Restriction_Relation_Law_4 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H8.
apply H5.
apply (Restriction_Relation_Law_4 f X X0 y z).
split.
apply H.
split.
apply H0.
split.
apply H8.
split.
apply H9.
apply H6.

split.
intros.
destruct H5.
assert (x ∈ X/\y ∈ X).
split.
apply H.
apply H5.
apply H.
apply H6.
apply H2 in H7.
destruct H7.
left.
apply (Restriction_Relation_Law_3 f X X0 x y).
split.
apply H.
split.
apply H0.
split.
apply H5.
split.
apply H6.
apply H7.
right.
destruct H7.
left.
apply H7.
right.
apply (Restriction_Relation_Law_3 f X X0 y x).
split.
apply H.
split.
apply H0.
split.
apply H6.
split.
apply H5.
apply H7.

split.
intros.
intro.
assert (x ∈ X0).
apply H5.
apply H in H5.
apply H3 in H5.
apply H5.
apply (Restriction_Relation_Law_4 f X X0 x x).
split.
apply H.
split.
apply H0.
split.
apply H7.
split.
apply H7.
apply H6.

intros.
destruct H5.
assert (Y ⊂ X/\~Y=∅).
split.
intro.
intro.
apply H.
apply H5.
apply H7.
apply H6.
apply H4 in H7.
destruct H7.
destruct H7.
exists x.
split.
apply H7.
intros.
assert (x0 ∈ Y).
apply H9.
apply H8 in H9.
apply (Restriction_Relation_Law_3 f X X0 x x0).
split.
apply H.
split.
apply H0.
split.
apply H5.
apply H7.
split.
apply H5.
apply H10.
apply H9.
Qed.


Definition Predecessor_Set(f X x:Set):=Prop_Set (fun y=>y ∈ X/\Relation_Prop f y x).

Theorem Predecessor_Set_Law_1:forall f X x y:Set,y ∈ (Predecessor_Set f X x)<->(y ∈ X/\Relation_Prop f y x).
Proof.
intros.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H.
apply H.
Qed.

Theorem Predecessor_Set_Law_2:forall f X x:Set,(x ∈ X/\Well_Oredered_Relation f X)->Well_Oredered_Relation (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x).
Proof.
intros.
destruct H.
destruct H0.
destruct H0.

assert ((Predecessor_Set f X x) ⊂ X).
intro.
intro.
apply Predecessor_Set_Law_1 in H3.
destruct H3.
apply H3.

split.
split.
split.
apply (Restriction_Relation_Law_2 f X (Predecessor_Set f X x)).
split.
apply H3.
destruct H0.
apply H0.

split.
intro.
intros.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x)).
split.
apply H3.
split.
destruct H0.
apply H0.
split.
apply H4.
split.
apply H4.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
destruct H0.
destruct H6.
apply H6.
apply H4.

split.
intro.
intros.
destruct H4.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x)).
split.
apply H3.
split.
destruct H0.
apply H0.
split.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H4.
destruct H4.
destruct H6.
destruct H6.
destruct H6.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H8.
apply H6.
split.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H5.
destruct H5.
destruct H6.
destruct H6.
destruct H6.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H9.
apply H7.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H4.
destruct H4.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H5.
destruct H5.
destruct H0.
destruct H8.
destruct H9.
apply (H9 x0 y z).
split.
apply H4.
apply H5.

intro.
intros.
destruct H4.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H4.
destruct H4.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H5.
destruct H5.
destruct H0.
destruct H8.
destruct H9.
apply H10.
split.
apply H4.
apply H5.

intro.
intros.
destruct H4.
apply Predecessor_Set_Law_1 in H4.
destruct H4.
apply Predecessor_Set_Law_1 in H5.
destruct H5.
assert (x0 ∈ X/\y ∈ X).
split.
apply H4.
apply H5.
apply H2 in H8.
destruct H8.
left.
apply Restriction_Relation_Law_1.
split.
apply H8.
exists x0.
exists y.
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
split.
right.
apply Restriction_Relation_Law_1.
split.
apply H8.
exists y.
exists x0.
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
split.

intros.
destruct H4.
assert (Y ⊂ X/\~Y=∅).
split.
intro.
intro.
apply H4 in H6.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
apply H5.
apply H1 in H6.
destruct H6.
destruct H6.
exists x0.
split.
apply H6.
intros.
assert (x1 ∈ Y).
apply H8.
apply H7 in H8.
apply Restriction_Relation_Law_1.
split.
apply H8.
exists x0.
exists x1.
split.
apply Predecessor_Set_Law_1.
split.
apply H4 in H6.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H6.
apply H4 in H6.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply H10.
split.
apply Predecessor_Set_Law_1.
split.
destruct H0.
apply H0 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H11.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H13.
apply H12.
apply H4 in H9.
apply Predecessor_Set_Law_1 in H9.
destruct H9.
apply H10.
split.
Qed.

Theorem Predecessor_Set_Law_3:forall f X x:Set,(x ∈ X/\Narrow_Well_Oredered_Relation f X)->Narrow_Well_Oredered_Relation (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.

assert ((Predecessor_Set f X x) ⊂ X).
intro.
intro.
apply Predecessor_Set_Law_1 in H5.
destruct H5.
apply H5.

split.
apply (Restriction_Relation_Law_2 f X (Predecessor_Set f X x)).
split.
apply H5.
apply H0.

split.
intro.
intros.
destruct H6.
apply (Restriction_Relation_Law_3 f X (Predecessor_Set f X x)).
split.
apply H5.
split.
apply H0.
split.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H6.
destruct H6.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H10.
apply H8.
split.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H7.
destruct H7.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H11.
apply H9.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H6.
destruct H6.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)) in H7.
destruct H7.
apply (H1 x0 y z).
split.
apply H6.
apply H7.

split.
intros.
destruct H6.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
apply Predecessor_Set_Law_1 in H7.
destruct H7.
assert (x0 ∈ X/\y ∈ X).
split.
apply H6.
apply H7.
apply H2 in H10.
destruct H10.
left.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)).
split.
apply H10.
exists x0.
exists y.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H8.
split.
apply Predecessor_Set_Law_1.
split.
apply H7.
apply H9.
split.
right.
destruct H10.
left.
apply H10.
right.
apply (Restriction_Relation_Law_1 f (Predecessor_Set f X x)).
split.
apply H10.
exists y.
exists x0.
split.
apply Predecessor_Set_Law_1.
split.
apply H7.
apply H9.
split.
apply Predecessor_Set_Law_1.
split.
apply H6.
apply H8.
split.

split.
intros.
apply Predecessor_Set_Law_1 in H6.
destruct H6.
assert (x0 ∈ X).
apply H6.
apply H3 in H6.
intro.
apply H6.
apply (Restriction_Relation_Law_4 f X (Predecessor_Set f X x) x0 x0).
split.
intro.
intro.
apply Predecessor_Set_Law_1 in H10.
destruct H10.
apply H10.
split.
apply H0.
split.
apply Predecessor_Set_Law_1.
split.
apply H8.
apply H7.
split.
apply Predecessor_Set_Law_1.
split.
apply H8.
apply H7.
apply H9.

intros.
destruct H6.
assert (Y ⊂ X/\~Y=∅).
split.
intro.
intro.
apply H6 in H8.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply H8.
apply H7.
apply H4 in H8.
destruct H8.
destruct H8.
exists x0.
split.
apply H8.
intros.
assert (x1 ∈ Y).
destruct H10.
apply H10.
apply H9 in H10.
apply Restriction_Relation_Law_1.
split.
apply H10.
exists x0.
exists x1.
split.
apply Predecessor_Set_Law_1.
split.
apply H6 in H8.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply H8.
apply H6 in H8.
apply Predecessor_Set_Law_1 in H8.
destruct H8.
apply H12.
split.
apply Predecessor_Set_Law_1.
apply H6 in H11.
apply Predecessor_Set_Law_1 in H11.
apply H11.
split.
Qed.



(*超限帰納法*)
Theorem Transfinite_Induction_1:forall p:Set->Prop,forall f X:Set,Well_Oredered_Relation f X->((forall a:Set,a ∈ X->(forall x:Set,(x ∈ X->((Relation_Prop f x a/\~x=a->p x))))->p a)->(forall x:Set,x ∈ X->p x)).
Proof.
intros.

assert (forall a:Set,(a ∈ X->( (Prop_Set (fun x=>x ∈ X/\Relation_Prop f x a/\~x=a)) ⊂ (Prop_Set (fun x=>x ∈ X/\p x))))<->(a ∈ X->(forall x:Set,x ∈ X->(Relation_Prop f x a/\~x=a->p x)))).
split.
intros.
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
apply H2 in H4.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H7.
apply H7.
split.
apply H6.
apply H4.
apply H3.
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
apply H1.
intros.
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
specialize (H0 x1).
specialize (H0 H7).
apply H0.
apply H2.
apply H3.
apply H12.
apply H7.
apply Theorem_of_Extensionality.
intro.
split.
intro.
assert ((~z ∈ X)\/(~~z ∈ (Prop_Set (fun x=>x ∈ X/\p x)))).
apply Prop_Law_7.
intro.
apply (Definition_of_Empty_Set z).
rewrite <- H6.
apply Complement_Set_Law_1.
apply H8.
destruct H8.
destruct H8.
apply H7.
apply Prop_Law_3.
apply H8.
intro.
apply (Prop_Set_Law_1 (fun x=>x ∈ X/\p x)) in H7.
destruct H7.
apply H7.
exists X.
intros.
destruct H9.
apply H9.
apply H0 in H4.
apply H4.
apply H2.
apply H3.
intro.
rewrite <- H6.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1 in H8.
destruct H8.
rewrite -> Complement_Set_Law_2 in H9.
apply H9.
intro.
destruct (Definition_of_Empty_Set z).
apply H8.
apply H4.
Qed.

Theorem Transfinite_Induction_2:forall p:Set->Prop,forall f X:Set,Narrow_Well_Oredered_Relation f X->((forall a:Set,a ∈ X->(forall x:Set,(x ∈ X->((Relation_Prop f x a->p x))))->p a)->(forall x:Set,x ∈ X->p x)).
Proof.
intros.
apply (Transfinite_Induction_1 p (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X).
apply Well_Oredered_Relation_Law_4.
apply H.
intros.
apply H0.
apply H2.
intros.
apply H3.
apply H4.
split.
apply Well_Oredered_Relation_Law_3.
left.
apply H5.
intro.
destruct H.
destruct H7.
destruct H8.
destruct H9.
apply H9 in H4.
apply H4.
rewrite <- H6 in H5.
apply H5.
apply H1.
Qed.



(*写像*)
Definition Map(f X Y:Set):=(forall a:Set,a ∈ f->exists x y:Set,x ∈ X/\y ∈ Y/\a=(Ordered_Set x y))/\(forall x:Set,x ∈ X->exists! y:Set,(Ordered_Set x y) ∈ f/\y ∈ Y).

Definition Culculateion_Map(f x:Set):=Well_Defined (fun y=>(Ordered_Set x y) ∈ f).

Theorem Map_Law_1:forall f X Y x:Set,(Map f X Y/\x ∈ X)->(Ordered_Set x (Culculateion_Map f x)) ∈ f.
Proof.
intros.
unfold Culculateion_Map.
apply Well_Defined_1.
destruct H.
destruct H.
apply H1 in H0.
destruct H0.
destruct H0.
exists x0.
split.
apply H0.
intros.
apply H2.
split.
apply H3.
apply H in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H6.
apply H4.
Qed.

Theorem Map_Law_2:forall f X Y x:Set,Map f X Y/\x ∈ X->(Culculateion_Map f x) ∈ Y.
Proof.
intros.
assert ((Ordered_Set x (Culculateion_Map f x)) ∈ f).
apply Map_Law_1 in H.
apply H.
destruct H.
destruct H.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H5.
apply H3.
Qed.

Theorem Map_Law_3:forall f X Y x y:Set,(Map f X Y/\x ∈ X/\y ∈ Y/\(Ordered_Set x y) ∈ f)->(y=Culculateion_Map f x).
Proof.
intros.
destruct H.
destruct H.
destruct H0.
destruct H2.
apply H1 in H0.
destruct H0.
destruct H0.
assert ((Ordered_Set x (Culculateion_Map f x)) ∈ f/\(Culculateion_Map f x) ∈ Y).
split.
assert (Map f X Y/\x ∈ X).
split.
split.
apply H.
apply H1.
apply H in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H6.
apply H3.
apply Map_Law_1 in H5.
apply H5.
assert (Map f X Y/\x ∈ X).
split.
split.
apply H.
apply H1.
apply H in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H6.
apply H3.
apply Map_Law_2 in H5.
apply H5.
apply H4 in H5.
assert ((Ordered_Set x y) ∈ f/\y ∈ Y).
split.
apply H3.
apply H2.
apply H4 in H6.
rewrite <- H6.
apply H5.
Qed.

Theorem Map_Law_4:forall f h X Y:Set,(Map f X Y/\Map h X Y/\(forall x:Set,x ∈ X->(Culculateion_Map f x=Culculateion_Map h x))->f=h).
Proof.
assert (forall f h X Y:Set,(Map f X Y/\Map h X Y/\(forall x:Set,x ∈ X->(Culculateion_Map f x=Culculateion_Map h x)))->(forall z:Set,z ∈ f->z ∈ h)).
intro.
intro.
intro.
intro.
intro.
destruct H.
destruct H0.
destruct H.
destruct H0.
intros.

assert (z ∈ f).
apply H4.
apply H in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
assert (x ∈ X).
apply H4.
apply H2 in H4.
destruct H4.
destruct H4.
assert ((Ordered_Set x (Culculateion_Map f x)) ∈ f/\(Culculateion_Map f x) ∈ Y).
assert (Map f X Y/\x ∈ X).
split.
split.
apply H.
apply H2.
apply H8.
split.
apply Map_Law_1 in H10.
apply H10.
apply Map_Law_2 in H10.
apply H10.
apply H9 in H10.
assert ((Ordered_Set x x0) ∈ f/\x0 ∈ Y).
split.
rewrite <- H7.
apply H5.
apply H6.
apply H9 in H11.
assert (x ∈ X).
apply H8.
apply H1 in H8.
rewrite -> H7.
rewrite <- H11.
rewrite -> H10.
rewrite -> H8.
assert (Map h X Y/\x ∈ X).
split.
split.
apply H0.
apply H3.
apply H12.
apply Map_Law_1 in H13.
apply H13.

intros.
apply Theorem_of_Extensionality.
intros.
split.
specialize (H f).
specialize (H h).
specialize (H X).
specialize (H Y).
apply H.
apply H0.
specialize (H h).
specialize (H f).
specialize (H X).
specialize (H Y).
apply H.
intros.
destruct H0.
destruct H1.
split.
apply H1.
split.
apply H0.
intros.
apply H2 in H3.
rewrite -> H3.
split.
Qed.



Definition Surjective_Map(f X Y:Set):=Map f X Y/\forall y:Set,y ∈ Y->exists x:Set,x ∈ X/\y=Culculateion_Map f x.

Definition Injective_Map(f X Y:Set):=Map f X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Culculateion_Map f x1=Culculateion_Map f x2)->x1=x2.

Definition Bijective_Map(f X Y:Set):=Surjective_Map f X Y/\Injective_Map f X Y.



Definition Composite_Map(f h:Set):=Prop_Set (fun a=>exists x y:Set,(Ordered_Set x y) ∈ f/\a=Ordered_Set x (Culculateion_Map h y)).

Theorem Composite_Map_Law_1:forall f h X Y Z:Set,Map f X Y/\Map h Y Z->Map (Composite_Map f h) X Z.
Proof.
intros.

assert (forall a:Set,a ∈ (Composite_Map f h)<->exists x y:Set,(Ordered_Set x y) ∈ f/\a=Ordered_Set x (Culculateion_Map h y)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set (X ∪ Z))).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Union_Set_Law_1.
destruct H0.
destruct H0.
destruct H0.
assert (Map h Y Z/\x1 ∈ Y).
split.
apply H.
destruct H.
destruct H.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H6.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H8.
apply H6.
apply Map_Law_2 in H4.
rewrite -> H3 in H1.
apply Ordered_Set_Law_1 in H1.
destruct H1.
rewrite -> H1 in H2.
apply Pair_Set_Law_1 in H2.
destruct H.
destruct H.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
destruct H2.
rewrite -> H2.
rewrite -> H8.
left.
apply H0.
rewrite -> H2.
right.
apply H4.
rewrite -> H1 in H2.
apply Single_Set_Law_1 in H2.
rewrite -> H2.
right.
apply H4.

split.
intros.
apply H0 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H.
destruct H.
apply H in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H5.
apply Ordered_Set_Law_2 in H6.
destruct H6.
destruct H3.
assert (x2 ∈ Y).
apply H5.
apply H8 in H5.
destruct H5.
destruct H5.
destruct H5.
exists x.
exists x3.
split.
rewrite -> H6.
apply H1.
split.
apply H11.
rewrite -> H2.
apply Ordered_Set_Law_2.
split.
split.
assert ((Ordered_Set x2 (Culculateion_Map h x0)) ∈ h/\(Culculateion_Map h x0) ∈ Z).
rewrite -> H7.
assert (Map h Y Z/\x2 ∈ Y).
split.
split.
apply H3.
apply H8.
apply H9.
split.
apply Map_Law_1 in H12.
apply H12.
apply Map_Law_2 in H12.
apply H12.
apply H10 in H12.
rewrite <- H12.
split.

intros.
destruct H.
destruct H.
destruct H2.
apply H3 in H1.
destruct H1.
destruct H1.
destruct H1.
assert (x0 ∈ Y).
apply H6.
apply H4 in H6.
destruct H6.
destruct H6.
exists x1.
split.
split.
apply H0.
exists x.
exists x0.
split.
apply H1.
apply Ordered_Set_Law_2.
split.
split.
apply H8.
assert (Map h Y Z/\x0 ∈ Y).
split.
split.
apply H2.
apply H4.
apply H7.
split.
apply Map_Law_1 in H9.
apply H9.
apply Map_Law_2 in H9.
apply H9.
destruct H6.
apply H9.
intros.
apply H8.
destruct H9.
apply H0 in H9.
destruct H9.
destruct H9.
destruct H9.
apply Ordered_Set_Law_2 in H11.
destruct H11.
assert (Map h Y Z/\x3 ∈ Y).
split.
split.
apply H2.
apply H4.
apply H in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H13.
apply Ordered_Set_Law_2 in H14.
destruct H14.
rewrite -> H15.
apply H13.
apply Map_Law_1 in H13.
rewrite <- H12 in H13.
assert (x0=x3).
apply H5.
split.
rewrite -> H11.
apply H9.
apply H in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H14.
apply Ordered_Set_Law_2 in H15.
destruct H15.
rewrite -> H16.
apply H14.
rewrite -> H14.
split.
apply H13.
apply H10.
Qed.

Theorem Composite_Map_Law_2:forall f h x X Y Z:Set,(Map f X Y/\Map h Y Z/\x ∈ X)->(Culculateion_Map h (Culculateion_Map f x)=Culculateion_Map (Composite_Map f h) x).
Proof.
intros.
destruct H.
destruct H0.
assert (Map f X Y/\x ∈ X).
split.
apply H.
apply H1.
apply Map_Law_1 in H2.
assert (Map h Y Z/\(Culculateion_Map f x) ∈ Y).
split.
apply H0.
assert (Map f X Y/\x ∈ X).
split.
apply H.
apply H1.
apply Map_Law_2 in H3.
apply H3.
apply Map_Law_1 in H3.
assert ((Ordered_Set x (Culculateion_Map (Composite_Map f h) x)) ∈ (Composite_Map f h)).
assert (Map (Composite_Map f h) X Z/\x ∈ X).
split.
assert (Map f X Y/\Map h Y Z).
split.
apply H.
apply H0.
apply Composite_Map_Law_1 in H4.
apply H4.
apply H1.
apply Map_Law_1 in H4.
apply H4.
apply (Prop_Set_Law_1 (fun a=>exists x y:Set,(Ordered_Set x y) ∈ f/\a=Ordered_Set x (Culculateion_Map h y))) in H4.
destruct H4.
destruct H4.
destruct H4.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H6.
destruct H.
destruct H0.
assert ((Culculateion_Map f x) ∈ Y).
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H11.
apply H9.
apply H7 in H1.
destruct H1.
destruct H1.
assert (x2=(Culculateion_Map f x)).
apply H10.
split.
apply H2.
apply H9.
assert (x2=x1).
apply H10.
split.
rewrite -> H5.
apply H4.
apply H in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H12.
apply Ordered_Set_Law_2 in H13.
destruct H13.
rewrite -> H14.
apply H12.
rewrite <- H11.
rewrite -> H12.
split.
exists (Power_Set (Power_Set (X ∪ Z))).
intros.
destruct H6.
destruct H6.
destruct H6.
rewrite -> H7.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Ordered_Set_Law_1 in H8.
apply Pair_Union_Set_Law_1.
destruct H8.
rewrite -> H8 in H9.
apply Pair_Set_Law_1 in H9.
destruct H9.
left.
rewrite -> H9.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
rewrite -> H12.
apply H6.
right.
rewrite -> H9.
assert (Map h Y Z/\x2 ∈ Y).
split.
apply H0.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
rewrite -> H13.
apply H11.
apply Map_Law_2 in H10.
apply H10.
rewrite -> H8 in H9.
apply Single_Set_Law_1 in H9.
rewrite -> H9.
right.
assert (Map h Y Z/\x2 ∈ Y).
split.
apply H0.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
rewrite -> H13.
apply H11.
apply Map_Law_2 in H10.
apply H10.
Qed.

Theorem Composite_Map_Law_3:forall f h X Y Z:Set,(Surjective_Map f X Y/\Surjective_Map h Y Z)->(Surjective_Map (Composite_Map f h) X Z).
Proof.
intros.
split.
apply (Composite_Map_Law_1 f h X Y Z).
split.
destruct H.
destruct H.
apply H.
destruct H.
destruct H0.
apply H0.
intros.
destruct H.
destruct H.
destruct H1.
apply H3 in H0.
destruct H0.
destruct H0.
apply H2 in H0.
destruct H0.
destruct H0.
exists x0.
split.
apply H0.
assert (Map f X Y/\Map h Y Z/\x0 ∈ X).
split.
apply H.
split.
apply H1.
apply H0.
apply Composite_Map_Law_2 in H6.
rewrite <- H6.
rewrite <- H5.
apply H4.
Qed.

Theorem Composite_Map_Law_4:forall f h X Y Z:Set,(Injective_Map f X Y/\Injective_Map h Y Z)->(Injective_Map (Composite_Map f h) X Z).
Proof.
intros.
split.
apply (Composite_Map_Law_1 f h X Y Z).
destruct H.
destruct H.
destruct H0.
split.
apply H.
apply H0.
intros.
destruct H0.
destruct H1.
destruct H.
destruct H.
destruct H3.
apply H4.
split.
apply H0.
split.
apply H1.
apply H5.
split.
apply (Map_Law_2 f X Y x1).
split.
apply H.
apply H0.
split.
apply (Map_Law_2 f X Y x2).
split.
apply H.
apply H1.
assert (Map f X Y/\Map h Y Z/\x1 ∈ X).
split.
apply H.
split.
apply H3.
apply H0.
assert (Map f X Y/\Map h Y Z/\x2 ∈ X).
split.
apply H.
split.
apply H3.
apply H1.
apply Composite_Map_Law_2 in H6.
apply Composite_Map_Law_2 in H7.
rewrite -> H6.
rewrite -> H7.
apply H2.
Qed.

Theorem Composite_Map_Law_5:forall f h X Y Z:Set,(Bijective_Map f X Y/\Bijective_Map h Y Z)->(Bijective_Map (Composite_Map f h) X Z).
Proof.
intros.
destruct H.
destruct H.
destruct H0.
split.
apply (Composite_Map_Law_3  f h X Y Z).
split.
apply H.
apply H0.
apply (Composite_Map_Law_4  f h X Y Z).
split.
apply H1.
apply H2.
Qed.



Definition Identify_Map(X:Set):=Prop_Set (fun a=>exists x:Set,x ∈ X/\a=Ordered_Set x x).

Theorem Identify_Map_Law_1:forall a X:Set,a ∈ (Identify_Map X)<->exists x:Set,x ∈ X/\a=Ordered_Set x x.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set X)).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
destruct H.
destruct H.
rewrite -> H2 in H0.
apply Ordered_Set_Law_1 in H0.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H1.
rewrite -> H1.
apply H.
rewrite -> H1.
apply H.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
apply H.
Qed.

Theorem Identify_Map_Law_2:forall X:Set,Bijective_Map (Identify_Map X) X X.
Proof.
intros.
assert (forall a:Set,a ∈ (Identify_Map X)<->exists x:Set,x ∈ X/\a=Ordered_Set x x).
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set X)).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
destruct H.
destruct H.
rewrite -> H2 in H0.
apply Ordered_Set_Law_1 in H0.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H0.
destruct H1.
rewrite -> H0.
apply H.
rewrite -> H0.
apply H.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
apply H.

assert (Map (Identify_Map X) X X).
split.
intros.
apply H in H0.
destruct H0.
destruct H0.
exists x.
exists x.
split.
apply H0.
split.
apply H0.
apply H1.
intros.
exists x.
split.
split.
apply H.
exists x.
split.
apply H0.
split.
apply H0.
intros.
destruct H1.
apply H in H1.
destruct H1.
destruct H1.
apply Ordered_Set_Law_2 in H3.
destruct H3.
rewrite -> H4.
apply H3.
split.

split.
apply H0.
intros.
exists y.
split.
apply H1.
assert (Map (Identify_Map X) X X/\y ∈ X/\y ∈ X/\(Ordered_Set y y) ∈ (Identify_Map X)).
split.
apply H0.
split.
apply H1.
split.
apply H1.
apply H.
exists y.
split.
apply H1.
split.
apply Map_Law_3 in H2.
apply H2.

split.
apply H0.
intros.
destruct H1.
destruct H2.
assert (Map (Identify_Map X) X X/\x1 ∈ X/\x1 ∈ X/\(Ordered_Set x1 x1) ∈ (Identify_Map X)).
split.
apply H0.
split.
apply H1.
split.
apply H1.
apply H.
exists x1.
split.
apply H1.
split.
assert (Map (Identify_Map X) X X/\x2 ∈ X/\x2 ∈ X/\(Ordered_Set x2 x2) ∈ (Identify_Map X)).
split.
apply H0.
split.
apply H2.
split.
apply H2.
apply H.
exists x2.
split.
apply H2.
split.
apply Map_Law_3 in H4.
apply Map_Law_3 in H5.
rewrite -> H4.
rewrite -> H5.
apply H3.
Qed.

Theorem Identify_Map_Law_3:forall X x:Set,(x ∈ X)->x=(Culculateion_Map (Identify_Map X) x).
Proof.
intros.
apply (Map_Law_3 (Identify_Map X) X X x).
split.
destruct (Identify_Map_Law_2 X).
destruct H1.
apply H1.
split.
apply H.
split.
apply H.
apply Identify_Map_Law_1.
exists x.
split.
apply H.
split.
Qed.



Definition Inverse_Map(f X Y:Set):=Prop_Set (fun a=>exists x y:Set,x ∈ X/\y ∈ Y/\(Ordered_Set x y) ∈ f/\a=Ordered_Set y x).

Theorem Inverse_Map_Law_1:forall a f X Y:Set,a ∈ (Inverse_Map f X Y)<->exists x y:Set,x ∈ X/\y ∈ Y/\(Ordered_Set x y) ∈ f/\a=Ordered_Set y x.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set (X ∪ Y))).
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Union_Set_Law_1.
rewrite -> H2 in H3.
apply Ordered_Set_Law_1 in H3.
destruct H3.
rewrite -> H3 in H4.
apply Pair_Set_Law_1 in H4.
destruct H4.
rewrite -> H4.
right.
apply H0.
rewrite -> H4.
left.
apply H.
rewrite -> H3 in H4.
apply Single_Set_Law_1 in H4.
rewrite -> H4.
left.
apply H.
Qed.

Theorem Inverse_Map_Law_2:forall f X Y:Set,Bijective_Map f X Y->Map (Inverse_Map f X Y) Y X.
Proof.
intros.

split.
intros.
destruct H.
apply Inverse_Map_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H2.
destruct H3.
exists x0.
exists x.
split.
apply H2.
split.
apply H0.
apply H4.

intros.
destruct H.
destruct H.
apply H2 in H0.
destruct H0.
destruct H0.
exists x0.
split.
split.
apply Inverse_Map_Law_1.
exists x0.
exists x.
split.
apply H0.
split.
assert (Map f X Y/\x0 ∈ X).
split.
apply H.
apply H0.
apply Map_Law_2 in H4.
rewrite -> H3.
apply H4.
split.
assert (Map f X Y/\x0 ∈ X).
split.
apply H.
apply H0.
apply Map_Law_1 in H4.
rewrite -> H3.
apply H4.
split.
apply H0.
intros.
destruct H4.
destruct H1.
apply H6.
split.
apply H0.
split.
apply H5.
apply Inverse_Map_Law_1 in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H7.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
assert (Map f X Y/\x1 ∈ X/\x2 ∈ Y/\(Ordered_Set x1 x2) ∈ f).
split.
apply H.
split.
apply H4.
split.
apply H7.
apply H8.
apply Map_Law_3 in H11.
rewrite <- H10 in H11.
rewrite <- H3.
rewrite <- H11.
apply H9.
Qed.

Theorem Inverse_Map_Law_3:forall f x y X Y:Set,(Bijective_Map f X Y/\x ∈ X/\y ∈ Y/\(Ordered_Set x y) ∈ f)->(Ordered_Set y x) ∈ (Inverse_Map f X Y).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply Inverse_Map_Law_1.
exists x.
exists y.
split.
apply H0.
split.
apply H1.
split.
apply H2.
split.
Qed.

Theorem Inverse_Map_Law_4:forall f X Y:Set,Bijective_Map f X Y->Identify_Map X=Composite_Map f (Inverse_Map f X Y).
Proof.
intros.
assert (Map (Identify_Map X) X X/\Map (Composite_Map f (Inverse_Map f X Y)) X X/\(forall x:Set,x ∈ X->(Culculateion_Map (Identify_Map X) x=Culculateion_Map (Composite_Map f (Inverse_Map f X Y)) x))).
split.
apply Identify_Map_Law_2.
split.
assert (Map f X Y/\Map (Inverse_Map f X Y) Y X).
split.
destruct H.
destruct H.
apply H.
apply Inverse_Map_Law_2.
apply H.
apply Composite_Map_Law_1 in H0.
apply H0.
intros.
assert (Map (Identify_Map X) X X/\x ∈ X/\x ∈ X/\(Ordered_Set x x) ∈ (Identify_Map X)).
split.
apply Identify_Map_Law_2.
split.
apply H0.
split.
apply H0.
apply Identify_Map_Law_1.
exists x.
split.
apply H0.
split.
apply Map_Law_3 in H1.
assert (Map f X Y/\Map (Inverse_Map f X Y) Y X/\x ∈ X).
split.
destruct H.
destruct H.
apply H.
split.
apply Inverse_Map_Law_2.
apply H.
apply H0.
apply Composite_Map_Law_2 in H2.
rewrite <- H2.
destruct H.
destruct H.
destruct H.
assert (x ∈ X).
apply H0.
apply H5 in H0.
destruct H0.
destruct H0.
destruct H0.
assert (Map f X Y/\x ∈ X/\x0 ∈ Y/\(Ordered_Set x x0) ∈ f).
split.
split.
apply H.
apply H5.
split.
apply H6.
split.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite -> H11.
apply H9.
apply H0.
apply Map_Law_3 in H9.
rewrite <- H9.
assert (Bijective_Map f X Y/\x ∈ X/\x0 ∈ Y/\(Ordered_Set x x0) ∈ f).
split.
split.
split.
split.
apply H.
apply H5.
apply H4.
apply H3.
split.
apply H6.
split.
apply H8.
apply H0.
apply Inverse_Map_Law_3 in H10.
assert (Map (Inverse_Map f X Y) Y X/\x0 ∈ Y/\x ∈ X/\(Ordered_Set x0 x) ∈ (Inverse_Map f X Y)).
split.
apply Inverse_Map_Law_2.
split.
split.
split.
apply H.
apply H5.
apply H4.
apply H3.
split.
apply H8.
split.
apply H6.
apply H10.
apply Map_Law_3 in H11.
rewrite <- H11.
rewrite <- H1.
split.
apply Map_Law_4 in H0.
apply H0.
Qed.

Theorem Inverse_Map_Law_5:forall f X Y:Set,Bijective_Map f X Y->Identify_Map Y=Composite_Map (Inverse_Map f X Y) f.
Proof.
intros.
assert (Map (Identify_Map Y) Y Y/\Map (Composite_Map (Inverse_Map f X Y) f) Y Y/\(forall y:Set,y ∈ Y->(Culculateion_Map (Identify_Map Y) y=Culculateion_Map (Composite_Map (Inverse_Map f X Y) f) y))).
split.
apply Identify_Map_Law_2.
split.
assert (Map (Inverse_Map f X Y) Y X/\Map f X Y).
split.
apply Inverse_Map_Law_2.
apply H.
destruct H.
destruct H.
apply H.
apply Composite_Map_Law_1 in H0.
apply H0.
intros.
assert (Map (Identify_Map Y) Y Y/\y ∈ Y/\y ∈ Y/\(Ordered_Set y y) ∈ (Identify_Map Y)).
split.
apply Identify_Map_Law_2.
split.
apply H0.
split.
apply H0.
apply Identify_Map_Law_1.
exists y.
split.
apply H0.
split.
apply Map_Law_3 in H1.
rewrite <- H1.
assert (Map (Inverse_Map f X Y) Y X/\Map f X Y/\y ∈ Y).
split.
apply Inverse_Map_Law_2.
apply H.
destruct H.
destruct H.
split.
apply H.
apply H0.
apply Composite_Map_Law_2 in H2.
rewrite <- H2.
assert (Map (Inverse_Map f X Y) Y X).
apply Inverse_Map_Law_2.
apply H.
destruct H3.
apply H4 in H0.
destruct H0.
destruct H0.
destruct H0.
assert (Map (Inverse_Map f X Y) Y X/\y ∈ Y/\x ∈ X/\(Ordered_Set y x) ∈ (Inverse_Map f X Y)).
split.
apply Inverse_Map_Law_2.
apply H.
split.
apply Inverse_Map_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H7.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite <- H10 in H8.
rewrite <- H9 in H8.
rewrite -> H9.
apply H7.
split.
apply H6.
apply H0.
apply Map_Law_3 in H7.
apply Inverse_Map_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H8.
destruct H9.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite <- H10 in H9.
rewrite <- H11 in H9.
assert (Map f X Y/\x ∈ X/\y ∈ Y/\(Ordered_Set x y) ∈ f).
split.
destruct H.
destruct H.
apply H.
split.
apply H6.
split.
destruct H.
destruct H.
destruct H.
apply H in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H15.
apply Ordered_Set_Law_2 in H16.
destruct H16.
rewrite -> H17.
apply H15.
apply H9.
apply Map_Law_3 in H12.
rewrite <- H7.
apply H12.
apply Map_Law_4 in H0.
apply H0.
Qed.

Theorem Inverse_Map_Law_6:forall f X Y:Set,Bijective_Map f X Y->Bijective_Map (Inverse_Map f X Y) Y X.
Proof.
intros.
split.
split.
apply Inverse_Map_Law_2.
apply H.
intros.
exists (Culculateion_Map f y).
split.
apply (Map_Law_2 f X Y y).
split.
destruct H.
destruct H.
apply H.
apply H0.
assert (Map f X Y/\Map (Inverse_Map f X Y) Y X/\y ∈ X).
split.
destruct H.
destruct H.
apply H.
split.
apply Inverse_Map_Law_2.
apply H.
apply H0.
apply Inverse_Map_Law_4 in H.
apply Composite_Map_Law_2 in H1.
rewrite -> H1.
rewrite <- H.
apply Identify_Map_Law_3.
apply H0.

split.
apply Inverse_Map_Law_2.
apply H.
intros.
destruct H0.
destruct H1.
destruct H.
destruct H3.
assert (Culculateion_Map f (Culculateion_Map (Inverse_Map f X Y) x1)=Culculateion_Map f (Culculateion_Map (Inverse_Map f X Y) x2)).
rewrite -> H2.
split.
assert (Map (Inverse_Map f X Y) Y X/\Map f X Y/\x1 ∈ Y).
split.
apply Inverse_Map_Law_2.
split.
apply H.
split.
apply H3.
apply H4.
split.
apply H3.
apply H0.
assert (Map (Inverse_Map f X Y) Y X/\Map f X Y/\x2 ∈ Y).
split.
apply Inverse_Map_Law_2.
split.
apply H.
split.
apply H3.
apply H4.
split.
apply H3.
apply H1.
apply Composite_Map_Law_2 in H6.
apply Composite_Map_Law_2 in H7.
rewrite -> H6 in H5.
rewrite -> H7 in H5.
assert (Bijective_Map f X Y).
split.
apply H.
split.
apply H3.
apply H4.
apply Inverse_Map_Law_5 in H8.
rewrite <- H8 in H5.
apply Identify_Map_Law_3 in H0.
apply Identify_Map_Law_3 in H1.
rewrite <- H0 in H5.
rewrite <- H1 in H5.
apply H5.
Qed.



(*像*)
Definition Image_Map(f X Y:Set):=Prop_Set (fun y=>exists x:Set,x ∈ X/\y ∈ Y/\y=Culculateion_Map f x).

Theorem Image_Map_Law_1:forall f X Y y:Set,y ∈ (Image_Map f X Y)<->exists x:Set,x ∈ X/\y ∈ Y/\y=Culculateion_Map f x.
Proof.
intros.
apply Prop_Set_Law_1.
exists Y.
intros.
destruct H.
destruct H.
destruct H0.
apply H0.
Qed.



Definition Map_Set(X Y:Set):=Prop_Set (fun f=>Map f X Y).

Theorem Map_Set_Law_1:forall X Y f:Set,f ∈ (Map_Set X Y)<->Map f X Y.
Proof.
intros.
apply (Prop_Set_Law_1 (fun f=>Map f X Y)).
exists (Power_Set (Power_Set (Power_Set (X ∪ Y)))).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Union_Set_Law_1.
destruct H.
apply H in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H4.
rewrite -> H5 in H1.
apply Ordered_Set_Law_1 in H1.
destruct H1.
rewrite -> H1 in H2.
apply Pair_Set_Law_1 in H2.
destruct H2.
left.
rewrite -> H2.
apply H0.
right.
rewrite -> H2.
apply H4.
rewrite -> H1 in H2.
apply Single_Set_Law_1 in H2.
rewrite -> H2.
right.
apply H4.
Qed.



Definition Restriction_Map(f X:Set):=Prop_Set (fun a=>a ∈ f/\exists x:Set,x ∈ X/\a=Ordered_Set x (Culculateion_Map f x)).

Theorem Restriction_Map_Law_1:forall f X a0:Set,a0 ∈ Prop_Set (fun a=>a ∈ f/\exists x:Set,x ∈ X/\a=Ordered_Set x (Culculateion_Map f x))<->a0 ∈ f/\exists x:Set,x ∈ X/\a0=Ordered_Set x (Culculateion_Map f x).
Proof.
intros.
apply Prop_Set_Law_1.
exists f.
intros.
destruct H.
apply H.
Qed.

Theorem Restriction_Map_Law_2:forall f X X0 Y:Set,Map f X Y/\X0 ⊂ X->Map (Restriction_Map f X0) X0 Y.
Proof.
intros.
destruct H.
split.

intros.
apply Restriction_Map_Law_1 in H1.
destruct H1.
destruct H2.
destruct H2.
exists x.
exists (Culculateion_Map f x).
split.
apply H2.
split.
apply (Map_Law_2 f X Y x).
split.
apply H.
apply H0.
apply H2.
apply H3.

intros.
exists (Culculateion_Map f x).
split.
split.
apply Restriction_Map_Law_1.
split.
apply (Map_Law_1 f X Y x).
split.
apply H.
apply H0.
apply H1.
exists x.
split.
apply H1.
split.
apply (Map_Law_2 f X Y x).
split.
apply H.
apply H0.
apply H1.
intros.
destruct H2.
apply Restriction_Map_Law_1 in H2.
destruct H2.
destruct H4.
destruct H4.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H6.
rewrite -> H5.
split.
Qed.

Theorem Restriction_Map_Law_3:forall f X X0 Y x:Set,Map f X Y/\X0 ⊂ X/\x ∈ X0->Culculateion_Map (Restriction_Map f X0) x=Culculateion_Map f x.
Proof.
intros.
destruct H.
destruct H0.
assert ((Ordered_Set x (Culculateion_Map (Restriction_Map f X0) x)) ∈ (Restriction_Map f X0)).
apply (Map_Law_1 (Restriction_Map f X0) X0 Y).
split.
apply (Restriction_Map_Law_2 f X X0 Y).
split.
apply H.
apply H0.
apply H1.
apply Restriction_Map_Law_1 in H2.
destruct H2.
destruct H3.
destruct H3.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite <- H4 in H5.
apply H5.
Qed.



(*順序同型*)
Definition Ordered_Relation_homomorphic(f X g Y:Set):=Ordered_Relation f X/\Ordered_Relation g Y/\(exists a:Set,Map a X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->((Relation_Prop f x1 x2)<->(Relation_Prop g (Culculateion_Map a x1) (Culculateion_Map a x2)))).

Theorem Ordered_Relation_homomorphic_Law_1:forall f X:Set,Ordered_Relation f X->Ordered_Relation_homomorphic f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

exists (Identify_Map X).
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

Theorem Ordered_Relation_homomorphic_Law_2:forall f X g Y h Z:Set,Ordered_Relation_homomorphic f X g Y/\Ordered_Relation_homomorphic g Y h Z->Ordered_Relation_homomorphic f X h Z.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H2.
destruct H0.
destruct H4.
destruct H5.
destruct H5.
split.
apply H.

split.
apply H4.
exists (Composite_Map x x0).
split.
apply (Composite_Map_Law_1 x x0 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map x x1) ∈ Y/\(Culculateion_Map x x2) ∈ Y).
split.
apply (Map_Law_2 x X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 x X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 x x0 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 x x0 x2 X Y Z).
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

Definition Ordered_Relation_Isomorphic(f X g Y:Set):=Ordered_Relation f X/\Ordered_Relation g Y/\(exists a:Set,Bijective_Map a X Y/\forall x1 x2:Set,x1 ∈ X/\x2 ∈ X->(Relation_Prop f x1 x2<->(Relation_Prop g (Culculateion_Map a x1) (Culculateion_Map a x2)))).

Theorem Ordered_Relation_Isomorphic_Law_1:forall f X:Set,Ordered_Relation f X->Ordered_Relation_Isomorphic f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

exists (Identify_Map X).
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

Theorem Ordered_Relation_Isomorphic_Law_2:forall f X g Y h Z:Set,Ordered_Relation_Isomorphic f X g Y/\Ordered_Relation_Isomorphic g Y h Z->Ordered_Relation_Isomorphic f X h Z.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H2.
destruct H0.
destruct H4.
destruct H5.
destruct H5.
split.
apply H.
split.
apply H4.

exists (Composite_Map x x0).
split.
apply (Composite_Map_Law_5 x x0 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map x x1) ∈ Y/\(Culculateion_Map x x2) ∈ Y).
split.
apply (Map_Law_2 x X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 x X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 x x0 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 x x0 x2 X Y Z).
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

Theorem Ordered_Relation_Isomorphic_Law_3:forall f X g Y:Set,Ordered_Relation_Isomorphic f X g Y->Ordered_Relation_Isomorphic g Y f X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H1.
split.
apply H0.
split.
apply H.
exists (Inverse_Map x X Y).
split.
apply Inverse_Map_Law_6.
apply H1.

intros.
destruct H3.
assert  ((Culculateion_Map (Inverse_Map x X Y) x1) ∈ X/\(Culculateion_Map (Inverse_Map x X Y) x2) ∈ X).
split.
apply (Map_Law_2 (Inverse_Map x X Y) Y X x1).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map x X Y) Y X x2).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H4.
apply H2 in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x X Y) x x1 Y X Y) in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x X Y) x x2 Y X Y) in H5.
rewrite <- (Inverse_Map_Law_5 x X Y) in H5.
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



(*整列同型*)
Definition Well_Oredered_Relation_homomorphic(f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\(exists a:Set,Map a X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->(Relation_Prop f x1 x2->(Relation_Prop g (Culculateion_Map a x1) (Culculateion_Map a x2)))).

Theorem Well_Oredered_Relation_homomorphic_Law_1:forall f X:Set,Well_Oredered_Relation f X->Well_Oredered_Relation_homomorphic f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

exists (Identify_Map X).
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

Theorem Well_Oredered_Relation_homomorphic_Law_2:forall f X g Y h Z:Set,Well_Oredered_Relation_homomorphic f X g Y/\Well_Oredered_Relation_homomorphic g Y h Z->Well_Oredered_Relation_homomorphic f X h Z.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H2.
destruct H0.
destruct H4.
destruct H5.
destruct H5.
split.
apply H.

split.
apply H4.
exists (Composite_Map x x0).
split.
apply (Composite_Map_Law_1 x x0 X Y Z).
split.
apply H2.
apply H5.

intros.
rewrite <- (Composite_Map_Law_2 x x0 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 x x0 x2 X Y Z).
apply H6.
destruct H7.
split.
apply (Map_Law_2 x X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 x X Y x2).
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

Definition Well_Oredered_Relation_Isomorphic(f X g Y:Set):=Well_Oredered_Relation f X/\Well_Oredered_Relation g Y/\(exists a:Set,Bijective_Map a X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X)->((Relation_Prop f x1 x2)<->(Relation_Prop g (Culculateion_Map a x1) (Culculateion_Map a x2)))).

Theorem Well_Oredered_Relation_Isomorphic_Law_1:forall f X:Set,Well_Oredered_Relation f X->Well_Oredered_Relation_Isomorphic f X f X.
Proof.
intros.
split.
apply H.
split.
apply H.

exists (Identify_Map X).
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

Theorem Well_Oredered_Relation_Isomorphic_Law_2:forall f X g Y h Z:Set,Well_Oredered_Relation_Isomorphic f X g Y/\Well_Oredered_Relation_Isomorphic g Y h Z->Well_Oredered_Relation_Isomorphic f X h Z.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H2.
destruct H0.
destruct H4.
destruct H5.
destruct H5.
split.
apply H.
split.
apply H4.

exists (Composite_Map x x0).
split.
apply (Composite_Map_Law_5 x x0 X Y Z).
split.
apply H2.
apply H5.
intros.
assert (x1 ∈ X/\x2 ∈ X).
apply H7.
apply H3 in H8.
destruct H7.
assert ((Culculateion_Map x x1) ∈ Y/\(Culculateion_Map x x2) ∈ Y).
split.
apply (Map_Law_2 x X Y x1).
split.
apply H2.
apply H7.
apply (Map_Law_2 x X Y x2).
split.
apply H2.
apply H9.
apply H6 in H10.
rewrite <- (Composite_Map_Law_2 x x0 x1 X Y Z).
rewrite <- (Composite_Map_Law_2 x x0 x2 X Y Z).
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

Theorem Well_Oredered_Relation_Isomorphic_Law_3:forall f X g Y:Set,Well_Oredered_Relation_Isomorphic f X g Y->Well_Oredered_Relation_Isomorphic g Y f X.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H1.
split.
apply H0.
split.
apply H.
exists (Inverse_Map x X Y).
split.
apply Inverse_Map_Law_6.
apply H1.

intros.
destruct H3.
assert ((Culculateion_Map (Inverse_Map x X Y) x1) ∈ X/\(Culculateion_Map (Inverse_Map x X Y) x2) ∈ X).
split.
apply (Map_Law_2 (Inverse_Map x X Y) Y X x1).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map x X Y) Y X x2).
split.
apply Inverse_Map_Law_2.
apply H1.
apply H4.
apply H2 in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x X Y) x x1 Y X Y) in H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map x X Y) x x2 Y X Y) in H5.
rewrite <- (Inverse_Map_Law_5 x X Y) in H5.
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

Theorem Well_Oredered_Relation_Isomorphic_Law_4:forall f X x1 x2:Set,Well_Oredered_Relation f X/\x1 ∈ X/\x2 ∈ X/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2)->x1=x2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
assert (Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x1)) (Predecessor_Set f X x1) (Restriction_Relation f (Predecessor_Set f X x2)) (Predecessor_Set f X x2)).
apply H2.
destruct H3.
destruct H4.
destruct H5.
destruct H5.
assert (Well_Oredered_Relation f X).
apply H.

Qed.

Theorem Well_Oredered_Relation_Isomorphic_Law_5:forall f X g Y:Set,(Well_Oredered_Relation f X/\Well_Oredered_Relation g Y)->((exists x0:Set,x0 ∈ X/\Well_Oredered_Relation_Isomorphic (Restriction_Map f (Predecessor_Set f X x0)) (Predecessor_Set f X x0) g Y)\/Well_Oredered_Relation_Isomorphic f X g Y\/(exists y0:Set,y0 ∈ Y/\Well_Oredered_Relation_Isomorphic f X (Restriction_Map g (Predecessor_Set g Y y0)) (Predecessor_Set g Y y0))).
Proof.
intros.
destruct H.

assert (forall a:Set,a ∈ (Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))<->exists x y:Set,x ∈ X/\y ∈ Y/\a=Ordered_Set x y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)).
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
assert (exists h:Set,h=(Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y)))).
exists (Prop_Set (fun a0=>exists x y:Set,x ∈ X/\y ∈ Y/\a0=Ordered_Set x y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X x)) (Predecessor_Set f X x) (Restriction_Relation g (Predecessor_Set g Y y)) (Predecessor_Set g Y y))).
split.
destruct H2.
rewrite <- H2 in H1.
clear H2.

assert (forall a:Set,a ∈ (Prop_Set (fun a1=>exists a2:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2)))<->exists a2:Set,a ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a)) (Predecessor_Set f X a) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2)).
intros.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H2.
destruct H2.
destruct H3.
apply H2.
assert (exists X1:Set,X1=(Prop_Set (fun a1=>exists a2:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2)))).
exists (Prop_Set (fun a1=>exists a2:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2))).
split.
destruct H3.
rewrite <- H3 in H2.
clear H3.

assert (forall a:Set,a ∈ (Prop_Set (fun a2=>exists a1:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2)))<->exists a1:Set,a1 ∈ X/\a ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a)) (Predecessor_Set g Y a)).
intros.
apply Prop_Set_Law_1.
exists Y.
intros.
destruct H3.
destruct H3.
destruct H4.
apply H4.
assert (exists X2:Set,X2=(Prop_Set (fun a2=>exists a1:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2)))).
exists (Prop_Set (fun a2=>exists a1:Set,a1 ∈ X/\a2 ∈ Y/\Well_Oredered_Relation_Isomorphic (Restriction_Relation f (Predecessor_Set f X a1)) (Predecessor_Set f X a1) (Restriction_Relation g (Predecessor_Set g Y a2)) (Predecessor_Set g Y a2))).
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
rewrite <- H10 in H11.
rewrite <- H12 in H9.
rewrite <- H12 in H11.
clear H10.
clear H12.
Qed.



(*狭義整列同型*)
Definition Narrow_Well_Oredered_Relation_homomorphic(f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\(exists h:Set,Map g X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->(Relation_Prop g (Culculateion_Map h x1) (Culculateion_Map h x2))).

Definition Narrow_Well_Oredered_Relation_Isomorphic(f X g Y:Set):=Narrow_Well_Oredered_Relation f X/\Narrow_Well_Oredered_Relation g Y/\(exists h:Set,Bijective_Map g X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Relation_Prop f x1 x2)->(Relation_Prop g (Culculateion_Map h x1) (Culculateion_Map h x2))).

