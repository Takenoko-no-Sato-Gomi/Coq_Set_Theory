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

Theorem Equivalenc_Relation_Law_1:forall f X:Set,Equivalenc_Relation f X->Relation f X.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Equivalenc_Relation_Law_2:forall f X x:Set,Equivalenc_Relation f X/\x ∈ X->Relation_Prop f x x.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Equivalenc_Relation_Law_3:forall f X x y:Set,Equivalenc_Relation f X/\Relation_Prop f x y->Relation_Prop f y x.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Equivalenc_Relation_Law_4:forall f X x y z:Set,Equivalenc_Relation f X/\Relation_Prop f x y/\Relation_Prop f y z->Relation_Prop f x z.
Proof.
intros.
destruct H.
destruct H0.
destruct H.
destruct H2.
destruct H3.
apply (H4 x y z).
split.
apply H0.
apply H1.
Qed.

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

Theorem Ordered_Relation_Law_1:forall f X:Set,Ordered_Relation f X->Relation f X.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Ordered_Relation_Law_2:forall f X x:Set,Ordered_Relation f X/\x ∈ X->Relation_Prop f x x.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Ordered_Relation_Law_3:forall f X x y z:Set,Ordered_Relation f X/\Relation_Prop f x y/\Relation_Prop f y z->Relation_Prop f x z.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply (H2 x y z).
apply H0.
Qed.

Theorem Ordered_Relation_Law_4:forall f X x y:Set,Ordered_Relation f X/\Relation_Prop f x y/\Relation_Prop f y x->x=y.
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply H3.
apply H0.
Qed.

Theorem Ordered_Relation_Law_5:forall f X a:Set,(Ordered_Relation f X/\Maximum_Element f X a)->(Maximal_Element f X a).
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

Theorem Ordered_Relation_Law_6:forall f X a:Set,(Ordered_Relation f X/\Minimum_Element f X a)->(Minimal_Element f X a).
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

Theorem Totaly_Ordered_Relation_Law_1:forall f X:Set,Totaly_Ordered_Relation f X->Ordered_Relation f X.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Totaly_Ordered_Relation_Law_2:forall f X x y:Set,Totaly_Ordered_Relation f X/\x ∈ X/\y ∈ X->Relation_Prop f x y\/Relation_Prop f y x.
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
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