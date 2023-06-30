Require Export Coq_Basic.



(*関係*)
Definition Relation_Prop(f x y:Set):=(Ordered_Set x y) ∈ f.

Definition Reration(f X:Set):=forall a:Set,a ∈ f->exists x y:Set,a=Ordered_Set x y/\x ∈ X/\y ∈ X.



Definition Refrectiv_Law(f X:Set):=forall x:Set,x ∈ X->Relation_Prop f x x.

Definition Symmetric_Law(f X:Set):=forall x y:Set,Relation_Prop f x y->Relation_Prop f y x.

Definition Transitive_Law(f X:Set):=forall x y z:Set,(Relation_Prop f x y/\Relation_Prop f y z)->Relation_Prop f x z.

Definition Asymmetric_Law(f X:Set):=forall x y:Set,(Relation_Prop f x y/\Relation_Prop f y x)->x=y.

Definition Totaly_Odered_Law(f X:Set):=forall x y:Set,(x ∈ X/\y ∈ X)->(Relation_Prop f x y\/Relation_Prop f y x).



(*部分関係*)
Definition Sub_Reration_Set(f Y:Set):=Prop_Set (fun a=>exists x y:Set,a=(Ordered_Set x y)/\x ∈ Y/\y ∈ Y/\a ∈ f).

Theorem Sub_Reration_Law_1:forall f X Y:Set,(Reration f X/\Y ⊂ X)->Reration (Sub_Reration_Set f Y) X.
Proof.
intros.
destruct H.
intro.
intro.
apply (Prop_Set_Law_1 (fun a=>exists x y:Set,a=(Ordered_Set x y)/\x ∈ Y/\y ∈ Y/\a ∈ f)) in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
exists x.
exists x0.
split.
apply H1.
split.
apply H0.
apply H2.
apply H0.
apply H3.
exists (Power_Set (Power_Set X)).
intros.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
destruct H5.
rewrite -> H3.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Ordered_Set_Law_1 in H7.
destruct H7.
rewrite -> H7 in H8.
apply Pair_Set_Law_1 in H8.
destruct H8.
rewrite -> H8.
apply H0.
apply H4.
rewrite -> H8.
apply H0.
apply H5.
rewrite -> H7 in H8.
apply Single_Set_Law_1 in H8.
rewrite -> H8.
apply H0.
apply H5.
Qed.



(*同値関係*)
Definition Equivalenc_Relation(f X:Set):=Reration f X/\Refrectiv_Law f X/\Symmetric_Law f X/\Transitive_Law f X.

Definition Equivalence_Class(f x:Set):=Prop_Set (fun y=>Relation_Prop f x y).

Definition Quotient_Set(f X:Set):=Prop_Set (fun x'=>exists x:Set,x ∈ X/\x'=Equivalence_Class f x).

Theorem Equivalence_Class_Law_1:forall f x y X:Set,(Equivalenc_Relation f X/\x ∈ (Equivalence_Class f y))->(Relation_Prop f x y).
Proof.
intros.
destruct H.
apply (Prop_Set_Law_1 (fun z=>Relation_Prop f y z)) in H0.
destruct H.
destruct H1.
destruct H2.
apply H2.
apply H0.
exists X.
intros.
destruct H.
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
apply Ordered_Set_Law_2 in H2.
destruct H2.
rewrite -> H6.
apply H5.
Qed.

Theorem Equivalence_Class_Law_2:forall f x y X:Set,(Equivalenc_Relation f X/\(Relation_Prop f x y))->(x ∈ (Equivalence_Class f y)).
Proof.
intros.
destruct H.
destruct H.
apply Prop_Set_Law_1.
exists X.
intros.
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
apply Ordered_Set_Law_2 in H2.
destruct H2.
rewrite -> H5.
apply H4.
destruct H1.
destruct H2.
apply H2.
apply H0.
Qed.

Theorem Quotient_Set_Law_1:forall f X:Set,(Equivalenc_Relation f X/\~X=∅)->(X=Union_Set (Quotient_Set f X)).
Proof.
intros.
destruct H.
apply Empty_Set_Law_1 in H0.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Union_Set_Law_1.
exists (Equivalence_Class f z).
split.
apply Prop_Set_Law_1.
exists (Power_Set X).
intros.
apply Power_Set_Law_1.
destruct H2.
destruct H2.
rewrite -> H3.
intro.
intro.
apply (Prop_Set_Law_1 (fun y=>Relation_Prop f x0 y)) in H4.
destruct H.
apply H in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite -> H8.
apply H7.
exists X.
intros.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H9.
destruct H8.
apply H10.
exists z.
split.
apply H1.
split.
apply Prop_Set_Law_1.
exists X.
intros.
destruct H.
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
apply Ordered_Set_Law_2 in H2.
destruct H2.
rewrite -> H5.
destruct H4.
apply H6.
destruct H.
destruct H2.
apply H2.
apply H1.

intro.
apply Union_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply (Prop_Set_Law_1 (fun x'=>exists x:Set,x ∈ X/\x'=Equivalence_Class f x)) in H1.
destruct H1.
destruct H1.
rewrite -> H3 in H2.
destruct H.
apply (Prop_Set_Law_1 (fun y=>Relation_Prop f x0 y)) in H2.
apply H in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H5.
apply Ordered_Set_Law_2 in H2.
destruct H2.
rewrite -> H7.
apply H6.
exists X.
intros.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H8.
destruct H7.
apply H9.
exists (Power_Set X).
intros.
destruct H4.
destruct H4.
rewrite -> H5.
apply Power_Set_Law_1.
intro.
intro.
apply (Prop_Set_Law_1 (fun y=>Relation_Prop f x1 y)) in H6.
destruct H.
apply H in H6.
destruct H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H6.
destruct H6.
rewrite -> H9.
apply H8.
exists X.
intros.
destruct H.
apply H in H8.
destruct H8.
destruct H8.
destruct H8.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H11.
apply H10.
Qed.

Theorem Quotient_Set_Law_2:forall f x y X:Set,(Equivalenc_Relation f X/\x ∈ X/\y ∈ X)->(~(Relation_Prop f x y)->(Equivalence_Class f x) ∩ (Equivalence_Class f y)=∅).
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Pair_Meet_Set_Law_1 in H1.
destruct H1.
assert (Equivalenc_Relation f X/\z ∈ (Equivalence_Class f x)).
split.
apply H.
apply H1.
apply Equivalence_Class_Law_1 in H3.
assert (Equivalenc_Relation f X/\z ∈ (Equivalence_Class f y)).
split.
apply H.
apply H2.
apply Equivalence_Class_Law_1 in H4.
destruct H0.
destruct H.
destruct H.
destruct H5.
destruct H6.
assert (Relation_Prop f x z/\Relation_Prop f z y).
split.
apply H6.
apply H3.
apply H4.
apply H7 in H8.
apply H8.

intro.
destruct (Definition_of_Empty_Set z).
apply H1.
Qed.



(*順序関係*)
Definition Ordered_Relation(f X:Set):=Reration f X/\Refrectiv_Law f X/\Transitive_Law f X/\Asymmetric_Law f X.

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
Definition Well_Oredered_Reration(f X:Set):=Totaly_Ordered_Relation f X/\(forall Y:Set,(Y ⊂ X/\~Y=∅)->exists a:Set,Minimum_Element f Y a).

(*狭義整列順序*)
Definition Narrow_Well_Oredered_Reration(f X:Set):=Reration f X/\Transitive_Law f X/\(forall x y :Set,(x ∈ X/\y ∈ X)->(Relation_Prop f x y\/x=y\/Relation_Prop f y x))/\(forall x:Set,x ∈ X->~Relation_Prop f x x)/\(forall Y:Set,(Y ⊂ X/\~Y=∅)->exists a:Set,a ∈ Y/\forall x:Set,(x ∈ Y/\~a=x)->Relation_Prop f a x).

Theorem Well_Oredered_Reration_Law_1:forall f X a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f/\(forall x:Set,~a=Ordered_Set x x)))<->a0 ∈ f/\(forall x:Set,~a0=Ordered_Set x x).
Proof.
intros.
apply Prop_Set_Law_1.
exists f.
intros.
destruct H.
apply H.
Qed.

Theorem Well_Oredered_Reration_Law_2:forall f X:Set,Well_Oredered_Reration f X->Narrow_Well_Oredered_Reration (Prop_Set (fun a=>a ∈ f/\(forall x:Set,~a=(Ordered_Set x x)))) X.
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

Theorem Well_Oredered_Reration_Law_3:forall f X a0:Set,a0 ∈ (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x))))<->a0 ∈ f\/(exists x:Set,x ∈ X/\a0=(Ordered_Set x x)).
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


Theorem Well_Oredered_Reration_Law_4:forall f X:Set,Narrow_Well_Oredered_Reration f X->Well_Oredered_Reration (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X.
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



(*超限帰納法*)
Theorem Transfinite_Induction_1:forall p:Set->Prop,forall f X:Set,Well_Oredered_Reration f X->((forall a:Set,a ∈ X->(forall x:Set,(x ∈ X->((Relation_Prop f x a/\~x=a->p x))))->p a)->(forall x:Set,x ∈ X->p x)).
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

Theorem Transfinite_Induction_2:forall p:Set->Prop,forall f X:Set,Narrow_Well_Oredered_Reration f X->((forall a:Set,a ∈ X->(forall x:Set,(x ∈ X->((Relation_Prop f x a->p x))))->p a)->(forall x:Set,x ∈ X->p x)).
Proof.
intros.
apply (Transfinite_Induction_1 p (Prop_Set (fun a=>a ∈ f\/(exists x:Set,x ∈ X/\a=(Ordered_Set x x)))) X).
apply Well_Oredered_Reration_Law_4.
apply H.
intros.
apply H0.
apply H2.
intros.
apply H3.
apply H4.
split.
apply Well_Oredered_Reration_Law_3.
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