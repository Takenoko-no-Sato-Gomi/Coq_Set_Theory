Require Export Coq_Basic.
Require Export Coq_Reration.


(*順序数*)
Definition Ordered_Number(x:Set):=(forall y:Set,y ∈ x->y ⊂ x)/\(forall y z w:Set,(y ∈ x/\z ∈ x/\w ∈ x/\y ∈ z/\z ∈ w)->y ∈ w)/\(forall y z:Set,(y ∈ x/\z ∈ x)->(y ∈ z\/y=z\/z ∈ y))/\(forall y:Set,y ∈ x->~y ∈ y)/\(forall y:Set,((y ⊂ x/\~y=∅)->exists z:Set,(z ∈ y/\forall w:Set,(w ∈ y->~w ∈ z)))).

Theorem Ordered_Number_Law_1:forall x y:Set,(y ∈ x/\Ordered_Number x)->Ordered_Number y.
Proof.
intros.
split.
intros.
intro.
intro.
destruct H.
destruct H2.
destruct H3.
apply (H3 z y0 y).
split.
apply H2 in H.
apply H in H0.
apply H2 in H0.
apply H0.
apply H1.
split.
apply H2 in H.
apply H in H0.
apply H0.
split.
apply H.
split.
apply H1.
apply H0.
split.

intros.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H.
destruct H5.
destruct H6.
apply (H6 y0 z w).
split.
apply H5 in H.
apply H.
apply H0.
split.
apply H5 in H.
apply H.
apply H1.
split.
apply H5 in H.
apply H.
apply H2.
split.
apply H3.
apply H4.
split.

destruct H.
intros.
destruct H0.
destruct H2.
destruct H3.
assert (y0 ∈ x/\z ∈ x).
destruct H1.
apply H0 in H.
split.
apply H.
apply H1.
apply H.
apply H5.
apply H3 in H5.
destruct H5.
left.
apply H5.
right.
destruct H5.
left.
apply H5.
right.
apply H5.
split.

intros.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
apply H1 in H.
apply H in H0.
apply H4.
apply H0.

intros.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert (y0 ⊂ x/\~y0=∅).
destruct H0.
split.
intro.
intro.
apply H1 in H.
apply H.
apply H0.
apply H7.
apply H6.
apply H5 in H6.
destruct H6.
destruct H6.
exists x0.
split.
apply H6.
intros.
apply H7.
apply H8.
Qed.

Theorem Ordered_Number_Law_2:forall x y:Set,(Ordered_Number x/\Ordered_Number y)->(Ordered_Number (x ∩ y)).
Proof.
intros.
split.
intros.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H0.
destruct H0.
destruct H.
apply Pair_Meet_Set_Law_1.
split.
destruct H.
apply H in H0.
apply H0.
apply H1.
destruct H3.
apply H3 in H2.
apply H2.
apply H1.
split.

intros.
destruct H.
destruct H.
destruct H2.
apply (H2 y0 z w).
destruct H0.
destruct H4.
destruct H5.
destruct H6.
apply Pair_Meet_Set_Law_1 in H0.
apply Pair_Meet_Set_Law_1 in H4.
apply Pair_Meet_Set_Law_1 in H5.
destruct H0.
destruct H4.
destruct H5.
split.
apply H0.
split.
apply H4.
split.
apply H5.
split.
apply H6.
apply H7.
split.

intros.
destruct H0.
apply Pair_Meet_Set_Law_1 in H0.
apply Pair_Meet_Set_Law_1 in H1.
destruct H0.
destruct H1.
destruct H.
destruct H.
destruct H5.
destruct H6.
apply (H6 y0 z).
split.
apply H0.
apply H1.
split.

intros.
destruct H.
destruct H.
destruct H2.
destruct H3.
destruct H4.
apply Pair_Meet_Set_Law_1 in H0.
destruct H0.
apply H4.
apply H0.

intros.
destruct H.
destruct H.
destruct H2.
destruct H3.
destruct H4.
assert (y0 ⊂ x/\~y0=∅).
destruct H0.
split.
intro.
intro.
apply H0 in H7.
apply Pair_Meet_Set_Law_1 in H7.
destruct H7.
apply H7.
apply H6.
apply H5 in H6.
apply H6.
Qed.

Theorem Ordered_Number_Law_3:forall x y:Set,(Ordered_Number x/\Ordered_Number y/\(x ⊂ y))->(x ∈ y\/x=y).
Proof.
intros.
destruct H.
destruct H0.
destruct (Law_of_Excluded_Middle (x=y)).
right.
apply H2.
assert ((Complement_Set y x) ⊂ y/\~(Complement_Set y x)=∅).
split.
intro.
intro.
apply Complement_Set_Law_1 in H3.
destruct H3.
apply H3.
intro.
apply H2.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply H1.
apply H4.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x)).
apply H5.
destruct (Definition_of_Empty_Set z).
rewrite <- H3.
apply Complement_Set_Law_1.
split.
apply H4.
apply H5.
destruct H0.
destruct H4.
destruct H5.
destruct H6.
apply H7 in H3.
destruct H3.
destruct H3.
assert (x0 ⊂ x).
intro.
intro.
assert (z ∈ y).
apply Complement_Set_Law_1 in H3.
destruct H3.
apply H0 in H3.
apply H3.
apply H9.
assert (~z ∈ (Complement_Set y x)).
intro.
apply H8 in H11.
apply H11.
apply H9.
assert (~(z ∈ y/\~ z ∈ x)).
intro.
apply H11.
apply Complement_Set_Law_1.
apply H12.
apply Prop_Law_7 in H12.
destruct H12.
destruct H12.
apply H10.
apply Prop_Law_3.
apply H12.

destruct (Law_of_Excluded_Middle (x ⊂ x0)).
assert (x0=x).
apply Theorem_of_Extensionality.
intro.
split.
apply H9.
apply H10.
rewrite -> H11 in H3.
apply Complement_Set_Law_1 in H3.
left.
destruct H3.
apply H3.
assert (~(Complement_Set x x0)=∅).
intro.
apply H10.
intro.
intro.
destruct (Law_of_Excluded_Middle (z ∈ x0)).
apply H13.
destruct (Definition_of_Empty_Set z).
rewrite <- H11.
apply Complement_Set_Law_1.
split.
apply H12.
apply H13.
apply Empty_Set_Law_1 in H11.
destruct H11.

assert (x0 ∈ y/\x1 ∈ y).
apply Complement_Set_Law_1 in H3.
destruct H3.
apply Complement_Set_Law_1 in H11.
destruct H11.
split.
apply H3.
apply H1.
apply H11.
apply H5 in H12.
destruct H12.
destruct H.
apply Complement_Set_Law_1 in H11.
destruct H11.
apply H in H11.
apply H11 in H12.
apply Complement_Set_Law_1 in H3.
destruct H3.
destruct H15.
apply H12.
destruct H12.
apply Complement_Set_Law_1 in H3.
destruct H3.
apply Complement_Set_Law_1 in H11.
destruct H11.
destruct H13.
rewrite -> H12.
apply H11.
apply Complement_Set_Law_1 in H11.
destruct H11.
destruct H13.
apply H12.
Qed.

Theorem Ordered_Number_Law_4:forall x y z:Set,(Ordered_Number x/\Ordered_Number y/\Ordered_Number z/\x ∈ y/\y ∈ z)->x ∈ z.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H1.
apply H1 in H3.
apply H3.
apply H2.
Qed.

Theorem Ordered_Number_Law_5:forall x y:Set,(Ordered_Number x/\Ordered_Number y)->(x ∈ y\/x=y\/y ∈ x).
Proof.
intros.
destruct H.
assert ((x ∩ y) ⊂ x).
intro.
intro.
apply Pair_Meet_Set_Law_1 in H1.
destruct H1.
apply H1.
assert ((x ∩ y) ⊂ y).
intro.
intro.
apply Pair_Meet_Set_Law_1 in H2.
destruct H2.
apply H3.
assert (Ordered_Number (x ∩ y)).
apply Ordered_Number_Law_2.
split.
apply H.
apply H0.
assert ((x ∩ y) ∈ x\/(x ∩ y)=x).
apply Ordered_Number_Law_3.
split.
apply H3.
split.
apply H.
apply H1.
assert ((x ∩ y) ∈ y\/(x ∩ y)=y).
apply Ordered_Number_Law_3.
split.
apply H3.
split.
apply H0.
apply H2.
destruct H4.
destruct H5.
assert ((x ∩ y) ∈ (x ∩ y)).
apply Pair_Meet_Set_Law_1.
split.
apply H4.
apply H5.
destruct H.
destruct H7.
destruct H8.
destruct H9.
apply H9 in H4.
destruct H4.
apply H6.
assert (y ⊂ x).
intro.
intro.
rewrite <- H5 in H6.
apply Pair_Meet_Set_Law_1 in H6.
destruct H6.
apply H6.
assert (Ordered_Number y/\Ordered_Number x/\(y ⊂ x)).
split.
apply H0.
split.
apply H.
apply H6.
apply Ordered_Number_Law_3 in H7.
right.
destruct H7.
right.
apply H7.
left.
rewrite -> H7.
split.
assert (x ⊂ y).
intro.
intro.
rewrite <- H4 in H6.
apply Pair_Meet_Set_Law_1 in H6.
destruct H6.
apply H7.
assert (Ordered_Number x/\Ordered_Number y/\(x ⊂ y)).
split.
apply H.
split.
apply H0.
apply H6.
apply Ordered_Number_Law_3 in H7.
destruct H7.
left.
apply H7.
right.
left.
apply H7.
Qed.

Theorem Ordered_Number_Law_6:forall x:Set,(Ordered_Number x)->~x ∈ x.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct (Law_of_Excluded_Middle (x ∈ x)).
apply H2 in H4.
apply H4.
apply H4.
Qed.

Theorem Ordered_Number_Law_7:forall x a0:Set,a0 ∈ (Prop_Set (fun a=>exists y z:Set,y ∈x/\z ∈ x/\y ∈ z/\a=Ordered_Set y z))<->exists y z:Set,y ∈x/\z ∈ x/\y ∈ z/\a0=Ordered_Set y z.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set x x).
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
rewrite -> H2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H.
apply H0.
Qed.

Theorem Ordered_Number_Law_8:forall x:Set,Ordered_Number x->Narrow_Well_Oredered_Reration (Prop_Set (fun a=>exists y z:Set,y ∈x/\z ∈ x/\y ∈ z/\a=Ordered_Set y z)) x.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.

intro.
intro.
apply Ordered_Number_Law_7 in H4.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
destruct H6.
exists x0.
exists x1.
split.
apply H7.
split.
apply H4.
apply H5.

split.
intro.
intros.
destruct H4.
apply Ordered_Number_Law_7 in H4.
apply Ordered_Number_Law_7 in H5.
apply Ordered_Number_Law_7.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
destruct H5.
destruct H5.
destruct H5.
destruct H10.
destruct H11.
apply Ordered_Set_Law_2 in H12.
destruct H12.
exists x0.
exists z.
split.
rewrite -> H8.
apply H4.
split.
rewrite -> H13.
apply H10.
split.
apply (H0 x0 y z).
split.
rewrite -> H8.
apply H4.
split.
rewrite -> H12.
apply H5.
split.
rewrite -> H13.
apply H10.
split.
rewrite -> H8.
rewrite -> H9.
apply H7.
rewrite -> H12.
rewrite -> H13.
apply H11.
split.
split.

intros.
assert (x0 ∈ x /\ y ∈ x).
apply H4.
destruct H5.
apply H1 in H4.
destruct H4.
left.
apply Ordered_Number_Law_7.
exists x0.
exists y.
split.
apply H5.
split.
apply H6.
split.
apply H4.
split.
right.
destruct H4.
left.
apply H4.
right.
apply Ordered_Number_Law_7.
exists y.
exists x0.
split.
apply H6.
split.
apply H5.
split.
apply H4.
split.
split.

intros.
intro.
apply Ordered_Number_Law_7 in H5.
assert (~x0 ∈ x0).
apply H2.
apply H4.
apply H6.
destruct H5.
destruct H5.
destruct H5.
destruct H7.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite <- H9 in H8.
rewrite <- H10 in H8.
apply H8.

intros.
assert (Y ⊂ x).
destruct H4.
apply H4.
apply H3 in H4.
destruct H4.
destruct H4.
exists x0.
split.
apply H4.
intros.
destruct H7.
apply Ordered_Number_Law_7.
exists x0.
exists x1.
split.
apply H5.
apply H4.
split.
apply H5.
apply H7.
split.
assert (x0 ∈ x/\x1 ∈ x).
split.
apply H5.
apply H4.
apply H5.
apply H7.
apply H1 in H9.
destruct H9.
apply H9.
destruct H9.
destruct H8.
apply H9.
apply H6 in H7.
destruct H7.
apply H9.
split.
Qed.



Definition Ordered_Next(x:Set):=x ∪ (Single_Set x).

Theorem Ordered_Next_Law_1:forall x y:Set,y ∈ (Ordered_Next x)<->(y ∈ x\/y=x).
Proof.
intros.
split.
intro.
apply Pair_Union_Set_Law_1 in H.
destruct H.
left.
apply H.
right.
apply Single_Set_Law_1.
apply H.
intro.
apply Pair_Union_Set_Law_1.
destruct H.
left.
apply H.
right.
apply Single_Set_Law_1.
apply H.
Qed.

Theorem Ordered_Next_Law_2:forall x:Set,Ordered_Number x->Ordered_Number (Ordered_Next x).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
split.

intros.
intro.
intro.
apply Ordered_Next_Law_1.
apply Ordered_Next_Law_1 in H4.
destruct H4.
left.
apply H in H4.
apply H4.
apply H5.
left.
rewrite <- H4.
apply H5.
split.

intros.
destruct H4.
destruct H5.
destruct H6.
destruct H7.
apply Ordered_Next_Law_1 in H4.
apply Ordered_Next_Law_1 in H5.
apply Ordered_Next_Law_1 in H6.
destruct H4.
destruct H5.
destruct H6.
apply (H0 y z w).
split.
apply H4.
split.
apply H5.
split.
apply H6.
split.
apply H7.
apply H8.
rewrite -> H6 in H8.
apply H in H8.
apply H8 in H7.
rewrite -> H6.
apply H7.
destruct H5.
destruct H6.
apply H in H5.
apply H5 in H8.
assert (z ∈ z).
apply H8.
apply H2 in H8.
destruct H8.
apply H6.
rewrite -> H5.
apply H4.
destruct H5.
destruct H6.
rewrite -> H4 in H7.
apply H in H5.
apply H5 in H7.
assert (x ∈ x).
apply H7.
apply H2 in H7.
destruct H7.
apply H9.
rewrite -> H6 in H8.
apply H in H8.
apply H8 in H7.
rewrite -> H6.
apply H7.
destruct H6.
apply H in H6.
apply H6 in H8.
assert (z ∈ x).
apply H8.
apply H2 in H8.
destruct H8.
rewrite <- H5 in H9.
apply H9.
rewrite -> H4 in H7.
rewrite -> H5 in H7.
assert (x ∈ x).
apply H7.
apply H2 in H9.
destruct H9.
apply H7.
split.

intros.
destruct H4.
apply Ordered_Next_Law_1 in H4.
apply Ordered_Next_Law_1 in H5.
destruct H4.
destruct H5.
assert (y ∈ x/\z ∈ x).
split.
apply H4.
apply H5.
apply H1 in H6.
apply H6.
left.
rewrite -> H5.
apply H4.
destruct H5.
right.
right.
rewrite -> H4.
apply H5.
right.
left.
rewrite -> H4.
rewrite -> H5.
split.
split.

intros.
apply Ordered_Next_Law_1 in H4.
destruct H4.
apply H2 in H4.
apply H4.
intro.
rewrite -> H4 in H5.
assert (x ∈ x).
apply H5.
apply H2 in H5.
apply H5.
apply H6.

intros.
destruct H4.
destruct (Law_of_Excluded_Middle (x ∈ y)).
destruct (Law_of_Excluded_Middle (y=(Single_Set x))).
exists x.
split.
rewrite -> H7.
apply Single_Set_Law_1.
split.
intros.
rewrite -> H7 in H8.
apply Single_Set_Law_1 in H8.
rewrite -> H8.
apply Ordered_Number_Law_6.
split.
apply H.
split.
apply H0.
split.
apply H1.
split.
apply H2.
apply H3.
assert (~y=∅/\~y=Single_Set x).
split.
apply H5.
apply H7.
apply Single_Set_Law_3 in H8.
assert ((Complement_Set y (Single_Set x)) ⊂ x/\~(Complement_Set y (Single_Set x))=∅).
split.
intro.
intro.
apply Complement_Set_Law_1 in H9.
destruct H9.
apply H4 in H9.
apply Ordered_Next_Law_1 in H9.
destruct H9.
apply H9.
destruct H10.
apply Single_Set_Law_1.
apply H9.
apply Empty_Set_Law_1.
destruct H8.
destruct H8.
exists x0.
apply Complement_Set_Law_1.
split.
apply H8.
intro.
apply H9.
apply Single_Set_Law_1 in H10.
apply H10.
apply H3 in H9.
destruct H9.
destruct H9.
assert ((Complement_Set y (Single_Set x) ∪ (Single_Set x))=y).
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Union_Set_Law_1 in H11.
destruct H11.
apply Complement_Set_Law_1 in H11.
destruct H11.
apply H11.
apply Single_Set_Law_1 in H11.
rewrite -> H11. 
apply H6.
intro.
apply Pair_Union_Set_Law_1.
destruct (Law_of_Excluded_Middle (z ∈ Single_Set x)).
right.
apply H12.
left.
apply Complement_Set_Law_1.
split.
apply H11.
apply H12.
exists x0.
apply Complement_Set_Law_1 in H9.
destruct H9.
split.
apply H9.
intros.
rewrite <- H11 in H13.
apply Pair_Union_Set_Law_1 in H13.
destruct H13.
apply H10 in H13.
apply H13.
apply Single_Set_Law_1 in H13.
intro.
apply H4 in H9.
apply Ordered_Next_Law_1 in H9.
destruct H9.
assert (Ordered_Number x).
split.
apply H.
split.
apply H0.
split.
apply H1.
split.
apply H2.
apply H3.
assert (Ordered_Number x0).
apply (Ordered_Number_Law_1 x x0).
split.
apply H9.
apply H15.
assert (Ordered_Number w).
apply (Ordered_Number_Law_1 x0 w).
split.
apply H14.
apply H16.
assert (w ∈ x).
apply (Ordered_Number_Law_4 w x0 x).
split.
apply H17.
split.
apply H16.
split.
apply H15.
split.
apply H14.
apply H9.
rewrite -> H13 in H18.
apply Ordered_Number_Law_6 in H18.
apply H18.
apply H15.
assert (Ordered_Number x).
split.
apply H.
split.
apply H0.
split.
apply H1.
split.
apply H2.
apply H3.
apply Ordered_Number_Law_6 in H15.
apply H15.
rewrite -> H13 in H14.
rewrite -> H9 in H14.
apply H14.
assert ((Complement_Set y (Single_Set x)) ⊂ x).
intro.
intro.
apply Complement_Set_Law_1 in H7.
destruct H7.
apply H4 in H7.
apply Ordered_Next_Law_1 in H7.
destruct H7.
apply H7.
destruct H8.
apply Single_Set_Law_1.
apply H7.
assert (y ⊂ (Complement_Set y (Single_Set x))).
intro.
intro.
apply Complement_Set_Law_1.
split.
apply H8.
intro.
apply H6.
apply Single_Set_Law_1 in H9.
rewrite <- H9.
apply H8.
assert (y ⊂ x/\~y=∅).
split.
intro.
intro.
apply H7.
apply H8.
apply H9.
apply H5.
apply H3 in H9.
apply H9.
Qed.



(*自然数*)
Definition Natural_Number(n:Set):=Ordered_Number n/\(forall x:Set,x ∈n->((exists y:Set,Ordered_Next y=x)\/x=∅))/\((exists y:Set,Ordered_Next y=n)\/n=∅).

Definition Natural_Number_Set:=Prop_Set (fun n=>Natural_Number n).

(*無限公理*)
Axiom Axiom_of_Infinity:exists x:Set,∅ ∈ x/\forall y:Set,y ∈ x->(Ordered_Next y) ∈ x.

Theorem Natural_Number_Set_Law_1:forall n:Set,n ∈ Natural_Number_Set<->Natural_Number n.
Proof.
intro.
apply Prop_Set_Law_1.
destruct Axiom_of_Infinity.
exists x.
intros.
destruct H0.
destruct H1.
destruct H.
destruct (Law_of_Excluded_Middle (x0 ∈ x)).
apply H4.
assert ((Complement_Set (Ordered_Next x0) x) ⊂ (Ordered_Next x0)/\~(Complement_Set (Ordered_Next x0) x)=∅).
split.
intro.
intro.
apply Complement_Set_Law_1 in H5.
destruct H5.
apply H5.
apply Empty_Set_Law_1.
exists x0.
apply Complement_Set_Law_1.
split.
apply Ordered_Next_Law_1.
right.
split.
apply H4.
assert (Ordered_Number x0).
apply H0.
apply Ordered_Next_Law_2 in H0.
destruct H0.
clear H0.
destruct H7.
clear H0.
destruct H7.
clear H0.
destruct H7.
clear H0.
apply H7 in H5.
clear H7.
destruct H5.
destruct H0.
apply Complement_Set_Law_1 in H0.
destruct H0.
apply Ordered_Next_Law_1 in H0.
destruct H0.
assert (x1 ∈ x0).
apply H0.
apply H1 in H0.
destruct H0.
destruct H0.
assert (x2 ∈ Complement_Set (Ordered_Next x0) x).
apply Complement_Set_Law_1.
split.
apply Ordered_Next_Law_1.
left.
destruct H6.
apply H6 in H8.
apply H8.
rewrite <- H0.
apply Ordered_Next_Law_1.
right.
split.
rewrite <- H0 in H7.
intro.
apply H7.
apply H3.
apply H9.
apply H5 in H9.
destruct H9.
rewrite <- H0.
apply Ordered_Next_Law_1.
right.
split.
destruct H7.
rewrite -> H0.
apply H.
destruct H2.
destruct H2.
assert (x2 ∈ Complement_Set (Ordered_Next x0) x).
apply Complement_Set_Law_1.
split.
apply Ordered_Next_Law_1.
left.
rewrite <- H2.
apply Ordered_Next_Law_1.
right.
split.
intro.
apply H4.
rewrite <- H2.
apply H3.
apply H8.
apply H5 in H8.
destruct H8.
rewrite -> H0.
rewrite <- H2.
apply Ordered_Next_Law_1.
right.
split.
rewrite -> H2.
apply H.
Qed.

Theorem Natural_Number_Set_Law_2:Ordered_Number Natural_Number_Set.
Proof.
split.
intros.
apply Natural_Number_Set_Law_1 in H.
intro.
intro.
apply Natural_Number_Set_Law_1.
split.
destruct H.
apply (Ordered_Number_Law_1 y z).
split.
apply H0.
apply H.
split.
destruct H.
destruct H1.
intros.
apply H1.
destruct H.
apply H in H0.
apply H0.
apply H3.
destruct H.
destruct H1.
apply H1 in H0.
apply H0.
split.

intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Natural_Number_Set_Law_1 in H.
apply Natural_Number_Set_Law_1 in H0.
apply Natural_Number_Set_Law_1 in H1.
apply (Ordered_Number_Law_4 y z w).
split.
destruct H.
apply H.
split.
destruct H0.
apply H0.
split.
destruct H1.
apply H1.
split.
apply H2.
apply H3.
split.

intros.
destruct H.
apply Natural_Number_Set_Law_1 in H.
apply Natural_Number_Set_Law_1 in H0.
apply (Ordered_Number_Law_5 y z).
split.
destruct H.
apply H.
destruct H0.
apply H0.
split.

intros.
apply Ordered_Number_Law_6.
apply Natural_Number_Set_Law_1 in H.
destruct H.
apply H.

intros.
destruct H.
apply Empty_Set_Law_1 in H0.
destruct H0.
destruct (Law_of_Excluded_Middle (x ∩ y=∅)).
exists x.
split.
apply H0.
intros.
intro.
apply (Definition_of_Empty_Set w).
rewrite <- H1.
apply Pair_Meet_Set_Law_1.
split.
apply H3.
apply H2.
assert (x ∩ y ⊂ x/\~x ∩ y=∅).
split.
intro.
intro.
apply Pair_Meet_Set_Law_1 in H2.
destruct H2.
apply H2.
apply H1.
apply H in H0.
apply Natural_Number_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H4.
destruct H5.
destruct H6.
apply H7 in H2.
destruct H2.
destruct H2.
exists x0.
apply Pair_Meet_Set_Law_1 in H2.
destruct H2.
split.
apply H9.
intros.
destruct (Law_of_Excluded_Middle (w ∈ x)).
apply H8.
apply Pair_Meet_Set_Law_1.
split.
apply H11.
apply H10.
intro.
apply H0 in H2.
apply H11.
apply H2.
apply H12.
Qed.