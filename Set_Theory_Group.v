Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.



(*二項演算*)
Definition Binary_Operation(f G:Set):=Map f (Double_Direct_Product_Set G G) G.

Definition Operation(f x1 x2:Set):=Culculateion_Map f (Ordered_Set x1 x2).



(*群とモノイド*)
Definition Associative_Law(f G:Set):=(forall x1 x2 x3:Set,x1 ∈ G/\x2 ∈ G/\x3 ∈ G->(Operation f x1 (Operation f x2 x3))=(Operation f (Operation f x1 x2) x3)).

Definition Exists_of_Identify_Element(f G:Set):=(exists e:Set,e ∈ G/\forall x:Set,x ∈ G->(Operation f x e=x/\Operation f e x=x)).

Definition Identify_Element(f G:Set):=Well_Defined (fun e=>e ∈ G/\forall x:Set,x ∈ G->(Operation f x e=x/\Operation f e x=x)).

Definition Exists_of_Reverse_Element(f G:Set):=Exists_of_Identify_Element f G/\(forall x:Set,x ∈ G->exists x':Set,x' ∈ G/\(Operation f x x')=Identify_Element f G/\(Operation f x' x)=Identify_Element f G).

Definition Reverse_Element(f G x:Set):=Well_Defined (fun x'=>x' ∈ G/\(Operation f x x')=(Identify_Element f G)/\(Operation f x' x)=(Identify_Element f G)).



Definition Monoid(f G:Set):=Binary_Operation f G/\Associative_Law f G/\Exists_of_Identify_Element f G.

Theorem Monoid_Law_1:forall f G x1 x2:Set,Monoid f G/\x1 ∈ G/\x2 ∈ G->(Operation f x1 x2) ∈ G.
Proof.
intros.
destruct H.
destruct H.
unfold Operation.
apply (Map_Law_2 f (Double_Direct_Product_Set G G) G (Ordered_Set x1 x2)).
split.
apply H.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
apply H0.
Qed.

Theorem Monoid_Law_2:forall f G x1 x2 x3:Set,Monoid f G/\x1 ∈ G/\x2 ∈ G/\x3 ∈ G->(Operation f x1 (Operation f x2 x3))=(Operation f (Operation f x1 x2) x3).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
apply H1.
apply H0.
Qed.

Theorem Monoid_Law_3:forall f G:Set,Monoid f G->exists! e:Set,e ∈ G/\forall x:Set,x ∈ G->(Operation f x e=x/\Operation f e x=x).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
exists x.
split.
split.
apply H1.
intros.
split.
apply H1.
apply H2.
apply H1.
apply H2.
intros.
destruct H1.
apply H2 in H1.
destruct H2.
apply H3 in H2.
destruct H2.
destruct H1.
rewrite <- H1.
apply H5.
Qed.

Theorem Monoid_Law_4:forall f G:Set,Monoid f G->((Identify_Element f G) ∈ G/\forall x:Set,x ∈ G->(Operation f x (Identify_Element f G)=x/\Operation f (Identify_Element f G) x=x)).
Proof.
intros.
apply (Well_Defined_1 (fun e=>e ∈ G/\forall x:Set,x ∈ G->(Operation f x e=x/\Operation f e x=x))).
apply Monoid_Law_3.
apply H.
Qed.

Theorem Monoid_Law_5:forall f G:Set,Monoid f G->(Identify_Element f G) ∈ G.
Proof.
intros.
apply Monoid_Law_4 in H.
destruct H.
apply H.
Qed.

Theorem Monoid_Law_6:forall f G x:Set,Monoid f G/\x ∈ G->Operation f x (Identify_Element f G)=x.
Proof.
intros.
destruct H.
apply Monoid_Law_4 in H.
destruct H.
apply H1 in H0.
destruct H0.
apply H0.
Qed.

Theorem Monoid_Law_7:forall f G x:Set,Monoid f G/\x ∈ G->Operation f (Identify_Element f G) x=x.
Proof.
intros.
destruct H.
apply Monoid_Law_4 in H.
destruct H.
apply H1 in H0.
destruct H0.
apply H2.
Qed.

Theorem Monoid_Law_8:forall f G x:Set,Monoid f G/\x ∈ G/\(forall y:Set,y ∈ G->Operation f y x=y)->x=Identify_Element f G.
Proof.
intros.
destruct H.
destruct H0.
rewrite <- (H1 (Identify_Element f G)).
rewrite -> (Monoid_Law_7 f G).
split.
split.
apply H.
apply H0.
apply Monoid_Law_5.
apply H.
Qed.

Theorem Monoid_Law_9:forall f G x:Set,Monoid f G/\x ∈ G/\(forall y:Set,y ∈ G->Operation f x y=y)->x=Identify_Element f G.
Proof.
intros.
destruct H.
destruct H0.
rewrite <- (H1 (Identify_Element f G)).
rewrite -> (Monoid_Law_6 f G).
split.
split.
apply H.
apply H0.
apply Monoid_Law_5.
apply H.
Qed.



Definition Group(f G:Set):=Binary_Operation f G/\Associative_Law f G/\Exists_of_Reverse_Element f G.

Theorem Group_Law_1:forall f G:Set,Group f G->Monoid f G.
Proof.
intros.
split.
apply H.
split.
apply H.
destruct H.
destruct H0.
destruct H1.
apply H1.
Qed.

Theorem Group_Law_2:forall f G x1 x2:Set,Group f G/\x1 ∈ G/\x2 ∈ G->(Operation f x1 x2) ∈ G.
Proof.
intros.
apply (Monoid_Law_1 f G x1 x2).
destruct H.
split.
apply Group_Law_1.
apply H.
apply H0.
Qed.

Theorem Group_Law_3:forall f G x1 x2 x3:Set,Group f G/\x1 ∈ G/\x2 ∈ G/\x3 ∈ G->(Operation f x1 (Operation f x2 x3))=(Operation f (Operation f x1 x2) x3).
Proof.
intros.
apply (Monoid_Law_2 f G x1 x2 x3).
destruct H.
split.
apply Group_Law_1.
apply H.
apply H0.
Qed.

Theorem Group_Law_4:forall f G:Set,Group f G->(Identify_Element f G) ∈ G.
Proof.
intros.
apply Monoid_Law_5.
apply Group_Law_1.
apply H.
Qed.

Theorem Group_Law_5:forall f G x:Set,Group f G/\x ∈ G->Operation f x (Identify_Element f G)=x.
Proof.
intros.
apply Monoid_Law_6.
destruct H.
split.
apply Group_Law_1.
apply H.
apply H0.
Qed.

Theorem Group_Law_6:forall f G x:Set,Group f G/\x ∈ G->Operation f (Identify_Element f G) x=x.
Proof.
intros.
apply Monoid_Law_7.
destruct H.
split.
apply Group_Law_1.
apply H.
apply H0.
Qed.

Theorem Group_Law_7:forall f G x:Set,Group f G/\x ∈ G->exists! x':Set,x' ∈ G/\(Operation f x x'=(Identify_Element f G)/\Operation f x' x=(Identify_Element f G)).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
assert (x ∈ G).
apply H0.
apply H3 in H0.
destruct H0.
exists x0.
split.
apply H0.

intros.
assert (Operation f x0 (Operation f x x0)=Operation f x0 (Operation f x x')).
destruct H0.
destruct H6.
destruct H5.
destruct H8.
rewrite -> H6.
rewrite -> H8.
split.
assert (Operation f x0 (Operation f x x0)=Operation f (Operation f x0 x) x0).
destruct H0.
apply H1.
split.
apply H0.
split.
apply H4.
apply H0.
assert (Operation f x0 (Operation f x x')=Operation f (Operation f x0 x) x').
destruct H0.
destruct H5.
apply H1.
split.
apply H0.
split.
apply H4.
apply H5.
rewrite -> H7 in H6.
rewrite -> H8 in H6.
clear H7.
clear H8.
destruct H0.
destruct H7.
rewrite -> H8 in H6.
rewrite -> (Group_Law_6 f G x0) in H6.
rewrite -> (Group_Law_6 f G x') in H6.
apply H6.
split.
split.
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
destruct H5.
apply H5.
split.
split.
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
apply H0.
Qed.

Theorem Group_Law_8:forall f G x:Set,Group f G/\x ∈ G->(Reverse_Element f G x) ∈ G/\(Operation f x (Reverse_Element f G x))=(Identify_Element f G)/\(Operation f (Reverse_Element f G x) x)=(Identify_Element f G).
Proof.
intros.
apply (Well_Defined_1 (fun x'=>x' ∈ G/\(Operation f x x')=(Identify_Element f G)/\(Operation f x' x)=(Identify_Element f G))).
apply Group_Law_7.
apply H.
Qed.

Theorem Group_Law_9:forall f G x:Set,Group f G/\x ∈ G->(Reverse_Element f G x) ∈ G.
Proof.
intros.
apply Group_Law_8 in H.
destruct H.
apply H.
Qed.

Theorem Group_Law_10:forall f G x:Set,Group f G/\x ∈ G->(Operation f x (Reverse_Element f G x))=(Identify_Element f G).
Proof.
intros.
apply Group_Law_8 in H.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Group_Law_11:forall f G x:Set,Group f G/\x ∈ G->(Operation f (Reverse_Element f G x) x)=(Identify_Element f G).
Proof.
intros.
apply Group_Law_8 in H.
destruct H.
destruct H0.
apply H1.
Qed.

Theorem Group_Law_12:forall f G x1 x2 x3:Set,Group f G/\x1 ∈ G/\x2 ∈ G/\x3 ∈ G/\Operation f x1 x2=Operation f x1 x3->x2=x3.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
assert (Operation f (Reverse_Element f G x1) (Operation f x1 x2)=Operation f (Reverse_Element f G x1) (Operation f x1 x3)).
rewrite -> H3.
split.
rewrite -> (Group_Law_3 f G (Reverse_Element f G x1) x1 x2) in H4.
rewrite -> (Group_Law_3 f G (Reverse_Element f G x1) x1 x3) in H4.
rewrite -> (Group_Law_11 f G x1) in H4.
rewrite -> (Group_Law_6 f G x2) in H4.
rewrite -> (Group_Law_6 f G x3) in H4.
apply H4.
split.
apply H.
apply H2.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H0.
apply H2.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H0.
apply H1.
Qed.

Theorem Group_Law_13:forall f G x1 x2 x3:Set,Group f G/\x1 ∈ G/\x2 ∈ G/\x3 ∈ G/\Operation f x2 x1=Operation f x3 x1->x2=x3.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
assert (Operation f (Operation f x2 x1) (Reverse_Element f G x1)=Operation f (Operation f x3 x1) (Reverse_Element f G x1)).
rewrite -> H3.
split.
rewrite <- (Group_Law_3 f G x2 x1 (Reverse_Element f G x1)) in H4.
rewrite <- (Group_Law_3 f G x3 x1 (Reverse_Element f G x1)) in H4.
rewrite -> (Group_Law_10 f G x1) in H4.
rewrite -> (Group_Law_5 f G x2) in H4.
rewrite -> (Group_Law_5 f G x3) in H4.
apply H4.
split.
apply H.
apply H2.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply H2.
split.
apply H0.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H.
split.
apply H1.
split.
apply H0.
apply Group_Law_9.
split.
apply H.
apply H0.
Qed.

Theorem Group_Law_14:forall f G x:Set,Group f G/\x ∈ G->x=(Reverse_Element f G (Reverse_Element f G x)).
Proof.
intros.
destruct H.
assert (Operation f x (Reverse_Element f G x)=Operation f (Reverse_Element f G (Reverse_Element f G x)) (Reverse_Element f G x)).
rewrite -> Group_Law_10.
rewrite -> Group_Law_11.
split.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H.
apply H0.
assert (Operation f (Operation f x (Reverse_Element f G x)) x=Operation f (Operation f (Reverse_Element f G (Reverse_Element f G x)) (Reverse_Element f G x)) x).
rewrite -> H1.
split.
assert (Group f G).
apply H.
destruct H3.
destruct H4.
rewrite -> Group_Law_10 in H2.
rewrite -> Group_Law_6 in H2.
rewrite <- (H4 (Reverse_Element f G (Reverse_Element f G x)) (Reverse_Element f G x) x) in H2.
rewrite -> Group_Law_11 in H2.
rewrite -> Group_Law_5 in H2.
apply H2.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H.
apply H0.
split.
apply Group_Law_9.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply Group_Law_9.
split.
apply H.
apply H0.
apply H0.
split.
apply H.
apply H0.
split.
apply H.
apply H0.
Qed.

Theorem Group_Law_15:forall f G x1 x2:Set,Group f G/\x1 ∈ G/\x2 ∈ G->Reverse_Element f G (Operation f x1 x2)=Operation f (Reverse_Element f G x2) (Reverse_Element f G x1).
Proof.
intros.
destruct H.
destruct H0.
apply (Group_Law_13 f G (Operation f x1 x2) (Reverse_Element f G (Operation f x1 x2)) (Operation f (Reverse_Element f G x2) (Reverse_Element f G x1))).
split.
apply H.
split.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
split.
apply Group_Law_9.
split.
apply H.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
split.
apply Group_Law_2.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H1.
apply Group_Law_9.
split.
apply H.
apply H0.
rewrite -> (Group_Law_11 f G (Operation f x1 x2)).
rewrite -> (Group_Law_3 f G (Operation f (Reverse_Element f G x2) (Reverse_Element f G x1)) x1 x2).
rewrite <- (Group_Law_3 f G (Reverse_Element f G x2) (Reverse_Element f G x1) x1).
rewrite -> (Group_Law_11 f G x1).
rewrite -> (Group_Law_5 f G (Reverse_Element f G x2)).
symmetry.
apply (Group_Law_11 f G x2).
split.
apply H.
apply H1.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H1.
split.
apply Group_Law_9.
split.
apply H.
apply H0.
apply H0.
split.
apply H.
split.
apply Group_Law_2.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H1.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H0.
apply H1.
split.
apply H.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Group_Law_16:forall f G:Set,Group f G->Reverse_Element f G ((Identify_Element f G))=(Identify_Element f G).
Proof.
intros.
apply (Group_Law_12 f G (Identify_Element f G) (Reverse_Element f G (Identify_Element f G)) (Identify_Element f G)).
split.
apply H.
split.
apply Group_Law_4.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply Group_Law_4.
apply H.
split.
apply Group_Law_4.
apply H.
rewrite -> (Group_Law_10 f G (Identify_Element f G)).
rewrite -> (Group_Law_5 f G (Identify_Element f G)).
split.
split.
apply H.
apply Group_Law_4.
apply H.
split.
apply H.
apply Group_Law_4.
apply H.
Qed.

Theorem Group_Law_17:forall f G x:Set,Group f G/\x ∈ G/\(forall y:Set,y ∈ G->Operation f y x=y)->x=Identify_Element f G.
Proof.
intros.
destruct H.
destruct H0.
apply (Monoid_Law_8 f G x).
split.
apply Group_Law_1.
apply H.
split.
apply H0.
intros.
apply H1.
apply H2.
Qed.

Theorem Group_Law_18:forall f G x:Set,Group f G/\x ∈ G/\(forall y:Set,y ∈ G->Operation f x y=y)->x=Identify_Element f G.
Proof.
intros.
destruct H.
destruct H0.
apply (Monoid_Law_9 f G x).
split.
apply Group_Law_1.
apply H.
split.
apply H0.
apply H1.
Qed.

Theorem Group_Law_19:forall f G x y:Set,Group f G/\x ∈ G/\y ∈ G/\Operation f x y=Identify_Element f G->y=Reverse_Element f G x.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
rewrite <- (Group_Law_5 f G (Reverse_Element f G x)).
rewrite <- H2.
rewrite -> (Group_Law_3 f G (Reverse_Element f G x) x y).
rewrite -> (Group_Law_11 f G x).
rewrite -> (Group_Law_6 f G y).
split.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H0.
apply H1.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
Qed.

Theorem Group_Law_20:forall f G x y:Set,Group f G/\x ∈ G/\y ∈ G/\Operation f y x=Identify_Element f G->y=Reverse_Element f G x.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
rewrite <- (Group_Law_6 f G (Reverse_Element f G x)).
rewrite <- H2.
rewrite <- (Group_Law_3 f G y x (Reverse_Element f G x)).
rewrite -> (Group_Law_10 f G x).
rewrite -> (Group_Law_5 f G y).
split.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
split.
apply H.
split.
apply H1.
split.
apply H0.
apply Group_Law_9.
split.
apply H.
apply H0.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
Qed.



Definition Restriction_Binary_Operation(f G0:Set):=Restriction_Map f (Double_Direct_Product_Set G0 G0).

Theorem Restriction_Binary_Operation_Law_1:forall f G G0:Set,Binary_Operation f G/\G0 ⊂ G/\(forall x1 x2:Set,x1 ∈ G0/\x2 ∈ G0->(Operation f x1 x2) ∈ G0)->Binary_Operation (Restriction_Binary_Operation f G0) G0.
Proof.
intros.
destruct H.
destruct H0.
unfold Binary_Operation in H.
unfold Binary_Operation.
apply (Map_Law_5 (Restriction_Map f (Double_Direct_Product_Set G0 G0)) (Double_Direct_Product_Set G0 G0) G G0).
split.
apply (Restriction_Map_Law_2 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G).
split.
apply H.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
apply H2.
split.
apply H0.
apply H3.
apply H0.
apply H4.
split.
apply H0.
intros.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G x).
apply Double_Direct_Product_Set_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
rewrite <- H2.
unfold Operation in H1.
apply H1.
apply H3.
split.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
apply H3.
split.
apply H0.
apply H4.
apply H0.
apply H5.
apply H2.
Qed.

Theorem Restriction_Binary_Operation_Law_2:forall f G G0 x1 x2:Set,Binary_Operation f G/\G0 ⊂ G/\x1 ∈ G0/\x2 ∈ G0->Operation (Restriction_Binary_Operation f G0) x1 x2=Operation f x1 x2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
unfold Operation.
apply (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x1 x2)).
split.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H3.
destruct H3.
destruct H3.
destruct H3.
destruct H4.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
apply H3.
split.
apply H0.
apply H4.
apply H0.
apply H5.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H1.
apply H2.
Qed.



Definition Sub_Group(f G f0 G0:Set):=Group f G/\Group f0 G0/\G0 ⊂ G/\f0=Restriction_Binary_Operation f G0.

Theorem Sub_Group_Law_1:forall f G f0 G0 x1 x2:Set,Sub_Group f G f0 G0/\x1 ∈ G0/\x2 ∈ G0->Operation f0 x1 x2=Operation f x1 x2.
Proof.
intros.
destruct H.
destruct H0.
unfold Operation.
destruct H.
destruct H2.
destruct H3.
rewrite -> H4.
apply (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x1 x2)).
split.
destruct H.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1.
apply Double_Direct_Product_Set_Law_1 in H5.
destruct H5.
destruct H5.
exists x.
exists x0.
destruct H5.
destruct H6.
split.
apply H5.
split.
apply H3.
apply H6.
apply H3.
apply H7.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H0.
apply H1.
Qed.

Theorem Sub_Group_Law_2:forall f G f0 G0:Set,Sub_Group f G f0 G0->Identify_Element f G=Identify_Element f0 G0.
Proof.
intros.
assert (Sub_Group f G f0 G0).
apply H.
destruct H0.
destruct H1.
destruct H2.

assert (Identify_Element f G=Operation f (Identify_Element f0 G0) (Reverse_Element f G (Identify_Element f0 G0))).
rewrite -> (Group_Law_10 f G (Identify_Element f0 G0)).
split.
split.
apply H0.
apply H2.
apply Group_Law_4.
apply H1.

assert (Identify_Element f0 G0=Operation f (Operation f (Identify_Element f0 G0) (Identify_Element f0 G0)) (Reverse_Element f G (Identify_Element f0 G0))).
assert (Group f G/\(Identify_Element f0 G0) ∈ G/\(Identify_Element f0 G0) ∈ G/\(Reverse_Element f G (Identify_Element f0 G0)) ∈ G).
split.
apply H0.
split.
apply H2.
apply Group_Law_4.
apply H1.
split.
apply H2.
apply Group_Law_4.
apply H1.
apply Group_Law_9.
split.
apply H0.
apply H2.
apply Group_Law_4.
apply H1.
apply (Group_Law_3 f G (Identify_Element f0 G0) (Identify_Element f0 G0) (Reverse_Element f G (Identify_Element f0 G0))) in H5.
rewrite <- H5.
clear H5.
rewrite -> (Group_Law_10 f G (Identify_Element f0 G0)).
rewrite -> (Group_Law_5 f G (Identify_Element f0 G0)).
split.
split.
apply H0.
apply H2.
apply Group_Law_4.
apply H1.
split.
apply H0.
apply H2.
apply Group_Law_4.
apply H1.

rewrite -> H5.
clear H5.
rewrite -> H4.
clear H4.
rewrite <- (Sub_Group_Law_1 f G f0 G0 (Identify_Element f0 G0) (Identify_Element f0 G0)).
rewrite -> (Group_Law_5 f0 G0 (Identify_Element f0 G0)).
split.
split.
apply H1.
apply Group_Law_4.
apply H1.
split.
apply H.
split.
apply Group_Law_4.
apply H1.
apply Group_Law_4.
apply H1.
Qed.

Theorem Sub_Group_Law_3:forall f G f0 G0 x:Set,Sub_Group f G f0 G0/\x ∈ G0->Reverse_Element f G x=Reverse_Element f0 G0 x.
Proof.
intros.
assert (Sub_Group f G f0 G0).
apply H.
destruct H0.
destruct H1.
destruct H2.
destruct H.
apply (Group_Law_12 f G x (Reverse_Element f G x) (Reverse_Element f0 G0 x)).
split.
apply H0.
split.
apply H2.
apply H4.
split.
apply Group_Law_9.
split.
apply H0.
apply H2.
apply H4.
split.
apply H2.
apply Group_Law_9.
split.
apply H1.
apply H4.
rewrite -> (Group_Law_10 f G x).
rewrite <- (Sub_Group_Law_1 f G f0 G0 x (Reverse_Element f0 G0 x)).
rewrite -> (Group_Law_10 f0 G0 x).
apply Sub_Group_Law_2.
apply H.
split.
apply H1.
apply H4.
split.
apply H.
split.
apply H4.
apply Group_Law_9.
split.
apply H1.
apply H4.
split.
apply H0.
apply H2.
apply H4.
Qed.

Theorem Sub_Group_Law_4:forall f G G0:Set,Sub_Group f G (Restriction_Binary_Operation f G0) G0<->(Group f G/\G0 ⊂ G/\(forall x1 x2:Set,x1 ∈ G0/\x2 ∈ G0->(Operation f x1 (Reverse_Element f G x2)) ∈ G0)/\~G0=∅).
Proof.
intros.
split.

intros.
assert (Sub_Group f G (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0).
apply H.
destruct H0.
destruct H1.
destruct H2.
clear H3.
split.
apply H0.
split.
apply H2.
split.
intros.
destruct H3.
rewrite <- (Sub_Group_Law_1 f G (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0 x1 (Reverse_Element f G x2)).
apply (Group_Law_2 (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0 x1 (Reverse_Element f G x2)).
split.
apply H1.
split.
apply H3.
rewrite -> (Sub_Group_Law_3 f G (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0 x2).
apply Group_Law_9.
split.
apply H1.
apply H4.
split.
apply H.
apply H4.
split.
apply H.
split.
apply H3.
rewrite -> (Sub_Group_Law_3 f G (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0 x2).
apply Group_Law_9.
split.
apply H1.
apply H4.
split.
apply H.
apply H4.
apply Empty_Set_Law_1.
exists (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0).
apply Group_Law_4.
apply H1.

intro.
destruct H.
destruct H0.
destruct H1.
assert (forall x1 x2:Set,x1 ∈ G0/\x2 ∈ G0->(Operation f x1 x2) ∈ G0).
intros.
destruct H3.
rewrite -> (Group_Law_14 f G x2).
apply H1.
split.
apply H3.
rewrite <- (Group_Law_6 f G (Reverse_Element f G x2)).
apply (H1 (Identify_Element f G) x2).
split.
rewrite <- (Group_Law_10 f G x1).
apply H1.
split.
apply H3.
apply H3.
split.
apply H.
apply H0.
apply H3.
apply H4.
split.
apply H.
apply Group_Law_8.
split.
apply H.
apply H0.
apply H4.
split.
apply H.
apply H0.
apply H4.

assert (forall x:Set,x ∈ G0->(Reverse_Element f G x) ∈ G0).
intros.
rewrite <- (Group_Law_6 f G (Reverse_Element f G x)).
apply H1.
split.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H4.
apply H4.
split.
apply H.
apply H0.
apply H4.
apply H4.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H0.
apply H4.

split.
apply H.
split.

assert (Monoid (Restriction_Binary_Operation f G0) G0).
split.
split.
intros.
apply Restriction_Map_Law_1 in H5.
destruct H5.
destruct H6.
destruct H6.
exists x.
exists (Culculateion_Map f x).
split.
apply H6.
split.
apply Double_Direct_Product_Set_Law_1 in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H8.
rewrite <- H6.
apply H3.
split.
apply H8.
apply H9.
apply H7.
intros.
assert (x ∈ Double_Direct_Product_Set G G).
apply Double_Direct_Product_Set_Law_1 in H5.
apply Double_Direct_Product_Set_Law_1.
destruct H5.
destruct H5.
destruct H5.
destruct H6.
exists x0.
exists x1.
split.
apply H5.
split.
apply H0.
apply H6.
apply H0.
apply H7.
assert (Group f G).
apply H.
destruct H7.
destruct H7.
apply H9 in H6.
destruct H6.
destruct H6.
destruct H6.
exists x0.
split.
split.
apply Restriction_Map_Law_1.
split.
apply H6.
exists x.
split.
apply H5.
rewrite <- (Map_Law_3 f (Double_Direct_Product_Set G G) G x x0).
split.
split.
destruct H.
apply H.
split.
apply Double_Direct_Product_Set_Law_1 in H5.
apply Double_Direct_Product_Set_Law_1.
destruct H5.
destruct H5.
destruct H5.
destruct H12.
exists x1.
exists x2.
split.
apply H5.
split.
apply H0.
apply H12.
apply H0.
apply H13.
split.
apply H11.
apply H6.
rewrite -> (Map_Law_3 f (Double_Direct_Product_Set G G) G x x0).
apply Double_Direct_Product_Set_Law_1 in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H12.
rewrite <- H5.
apply H3.
split.
apply H12.
apply H13.
split.
split.
apply H7.
apply H9.
split.
apply Double_Direct_Product_Set_Law_1 in H5.
apply Double_Direct_Product_Set_Law_1.
destruct H5.
destruct H5.
destruct H5.
destruct H12.
exists x1.
exists x2.
split.
apply H5.
split.
apply H0.
apply H12.
apply H0.
apply H13.
split.
apply H11.
apply H6.
intros.
apply H10.
destruct H12.
apply Restriction_Map_Law_1 in H12.
destruct H12.
split.
apply H12.
apply H0.
apply H13.

split.
intro.
intros.
destruct H5.
destruct H6.
assert (Map f (Double_Direct_Product_Set G G) G).
destruct H.
apply H.
assert (Double_Direct_Product_Set G0 G0 ⊂ Double_Direct_Product_Set G G).
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H9.
apply Double_Direct_Product_Set_Law_1.
destruct H9.
destruct H9.
destruct H9.
destruct H10.
exists x.
exists x0.
split.
apply H9.
split.
apply H0.
apply H10.
apply H0.
apply H11.
unfold Restriction_Binary_Operation.
unfold Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x2 x3)).
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x1 x2)).
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x1 (Culculateion_Map f (Ordered_Set x2 x3)))).
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set (Culculateion_Map f (Ordered_Set x1 x2)) x3)).
destruct H.
destruct H10.
apply H10.
split.
apply H0.
apply H5.
split.
apply H0.
apply H6.
apply H0.
apply H7.
split.
apply H8.
split.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map f (Ordered_Set x1 x2)).
exists x3.
split.
split.
split.
apply H3.
split.
apply H5.
apply H6.
apply H7.
split.
apply H8.
split.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists (Culculateion_Map f (Ordered_Set x2 x3)).
split.
split.
split.
apply H5.
apply H3.
split.
apply H6.
apply H7.
split.
apply H8.
split.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H5.
apply H6.
split.
apply H8.
split.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H6.
apply H7.

exists (Identify_Element f G).
split.
apply Empty_Set_Law_1 in H2.
destruct H2.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H2.
apply H2.
split.
apply H.
apply H0.
apply H2.
intros.
assert (Map f (Double_Direct_Product_Set G G) G).
destruct H.
apply H.
assert (Double_Direct_Product_Set G0 G0 ⊂ Double_Direct_Product_Set G G).
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H7.
apply Double_Direct_Product_Set_Law_1.
destruct H7.
destruct H7.
destruct H7.
destruct H8.
exists x0.
exists x1.
split.
apply H7.
split.
apply H0.
apply H8.
apply H0.
apply H9.
split.
unfold Restriction_Binary_Operation.
unfold Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x (Identify_Element f G))).
apply (Group_Law_5 f G x).
split.
apply H.
apply H0.
apply H5.
split.
apply H6.
split.
apply H7.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists (Identify_Element f G).
split.
split.
split.
apply H5.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H5.
apply H5.
split.
apply H.
apply H0.
apply H5.
unfold Restriction_Binary_Operation.
unfold Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set (Identify_Element f G) x)).
apply (Group_Law_6 f G x).
split.
apply H.
apply H0.
apply H5.
split.
apply H6.
split.
apply H7.
apply Double_Direct_Product_Set_Law_1.
exists (Identify_Element f G).
exists x.
split.
split.
split.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H5.
apply H5.
split.
apply H.
apply H0.
apply H5.
apply H5.
intros.

split.
destruct H5.
apply H5.
split.
destruct H5.
destruct H6.
apply H6.
split.
destruct H5.
destruct H6.
apply H7.
intros.
exists (Reverse_Element f G x).
split.
apply H4.
apply H6.
assert (Operation (Restriction_Map f (Double_Direct_Product_Set G0 G0)) (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0) (Identify_Element f G)=Operation f (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0) (Identify_Element f G)).
unfold Restriction_Binary_Operation.
unfold Operation.
apply (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0) (Identify_Element f G))).
split.
destruct H.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H7.
apply Double_Direct_Product_Set_Law_1.
destruct H7.
destruct H7.
destruct H7.
destruct H8.
exists x0.
exists x1.
split.
apply H7.
split.
apply H0.
apply H8.
apply H0.
apply H9.
apply Double_Direct_Product_Set_Law_1.
exists (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0).
exists (Identify_Element f G).
split.
split.
split.
apply Monoid_Law_4.
apply H5.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H6.
apply H6.
split.
apply H.
apply H0.
apply H6.
unfold Restriction_Binary_Operation.
unfold Operation.
rewrite -> (Monoid_Law_7 (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0 (Identify_Element f G)) in H7.
rewrite -> (Group_Law_5 f G (Identify_Element (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0)) in H7.
rewrite <- H7.
split.
unfold Restriction_Binary_Operation.
unfold Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set x (Reverse_Element f G x))).
apply Group_Law_10.
split.
apply H.
apply H0.
apply H6.
split.
destruct H.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H8.
apply Double_Direct_Product_Set_Law_1.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
exists x0.
exists x1.
split.
apply H8.
split.
apply H0.
apply H9.
apply H0.
apply H10.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists (Reverse_Element f G x).
split.
split.
split.
apply H6.
apply H4.
apply H6.
unfold Operation.
rewrite -> (Restriction_Map_Law_3 f (Double_Direct_Product_Set G G) (Double_Direct_Product_Set G0 G0) G (Ordered_Set (Reverse_Element f G x) x)).
apply Group_Law_11.
split.
apply H.
apply H0.
apply H6.
split.
destruct H.
apply H.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1 in H8.
apply Double_Direct_Product_Set_Law_1.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
exists x0.
exists x1.
split.
apply H8.
split.
apply H0.
apply H9.
apply H0.
apply H10.
apply Double_Direct_Product_Set_Law_1.
exists (Reverse_Element f G x).
exists x.
split.
split.
split.
apply H4.
apply H6.
apply H6.
split.
apply H.
apply H0.
apply (Monoid_Law_4 (Restriction_Map f (Double_Direct_Product_Set G0 G0)) G0).
apply H5.
split.
apply H5.
rewrite <- (Group_Law_10 f G x).
apply H1.
split.
apply H6.
apply H6.
split.
apply H.
apply H0.
apply H6.

split.
apply H0.

split.
Qed.



(*剰余群*)
Definition Left_Equivalenc_Relation(f G G0:Set):=Prop_Set (fun a0=>exists x y:Set,a0=Ordered_Set x y/\x ∈ G/\y ∈ G/\(Operation f (Reverse_Element f G x) y) ∈ G0).

Definition Left_Quotient_Group(f G G0:Set):=Quotient_Set (Left_Equivalenc_Relation f G G0) G.

Theorem Left_Equivalenc_Relation_Law_1:forall f G G0 a:Set,a ∈ (Left_Equivalenc_Relation f G G0)<->(exists x y:Set,a=Ordered_Set x y/\x ∈ G/\y ∈ G/\(Operation f (Reverse_Element f G x) y) ∈ G0).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set G)).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
destruct H.
destruct H.
destruct H.
destruct H2.
destruct H3.
rewrite -> H in H0.
apply Ordered_Set_Law_1 in H0.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H1.
rewrite -> H1.
apply H2.
rewrite -> H1.
apply H3.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
apply H3.
Qed.

Theorem Left_Equivalenc_Relation_Law_2:forall f G f0 G0:Set,Sub_Group f G f0 G0->Equivalenc_Relation (Left_Equivalenc_Relation f G G0) G.
Proof.
intros.
split.
intro.
intro.
apply Left_Equivalenc_Relation_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
destruct H2.
exists x.
exists x0.
split.
apply H0.
split.
apply H1.
apply H2.

split.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intro.
intro.
apply Left_Equivalenc_Relation_Law_1.
exists x.
exists x.
split.
split.
split.
apply H4.
split.
apply H4.
rewrite -> (Group_Law_11 f G x).
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply (Group_Law_4 f0 G0).
apply H1.
apply H0.
split.
apply H.
apply H4.
split.

intro.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intro.
intro.
apply Left_Equivalenc_Relation_Law_1 in H4.
apply Left_Equivalenc_Relation_Law_1.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite <- H4 in H5.
rewrite <- H8 in H6.
rewrite <- H4 in H7.
rewrite <- H8 in H7.
exists y.
exists x.
split.
split.
split.
apply H6.
split.
apply H5.
rewrite -> (Group_Law_14 f G x).
rewrite <- (Group_Law_15 f G (Reverse_Element f G x) y).
rewrite -> (Sub_Group_Law_3 f G f0 G0 (Operation f (Reverse_Element f G x) y)).
apply (Group_Law_9 f0 G0 (Operation f (Reverse_Element f G x) y)).
split.
apply H1.
apply H7.
split.
apply H0.
apply H7.
split.
apply H.
split.
apply (Group_Law_9 f G x).
split.
apply H.
apply H5.
apply H6.
split.
apply H.
apply H5.

intro.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intros.
destruct H4.
apply Left_Equivalenc_Relation_Law_1 in H4.
apply Left_Equivalenc_Relation_Law_1 in H5.
apply Left_Equivalenc_Relation_Law_1.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
destruct H7.
apply Ordered_Set_Law_2 in H4.
destruct H4.
destruct H5.
destruct H5.
destruct H5.
destruct H10.
destruct H11.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite <- H4 in H6.
rewrite <- H9 in H7.
rewrite <- H4 in H8.
rewrite <- H9 in H8.
rewrite <- H5 in H10.
rewrite <- H13 in H11.
rewrite <- H5 in H12.
rewrite <- H13 in H12.
exists x.
exists z.
split.
split.
split.
apply H6.
split.
apply H11.
assert (Operation f (Operation f (Reverse_Element f G x) y) (Operation f (Reverse_Element f G y) z)=Operation f (Reverse_Element f G x) z).
rewrite -> (Group_Law_3 f G (Operation f (Reverse_Element f G x) y) (Reverse_Element f G y) z).
rewrite <- (Group_Law_3 f G (Reverse_Element f G x) y (Reverse_Element f G y)).
rewrite -> (Group_Law_10 f G y).
rewrite -> (Group_Law_5 f G (Reverse_Element f G x)).
split.
split.
apply H.
apply Group_Law_9.
split.
apply H.
apply H6.
split.
apply H.
apply H7.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H6.
split.
apply H7.
apply Group_Law_9.
split.
apply H.
apply H7.
split.
apply H.
split.
apply Group_Law_2.
split.
apply H.
split.
apply Group_Law_9.
split.
apply H.
apply H6.
apply H7.
split.
apply Group_Law_9.
split.
apply H.
apply H7.
apply H11.
rewrite <- H14.
clear H14.
rewrite <- (Sub_Group_Law_1 f G f0 G0 (Operation f (Reverse_Element f G x) y) (Operation f (Reverse_Element f G y) z)).
apply Group_Law_2.
split.
apply H1.
split.
apply H8.
apply H12.
split.
apply H0.
split.
apply H8.
apply H12.
Qed.



Definition Right_Equivalenc_Relation(f G G0:Set):=Prop_Set (fun a=>exists x y:Set,a=Ordered_Set x y/\x ∈ G/\y ∈ G/\(Operation f x (Reverse_Element f G y)) ∈ G0).

Definition Right_Quotient_Group(f G G0:Set):=Equivalence_Class (Left_Equivalenc_Relation f G G0).

Theorem Right_Equivalenc_Relation_Law_1:forall f G G0 a:Set,a ∈ (Right_Equivalenc_Relation f G G0)<->(exists x y:Set,a=Ordered_Set x y/\x ∈ G/\y ∈ G/\(Operation f x (Reverse_Element f G y)) ∈ G0).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set G)).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
destruct H.
destruct H.
destruct H.
destruct H2.
destruct H3.
rewrite -> H in H0.
apply Ordered_Set_Law_1 in H0.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H1.
rewrite -> H1.
apply H2.
rewrite -> H1.
apply H3.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
apply H3.
Qed.

Theorem Right_Equivalenc_Relation_Law_2:forall f G f0 G0:Set,Sub_Group f G f0 G0->Equivalenc_Relation (Right_Equivalenc_Relation f G G0) G.
Proof.
intros.
split.
intro.
intro.
apply Right_Equivalenc_Relation_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
destruct H2.
exists x.
exists x0.
split.
apply H0.
split.
apply H1.
apply H2.

split.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intro.
intro.
apply Right_Equivalenc_Relation_Law_1.
exists x.
exists x.
split.
split.
split.
apply H4.
split.
apply H4.
rewrite -> (Group_Law_10 f G x).
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply (Group_Law_4 f0 G0).
apply H1.
apply H0.
split.
apply H.
apply H4.
split.

intro.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intro.
intro.
apply Right_Equivalenc_Relation_Law_1 in H4.
apply Right_Equivalenc_Relation_Law_1.
destruct H4.
destruct H4.
destruct H4.
destruct H5.
destruct H6.
apply Ordered_Set_Law_2 in H4.
destruct H4.
rewrite <- H4 in H5.
rewrite <- H8 in H6.
rewrite <- H4 in H7.
rewrite <- H8 in H7.
exists y.
exists x.
split.
split.
split.
apply H6.
split.
apply H5.
rewrite -> (Group_Law_14 f G y).
rewrite <- (Group_Law_15 f G x (Reverse_Element f G y)).
rewrite -> (Sub_Group_Law_3 f G f0 G0 (Operation f x (Reverse_Element f G y))).
apply (Group_Law_9 f0 G0 (Operation f x (Reverse_Element f G y))).
split.
apply H1.
apply H7.
split.
apply H0.
apply H7.
split.
apply H.
split.
apply H5.
apply (Group_Law_9 f G y).
split.
apply H.
apply H6.
split.
apply H.
apply H6.

intro.
assert (Sub_Group f G f0 G0).
apply H.
destruct H.
destruct H1.
destruct H2.
intros.
destruct H4.
apply Right_Equivalenc_Relation_Law_1 in H4.
apply Right_Equivalenc_Relation_Law_1 in H5.
apply Right_Equivalenc_Relation_Law_1.
destruct H4.
destruct H4.
destruct H4.
destruct H6.
destruct H7.
apply Ordered_Set_Law_2 in H4.
destruct H4.
destruct H5.
destruct H5.
destruct H5.
destruct H10.
destruct H11.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite <- H4 in H6.
rewrite <- H9 in H7.
rewrite <- H4 in H8.
rewrite <- H9 in H8.
rewrite <- H5 in H10.
rewrite <- H13 in H11.
rewrite <- H5 in H12.
rewrite <- H13 in H12.
exists x.
exists z.
split.
split.
split.
apply H6.
split.
apply H11.
assert (Operation f (Operation f x (Reverse_Element f G y)) (Operation f y (Reverse_Element f G z))=Operation f x (Reverse_Element f G z)).
rewrite -> (Group_Law_3 f G (Operation f x (Reverse_Element f G y)) y (Reverse_Element f G z)).
rewrite <- (Group_Law_3 f G x (Reverse_Element f G y) y).
rewrite -> (Group_Law_11 f G y).
rewrite -> (Group_Law_5 f G x).
split.
split.
apply H.
apply H6.
split.
apply H.
apply H10.
split.
apply H.
split.
apply H6.
split.
apply Group_Law_9.
split.
apply H.
apply H7.
apply H7.
split.
apply H.
split.
apply H2.
apply H8.
split.
apply H7.
apply Group_Law_9.
split.
apply H.
apply H11.
rewrite <- H14.
clear H14.
rewrite <- (Sub_Group_Law_1 f G f0 G0 (Operation f x (Reverse_Element f G y)) (Operation f y (Reverse_Element f G z))).
apply Group_Law_2.
split.
apply H1.
split.
apply H8.
apply H12.
split.
apply H0.
split.
apply H8.
apply H12. 
Qed.



(*正規部分群*)
Definition Normal_Sub_Group(f G f0 G0:Set):=Sub_Group f G f0 G0/\forall x x0:Set,(x ∈ G/\x0 ∈ G0)->(Operation f (Operation f x x0) (Reverse_Element f G x)) ∈ G0.

Theorem Normal_Sub_Group_Law_1:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0<->Sub_Group f G f0 G0/\(forall x x0:Set,(x ∈ G/\x0 ∈ G0)->((Operation f (Operation f (Reverse_Element f G x) x0) x) ∈ G0)).
Proof.
intros.
split.

intro.
destruct H.
assert (Sub_Group f G f0 G0).
apply H.
destruct H1.
destruct H2.
destruct H3.
split.
apply H.
intros.
destruct H5.
assert ((Reverse_Element f G x) ∈ G/\x0 ∈ G0).
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
apply H6.
apply H0 in H7.
rewrite <- (Group_Law_14 f G x) in H7.
apply H7.
split.
apply H1.
apply H5.

intro.
destruct H.
assert (Sub_Group f G f0 G0).
apply H.
destruct H1.
destruct H2.
destruct H3.
split.
apply H.
intros.
destruct H5.
assert ((Reverse_Element f G x) ∈ G/\x0 ∈ G0).
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
apply H6.
apply H0 in H7.
rewrite <- (Group_Law_14 f G x) in H7.
apply H7.
split.
apply H1.
apply H5.
Qed.

Theorem Normal_Sub_Group_Law_2:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0<->Sub_Group f G f0 G0/\(Left_Equivalenc_Relation f G G0)=(Right_Equivalenc_Relation f G G0).
Proof.
intros.
split.

intro.
assert (Normal_Sub_Group f G f0 G0).
apply H.
apply Normal_Sub_Group_Law_1 in H0.
destruct H.
destruct H0.
clear H0.
split.
apply H.
apply (Relation_Law_1 (Left_Equivalenc_Relation f G G0) (Right_Equivalenc_Relation f G G0) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
split.
apply (Right_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
assert (Sub_Group f G f0 G0).
apply H.
destruct H0.
destruct H3.
destruct H4.
intros.
split.
intro.
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x1 x2)) in H7.
apply (Right_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x1 x2)).
destruct H7.
destruct H7.
destruct H7.
destruct H8.
destruct H9.
exists x.
exists x0.
split.
apply H7.
split.
apply H8.
split.
apply H9.
assert ((Reverse_Element f G x) ∈ G/\(Operation f (Reverse_Element f G x) x0) ∈ G0).
split.
apply Group_Law_9.
split.
destruct H.
apply H.
apply H8.
apply H10.
apply H2 in H11.
rewrite <- (Group_Law_14 f G x) in H11.
rewrite -> (Group_Law_3 f G x (Reverse_Element f G x) x0) in H11.
rewrite -> (Group_Law_10 f G x) in H11.
rewrite -> (Group_Law_6 f G x0) in H11.
assert (Group f0 G0/\Operation f x0 (Reverse_Element f G x) ∈ G0).
split.
apply H3.
apply H11.
apply Group_Law_9 in H12.
rewrite <- (Sub_Group_Law_3 f G f0 G0 (Operation f x0 (Reverse_Element f G x))) in H12.
rewrite -> (Group_Law_15 f G x0 (Reverse_Element f G x)) in H12.
rewrite <- (Group_Law_14 f G x) in H12.
apply H12.
split.
apply H0.
apply H8.
split.
apply H0.
split.
apply H9.
apply Group_Law_9.
split.
apply H0.
apply H8.
split.
apply H.
apply H11.
split.
apply H0.
apply H9.
split.
apply H0.
apply H8.
split.
apply H0.
split.
apply H8.
split.
apply Group_Law_9.
split.
apply H0.
apply H8.
apply H9.
split.
apply H0.
apply H8.
intro.
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x1 x2)).
apply (Right_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x1 x2)) in H7.
destruct H7.
destruct H7.
destruct H7.
destruct H8.
destruct H9.
exists x.
exists x0.
split.
apply H7.
split.
apply H8.
split.
apply H9.
assert ((Reverse_Element f G x) ∈ G/\(Operation f x (Reverse_Element f G x0)) ∈ G0).
split.
apply Group_Law_9.
split.
apply H0.
apply H8.
apply H10.
apply H1 in H11.
rewrite -> (Group_Law_3 f G (Reverse_Element f G x) x (Reverse_Element f G x0)) in H11.
rewrite -> (Group_Law_11 f G x) in H11.
rewrite -> (Group_Law_6 f G (Reverse_Element f G x0)) in H11.
rewrite <- (Group_Law_14 f G x) in H11.
assert (Group f0 G0/\Operation f (Reverse_Element f G x0) x ∈ G0).
split.
apply H3.
apply H11.
apply Group_Law_9 in H12.
rewrite <- (Sub_Group_Law_3 f G f0 G0 (Operation f (Reverse_Element f G x0) x)) in H12.
rewrite -> (Group_Law_15 f G (Reverse_Element f G x0) x) in H12.
rewrite <- (Group_Law_14 f G x0) in H12.
apply H12.
split.
apply H0.
apply H9.
split.
apply H0.
split.
apply Group_Law_9.
split.
apply H0.
apply H9.
apply H8.
split.
apply H.
apply H11.
split.
apply H0.
apply H8.
split.
apply H0.
apply Group_Law_9.
split.
apply H0.
apply H9.
split.
apply H0.
apply H8.
split.
apply H0.
split.
apply Group_Law_9.
split.
apply H0.
apply H8.
split.
apply H8.
apply Group_Law_9.
split.
apply H0.
apply H9.

intro.
destruct H.
split.
apply H.
intros.
destruct H1.
assert (Sub_Group f G f0 G0).
apply H.
destruct H3.
destruct H4.
destruct H5.
assert (Relation_Prop (Left_Equivalenc_Relation f G G0) x (Operation f x (Reverse_Element f G x0))).
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x (Operation f x (Reverse_Element f G x0)))).
exists x.
exists (Operation f x (Reverse_Element f G x0)).
split.
split.
split.
apply H1.
split.
apply Group_Law_2.
split.
apply H3.
split.
apply H1.
apply Group_Law_9.
split.
apply H3.
apply H5.
apply H2.
rewrite -> (Group_Law_3 f G (Reverse_Element f G x) x (Reverse_Element f G x0)).
rewrite -> (Group_Law_11 f G x).
rewrite -> (Group_Law_6 f G (Reverse_Element f G x0)).
rewrite -> (Sub_Group_Law_3 f G f0 G0 x0).
apply Group_Law_9.
split.
apply H4.
apply H2.
split.
apply H.
apply H2.
split.
apply H3.
apply Group_Law_9.
split.
apply H3.
apply H5.
apply H2.
split.
apply H3.
apply H1.
split.
apply H3.
split.
apply Group_Law_9.
split.
apply H3.
apply H1.
split.
apply H1.
apply Group_Law_9.
split.
apply H3.
apply H5.
apply H2.
rewrite -> H0 in H7.
apply (Right_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set x (Operation f x (Reverse_Element f G x0)))) in H7.
destruct H7.
destruct H7.
destruct H7.
destruct H8.
destruct H9.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite <- H7 in H8.
rewrite <- H7 in H10.
rewrite <- H11 in H9.
rewrite <- H11 in H10.
rewrite -> (Group_Law_15 f G x (Reverse_Element f G x0)) in H10.
rewrite <- (Group_Law_14 f G x0) in H10.
rewrite <- (Group_Law_3 f G x x0 (Reverse_Element f G x)).
apply H10.
split.
apply H3.
split.
apply H1.
split.
apply H5.
apply H2.
apply Group_Law_9.
split.
apply H3.
apply H1.
split.
apply H3.
apply H5.
apply H2.
split.
apply H3.
split.
apply H1.
apply Group_Law_9.
split.
apply H3.
apply H5.
apply H2.
Qed.

Theorem Normal_Sub_Group_Law_3:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0<->(Sub_Group f G f0 G0/\(forall x1 x2 a1 a2:Set,a1 ∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1)/\a2 ∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)->(Operation f a1 a2) ∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x1 x2)))).
Proof.
intros.
split.

intro.
assert (Normal_Sub_Group f G f0 G0).
apply H.
apply Normal_Sub_Group_Law_1 in H0.
destruct H.
destruct H0.
clear H0.
split.
apply H.
intros.
destruct H0.
assert (Sub_Group f G f0 G0).
apply H.
destruct H4.
destruct H5.
destruct H6.
assert (Equivalenc_Relation (Left_Equivalenc_Relation f G G0) G/\a1 ∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1)).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
apply H0.
apply Equivalence_Class_Law_2 in H8.
assert (Equivalenc_Relation (Left_Equivalenc_Relation f G G0) G/\a2∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
apply H3.
apply Equivalence_Class_Law_2 in H9.
clear H0.
clear H3.
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set a1 x1)) in H8.
destruct H8.
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set a2 x2)) in H9.
destruct H9.
destruct H0.
destruct H0.
destruct H8.
destruct H9.
destruct H3.
destruct H3.
destruct H11.
destruct H12.
apply Ordered_Set_Law_2 in H0.
destruct H0.
rewrite <- H0 in H8.
rewrite <- H0 in H10.
clear H0.
rewrite <-  H14 in H9.
rewrite <-  H14 in H10.
clear H14.
apply Ordered_Set_Law_2 in H3.
destruct H3.
rewrite <- H0 in H11.
rewrite <- H0 in H13.
clear H0.
rewrite <- H3 in H12.
rewrite <- H3 in H13.
clear H3.
apply (Equivalence_Class_Law_3 (Left_Equivalenc_Relation f G G0) (Operation f a1 a2) (Operation f x1 x2) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
apply (Left_Equivalenc_Relation_Law_1 f G G0 (Ordered_Set (Operation f a1 a2) (Operation f x1 x2))).
exists (Operation f a1 a2).
exists (Operation f x1 x2).
split.
split.
split.
apply Group_Law_2.
split.
apply H4.
split.
apply H8.
apply H11.
split.
apply Group_Law_2.
split.
apply H4.
split.
apply H9.
apply H12.
rewrite <- (Group_Law_6 f G x2).
rewrite <- (Group_Law_10 f G a2).
rewrite <- (Group_Law_3 f G a2 (Reverse_Element f G a2) x2).
rewrite -> (Group_Law_3 f G (Reverse_Element f G (Operation f a1 a2)) x1 (Operation f a2 (Operation f (Reverse_Element f G a2) x2))).
rewrite -> (Group_Law_3 f G (Operation f (Reverse_Element f G (Operation f a1 a2)) x1) a2 (Operation f (Reverse_Element f G a2) x2)).
rewrite <- (Sub_Group_Law_1 f G f0 G0 (Operation f (Operation f (Reverse_Element f G (Operation f a1 a2)) x1) a2) (Operation f (Reverse_Element f G a2) x2)).
apply Group_Law_2.
split.
apply H5.
split.
rewrite -> (Group_Law_15 f G a1 a2).
rewrite <- (Group_Law_3 f G (Reverse_Element f G a2) (Reverse_Element f G a1) x1).
apply H2.
split.
apply H11.
apply H10.
split.
apply H4.
split.
apply Group_Law_9.
split.
apply H4.
apply H11.
split.
apply Group_Law_9.
split.
apply H4.
apply H8.
apply H9.
split.
apply H4.
split.
apply H8.
apply H11.
apply H13.
split.
apply H.
split.
rewrite -> (Group_Law_15 f G a1 a2).
rewrite <- (Group_Law_3 f G (Reverse_Element f G a2) (Reverse_Element f G a1) x1).
apply H2.
split.
apply H11.
apply H10.
split.
apply H4.
split.
apply Group_Law_9.
split.
apply H4.
apply H11.
split.
apply Group_Law_9.
split.
apply H4.
apply H8.
apply H9.
split.
apply H4.
split.
apply H8.
apply H11.
apply H13.
split.
apply H4.
split.
apply (Group_Law_2 f G (Reverse_Element f G (Operation f a1 a2)) x1).
split.
apply H4.
split.
apply Group_Law_9.
split.
apply H4.
apply Group_Law_2.
split.
apply H4.
split.
apply H8.
apply H11.
apply H9.
split.
apply H11.
apply Group_Law_2.
split.
apply H4.
split.
apply Group_Law_9.
split.
apply H4.
apply H11.
apply H12.
split.
apply H4.
split.
apply Group_Law_9.
split.
apply H4.
apply Group_Law_2.
split.
apply H4.
split.
apply H8.
apply H11.
split.
apply H9.
apply (Group_Law_2 f G a2 (Operation f (Reverse_Element f G a2) x2)).
split.
apply H4.
split.
apply H11.
apply H6.
apply H13.
split.
apply H4.
split.
apply H11.
split.
apply Group_Law_9.
split.
apply H4.
apply H11.
apply H12.
split.
apply H4.
apply H11.
split.
apply H4.
apply H12.

intros.
destruct H.
split.
apply H.
intros.
destruct H1.
assert (Sub_Group f G f0 G0).
apply H.
destruct H3.
destruct H4.
destruct H5.
assert ((Identify_Element f G) ∈ Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Reverse_Element f G x0)/\(Reverse_Element f G x) ∈ Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Reverse_Element f G x)).
split.
apply Equivalence_Class_Law_1.
split.
apply H5.
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply Group_Law_4.
apply H4.
apply H.
apply Left_Equivalenc_Relation_Law_1.
exists (Reverse_Element f G x0).
exists (Identify_Element f G).
split.
split.
split.
apply H5.
rewrite -> (Sub_Group_Law_3 f G f0 G0 x0).
apply Group_Law_9.
split.
apply H4.
apply H2.
split.
apply H.
apply H2.
split.
apply Group_Law_4.
apply H3.
rewrite -> (Group_Law_5 f G (Reverse_Element f G (Reverse_Element f G x0))).
rewrite -> (Sub_Group_Law_3 f G f0 G0 (Reverse_Element f G x0)).
apply Group_Law_9.
split.
apply H4.
rewrite -> (Sub_Group_Law_3 f G f0 G0 x0).
apply Group_Law_9.
split.
apply H4.
apply H2.
split.
apply H.
apply H2.
split.
apply H.
rewrite -> (Sub_Group_Law_3 f G f0 G0 x0).
apply Group_Law_9.
split.
apply H4.
apply H2.
split.
apply H.
apply H2.
split.
apply H3.
apply Group_Law_9.
split.
apply H3.
apply H5.
rewrite -> (Sub_Group_Law_3 f G f0 G0 x0).
apply Group_Law_9.
split.
apply H4.
apply H2.
split.
apply H.
apply H2.
apply Equivalence_Class_Law_1.
split.
apply Group_Law_9.
split.
apply H3.
apply H1.
apply Left_Equivalenc_Relation_Law_1.
exists (Reverse_Element f G x).
exists (Reverse_Element f G x).
split.
split.
split.
apply Group_Law_9.
split.
apply H3.
apply H1.
split.
apply Group_Law_9.
split.
apply H3.
apply H1.
rewrite -> (Group_Law_11 f G (Reverse_Element f G x)).
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply Group_Law_4.
apply H4.
apply H.
split.
apply H3.
apply Group_Law_9.
split.
apply H3.
apply H1.
apply H0 in H7.
apply Equivalence_Class_Law_1 in H7.
destruct H7.
apply Left_Equivalenc_Relation_Law_1 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
destruct H10.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite <- H8 in H9.
rewrite <- H8 in H11.
clear H8.
rewrite <- H12 in H10.
rewrite <- H12 in H11.
clear H12.
rewrite -> (Group_Law_15 f G (Reverse_Element f G x0) (Reverse_Element f G x)) in H11.
rewrite <- (Group_Law_14 f G x) in H11.
rewrite <- (Group_Law_14 f G x0) in H11.
rewrite -> (Group_Law_6 f G (Reverse_Element f G x)) in H11.
apply H11.
split.
apply H3.
apply Group_Law_9.
split.
apply H3.
apply H1.
split.
apply H3.
apply H5.
apply H2.
split.
apply H3.
apply H1.
split.
apply H3.
split.
apply Group_Law_9.
split.
apply H3.
apply H5.
apply H2.
apply Group_Law_9.
split.
apply H3.
apply H1.
Qed.



(*剰余群*)
Definition Group_Quotient_Operation(f G G0:Set):=Prop_Set (fun a=>exists x1 x2:Set,x1 ∈ G/\x2 ∈ G/\a=Ordered_Set (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x1 x2))).

Theorem Quotient_Group_Law_1:forall f G G0 a:Set,a ∈ (Group_Quotient_Operation f G G0)<->exists x1 x2:Set,x1 ∈ G/\x2 ∈ G/\a=Ordered_Set (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x1 x2)).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set ((Power_Set (Power_Set (Power_Set G))) ∪ (Power_Set G)))).
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
rewrite -> H1.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Union_Set_Law_1.
apply Ordered_Set_Law_1 in H2.
destruct H2.
rewrite -> H2 in H3.
apply Pair_Set_Law_1 in H3.
destruct H3.
rewrite -> H3.
left.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Ordered_Set_Law_1 in H4.
destruct H4.
rewrite -> H4 in H5.
apply Pair_Set_Law_1 in H5.
destruct H5.
rewrite -> H5 in H6.
apply Equivalence_Class_Law_1 in H6.
destruct H6.
apply H6.
rewrite -> H5 in H6.
apply Equivalence_Class_Law_1 in H6.
destruct H6.
apply H6.
rewrite -> H4 in H5.
apply Single_Set_Law_1 in H5.
rewrite -> H5 in H6.
apply Equivalence_Class_Law_1 in H6.
destruct H6.
apply H6.
rewrite -> H3.
right.
apply Power_Set_Law_1.
intro.
intro.
apply Equivalence_Class_Law_1 in H4.
destruct H4.
apply H4.
rewrite -> H2 in H3.
apply Single_Set_Law_1 in H3.
right.
rewrite -> H3.
apply Power_Set_Law_1.
intro.
intro.
apply Equivalence_Class_Law_1 in H4.
destruct H4.
apply H4.
Qed.

Theorem Quotient_Group_Law_2:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0->Binary_Operation (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G).
Proof.
intros.
split.

intros.
apply Quotient_Group_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
exists (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x0)).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x x0)).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x0).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H0.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H1.
split.
split.
apply Quotient_Set_Law_1.
exists (Operation f x x0).
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H0.
apply H1.
split.
apply H2.

intros.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x2 x3)).
split.
split.
apply Quotient_Group_Law_1.
exists x2.
exists x3.
split.
apply H1.
split.
apply H2.
rewrite <- H0.
rewrite -> H3.
rewrite -> H4.
split.
apply Quotient_Set_Law_1.
exists (Operation f x2 x3).
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
apply H2.
split.
intros.
destruct H5.
apply Quotient_Set_Law_1 in H6.
destruct H6.
destruct H6.
symmetry.
apply Quotient_Group_Law_1 in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H8.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite <- H0 in H9.
apply Ordered_Set_Law_2 in H9.
destruct H9.
rewrite -> H10.
apply Equivalence_Class_Law_5.
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
split.
apply Group_Law_2.
split.
apply H.
split.
apply H5.
apply H8.
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
apply H2.
apply (Equivalence_Class_Law_2 (Left_Equivalenc_Relation f G G0) (Operation f x5 x6) (Operation f x2 x3) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
assert (Normal_Sub_Group f G f0 G0).
apply H.
apply Normal_Sub_Group_Law_3 in H12.
destruct H12.
apply H13.
split.
rewrite <- H3.
rewrite -> H9.
apply Equivalence_Class_Law_3.
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply (Equivalenc_Relation_Law_2 (Left_Equivalenc_Relation f G G0) G x5).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply H5.
rewrite <- H4.
rewrite -> H11.
apply Equivalence_Class_Law_3.
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply (Equivalenc_Relation_Law_2 (Left_Equivalenc_Relation f G G0) G x6).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply H8.
Qed.

Theorem Quotient_Group_Law_3:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0->Group (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G).
Proof.
intros.

assert (Binary_Operation (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)).
split.
intros.
apply Quotient_Group_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
exists (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x0)).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x x0)).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x0).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H0.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H1.
split.
split.
apply Quotient_Set_Law_1.
exists (Operation f x x0).
split.
destruct H.
destruct H.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
split.
apply H2.
intros.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
rewrite <- H0.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x2 x3)).
split.
split.
apply Quotient_Group_Law_1.
exists x2.
exists x3.
rewrite -> H3.
rewrite -> H4.
split.
apply H1.
split.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Operation f x2 x3).
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
apply H2.
split.
intros.
destruct H5.
apply Quotient_Group_Law_1 in H5.
destruct H5.
destruct H5.
destruct H5.
destruct H7.
apply Ordered_Set_Law_2 in H8.
destruct H8.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H9.
assert ((Operation f x2 x3) ∈ (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x4 x5))).
assert (Normal_Sub_Group f G f0 G0).
apply H.
apply Normal_Sub_Group_Law_3 in H11.
apply H11.
clear H11.
split.
rewrite <- H8.
rewrite -> H3.
apply Equivalence_Class_Law_1.
split.
apply H1.
apply Left_Equivalenc_Relation_Law_1.
exists x2.
exists x2.
split.
split.
split.
apply H1.
split.
apply H1.
rewrite -> (Group_Law_11 f G x2).
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply Group_Law_4.
destruct H.
destruct H.
destruct H12.
apply H12.
destruct H.
apply H.
split.
destruct H.
destruct H.
apply H.
apply H1.
rewrite <- H10.
rewrite -> H4.
apply Equivalence_Class_Law_1.
split.
apply H2.
apply Left_Equivalenc_Relation_Law_1.
exists x3.
exists x3.
split.
split.
split.
apply H2.
split.
apply H2.
rewrite -> (Group_Law_11 f G x3).
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply Group_Law_4.
destruct H.
destruct H.
destruct H12.
apply H12.
destruct H.
apply H.
split.
destruct H.
destruct H.
apply H.
apply H2.
assert (Relation_Prop (Left_Equivalenc_Relation f G G0) (Operation f x2 x3) (Operation f x4 x5)).
apply (Equivalence_Class_Law_2 (Left_Equivalenc_Relation f G G0) (Operation f x2 x3) (Operation f x4 x5) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply H11.
clear H11.
apply Theorem_of_Extensionality.
intros.
split.
intro.
apply (Equivalence_Class_Law_3 (Left_Equivalenc_Relation f G G0) z (Operation f x4 x5) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
assert (Equivalenc_Relation (Left_Equivalenc_Relation f G G0) G).
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
destruct H13.
destruct H14.
destruct H15.
apply (H16 z (Operation f x2 x3) (Operation f x4 x5)).
split.
apply (Equivalence_Class_Law_2 (Left_Equivalenc_Relation f G G0) z (Operation f x2 x3) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply H11.
apply H12.
intros.
apply (Equivalence_Class_Law_3 (Left_Equivalenc_Relation f G G0) z (Operation f x2 x3) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
assert (Equivalenc_Relation (Left_Equivalenc_Relation f G G0) G).
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
destruct H13.
destruct H14.
destruct H15.
apply (H16 z (Operation f x4 x5) (Operation f x2 x3)).
split.
apply (Equivalence_Class_Law_2 (Left_Equivalenc_Relation f G G0) z (Operation f x4 x5) G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
destruct H.
apply H.
apply H11.
apply H15.
apply H12.
split.
apply H0.

assert (forall x1 x2:Set,x1 ∈ G/\x2 ∈ G->Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x1 x2)=Operation (Group_Quotient_Operation f G G0) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)).
intros.
destruct H1.
apply (Map_Law_3 (Group_Quotient_Operation f G G0) (Double_Direct_Product_Set (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)) (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2)) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x1 x2))).
split.
apply H0.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x1).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x2).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H1.
split.
apply Quotient_Set_Law_1.
exists x2.
split.
apply H2.
split.
split.
apply Quotient_Set_Law_1.
exists (Operation f x1 x2).
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
apply H2.
split.
apply Quotient_Group_Law_1.
exists x1.
exists x2.
split.
apply H1.
split.
apply H2.
split.
assert (Monoid (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)).
split.
apply H0.

split.
intro.
intros.
destruct H2.
destruct H3.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
apply Quotient_Set_Law_1 in H4.
destruct H4.
destruct H4.
rewrite -> H5.
rewrite -> H6.
rewrite -> H7.
rewrite <- (H1 x0 x4).
rewrite <- (H1 x x0).
rewrite <- (H1 x (Operation f x0 x4)).
rewrite <- (H1 (Operation f x x0) x4).
rewrite -> (Group_Law_3 f G x x0 x4).
split.
split.
destruct H.
destruct H.
apply H.
split.
apply H2.
split.
apply H3.
apply H4.
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H2.
apply H3.
apply H4.
split.
apply H2.
destruct H.
destruct H.
apply Group_Law_2.
split.
apply H.
split.
apply H3.
apply H4.
split.
apply H2.
apply H3.
split.
apply H3.
apply H4.

exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Identify_Element f G)).
split.
apply Quotient_Set_Law_1.
exists (Identify_Element f G).
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
split.
intros.
split.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
rewrite -> H3.
rewrite <- (H1 x0 (Identify_Element f G)).
rewrite -> (Group_Law_5 f G).
split.
split.
destruct H.
destruct H.
apply H.
apply H2.
split.
apply H2.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
apply Quotient_Set_Law_1 in H2.
destruct H2.
destruct H2.
rewrite -> H3.
rewrite <- (H1 (Identify_Element f G) x0).
rewrite -> (Group_Law_6 f G).
split.
split.
destruct H.
destruct H.
apply H.
apply H2.
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
apply H2.
split.
destruct H2.
destruct H3.
apply H3.
split.
destruct H2.
destruct H3.
apply H4.

intros.
apply Quotient_Set_Law_1 in H3.
destruct H3.
destruct H3.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Reverse_Element f G x0)).
split.
apply Quotient_Set_Law_1.
exists (Reverse_Element f G x0).
split.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H3.
split.
assert (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Identify_Element f G)=Identify_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)).
assert (Monoid (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)).
apply H2.
apply Monoid_Law_3 in H5.
destruct H5.
destruct H5.
rewrite <- (H6 (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Identify_Element f G))).
rewrite <- (H6 (Identify_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G))).
split.
split.
apply Monoid_Law_5.
apply H2.
intros.
split.
apply Monoid_Law_6.
split.
apply H2.
apply H7.
apply Monoid_Law_7.
split.
apply H2.
apply H7.
split.
apply Quotient_Set_Law_1.
exists (Identify_Element f G).
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
split.
intros.
split.
apply Quotient_Set_Law_1 in H7.
destruct H7.
destruct H7.
rewrite -> H8.
rewrite <- H1.
rewrite -> Group_Law_5.
split.
split.
destruct H.
destruct H.
apply H.
apply H7.
split.
apply H7.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
apply Quotient_Set_Law_1 in H7.
destruct H7.
destruct H7.
rewrite -> H8.
rewrite <- H1.
rewrite -> Group_Law_6.
split.
split.
destruct H.
destruct H.
apply H.
apply H7.
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
apply H7.
rewrite -> H4.
split.
rewrite <- (H1 x0 (Reverse_Element f G x0)).
rewrite -> (Group_Law_10 f G x0).
apply H5.
split.
destruct H.
destruct H.
apply H.
apply H3.
split.
apply H3.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H3.
rewrite <- H1.
rewrite -> (Group_Law_11 f G x0).
apply H5.
split.
destruct H.
destruct H.
apply H.
apply H3.
split.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H3.
apply H3.
Qed.

Theorem Quotient_Group_Law_4:forall f G f0 G0 x y:Set,Normal_Sub_Group f G f0 G0/\x ∈ G/\y ∈ G->Operation (Group_Quotient_Operation f G G0) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G y)=Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x y).
Proof.
intros.
destruct H.
destruct H0.
symmetry.

apply (Map_Law_3 (Group_Quotient_Operation f G G0) (Double_Direct_Product_Set (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)  (Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G y)) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Operation f x y))).
split.
apply (Quotient_Group_Law_2 f G f0 G0).
apply H.

split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x).
exists (Equivalence_Class (Left_Equivalenc_Relation f G G0) G y).
split.
split.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H0.
split.
apply Quotient_Set_Law_1.
exists y.
split.
apply H1.
split.

split.
apply Quotient_Set_Law_1.
exists (Operation f x y).
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H0.
apply H1.
split.

apply Quotient_Group_Law_1.
exists x.
exists y.
split.
apply H0.
split.
apply H1.
split.
Qed.

Theorem Quotient_Group_Law_5:forall f G f0 G0:Set,Normal_Sub_Group f G f0 G0->Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Identify_Element f G)=Identify_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G).
Proof.
intros.
apply (Group_Law_18 (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Identify_Element f G))).
split.
apply (Quotient_Group_Law_3 f G f0 G0).
apply H.
split.
apply Quotient_Set_Law_1.
exists (Identify_Element f G).
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
split.
intros.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
rewrite -> H1.
rewrite -> (Quotient_Group_Law_4 f G f0 G0 (Identify_Element f G) x).
rewrite -> (Group_Law_6 f G x).
split.
split.
destruct H.
destruct H.
apply H.
apply H0.
split.
apply H.
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
apply H0.
Qed.

Theorem Quotient_Group_Law_6:forall f G f0 G0 x:Set,Normal_Sub_Group f G f0 G0/\x ∈ G0->Equivalence_Class (Left_Equivalenc_Relation f G G0) G x=Identify_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G).
Proof.
intros.
destruct H.
apply (Group_Law_17 (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x)).
split.
apply (Quotient_Group_Law_3 f G f0 G0).
apply H.
split.
apply Quotient_Set_Law_1.
exists x.
split.
destruct H.
destruct H.
destruct H2.
destruct H3.
apply H3.
apply H0.
split.

intros.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
rewrite -> H2.
rewrite -> (Quotient_Group_Law_4 f G f0 G0 x0 x).
apply (Equivalence_Class_Law_5 (Left_Equivalenc_Relation f G G0) (Operation f x0 x) x0 G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
split.
apply H1.
apply Left_Equivalenc_Relation_Law_1.
exists (Operation f x0 x).
exists x0.
split.
split.
split.
apply Group_Law_2.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
split.
apply H1.
rewrite -> (Group_Law_15 f G x0 x).
rewrite <- (Group_Law_3 f G (Reverse_Element f G x) (Reverse_Element f G x0) x0).
rewrite -> (Group_Law_11 f G x0).
rewrite -> Group_Law_5.
rewrite -> (Sub_Group_Law_3 f G f0 G0 x).
apply Group_Law_9.
split.
destruct H.
destruct H.
destruct H4.
apply H4.
apply H0.
split.
destruct H.
apply H.
apply H0.
split.
destruct H.
destruct H.
apply H.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
split.
destruct H.
destruct H.
apply H.
apply H1.
split.
destruct H.
destruct H.
apply H.
split.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
split.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H1.
apply H1.
split.
destruct H.
destruct H.
apply H.
split.
apply H1.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
split.
apply H.
split.
apply H1.
destruct H.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H0.
Qed.

Theorem Quotient_Group_Law_7:forall f G f0 G0 x:Set,Normal_Sub_Group f G f0 G0/\x ∈ G/\Equivalence_Class (Left_Equivalenc_Relation f G G0) G x=Identify_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G)->x ∈ G0.
Proof.
intros.
destruct H.
destruct H0.
rewrite <- (Group_Law_6 f G x).
rewrite <- Group_Law_16.
rewrite <- (Quotient_Group_Law_5 f G f0 G0) in H1.
assert (Relation_Prop (Left_Equivalenc_Relation f G G0) (Identify_Element f G) x).
apply (Equivalence_Class_Law_4 (Left_Equivalenc_Relation f G G0) (Identify_Element f G) x G).
split.
apply (Left_Equivalenc_Relation_Law_2 f G f0 G0).
apply H.
split.
apply Group_Law_4.
destruct H.
destruct H.
apply H.
split.
apply H0.
symmetry.
apply H1.
apply Left_Equivalenc_Relation_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
destruct H4.
apply Ordered_Set_Law_2 in H2.
destruct H2.
rewrite -> H2.
rewrite -> H6.
apply H5.
apply H.
destruct H.
destruct H.
apply H.
split.
destruct H.
destruct H.
apply H.
apply H0.
Qed.

Theorem Quotient_Group_Law_8:forall f G f0 G0 x:Set,Normal_Sub_Group f G f0 G0/\x ∈ G->Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Reverse_Element f G x)=Reverse_Element (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x).
Proof.
intros.
destruct H.
apply (Group_Law_19 (Group_Quotient_Operation f G G0) (Quotient_Set (Left_Equivalenc_Relation f G G0) G) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G x) (Equivalence_Class (Left_Equivalenc_Relation f G G0) G (Reverse_Element f G x))).
split.
apply (Quotient_Group_Law_3 f G f0 G0).
apply H.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H0.
split.
split.
apply Quotient_Set_Law_1.
exists (Reverse_Element f G x).
split.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H0.
split.
rewrite -> (Quotient_Group_Law_4 f G f0 G0 x (Reverse_Element f G x)).
rewrite -> (Group_Law_10 f G).
apply (Quotient_Group_Law_6 f G f0 G0).
split.
apply H.
rewrite -> (Sub_Group_Law_2 f G f0 G0).
apply Group_Law_4.
destruct H.
destruct H.
destruct H2.
apply H2.
destruct H.
apply H.
split.
destruct H.
destruct H.
apply H.
apply H0.
split.
apply H.
split.
apply H0.
apply Group_Law_9.
split.
destruct H.
destruct H.
apply H.
apply H0.
Qed.



(*核*)
Definition Map_Kernel(h G1 f2 G2:Set):=Prop_Set (fun x=>x ∈ G1/\(Identify_Element f2 G2)=Culculateion_Map h x).

Theorem Map_Kernel_Law_1:forall h G1 f2 G2 x:Set,x ∈ (Map_Kernel h G1 f2 G2)<->x ∈ G1/\(Identify_Element f2 G2)=Culculateion_Map h x.
Proof.
intros.
apply Prop_Set_Law_1.
exists G1.
intros.
destruct H.
apply H.
Qed.



(*群準同型*)
Definition Group_homomorphism(h f1 G1 f2 G2:Set):=Group f1 G1/\Group f2 G2/\Map h G1 G2/\(forall x y:Set,(x ∈ G1/\y ∈ G1)->Operation f2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation f1 x y)).

Theorem Group_homomorphism_Law_1:forall f G:Set,Group f G->Group_homomorphism (Identify_Map G) f G f G.
Proof.
intros.
split.
apply H.
split.
apply H.
split.
apply Identify_Map_Law_4.

intros.
destruct H0.
rewrite <- (Identify_Map_Law_3 G x).
rewrite <- (Identify_Map_Law_3 G y).
rewrite <- (Identify_Map_Law_3 G (Operation f x y)).
split.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.
Qed.

Theorem Group_homomorphism_Law_2:forall h1 h2 f1 G1 f2 G2 f3 G3:Set,Group_homomorphism h1 f1 G1 f2 G2/\Group_homomorphism h2 f2 G2 f3 G3->Group_homomorphism (Composite_Map h1 h2) f1 G1 f3 G3.
Proof.
intros.
destruct H.
split.
destruct H.
apply H.
split.
destruct H0.
destruct H1.
apply H1.
split.
assert (Map (Composite_Map h1 h2) G1 G3).
apply (Composite_Map_Law_1 h1 h2 G1 G2 G3).
split.
destruct H.
destruct H1.
destruct H2.
apply H2.
destruct H0.
destruct H1.
destruct H2.
apply H2.
apply H1.
intros.
rewrite <- (Composite_Map_Law_2 h1 h2 x G1 G2 G3).
rewrite <- (Composite_Map_Law_2 h1 h2 y G1 G2 G3).
rewrite <- (Composite_Map_Law_2 h1 h2 (Operation f1 x y) G1 G2 G3).
destruct H1.
destruct H.
destruct H3.
destruct H4.
destruct H0.
destruct H6.
destruct H7.
rewrite -> (H8 (Culculateion_Map h1 x) (Culculateion_Map h1 y)).
rewrite -> (H5 x y).
split.
split.
apply H1.
apply H2.
split.
apply (Map_Law_2 h1 G1 G2 x).
split.
apply H4.
apply H1.
apply (Map_Law_2 h1 G1 G2 y).
split.
apply H4.
apply H2.
split.
destruct H.
destruct H2.
destruct H3.
apply H3.
split.
destruct H0.
destruct H2.
destruct H3.
apply H3.
apply Group_Law_2.
split.
destruct H.
apply H.
apply H1.
split.
destruct H.
destruct H2.
destruct H3.
apply H3.
split.
destruct H0.
destruct H2.
destruct H3.
apply H3.
destruct H1.
apply H2.
split.
destruct H.
destruct H2.
destruct H3.
apply H3.
split.
destruct H0.
destruct H2.
destruct H3.
apply H3.
destruct H1.
apply H1.
Qed.

Theorem Group_homomorphism_Law_3:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Culculateion_Map h (Identify_Element f1 G1)=Identify_Element f2 G2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply (Group_Law_13 f2 G2 (Culculateion_Map h (Identify_Element f1 G1)) (Culculateion_Map h (Identify_Element f1 G1)) (Identify_Element f2 G2)).
split.
apply H0.
split.
apply (Map_Law_2 h G1 G2 (Identify_Element f1 G1)).
split.
apply H1.
apply Group_Law_4.
apply H.
split.
apply (Map_Law_2 h G1 G2 (Identify_Element f1 G1)).
split.
apply H1.
apply Group_Law_4.
apply H.
split.
apply Group_Law_4.
apply H0.
rewrite -> (Group_Law_6 f2 G2 (Culculateion_Map h (Identify_Element f1 G1))).
rewrite -> (H2 (Identify_Element f1 G1) (Identify_Element f1 G1)).
rewrite -> (Group_Law_5 f1 G1 (Identify_Element f1 G1)).
split.
split.
apply H.
apply Group_Law_4.
apply H.
split.
apply Group_Law_4.
apply H.
apply Group_Law_4.
apply H.
split.
apply H0.
apply (Map_Law_2 h G1 G2 (Identify_Element f1 G1)).
split.
apply H1.
apply Group_Law_4.
apply H.
Qed.

Theorem Group_homomorphism_Law_4:forall h f1 G1 f2 G2 x:Set,Group_homomorphism h f1 G1 f2 G2/\x ∈ G1->Culculateion_Map h (Reverse_Element f1 G1 x)=Reverse_Element f2 G2 (Culculateion_Map h x).
Proof.
intros.
destruct H.
destruct H.
destruct H1.
destruct H2.
apply (Group_Law_19 f2 G2 (Culculateion_Map h x) (Culculateion_Map h (Reverse_Element f1 G1 x))).
split.
apply H1.
split.
apply (Map_Law_2 h G1 G2 x).
split.
apply H2.
apply H0.
split.
apply (Map_Law_2 h G1 G2 (Reverse_Element f1 G1 x)).
split.
apply H2.
apply Group_Law_9.
split.
apply H.
apply H0.
rewrite -> (H3 x (Reverse_Element f1 G1 x)).
rewrite -> (Group_Law_10 f1 G1 x).
apply Group_homomorphism_Law_3.
split.
apply H.
split.
apply H1.
split.
apply H2.
apply H3.
split.
apply H.
apply H0.
split.
apply H0.
apply Group_Law_9.
split.
apply H.
apply H0.
Qed.

Theorem Group_homomorphism_Law_5:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Sub_Group f2 G2 (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2).
Proof.
intros.
apply Sub_Group_Law_4.
destruct H.
destruct H0.
destruct H1.
split.

apply H0.
split.

intro.
intro.
apply Map_Image_Law_1 in H3.
destruct H3.
apply H3.
split.

intros.
destruct H3.
apply Map_Image_Law_1 in H3.
destruct H3.
destruct H5.
destruct H5.
apply Map_Image_Law_1 in H4.
destruct H4.
destruct H7.
destruct H7.
rewrite -> H6.
rewrite -> H8.
rewrite <- (Group_homomorphism_Law_4 h f1 G1 f2 G2 x0).
rewrite -> (H2 x (Reverse_Element f1 G1 x0)).
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 (Operation f1 x (Reverse_Element f1 G1 x0))).
split.
apply H1.
apply Group_Law_2.
split.
apply H.
split.
apply H5.
apply Group_Law_9.
split.
apply H.
apply H7.
exists (Operation f1 x (Reverse_Element f1 G1 x0)).
split.
apply Group_Law_2.
split.
apply H.
split.
apply H5.
apply Group_Law_9.
split.
apply H.
apply H7.
split.
split.
apply H5.
apply Group_Law_9.
split.
apply H.
apply H7.
split.
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
apply H7.

apply Empty_Set_Law_1.
exists (Identify_Element f2 G2).
apply Map_Image_Law_1.
split.
apply Group_Law_4.
apply H0.
exists (Identify_Element f1 G1).
split.
apply Group_Law_4.
apply H.
symmetry.
apply (Group_homomorphism_Law_3 h f1 G1 f2 G2).
split.
apply H.
split.
apply H0.
split.
apply H1.
apply H2.
Qed.

Theorem Group_homomorphism_Law_6:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Group (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2).
Proof.
intros.
apply Group_homomorphism_Law_5 in H.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Group_homomorphism_Law_7:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Sub_Group f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2).
Proof.
intros.
apply Sub_Group_Law_4.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H0.
destruct H1.
destruct H2.
split.

apply H0.
split.

intro.
intro.
apply Map_Kernel_Law_1 in H4.
destruct H4.
apply H4.
split.

intros.
destruct H4.
apply Map_Kernel_Law_1 in H4.
apply Map_Kernel_Law_1 in H5.
destruct H4.
destruct H5.
apply Map_Kernel_Law_1.
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply Group_Law_9.
split.
apply H0.
apply H5.
rewrite <- (H3 x1 (Reverse_Element f1 G1 x2)).
rewrite <- H6.
rewrite -> (Group_homomorphism_Law_4 h f1 G1 f2 G2 x2).
rewrite <- H7.
rewrite -> (Group_Law_16 f2 G2).
rewrite -> (Group_Law_6 f2 G2).
split.
split.
apply H1.
apply Group_Law_4.
apply H1.
apply H1.
split.
apply H.
apply H5.
split.
apply H4.
apply Group_Law_9.
split.
apply H0.
apply H5.

apply Empty_Set_Law_1.
exists (Identify_Element f1 G1).
apply Map_Kernel_Law_1.
split.
apply Group_Law_4.
apply H0.
symmetry.
apply Group_homomorphism_Law_3.
apply H.
Qed.

Theorem Group_homomorphism_Law_8:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Normal_Sub_Group f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2).
Proof.
intros.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H0.
destruct H1.
destruct H2.
split.

apply Group_homomorphism_Law_7.
apply H.
intros.
destruct H4.
apply Map_Kernel_Law_1 in H5.
destruct H5.
apply Map_Kernel_Law_1.
split.
apply Group_Law_2.
split.
apply H0.
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
apply Group_Law_9.
split.
apply H0.
apply H4.
rewrite <- (H3 (Operation f1 x x0) (Reverse_Element f1 G1 x)).
rewrite <- (H3 x x0).
rewrite <- H6.
rewrite -> (Group_Law_5 f2 G2 (Culculateion_Map h x)).
rewrite -> (Group_homomorphism_Law_4 h f1 G1 f2 G2 x).
rewrite -> (Group_Law_10 f2 G2 (Culculateion_Map h x)).
split.
split.
apply H1.
apply (Map_Law_2 h G1 G2 x).
split.
apply H2.
apply H4.
split.
apply H.
apply H4.
split.
apply H1.
apply (Map_Law_2 h G1 G2 x).
split.
apply H2.
apply H4.
split.
apply H4.
apply H5.
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
apply Group_Law_9.
split.
apply H0.
apply H4.
Qed.

Theorem Group_homomorphism_Law_9:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Group (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2).
Proof.
intros.
apply Group_homomorphism_Law_7 in H.
destruct H.
destruct H0.
apply H0.
Qed.

Theorem Group_homomorphism_Law_10:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2/\(forall x:Set,x ∈ Map_Kernel h G1 f2 G2->x=Identify_Element f1 G1)->Injective_Map h G1 G2.
Proof.
intros.
destruct H.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H1.
destruct H2.
destruct H3.
split.

apply H3.
intros.
destruct H5.
destruct H6.
apply (Group_Law_12 f1 G1 (Reverse_Element f1 G1 x1) x1 x2).
split.
apply H.
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
split.
apply H5.
split.
apply H6.
rewrite -> (Group_Law_11 f1 G1 x1).
symmetry.
apply H0.
apply Map_Kernel_Law_1.
split.
apply Group_Law_2.
split.
apply H1.
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
apply H6.
rewrite <- (H4 (Reverse_Element f1 G1 x1) x2).
rewrite <- H7.
rewrite -> (H4 (Reverse_Element f1 G1 x1) x1).
rewrite -> (Group_Law_11 f1 G1 x1).
symmetry.
apply Group_homomorphism_Law_3.
apply H.
split.
apply H1.
apply H5.
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
apply H5.
split.
apply Group_Law_9.
split.
apply H1.
apply H5.
apply H6.
split.
apply H1.
apply H5.
Qed.

Theorem Group_homomorphism_Law_11:forall h f1 G1 f2 G2 x:Set,Group_homomorphism h f1 G1 f2 G2/\Injective_Map h G1 G2/\x ∈ Map_Kernel h G1 f2 G2->x=Identify_Element f1 G1.
Proof.
intros.
destruct H.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H1.
destruct H2.
destruct H3.
destruct H0.

apply Map_Kernel_Law_1 in H5.
destruct H5.
destruct H0.
apply H7.
split.
apply H5.
split.
apply Group_Law_4.
apply H1.
rewrite <- H6.
symmetry.
apply Group_homomorphism_Law_3.
apply H.
Qed.



(*群同型*)
Definition Group_Isomorphism(h f1 G1 f2 G2:Set):=Group f1 G1/\Group f2 G2/\Bijective_Map h G1 G2/\(forall x y:Set,(x ∈ G1/\y ∈ G1)->Operation f2 (Culculateion_Map h x) (Culculateion_Map h y)=Culculateion_Map h (Operation f1 x y)).

Theorem Group_Isomorphism_Law_1:forall h f1 G1 f2 G2:Set,Group_Isomorphism h f1 G1 f2 G2->Group_homomorphism h f1 G1 f2 G2.
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
destruct H1.
destruct H1.
apply H1.
intros.
apply H2.
apply H3.
Qed.

Theorem Group_Isomorphism_Law_2:forall f G:Set,Group f G->Group_Isomorphism (Identify_Map G) f G f G.
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
rewrite <- (Identify_Map_Law_3 G x).
rewrite <- (Identify_Map_Law_3 G y).
rewrite <- (Identify_Map_Law_3 G (Operation f x y)).
split.
apply Group_Law_2.
split.
apply H.
split.
apply H0.
apply H1.
apply H1.
apply H0.
Qed.

Theorem Group_Isomorphism_Law_3:forall h1 h2 f1 G1 f2 G2 f3 G3:Set,Group_Isomorphism h1 f1 G1 f2 G2/\Group_Isomorphism h2 f2 G2 f3 G3->Group_Isomorphism (Composite_Map h1 h2) f1 G1 f3 G3.
Proof.
intros.
destruct H.
split.
destruct H.
apply H.
split.
destruct H0.
destruct H1.
apply H1.
split.
apply (Composite_Map_Law_5 h1 h2 G1 G2 G3).
split.
destruct H.
destruct H1.
destruct H2.
apply H2.
destruct H0.
destruct H1.
destruct H2.
apply H2.
intros.
destruct H1.
rewrite <- (Composite_Map_Law_2 h1 h2 x G1 G2 G3).
rewrite <- (Composite_Map_Law_2 h1 h2 y G1 G2 G3).
rewrite <- (Composite_Map_Law_2 h1 h2 (Operation f1 x y) G1 G2 G3).
destruct H.
destruct H3.
destruct H4.
destruct H0.
destruct H6.
destruct H7.
rewrite -> (H8 (Culculateion_Map h1 x) (Culculateion_Map h1 y)).
rewrite -> (H5 x y).
split.
split.
apply H1.
apply H2.
split.
apply (Map_Law_2 h1 G1 G2 x).
split.
apply H4.
apply H1.
apply (Map_Law_2 h1 G1 G2 y).
split.
apply H4.
apply H2.
split.
destruct H.
destruct H3.
destruct H4.
destruct H4.
destruct H4.
apply H4.
split.
destruct H0.
destruct H3.
destruct H4.
destruct H4.
destruct H6.
apply H6.
destruct H.
apply Group_Law_2.
split.
apply H.
split.
apply H1.
apply H2.
split.
destruct H.
destruct H3.
destruct H4.
destruct H4.
destruct H4.
apply H4.
split.
destruct H0.
destruct H3.
destruct H4.
destruct H4.
destruct H6.
apply H6.
apply H2.
split.
destruct H.
destruct H3.
destruct H4.
destruct H4.
destruct H4.
apply H4.
split.
destruct H0.
destruct H3.
destruct H4.
destruct H4.
destruct H6.
apply H6.
apply H1.
Qed.

Theorem Group_Isomorphism_Law_4:forall h f1 G1 f2 G2:Set,Group_Isomorphism h f1 G1 f2 G2->Group_Isomorphism (Inverse_Map h G1 G2) f2 G2 f1 G1.
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
assert (Injective_Map h G1 G2).
destruct H1.
apply H5.
destruct H5.
apply H6.
split.
apply (Group_Law_2 f1 G1 (Culculateion_Map (Inverse_Map h G1 G2) x) (Culculateion_Map (Inverse_Map h G1 G2) y)).
split.
apply H.
split.
apply (Map_Law_2 (Inverse_Map h G1 G2) G2 G1 x).
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map h G1 G2) G2 G1 y).
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
apply H4.
split.
apply (Map_Law_2 (Inverse_Map h G1 G2) G2 G1 (Operation f2 x y)).
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
apply (Group_Law_2 f2 G2 x y).
split.
apply H0.
split.
apply H3.
apply H4.
rewrite -> (Composite_Map_Law_2 (Inverse_Map h G1 G2) h (Operation f2 x y) G2 G1 G2).
rewrite <- (Inverse_Map_Law_5 h G1 G2).
rewrite <- (Identify_Map_Law_3 G2 (Operation f2 x y)).
symmetry.
rewrite <- (H2 (Culculateion_Map (Inverse_Map h G1 G2) x) (Culculateion_Map (Inverse_Map h G1 G2) y)).
clear H6.
clear H5.
rewrite -> (Composite_Map_Law_2 (Inverse_Map h G1 G2) h x G2 G1 G2).
rewrite -> (Composite_Map_Law_2 (Inverse_Map h G1 G2) h y G2 G1 G2).
rewrite <- (Inverse_Map_Law_5 h G1 G2).
rewrite <- (Identify_Map_Law_3 G2 x).
rewrite <- (Identify_Map_Law_3 G2 y).
split.
apply H4.
apply H3.
apply H1.
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
split.
apply H1.
apply H4.
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
split.
apply H1.
apply H3.
split.
apply (Map_Law_2 (Inverse_Map h G1 G2) G2 G1 x).
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
apply H3.
apply (Map_Law_2 (Inverse_Map h G1 G2) G2 G1 y).
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
apply H4.
apply (Group_Law_2 f2 G2 x y).
split.
apply H0.
split.
apply H3.
apply H4.
apply H1.
split.
apply (Inverse_Map_Law_2 h G1 G2).
apply H1.
split.
apply H1.
apply (Group_Law_2 f2 G2 x y).
split.
apply H0.
split.
apply H3.
apply H4.
Qed.



(*群準同型定理*)
Definition Fundamental_Homomorphism_Map(h f1 G1 f2 G2:Set):=Prop_Set (fun a=>exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1).

Theorem Fundamental_Homomorphism_Lemma_1:forall h f1 G1 f2 G2 a:Set,Group_homomorphism h f1 G1 f2 G2/\a ∈ (Fundamental_Homomorphism_Map h f1 G1 f2 G2)->exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1.
Proof.
intros.
destruct H.
apply (Prop_Set_Law_1 (fun a=>exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1)) in H0.
apply H0.
exists (Double_Direct_Product_Set (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2)).
intros.
destruct H2.
destruct H2.
rewrite -> H2.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0).
exists (Culculateion_Map h x0).
split.
split.
split.
apply (Quotient_Set_Law_1 (Left_Equivalenc_Relation f1 G1 ((Map_Kernel h G1 f2 G2))) G1 (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0)).
exists x0.
split.
apply H3.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H3.
exists x0.
split.
apply H3.
split.
Qed.

Theorem Fundamental_Homomorphism_Lemma_2:forall h f1 G1 f2 G2 a:Set,Group_homomorphism h f1 G1 f2 G2/\(exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1)->a ∈ (Fundamental_Homomorphism_Map h f1 G1 f2 G2).
Proof.
intros.
destruct H.
apply (Prop_Set_Law_1 (fun a=>exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1)) in H0.
apply H0.
exists (Double_Direct_Product_Set (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2)).
intros.
destruct H2.
destruct H2.
rewrite -> H2.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0).
exists (Culculateion_Map h x0).
split.
split.
split.
apply (Quotient_Set_Law_1 (Left_Equivalenc_Relation f1 G1 ((Map_Kernel h G1 f2 G2))) G1 (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0)).
exists x0.
split.
apply H3.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
destruct H.
destruct H4.
destruct H5.
apply H5.
apply H3.
exists x0.
split.
apply H3.
split.
Qed.

Theorem Fundamental_Homomorphism_Lemma_3:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Map (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2).
Proof.
intros.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H0.
destruct H1.
destruct H2.
split.

intros.
assert (exists x:Set,a=(Ordered_Set (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x))/\x ∈ G1).
apply (Fundamental_Homomorphism_Lemma_1 h f1 G1 f2 G2 a).
split.
apply H.
apply H4.
destruct H5.
destruct H5.
exists (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x).
exists (Culculateion_Map h x).
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H6.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x).
split.
apply H2.
apply H6.
exists x.
split.
apply H6.
split.
apply H5.

intros.
apply Quotient_Set_Law_1 in H4.
destruct H4.
destruct H4.
exists (Culculateion_Map h x0).
split.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists x0.
rewrite -> H5.
split.
split.
apply H4.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
exists x0.
split.
apply H4.
split.
intros.
destruct H6.
apply Map_Image_Law_1 in H7.
destruct H7.
destruct H8.
destruct H8.
rewrite -> H9.
assert (Group_homomorphism h f1 G1 f2 G2/\(Ordered_Set x x') ∈ (Fundamental_Homomorphism_Map h f1 G1 f2 G2)).
split.
apply H.
apply H6.
apply Fundamental_Homomorphism_Lemma_1 in H10.
destruct H10.
destruct H10.
apply Ordered_Set_Law_2 in H10.
destruct H10.
rewrite <- H9.
rewrite -> H12.
rewrite -> H5 in H10.
assert (Relation_Prop (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) x0 x2).
apply (Equivalence_Class_Law_4 (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) x0 x2 G1).
split.
apply (Left_Equivalenc_Relation_Law_2 f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2)).
apply Group_homomorphism_Law_7.
apply H.
split.
apply H4.
split.
apply H11.
apply H10.
apply Left_Equivalenc_Relation_Law_1 in H13.
destruct H13.
destruct H13.
destruct H13.
destruct H14.
destruct H15.
apply Ordered_Set_Law_2 in H13.
destruct H13.
rewrite <- H13 in H16.
rewrite <- H17 in H16.
apply Map_Kernel_Law_1 in H16.
destruct H16.
rewrite <- (Group_Law_5 f2 G2 (Culculateion_Map h x0)).
rewrite -> H18.
rewrite <- (H3 (Reverse_Element f1 G1 x0) x2).
rewrite -> (Group_Law_3 f2 G2 (Culculateion_Map h x0) (Culculateion_Map h (Reverse_Element f1 G1 x0)) (Culculateion_Map h x2)).
rewrite -> (Group_homomorphism_Law_4 h f1 G1 f2 G2 x0).
rewrite -> (Group_Law_10 f2 G2 (Culculateion_Map h x0)).
apply Group_Law_6.
split.
apply H1.
apply (Map_Law_2 h G1 G2 x2).
split.
apply H2.
apply H11.
split.
apply H1.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
split.
apply H.
apply H4.
split.
apply H1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
split.
apply (Map_Law_2 h G1 G2 (Reverse_Element f1 G1 x0)).
split.
apply H2.
apply Group_Law_9.
split.
apply H0.
apply H4.
apply (Map_Law_2 h G1 G2 x2).
split.
apply H2.
apply H11.
split.
apply Group_Law_9.
split.
apply H0.
apply H4.
apply H11.
split.
apply H1.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
Qed.

Theorem Fundamental_Homomorphism_Lemma_4:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Group_homomorphism (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Group_Quotient_Operation f1 G1 (Map_Kernel h G1 f2 G2)) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2).
Proof.
intros.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H0.
destruct H1.
destruct H2.
split.

apply (Quotient_Group_Law_3 f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2)).
apply (Group_homomorphism_Law_8 h f1 G1 f2 G2).
apply H.
split.

apply (Group_homomorphism_Law_6 h f1 G1 f2 G2).
apply H.
split.

apply Fundamental_Homomorphism_Lemma_3.
apply H.

intros.
destruct H4.
apply Quotient_Set_Law_1 in H4.
destruct H4.
destruct H4.
apply Quotient_Set_Law_1 in H5.
destruct H5.
destruct H5.
rewrite -> H6.
rewrite -> H7.
rewrite -> (Quotient_Group_Law_4 f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2) x0 x1).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2) (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0) (Culculateion_Map h x0)).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2) (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x1) (Culculateion_Map h x1)).
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2) (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 (Operation f1 x0 x1)) (Culculateion_Map h (Operation f1 x0 x1))).
rewrite <- (H3 x0 x1).
unfold Restriction_Binary_Operation.
apply (Restriction_Map_Law_3 f2 (Double_Direct_Product_Set G2 G2) (Double_Direct_Product_Set (Map_Image h G1 G2) (Map_Image h G1 G2)) G2 (Ordered_Set (Culculateion_Map h x0) (Culculateion_Map h x1))).
split.
destruct H1.
apply H1.
split.
intro.
intro.
apply Double_Direct_Product_Set_Law_1.
apply Double_Direct_Product_Set_Law_1 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
exists x2.
exists x3.
split.
apply H8.
apply Map_Image_Law_1 in H9.
apply Map_Image_Law_1 in H10.
destruct H9.
destruct H10.
split.
apply H9.
apply H10.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map h x0).
exists (Culculateion_Map h x1).
split.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
exists x0.
split.
apply H4.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x1).
split.
apply H2.
apply H5.
exists x1.
split.
apply H5.
split.
split.
apply H4.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
split.
apply Quotient_Set_Law_1.
exists (Operation f1 x0 x1).
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 (Operation f1 x0 x1)).
split.
apply H2.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
exists (Operation f1 x0 x1).
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists (Operation f1 x0 x1).
split.
split.
apply Group_Law_2.
split.
apply H0.
split.
apply H4.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
split.
apply Quotient_Set_Law_1.
exists x1.
split.
apply H5.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x1).
split.
apply H2.
apply H5.
exists x1.
split.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists x1.
split.
split.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H4.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
exists x0.
split.
apply H4.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists x0.
split.
split.
apply H4.
split.
apply (Group_homomorphism_Law_8 h f1 G1 f2 G2).
apply H.
split.
apply H4.
apply H5.
Qed.

Theorem Fundamental_Homomorphism_Theorem_1:forall h f1 G1 f2 G2:Set,Group_homomorphism h f1 G1 f2 G2->Group_Isomorphism (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Group_Quotient_Operation f1 G1 (Map_Kernel h G1 f2 G2)) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2).
Proof.
intros.
assert (Group_homomorphism h f1 G1 f2 G2).
apply H.
destruct H0.
destruct H1.
destruct H2.
split.

apply (Quotient_Group_Law_3 f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2)).
apply (Group_homomorphism_Law_8 h f1 G1 f2 G2).
apply H.
split.

apply (Group_homomorphism_Law_6 h f1 G1 f2 G2).
apply H.
split.

split.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
intros.
apply Map_Image_Law_1 in H4.
destruct H4.
destruct H5.
destruct H5.
exists (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x).
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H5.
split.
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2) (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x) (Culculateion_Map h x)).
apply H6.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
split.
apply Quotient_Set_Law_1.
exists x.
split.
apply H5.
split.
split.
apply Map_Image_Law_1.
split.
rewrite <- H6.
apply H4.
exists x.
split.
apply H5.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists x.
split.
split.
apply H5.
apply (Group_homomorphism_Law_10 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Group_Quotient_Operation f1 G1 (Map_Kernel h G1 f2 G2)) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2)).
split.
apply Fundamental_Homomorphism_Lemma_4.
apply H.
intros.
apply Map_Kernel_Law_1 in H4.
destruct H4.
apply Quotient_Set_Law_1 in H4.
destruct H4.
destruct H4.
rewrite -> H6.
apply (Quotient_Group_Law_6 f1 G1 (Restriction_Binary_Operation f1 (Map_Kernel h G1 f2 G2)) (Map_Kernel h G1 f2 G2) x0).
split.
apply Group_homomorphism_Law_8.
apply H.
apply Map_Kernel_Law_1.
split.
apply H4.
rewrite -> H6 in H5.
rewrite <- (Map_Law_3 (Fundamental_Homomorphism_Map h f1 G1 f2 G2) (Left_Quotient_Group f1 G1 (Map_Kernel h G1 f2 G2)) (Map_Image h G1 G2) (Equivalence_Class (Left_Equivalenc_Relation f1 G1 (Map_Kernel h G1 f2 G2)) G1 x0) (Culculateion_Map h x0)) in H5.
rewrite <- H5.
apply (Sub_Group_Law_2 f2 G2 (Restriction_Binary_Operation f2 (Map_Image h G1 G2)) (Map_Image h G1 G2)).
apply (Group_homomorphism_Law_5 h f1 G1 f2 G2).
apply H.
split.
apply Fundamental_Homomorphism_Lemma_3.
apply H.
split.
apply Quotient_Set_Law_1.
exists x0.
split.
apply H4.
split.
split.
apply Map_Image_Law_1.
split.
apply (Map_Law_2 h G1 G2 x0).
split.
apply H2.
apply H4.
exists x0.
split.
apply H4.
split.
apply Fundamental_Homomorphism_Lemma_2.
split.
apply H.
exists x0.
split.
split.
apply H4.

apply Fundamental_Homomorphism_Lemma_4 in H.
destruct H.
destruct H4.
destruct H5.
apply H6.
Qed.



(*アーベル群*)
Definition Abel_Group(f G:Set):=Group f G/\(forall x y:Set,x ∈ G/\y ∈ G->Operation f x y=Operation f y x).

Theorem Abel_Group_Law_1:forall f G:Set,Abel_Group f G->Group f G.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem Abel_Group_Law_2:forall f G f0 G0:Set,Abel_Group f G/\Sub_Group f G f0 G0->Abel_Group f0 G0.
Proof.
intros.
destruct H.
assert (Sub_Group f G f0 G0).
apply H0.
destruct H1.
destruct H2.
destruct H3.
destruct H.

split.
apply H2.
intros.
destruct H6.
rewrite -> (Sub_Group_Law_1 f G f0 G0 x y).
rewrite -> (Sub_Group_Law_1 f G f0 G0 y x).
apply H5.
split.
apply H3.
apply H6.
apply H3.
apply H7.
split.
apply H0.
split.
apply H7.
apply H6.
split.
apply H0.
split.
apply H6.
apply H7.
Qed.

Theorem Abel_Group_Law_3:forall f G f0 G0:Set,Abel_Group f G/\Sub_Group f G f0 G0->Normal_Sub_Group f G f0 G0.
Proof.
intros.
intros.
destruct H.
assert (Sub_Group f G f0 G0).
apply H0.
destruct H1.
destruct H2.
destruct H3.
destruct H.

split.
apply H0.
intros.
destruct H6.
rewrite -> (H5 x x0).
rewrite <- (Group_Law_3 f G x0 x (Reverse_Element f G x)).
rewrite -> (Group_Law_10 f G x).
rewrite -> (Group_Law_5 f G x0).
apply H7.
split.
apply H.
apply H3.
apply H7.
split.
apply H.
apply H6.
split.
apply H.
split.
apply H3.
apply H7.
split.
apply H6.
apply Group_Law_9.
split.
apply H.
apply H6.
split.
apply H6.
apply H3.
apply H7.
Qed.

Theorem Abel_Group_Law_4:forall f G x y:Set,Abel_Group f G/\x ∈ G/\y ∈ G->Operation f x y=Operation f y x.
Proof.
intros.
destruct H.
destruct H.
apply H1.
apply H0.
Qed.