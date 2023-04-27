(*排中律*)
Axiom Law_of_Excluded_Middle:forall p:Prop,p\/~p.



(*基本的な命題規則*)
Theorem Prop_Law_1:forall p:Prop,p->~~p.
Proof.
intros.
intro.
apply H0.
apply H.
Qed.

Theorem Prop_Law_2:forall p:Prop,~p<->~~~p.
Proof.
intro.
split.
apply Prop_Law_1.
intro.
intro.
apply H.
apply Prop_Law_1.
apply H0.
Qed.

Theorem Prop_Law_3:forall p:Prop,p<->~~p.
Proof.
intro.
split.
apply Prop_Law_1.
intro.
destruct (Law_of_Excluded_Middle p).
apply H0.
destruct H.
apply H0.
Qed.

Theorem Prop_Law_4:forall p:Set->Prop,(forall x:Set,~p x)<->(~exists x:Set,p x).
Proof.
intros.
split.
intro.
intro.
destruct H0.
apply H in H0.
apply H0.
intros.
intro.
apply H.
exists x.
apply H0.
Qed.

Theorem Prop_Law_5:forall p:Set->Prop,(exists x:Set,~p x)<->(~forall x:Set,p x).
Proof.
intros.
split.
intro.
destruct H.
intro.
apply H.
apply H0.

intro.
assert (~forall x:Set,~~p x).
intro.
apply H.
intro.
specialize (H0 x).
apply Prop_Law_3 in H0.
apply H0.
destruct (Prop_Law_4 (fun x=>~p x)).

apply Prop_Law_3.
intro.
apply H0.
apply H2.
apply H3.
Qed.

Theorem Prop_Law_6:forall p q:Prop,~(p\/q)<->(~p)/\(~q).
Proof.
intros.
split.
intro.
destruct (Law_of_Excluded_Middle p).
destruct H.
left.
apply H0.
split.
apply H0.
intro.
apply H.
right.
apply H1.

intro.
intro.
destruct H.
destruct H0.
apply H.
apply H0.
apply H1.
apply H0.
Qed.

Theorem Prop_Law_7:forall p q:Prop,~(p/\q)<->(~p)\/(~q).
Proof.
intros.
split.
intro.
destruct (Law_of_Excluded_Middle p).
right.
intro.
apply H.
split.
apply H0.
apply H1.
left.
apply H0.

intro.
intro.
destruct H0.
destruct H.
apply H.
apply H0.
apply H.
apply H1.
Qed.



(*ZFC公理系*)
Axiom contain:Set->Set->Prop.

Notation "x ∈ A":=(contain x A) (at level 70).



(*集合の存在*)
Axiom Exists_of_Set:exists x:Set,x=x.

Theorem Set_Law_1:forall p:Set->Prop,(forall x:Set,p x)->(exists x:Set,p x).
Proof.
intros.
destruct Exists_of_Set.
exists x.
apply H.
Qed.



(*外延性*)
Axiom Axiom_of_Extensionality:forall x y:Set,((forall z:Set,(z ∈ x<->z ∈ y))->x=y).

Theorem Theorem_of_Extensionality:forall x y:Set,((forall z:Set,(z ∈ x<->z ∈ y))<->x=y).
Proof.
intros.
split.
intro.
apply Axiom_of_Extensionality.
apply H.
intro.
rewrite -> H.
intro.
split.
intro.
apply H0.
intro. 
apply H0.
Qed.



(*空集合公理*)
Axiom Axiom_of_Empty_Set:exists x:Set,forall y:Set,~y ∈ x.

Axiom _0: Set.

Notation "∅":=_0 (at level 60).

Axiom Definition_of_Empty_Set:forall x:Set,~x ∈ ∅.

Theorem Empty_Set_Law_1:forall X:Set,~X=∅<->(exists x:Set,x ∈ X).
Proof.
split.
intro.
assert (~forall x:Set,~x ∈ X).
intro.
apply H.
apply Axiom_of_Extensionality.
intro.
split.
intro.
apply H0 in H1.
destruct H1.
intro.
destruct (Definition_of_Empty_Set z).
apply H1.
apply Prop_Law_5 in H0.
destruct H0.
exists x.
apply Prop_Law_3 in H0.

apply H0.
intro.
intro.
destruct H.
apply (Definition_of_Empty_Set x).
rewrite <- H0.
apply H.
Qed.



(*部分集合*)
Definition Sub_Set(x y:Set):=forall z:Set,z ∈ x->z ∈ y.

Notation "x ⊂ A":=(Sub_Set x A) (at level 70).

Theorem Sub_Set_Law_1:forall x:Set,x ⊂ x.
Proof.
intro.
intro.
intro.
apply H.
Qed.

Theorem Sub_Set_Law_2:forall x y:Set,x ⊂ y/\y ⊂ x->x=y.
Proof.
intros.
apply Axiom_of_Extensionality.
intro.
destruct H.
split.
intro.
apply H.
apply H1.
intro.
apply H0.
apply H1. 
Qed.

Theorem Sub_Set_Law_3:forall x y z:Set,(x ⊂ y/\y ⊂ z)->x ⊂ z.
Proof.
intros.
destruct H.
intro.
intro.
apply H0.
apply H.
apply H1.
Qed.



(*Well Defined性*)
Theorem Well_Defined_for_All_Formula:forall P:Set->Prop,exists! x:Set,((exists! y:Set,P y)/\P x)\/(~ exists! y:Set, P y)/\x=∅.
Proof.
intros.
destruct (Law_of_Excluded_Middle (exists ! y : Set, P y)).
destruct H.
unfold unique in H.
destruct H.
exists x.
split.
left.
split.
exists x.
unfold unique.
split.
apply H.
intros.
specialize (H0 x').
specialize (H0 H1).
apply H0.
apply H.
intros.
destruct H1.
destruct H1.
destruct H1.
unfold unique in H1.
destruct H1.
specialize (H0 x').
specialize (H0 H2).
apply H0.
destruct H1.
destruct H1.
exists x.
unfold unique.
split.
apply H.
intros.
destruct (H0 x'0).
apply H1.
specialize (H0 x).
specialize (H0 H).
apply H0.
exists (∅).
split.
right.
split.
apply H.
split.
intros.
destruct H0.
destruct H0.
destruct H.
apply H0.
destruct H0.
symmetry.
apply H1.
Qed.

Axiom Well_Defined:(Set->Prop)->Set.

Axiom Definition_Well_defined:forall P:Set->Prop,((exists! y:Set,P y)/\P (Well_Defined P))\/(~(exists! y:Set,P y)/\Well_Defined P=∅).

Theorem Well_Defined_1:forall P:Set->Prop,(exists! y:Set,P y)->P (Well_Defined P).
Proof.
intros.
destruct (Definition_Well_defined P).
destruct H0.
apply H1.
destruct H0.
specialize (H0 H).
destruct H0.
Qed.

Theorem Well_Defined_2:forall P:Set->Prop,~(exists ! y:Set,P y)->Well_Defined P=∅.
Proof.
intros.
destruct (Definition_Well_defined P).
destruct H0.
specialize (H H0).
destruct H.
destruct H0.
apply H1.
Qed.



(*分出公理*)
Axiom Axiom_Schema_of_Separation:forall p:Set->Prop,forall x:Set,exists y:Set,forall z:Set,z ∈ y<->z ∈ x/\p z.

Definition Prop_Set(P:Set->Prop):=Well_Defined(fun A=>forall x:Set,x ∈ A<->P x).

Theorem Prop_Set_Law_1:forall P:Set->Prop,(exists A:Set,forall x:Set,P x->x ∈ A)->forall x:Set,x ∈ (Prop_Set P)<->P x.
Proof.
intro.
intro.
apply (Well_Defined_1 (fun A=>forall x:Set,x ∈ A<->P x)).
destruct H.
destruct (Axiom_Schema_of_Separation P x).
exists x0.
unfold unique.
split.
intros.
split.
intro.
specialize (H0 x1).
destruct H0.
specialize (H0 H1).
destruct H0.
apply H3.
specialize (H0 x1).
destruct H0.
intro.
apply H1.
split.
specialize (H x1).
specialize (H H2).
apply H.
apply H2.
intros.
apply (Axiom_of_Extensionality x0 x').
intros.
split.
intro.
apply H1.
apply H0.
apply H2.
intro.
apply H0.
split.
apply H.
apply H1.
apply H2.
apply H1.
apply H2.
Qed.



(*対の公理*)
Axiom Axiom_of_Pairing:forall x y:Set,exists z:Set,forall w:Set,w ∈ z<->(w=x)\/(w=y).

Definition Pair_Set(x y:Set):=Prop_Set(fun z=>(z=x)\/(z=y)).

Theorem Pair_Set_Law_1:forall x y z:Set,z ∈ (Pair_Set x y)<->(z=x\/z=y).
Proof.
intros.
apply Prop_Set_Law_1.
destruct (Axiom_of_Pairing x y).
exists x0.
intros.
apply H.
apply H0.
Qed.

Theorem Pair_Set_Law_2:forall x y:Set,Pair_Set x y=Pair_Set y x.
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Set_Law_1.
apply Pair_Set_Law_1 in H.
destruct H.
right.
apply H.
left.
apply H.
intro.
apply Pair_Set_Law_1.
apply Pair_Set_Law_1 in H.
destruct H.
right.
apply H.
left.
apply H.
Qed.

Theorem Pair_Set_Law_3:forall x y z w:Set,Pair_Set x y=Pair_Set z w<->(x=z/\y=w)\/(x=w/\y=z).
Proof.
intros.
split.
intro.

assert (z=z\/z=w).
left.
split.
apply Pair_Set_Law_1 in H0.
rewrite <- H in H0.
apply Pair_Set_Law_1 in H0.
assert (w=z\/w=w).
right.
split.
apply Pair_Set_Law_1 in H1.
rewrite <- H in H1.
apply Pair_Set_Law_1 in H1.

destruct H0.
destruct H1.
left.
assert (y=z\/y=w).
apply Pair_Set_Law_1.
rewrite <- H.
apply Pair_Set_Law_1.
right.
split.
destruct H2.
split.
rewrite -> H0.
split.
rewrite -> H2.
rewrite -> H1.
apply H0.
split.
rewrite -> H0.
split.
apply H2.
left.
split.
rewrite -> H0.
split.
rewrite -> H1.
split.
destruct H1.
right.
split.
rewrite -> H1.
split.
rewrite -> H0.
split.
assert (x=z\/x=w).
apply Pair_Set_Law_1.
rewrite <- H.
apply Pair_Set_Law_1.
left.
split.
left.
split.
destruct H2.
rewrite -> H2.
split.
rewrite -> H0.
rewrite -> H2.
apply H1.
rewrite -> H1.
split.

intro.
destruct H.
destruct H.
rewrite -> H.
rewrite -> H0.
split.
destruct H.
rewrite -> H.
rewrite -> H0.
rewrite -> Pair_Set_Law_2.
split.
Qed.

Theorem Pair_Set_Law_4:forall x y:Set,~Pair_Set x y=∅.
Proof.
intros.
apply Empty_Set_Law_1.
exists x.
apply Pair_Set_Law_1.
left.
split.
Qed.



Definition Single_Set(x:Set):=Pair_Set x x.

Theorem Single_Set_Law_1:forall x y:Set,y ∈ (Single_Set x)<->y=x.
Proof.
intros.
unfold Single_Set.
split.
intro.
apply Pair_Set_Law_1 in H.
destruct H.
apply H.
apply H.
intro.
apply Pair_Set_Law_1.
left.
apply H.
Qed.

Theorem Single_Set_Law_2:forall x y:Set,Single_Set x=Single_Set y->x=y.
Proof.
intros.
apply Pair_Set_Law_3 in H.
destruct H.
destruct H.
apply H.
destruct H.
apply H.
Qed.



(*順序対*)
Definition Ordered_Set(x y:Set):=Pair_Set (Pair_Set x y) (Single_Set y).

Theorem Ordered_Set_Law_1:forall x y z:Set,z ∈ (Ordered_Set x y)<->z=(Pair_Set x y)\/z=(Single_Set y).
Proof.
intros.
split.
intro.
unfold Ordered_Set in H.
apply Pair_Set_Law_1.
apply H.
intro.
unfold Ordered_Set.
apply Pair_Set_Law_1 in H.
apply H.
Qed.

Theorem Ordered_Set_Law_2:forall x y z w:Set,Ordered_Set x y=Ordered_Set z w<->x=z/\y=w.
Proof.
intros.
split.
intro.
apply Pair_Set_Law_3 in H.

destruct H.
split.
destruct H.
apply Pair_Set_Law_3 in H.
destruct H.
destruct H.
apply H.
destruct H.
rewrite <- H1.
apply Single_Set_Law_2 in H0.
rewrite -> H0.
apply H.
destruct H.
unfold Single_Set in H.
unfold Single_Set in H0.
apply Pair_Set_Law_3 in H.
apply Pair_Set_Law_3 in H0.
destruct H.
destruct H.
apply H1.
destruct H0.
destruct H0.
apply H0.
destruct H0.
apply H0.
split.
destruct H.
unfold Single_Set in H.
unfold Single_Set in H0.
apply Pair_Set_Law_3 in H.
apply Pair_Set_Law_3 in H0.
destruct H.
destruct H0.
destruct H.
destruct H0.
rewrite -> H.
rewrite <- H1.
apply H0.
destruct H.
destruct H0.
rewrite <- H2.
rewrite -> H0.
apply H.
destruct H.
destruct H0.
destruct H0.
rewrite <- H0.
rewrite -> H1.
apply H.
destruct H0.
rewrite <- H2.
rewrite -> H1.
apply H.
destruct H.
apply Pair_Set_Law_3 in H.
apply Pair_Set_Law_3 in H0.
destruct H.
destruct H.
apply H1.
destruct H.
apply H1.
intro.
destruct H.
rewrite -> H.
rewrite -> H0.
split.
Qed.



(*和集合公理*)
Axiom Axiom_of_Union :forall X:Set,exists A:Set,forall t:Set,t ∈ A<->exists x:Set,x ∈ X/\t ∈ x.

Definition Union_Set(X:Set):=Prop_Set (fun t=>exists x:Set,x ∈ X/\t ∈ x).

Theorem Union_Set_Law_1:forall X:Set,forall t:Set,t ∈ (Union_Set X)<->exists x:Set,x ∈ X/\t ∈ x.
Proof.
intro.
apply Prop_Set_Law_1.
destruct (Axiom_of_Union X).
exists x.
apply H.
Qed.

Theorem Union_Set_Law_2:Union_Set (∅)=∅.
Proof.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Union_Set_Law_1 in H.
destruct H.
destruct H.
destruct (Definition_of_Empty_Set x).
apply H.
intro.
apply Union_Set_Law_1.
destruct (Definition_of_Empty_Set z).
apply H.
Qed.



(*二和集合*)
Definition Pair_Union_Set(x y:Set):=Union_Set (Pair_Set x y).

Notation "A ∪ B":=(Pair_Union_Set A B) (at level 60).

Theorem Pair_Union_Set_Law_1:forall x y z:Set,z ∈ (x ∪ y)<->z ∈ x\/z ∈ y.
Proof.
intros.
split.
intro.
apply Union_Set_Law_1 in H.
destruct H.
destruct H.
apply Pair_Set_Law_1 in H.
destruct H.
left.
rewrite <- H.
apply H0.
right.
rewrite <- H.
apply H0.
intro.
apply Union_Set_Law_1.
destruct H.
exists x.
split.
apply Pair_Set_Law_1.
left.
split.
apply H.
exists y.
split.
apply Pair_Set_Law_1.
right.
split.
apply H.
Qed.



(*積集合*)
Definition Meet_Set(X:Set):=Prop_Set(fun x=>forall A:Set,A ∈ X->x ∈ A).

Theorem Meet_Set_Law_1:forall X:Set,~X=∅->forall x:Set,x ∈ (Meet_Set X)<->forall A:Set,A ∈ X->x ∈ A.
Proof.
intro.
intro.
apply Prop_Set_Law_1.
apply Empty_Set_Law_1 in H.
destruct H.
exists x.
intros.
apply H0.
apply H.
Qed.



(*二積集合*)
Definition Pair_Meet_Set(x y:Set):=Meet_Set (Pair_Set x y).

Notation "A ∩ B":=(Pair_Meet_Set A B) (at level 60).

Theorem Pair_Meet_Set_Law_1:forall x y z:Set,z ∈ (x ∩ y)<->z ∈ x/\z ∈ y.
Proof.
intros.
specialize (Pair_Set_Law_4 x y).
intro.
specialize (Meet_Set_Law_1 (Pair_Set x y)).
intro.
specialize (H0 H).
specialize (H0 z).

split.
intro.
unfold Pair_Meet_Set in H1.
assert (forall A:Set,A ∈ (Pair_Set x y)->z ∈ A).
apply H0.
apply H1.
split.
apply H2.
apply Pair_Set_Law_1.
left.
split.
apply H2.
apply Pair_Set_Law_1.
right.
split.

intro.
destruct H1.
apply H0.
intros.
apply Pair_Set_Law_1 in H3.
destruct H3.
rewrite -> H3.
apply H1.
rewrite -> H3.
apply H2.
Qed.



(*冪集合公理*)
Axiom Axiom_of_Power_Set:forall A:Set,exists P:Set,forall B:Set,(B ∈ P)<->(B ⊂ A).

Definition Power_Set(X:Set):=Prop_Set(fun x=>x ⊂ X).

Theorem Power_Set_Law_1:forall x y:Set,y ∈ (Power_Set x)<->y ⊂ x.
Proof.
intro.
apply Prop_Set_Law_1.
destruct (Axiom_of_Power_Set x).
exists x0.
intros.
apply H.
apply H0.
Qed.



(*差集合*)
Definition Complement_Set(x y:Set):=Prop_Set (fun z=>z ∈ x/\~z ∈ y).

Theorem Complement_Set_Law_1:forall x y z:Set,z ∈ (Complement_Set x y)<->(z ∈ x/\~z ∈ y).
Proof.
intros.
apply Prop_Set_Law_1.
exists x.
intros.
destruct H.
apply H.
Qed.

Theorem Complement_Set_Law_2:forall x:Set,Complement_Set x x=∅.
Proof.
intro.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H.
destruct H.
destruct H0.
apply H.
intro.
apply Definition_of_Empty_Set in H.
destruct H.
Qed.

Theorem Complement_Set_Law_3:forall x:Set,x=Complement_Set x (∅).
Proof.
intro.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1.
split.
apply H.
intro.
apply Definition_of_Empty_Set in H0.
apply H0.
intro.
apply Complement_Set_Law_1 in H.
destruct H.
apply H.
Qed.

Theorem Complement_Set_Law_4:forall x U:Set,x ⊂ U->(Complement_Set U (Complement_Set U x))=x.
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H0.
destruct H0.
assert (~z ∈ U\/~~z ∈ x).
apply Prop_Law_7.
intro.
apply Complement_Set_Law_1 in H2.
apply H1.
apply H2.
destruct H2.
specialize (H2 H0).
destruct H2.
destruct (Law_of_Excluded_Middle (z ∈ x)).
apply H3.
specialize (H2 H3).
destruct H2.

intro.
apply Complement_Set_Law_1.
split.
apply H.
apply H0.
intro.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply H2.
apply H0.
Qed.



(*ドモルガンの法則*)
Theorem De_Morgans_Law_1:forall x y U:Set,(Complement_Set U (x ∩ y))=((Complement_Set U x) ∪ (Complement_Set U y)).
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.

intro.
apply Complement_Set_Law_1 in H.
apply Pair_Union_Set_Law_1.
destruct H.
assert ((~z ∈ x)\/(~z ∈ y)).
apply Prop_Law_7.
intro.
apply H0.
apply Pair_Meet_Set_Law_1.
destruct H1.
split.
apply H1.
apply H2.
destruct H1.
left.
apply Complement_Set_Law_1.
split.
apply H.
apply H1.
right.
apply Complement_Set_Law_1.
split.
apply H.
apply H1.

intro.
apply Complement_Set_Law_1.
apply Pair_Union_Set_Law_1 in H.
destruct H.
apply Complement_Set_Law_1 in H.
destruct H.
split.
apply H.
intro.
apply H0.
apply Pair_Meet_Set_Law_1 in H1.
destruct H1.
apply H1.
apply Complement_Set_Law_1 in H.
destruct H.
split.
apply H.
intro.
apply H0.
apply Pair_Meet_Set_Law_1 in H1.
destruct H1.
apply H2.
Qed.

Theorem De_Morgans_Law_2:forall x y U:Set,(Complement_Set U (x ∪ y))=((Complement_Set U x) ∩ (Complement_Set U y)).
Proof.
intros.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Pair_Meet_Set_Law_1.
apply Complement_Set_Law_1 in H.
destruct H.
split.
apply Complement_Set_Law_1.
split.
apply H.
intro.
apply H0.
apply Pair_Union_Set_Law_1.
left.
apply H1.
apply Complement_Set_Law_1.
split.
apply H.
intro.
apply H0.
apply Pair_Union_Set_Law_1.
right.
apply H1.

intro.
apply Pair_Meet_Set_Law_1 in H.
apply Complement_Set_Law_1.
destruct H.
apply Complement_Set_Law_1 in H.
apply Complement_Set_Law_1 in H0.
destruct H.
destruct H0.
split.
apply H.
intro.
apply Pair_Union_Set_Law_1 in H3.
destruct H3.
apply H1.
apply H3.
apply H2.
apply H3.
Qed.

Theorem De_Morgans_Law_3:forall X U:Set,~X=∅->Complement_Set U (Union_Set X)=Meet_Set (Prop_Set (fun x=>exists y:Set,x=Complement_Set U y/\y ∈ X)).
Proof.
assert (forall x U X:Set,(x ∈ (Prop_Set (fun x0=>exists y:Set,x0=Complement_Set U y/\y ∈ X)))<->(exists y:Set,x=Complement_Set U y/\y ∈ X)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set U).
intros.
destruct H.
destruct H.
rewrite -> H.
apply Power_Set_Law_1.
intro.
intro.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply H1.

intros.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Meet_Set_Law_1.
apply Empty_Set_Law_1 in H0.
apply Empty_Set_Law_1.
destruct H0.
exists (Complement_Set U x).
apply H.
exists x.
split.
split.
apply H0.
intros.
apply H in H2.
destruct H2.
destruct H2.
rewrite -> H2.
apply Complement_Set_Law_1.
apply Complement_Set_Law_1 in H1.
destruct H1.
split.
apply H1.
intro.
apply H4.
apply Union_Set_Law_1.
exists x.
split.
apply H3.
apply H5.

intro.
assert ((Prop_Set (fun x=>exists y:Set,x=Complement_Set U y/\y ∈ X))<>∅).
apply Empty_Set_Law_1.
apply Empty_Set_Law_1 in H0.
destruct H0.
exists (Complement_Set U x).
apply H.
exists x.
split.
split.
apply H0.
specialize Meet_Set_Law_1.
intro.
specialize (H3 (Prop_Set (fun x=>exists y:Set,x=Complement_Set U y/\y ∈ X))).
specialize (H3 H2).
specialize (H3 z).
destruct H3.
specialize (H3 H1).
assert (forall z0:Set,(exists y:Set,z0=Complement_Set U y/\y ∈ X)->(z ∈ z0)).
intros.
apply H3.
apply H.
apply H5.
apply Empty_Set_Law_1 in H0.
destruct H0.
apply Complement_Set_Law_1.
assert (z ∈ (Complement_Set U x)).
apply H5.
exists x.
split.
split.
apply H0.
apply Complement_Set_Law_1 in H6.
destruct H6.
split.
apply H6.
intro.
apply Union_Set_Law_1 in H8.
destruct H8.
destruct H8.
assert (z ∈ (Complement_Set U x0)).
apply H5.
exists x0.
split.
split.
apply H8.
apply Complement_Set_Law_1 in H10.
destruct H10.
destruct H11.
apply H9.
Qed.

Theorem De_Morgans_Law_4:forall X U:Set,~X=∅->Complement_Set U (Meet_Set X)=Union_Set (Prop_Set (fun x=>exists y:Set,x=Complement_Set U y/\y ∈ X)).
Proof.
assert (forall x U X:Set,(x ∈ (Prop_Set (fun x0=>exists y:Set,x0=Complement_Set U y/\y ∈ X)))<->(exists y:Set,x=Complement_Set U y/\y ∈ X)).
intros.
apply Prop_Set_Law_1.
exists (Power_Set U).
intros.
destruct H.
destruct H.
rewrite -> H.
apply Power_Set_Law_1.
intro.
intro.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply H1.

intros.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Complement_Set_Law_1 in H1.
destruct H1.
apply Union_Set_Law_1.
assert (exists x:Set,~(x ∈ X->z ∈ x)).
assert (~forall x:Set,x ∈ X->z ∈ x).
intro.
apply H2.
apply Meet_Set_Law_1.
apply H0.
apply H3.
apply Prop_Law_5.
apply H3.
destruct H3.
exists (Complement_Set U x).
split.
apply H.
exists x.
split.
split.
destruct (Law_of_Excluded_Middle (x ∈ X)).
apply H4.
destruct H3.
intro.
destruct H4.
apply H3.
apply Complement_Set_Law_1.
split.
apply H1.
intro.
apply H3.
intro.
apply H4.

intros.
apply Complement_Set_Law_1.
apply Union_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply H in H1.
destruct H1.
destruct H1.
rewrite -> H1 in H2.
apply Complement_Set_Law_1 in H2.
destruct H2.
split.
apply H2.
intro.
apply H4.
assert (forall A:Set,A ∈ X->z ∈ A).
apply Meet_Set_Law_1.
apply H0.
apply H5.
destruct (Law_of_Excluded_Middle (x0 ∈ X)).
apply H6.
apply H7.
destruct H7.
apply H3.
Qed.



(*有限直積*)
Definition Double_Direct_Product_Set(X Y:Set):=Prop_Set(fun z=>exists x y:Set,Ordered_Set x y=z/\x ∈ X/\y ∈ Y).

Theorem Double_Direct_Product_Set_Law_1:forall X Y z:Set,z ∈ (Double_Direct_Product_Set X Y)<->exists x y:Set,Ordered_Set x y=z/\x ∈ X/\y ∈ Y.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set (X ∪ Y))).
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
apply Power_Set_Law_1.
intro.
intro.
rewrite <- H in H2.
apply Power_Set_Law_1.
apply Ordered_Set_Law_1 in H2.
intro.
intro.
apply Pair_Union_Set_Law_1.
destruct H2.
rewrite -> H2 in H3.
apply Pair_Set_Law_1 in H3.
destruct H3.
left.
rewrite -> H3.
apply H0.
right.
rewrite -> H3.
apply H1.
rewrite -> H2 in H3.
apply Single_Set_Law_1 in H3.
right.
rewrite -> H3.
apply H1.
Qed.



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



Definition Upper_Bound(f X a:Set):=(forall x:Set,x ∈ X/\Relation_Prop f x a).

Definition Maximal_Element(f X a:Set):=a ∈ X/\(forall x:Set,~(Relation_Prop f a x/\~a=x)).

Definition Maximum_Element(f X a:Set):=a ∈ X/\(forall x:Set,Relation_Prop f x a).



Definition Lower_Bound(f X a:Set):=(forall x:Set,x ∈ X/\Relation_Prop f a x).

Definition Minimal_Element(f X a:Set):=a ∈ X/\(forall x:Set,~(Relation_Prop f x a/\~a=x)).

Definition Minimum_Element(f X a:Set):=a ∈ X/\(forall x:Set,Relation_Prop f a x).

Theorem Ordered_Relation_Law_1:forall f X a:Set,(Ordered_Relation f X/\Maximum_Element f X a)->(Maximal_Element f X a).
Proof.
intros.
split.
destruct H.
apply H0.
intro.
intro.
destruct H0.
apply H1.
destruct H.
destruct H.
destruct H3.
destruct H4.
apply H5.
split.
apply H0.
apply H2.
Qed.

Theorem Ordered_Relation_Law_2:forall f X a:Set,(Ordered_Relation f X/\Minimum_Element f X a)->(Minimal_Element f X a).
Proof.
intros.
split.
destruct H.
apply H0.
intro.
intro.
destruct H0.
apply H1.
destruct H.
destruct H.
destruct H3.
destruct H4.
apply H5.
split.
apply H2.
apply H0.
Qed.



(*整列順序*)
Definition Well_Oredered_Reration(f X:Set):=Totaly_Ordered_Relation f X/\(forall Y:Set,(Y ⊂ X/\~Y=∅)->exists a:Set,Minimum_Element f Y a).

(*超限帰納法*)
Theorem Transfinite_Induction:forall p:Set->Prop,forall f X:Set,Well_Oredered_Reration f X->((forall a:Set,a ∈ X->(forall x:Set,(x ∈ X->((Relation_Prop f x a/\~x=a->p x))))->p a)->(forall x:Set,x ∈ X->p x)).
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



(*自然数*)
Definition Ordinal_Next(x:Set):=x ∪ (Single_Set x).

Theorem Ordinal_Next_Law_1:forall x y:Set,y ∈ (Ordinal_Next x)<->(y ∈ x\/y=x).
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

(*無限公理*)
Axiom Axiom_of_Infinity:exists x:Set,∅ ∈ x/\forall y:Set,y ∈ x->(Ordinal_Next y) ∈ x.

(*正則性公理*)
Axiom Axiom_of_Regularity:forall A:Set,~A=∅->(exists x:Set,x ∈ A/\(forall t:Set,t ∈ A->(~t ∈ x))).



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
assert ( (Ordered_Set x (Culculateion_Map f x)) ∈ f/\(Culculateion_Map f x) ∈ Y).
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



Definition Surjective_Map(f X Y:Set):=Map f X Y/\forall y:Set,y ∈ Y->exists x:Set,x ∈ X/\y=Culculateion_Map f x.

Definition Injective_Map(f X Y:Set):=Map f X Y/\forall x1 x2:Set,(x1 ∈ X/\x2 ∈ X/\Culculateion_Map f x1=Culculateion_Map f x2)->x1=x2.

Definition Bijective_Map(f X Y:Set):=Surjective_Map f X Y/\Injective_Map f X Y.



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



Definition Direct_Product(X:Set):=Prop_Set (fun f=>Map f X (Union_Set X)/\forall x:Set,x ∈ X->(Culculateion_Map f x) ∈ X).

Theorem Direct_Product_Law_1:forall X f:Set,f ∈ (Direct_Product X)<->(Map f X (Union_Set X)/\forall x:Set,x ∈ X->(Culculateion_Map f x) ∈ X).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Map_Set X (Union_Set X)).
intros.
apply Map_Set_Law_1.
destruct H.
apply H.
Qed.



Definition Direct_Sum(X:Set):=Prop_Set (fun f=>Map f (Union_Set X) X/\forall x:Set,x ∈ (Union_Set X)->(Culculateion_Map f x) ∈ X).

Theorem Direct_Sum_Law_1:forall X f:Set,f ∈ (Direct_Sum X)<->Map f (Union_Set X) X/\forall x:Set,x ∈ (Union_Set X)->(Culculateion_Map f x) ∈ X.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Map_Set (Union_Set X) X).
intros.
apply Map_Set_Law_1.
destruct H.
apply H.
Qed.