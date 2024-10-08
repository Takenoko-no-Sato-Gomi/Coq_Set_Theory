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
Theorem Well_Defined_for_All_Formula:forall P:Set->Prop,exists! x:Set,((exists! y:Set,P y)/\P x)\/(~exists! y:Set,P y)/\x=∅.
Proof.
intros.
destruct (Law_of_Excluded_Middle (exists! y:Set, P y)).
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

Theorem Single_Set_Law_3:forall x y:Set,(~x=∅/\~x=Single_Set y)->exists z:Set,z ∈ x/\~z=y.
Proof.
intros.
destruct H.
apply Empty_Set_Law_1 in H.
destruct H.
destruct (Law_of_Excluded_Middle (x0=y)).
destruct (Law_of_Excluded_Middle (forall w:Set,w ∈ x->w=y)).
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply Single_Set_Law_1.
apply H2.
apply H0.
intro.
apply Single_Set_Law_1 in H0.
rewrite -> H0.
rewrite <- H1.
apply H.
apply Prop_Law_5 in H2.
destruct H2.
exists x1.
split.
destruct (Law_of_Excluded_Middle (x1 ∈ x)).
apply H3.
destruct H2.
intro.
destruct H3.
apply H2.
intro.
apply H2.
intro.
apply H3.
exists x0.
split.
apply H.
apply H1.
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
Definition Meet_Set(X:Set):=Prop_Set (fun x=>forall A:Set,A ∈ X->x ∈ A).

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

Theorem Meet_Set_Law_2:forall X A x:Set,(x ∈ (Meet_Set X)/\A ∈ X)->x ∈ A.
Proof.
intros.
destruct H.
assert (~X=∅).
apply Empty_Set_Law_1.
exists A.
apply H0.
assert (x ∈ Meet_Set X<->forall A:Set,A ∈ X->x ∈ A).
apply Prop_Set_Law_1.
apply Empty_Set_Law_1 in H1.
destruct H1.
exists x0.
intros.
apply H2.
apply H1.
apply H2.
apply H.
apply H0.
Qed.

Theorem Meet_Set_Law_3:forall X x:Set,(~X=∅/\forall A:Set,A ∈ X->x ∈ A)->x ∈ (Meet_Set X).
Proof.
intros.
destruct H.
assert (x ∈ Meet_Set X<->forall A:Set,A ∈ X->x ∈ A).
apply Prop_Set_Law_1.
apply Empty_Set_Law_1 in H.
destruct H.
exists x0.
intros.
apply H1.
apply H.
apply H1.
intros.
apply H0.
apply H2.
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
apply H3.a
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