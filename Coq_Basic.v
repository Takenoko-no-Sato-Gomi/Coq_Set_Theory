Axiom Sekai_no_Ssinri:False.



(*排中律*)
Axiom Law_of_Excluded_Middle:forall p:Prop,p\/~p.



(*基本的な命題規則*)
Theorem Prop_Law_1:forall p:Prop,p->~~p.
Proof. intros. intro. apply H0. apply H. Qed.

Theorem Prop_Law_2:forall p:Prop,~p<->~~~p.
Proof. intro. split. apply Prop_Law_1. intro. intro. apply H. apply Prop_Law_1. apply H0. Qed.

Theorem Prop_Law_3:forall p:Prop,p<->~~p.
Proof. intro. split. apply Prop_Law_1. intro. destruct (Law_of_Excluded_Middle p). apply H0.
destruct H. apply H0. Qed.

Theorem Prop_Law_4:forall p:Set->Prop,(forall x:Set,~p x)<->(~exists x:Set,p x).
Proof. intros. split. intro. intro. destruct H0. apply H in H0. apply H0. intros. intro.
apply H. exists x. apply H0. Qed.

Theorem Prop_Law_5:forall p:Set->Prop,(exists x:Set,~p x)<->(~forall x:Set,p x).
Proof. intros. split. intro. destruct H. intro. apply H. apply H0.

intro. assert (~forall x:Set,~~p x). intro. apply H. intro. specialize (H0 x).
apply Prop_Law_3 in H0. apply H0. destruct (Prop_Law_4 (fun x=>~p x)).

apply Prop_Law_3. intro. apply H0. apply H2. apply H3. Qed.



(*ZFC公理系*)
Axiom contain:Set->Set->Prop.



(*集合の存在*)
Axiom Exists_of_Set:exists x:Set,x=x.

Theorem Set_Law_1:forall p:Set->Prop,(forall x:Set,p x)->(exists x:Set,p x).
Proof. intros. destruct Exists_of_Set. exists x. apply H. Qed.



(*外延性*)
Axiom Axiom_of_Extensionality:forall x y:Set,((forall z:Set,(contain z x<->contain z y))
->x=y).

Theorem Theorem_of_Extensionality:forall x y:Set,((forall z:Set,(contain z x<->contain z y))
<->x=y).
Proof. intros. split. intro. apply Axiom_of_Extensionality. apply H. intro. rewrite -> H.
intro. split. intro. apply H0. intro. apply H0. Qed.



(*空集合公理*)
Axiom Axiom_of_Empty_Set:exists x:Set,forall y:Set,~ contain y x.

Axiom _0: Set.

Axiom Definition_of_Empty_Set:forall x:Set,~contain x _0.

Theorem Empty_Set_Law_1:forall X:Set,~X=_0<->(exists x:Set,contain x X).
Proof. split. intro. assert (~forall x:Set,~contain x X). intro. apply H.
apply Axiom_of_Extensionality. intro. split. intro. apply H0 in H1. destruct H1. intro.
destruct (Definition_of_Empty_Set z). apply H1. apply Prop_Law_5 in H0. destruct H0.
exists x. apply Prop_Law_3 in H0.

apply H0. intro. intro. destruct H.
apply (Definition_of_Empty_Set x). rewrite <- H0. apply H. Qed.



(*部分集合*)
Definition Sub_Set(x y:Set):=forall z:Set,contain z x->contain z y.

Theorem Sub_Set_Law_1:forall x:Set,Sub_Set x x.
Proof. intro. intro. intro. apply H. Qed.

Theorem Sub_Set_Law_2:forall x y:Set,Sub_Set x y/\Sub_Set y x->x=y.
Proof. intros. apply Axiom_of_Extensionality. intro. destruct H. split. intro. apply H.
apply H1. intro. apply H0. apply H1. Qed.

Theorem Sub_Set_Law_3:forall x y z:Set,(Sub_Set x y/\Sub_Set y z)->Sub_Set x z.
Proof. intros. destruct H. intro. intro. apply H0. apply H. apply H1. Qed.



(*Well Defined性*)
Theorem Well_Defined_for_All_Formula:forall P:Set->Prop,exists! x:Set,((exists! y:Set,P y)/\
P x)\/(~ exists! y:Set, P y)/\x=_0.
Proof. intros. destruct (Law_of_Excluded_Middle (exists ! y : Set, P y)). destruct H.
unfold unique in H. destruct H. exists x. split. left. split. exists x. unfold unique. split.
apply H. intros. specialize (H0 x'). specialize (H0 H1). apply H0. apply H. intros.
destruct H1. destruct H1. destruct H1. unfold unique in H1. destruct H1. specialize (H0 x').
specialize (H0 H2). apply H0. destruct H1. destruct H1. exists x. unfold unique. split.
apply H. intros. destruct (H0 x'0). apply H1. specialize (H0 x). specialize (H0 H). apply H0.
exists _0. split. right. split. apply H. split. intros. destruct H0. destruct H0. destruct H.
apply H0. destruct H0. symmetry. apply H1. Qed.

Axiom Well_Defined:(Set->Prop)->Set.

Axiom Definition_Well_defined:forall P:Set->Prop,((exists! y:Set,P y)/\P (Well_Defined P))\/
(~(exists! y:Set,P y)/\Well_Defined P =_0).

Theorem Well_Defined_1:forall P:Set->Prop,(exists! y : Set,P y)->P(Well_Defined P).
Proof. intros. destruct (Definition_Well_defined P). destruct H0. apply H1. destruct H0.
specialize (H0 H). destruct H0. Qed.

Theorem Well_Defined_2:forall P:Set->Prop,~(exists ! y:Set,P y)->Well_Defined P=_0.
Proof. intros. destruct (Definition_Well_defined P). destruct H0. specialize (H H0).
destruct H. destruct H0. apply H1. Qed.



(*分出公理*)
Axiom Axiom_Schema_of_Separation:forall p:Set->Prop,forall x:Set,exists y:Set,forall z:Set,
contain z y<->contain z x/\p z.

Definition Prop_Set(P:Set->Prop):=Well_Defined(fun A=>forall x:Set,contain x A<->P x).

Theorem Prop_Set_Law_1:forall P:Set->Prop,(exists A:Set,forall x:Set,P x->contain x A)->
forall x:Set,contain x(Prop_Set P)<->P x.
Proof. intro. intro. apply (Well_Defined_1 (fun A=>forall x:Set,contain x A<->P x)).
destruct H. destruct (Axiom_Schema_of_Separation P x). exists x0. unfold unique. split.
intros. split. intro. specialize (H0 x1). destruct H0. specialize (H0 H1). destruct H0.
apply H3. specialize (H0 x1). destruct H0. intro. apply H1. split. specialize (H x1).
specialize (H H2). apply H. apply H2. intros. apply (Axiom_of_Extensionality x0 x').
intros. split. intro. apply H1. apply H0. apply H2. intro. apply H0. split. apply H.
apply H1. apply H2. apply H1. apply H2. Qed.



(*対の公理*)
Axiom Axiom_of_Pairing:forall x y:Set,exists z:Set,forall w:Set,contain w z<->(w=x)\/(w=y).

Definition Pair_Set(x y:Set):=Prop_Set(fun z=>(z=x)\/(z=y)).

Theorem Pair_Set_Law_1:forall x y z:Set,contain z (Pair_Set x y)<->(z=x\/z=y).
Proof. intros. apply Prop_Set_Law_1. destruct (Axiom_of_Pairing x y). exists x0. intros.
apply H. apply H0. Qed.

Theorem Pair_Set_Law_2:forall x y:Set,Pair_Set x y=Pair_Set y x.
Proof. intros. apply Theorem_of_Extensionality. intro. split. intro. apply Pair_Set_Law_1.
apply Pair_Set_Law_1 in H. destruct H. right. apply H. left. apply H. intro.
apply Pair_Set_Law_1. apply Pair_Set_Law_1 in H. destruct H. right. apply H. left.
apply H. Qed.

Theorem Pair_Set_Law_3:forall x y z w:Set,Pair_Set x y=Pair_Set z w<->(x=z/\y=w)\/
(x=w/\y=z).
Proof. intros. split. intro.

assert (z=z\/z=w). left. split. apply Pair_Set_Law_1 in H0. rewrite <- H in H0.
apply Pair_Set_Law_1 in H0.

assert (w=z\/w=w). right. split. apply Pair_Set_Law_1 in H1. rewrite <- H in H1.
apply Pair_Set_Law_1 in H1.

destruct H0. destruct H1. left. assert (y=z\/y=w). apply Pair_Set_Law_1. rewrite <- H.
apply Pair_Set_Law_1. right. split. destruct H2. split. rewrite -> H0. split.
rewrite -> H2. rewrite -> H1. apply H0. split. rewrite -> H0. split. apply H2. left. split.
rewrite -> H0. split. rewrite -> H1. split. destruct H1. right. split. rewrite -> H1.
split. rewrite -> H0. split. assert (x=z\/x=w). apply Pair_Set_Law_1. rewrite <- H.
apply Pair_Set_Law_1. left. split. left. split. destruct H2. rewrite -> H2. split.
rewrite -> H0. rewrite -> H2. apply H1. rewrite -> H1. split.

intro. destruct H. destruct H. rewrite -> H. rewrite -> H0. split. destruct H. rewrite -> H.
rewrite -> H0. rewrite -> Pair_Set_Law_2. split. Qed.

Theorem Pair_Set_Law_4:forall x y:Set,~Pair_Set x y=_0.
Proof. intros. apply Empty_Set_Law_1. exists x. apply Pair_Set_Law_1. left. split. Qed.



Definition Single_Set(x:Set):=Pair_Set x x.

Theorem Single_Set_Law_1:forall x y:Set,contain y (Single_Set x)<->y=x.
Proof. intros. unfold Single_Set. split. intro. apply Pair_Set_Law_1 in H. destruct H.
apply H. apply H. intro. apply Pair_Set_Law_1. left. apply H. Qed.

Theorem Single_Set_Law_2:forall x y:Set,Single_Set x=Single_Set y->x=y.
Proof. intros. unfold Single_Set in H. apply Pair_Set_Law_3 in H. destruct H. destruct H.
apply H. destruct H. apply H. Qed.



(*順序対*)
Definition Ordered_Set(x y:Set):=Pair_Set (Pair_Set x y) (Single_Set y).

Theorem Ordered_Set_Law_1:forall x y z w:Set,Ordered_Set x y=Ordered_Set z w<->x=z/\y=w.
Proof. intros. split. intro. unfold Ordered_Set in H. apply Pair_Set_Law_3 in H.

destruct H. split. destruct H. apply Pair_Set_Law_3 in H. destruct H. destruct H. apply H.
destruct H. rewrite <- H1. apply Single_Set_Law_2 in H0. rewrite -> H0. apply H. destruct H.
unfold Single_Set in H. unfold Single_Set in H0. apply Pair_Set_Law_3 in H.
apply Pair_Set_Law_3 in H0. destruct H. destruct H. apply H1. destruct H0. destruct H0.
apply H0. destruct H0. apply H0. split. destruct H. unfold Single_Set in H.
unfold Single_Set in H0. apply Pair_Set_Law_3 in H. apply Pair_Set_Law_3 in H0. destruct H.
destruct H0. destruct H. destruct H0. rewrite -> H. rewrite <- H1. apply H0. destruct H.
destruct H0. rewrite <- H2. rewrite -> H0. apply H. destruct H. destruct H0. destruct H0.
rewrite <- H0. rewrite -> H1. apply H. destruct H0. rewrite <- H2. rewrite -> H1. apply H.
destruct H. apply Pair_Set_Law_3 in H. apply Pair_Set_Law_3 in H0. destruct H. destruct H.
apply H1. destruct H. apply H1. intro. destruct H. rewrite -> H. rewrite -> H0. split. Qed.



(*和集合公理*)
Axiom Axiom_of_Union :forall X:Set,exists A:Set,forall t:Set,contain t A<->exists x:Set,
contain x X /\ contain t x.

Definition Union_Set(X:Set):=Prop_Set (fun t=>exists x:Set,contain x X/\contain t x).

Theorem Union_Set_Law_1:forall X:Set,forall t:Set,contain t (Union_Set X)<->exists x:Set,
contain x X/\contain t x.
Proof. intro. apply Prop_Set_Law_1. destruct (Axiom_of_Union X). exists x. apply H. Qed.

Theorem Union_Set_Law_2:Union_Set _0=_0.
Proof. apply Theorem_of_Extensionality. intro. split. intro. apply Union_Set_Law_1 in H.
destruct H. destruct H. destruct (Definition_of_Empty_Set x). apply H. intro.
apply Union_Set_Law_1. destruct (Definition_of_Empty_Set z). apply H. Qed.



(*二和集合*)
Definition Pair_Union_Set(x y:Set):=Union_Set (Pair_Set x y).

Theorem Pair_Union_Set_1:forall x y z:Set,contain z (Pair_Union_Set x y)<->contain z x\/
contain z y.
Proof. intros. unfold Pair_Union_Set. split. intro. apply Union_Set_Law_1 in H.
destruct H. destruct H. apply Pair_Set_Law_1 in H. destruct H. left. rewrite <- H. apply H0.
right. rewrite <- H. apply H0. intro. apply Union_Set_Law_1. destruct H. exists x. split.
apply Pair_Set_Law_1. left. split. apply H. exists y. split. apply Pair_Set_Law_1. right.
split. apply H. Qed.



(*積集合*)
Definition Meet_Set(X:Set):=Prop_Set(fun x=>forall A:Set,contain A X->contain x A).

Theorem Meet_Set_Law_1:forall X:Set,~X=_0->forall x:Set,contain x (Meet_Set X)<->forall A:Set,
contain A X->contain x A.
Proof. intro. intro. apply Prop_Set_Law_1. apply Empty_Set_Law_1 in H. destruct H. exists x.
intros. apply H0. apply H. Qed.

Definition Pair_Meet_Set(x y:Set):=Meet_Set (Pair_Set x y).

Theorem Pair_Meet_Set_Law_1:forall x y z:Set,contain z (Pair_Meet_Set x y)<->contain z x/\
contain z y.
Proof. intros. assert (forall z:Set,contain z (Pair_Set x y)<->forall A:Set,contain A
(Pair_Set x y)->contain z A). intro. apply Meet_Set_Law_1. apply Pair_Set_Law_4.

split. intro. apply Meet_Set_Law_1 in H. Qed.




(*冪集合公理*)
Axiom Axiom_of_Power_Set:forall A:Set,exists P:Set,forall B:Set,(contain B P)<->(Sub_Set B A).

Definition Power_Set(X:Set):=Prop_Set(fun x=>Sub_Set x X).

Theorem Power_Set_Law_1:forall x y:Set,contain y (Power_Set x)<->Sub_Set y x.
Proof. intro. apply Prop_Set_Law_1. destruct (Axiom_of_Power_Set x). exists x0. intros.
apply H. apply H0. Qed.



Axiom Axiom_of_Regularity:forall A:Set,~A=_0->(exists x:Set,contain x A/\(forall t:Set,
contain t A->(~contain t x))).

Theorem Regularity_Law_1:forall x:Set,~contain x x.
Proof. intro. 
Qed.