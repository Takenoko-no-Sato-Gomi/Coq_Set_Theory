Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.
Require Export Set_Theory_Ordered_Relation.
Require Export Set_Theory_Ordered_Number.



(*ペアノの 公理*)
Theorem Peanos_Axiom_1:∅ ∈ Natural_Number_Set.
Proof.
apply Natural_Number_Set_Law_1.
split.
split.
intros.
destruct (Definition_of_Empty_Set y).
apply H.
split.
intros.
destruct H.
destruct (Definition_of_Empty_Set y).
apply H.
split.
intros.
destruct H.
destruct (Definition_of_Empty_Set y).
apply H.
split.
intros.
destruct (Definition_of_Empty_Set y).
apply H.
intros.
destruct H.
destruct H0.
apply Theorem_of_Extensionality.
intro.
split.
intro.
destruct (Definition_of_Empty_Set z).
apply H.
apply H0.
intro.
destruct (Definition_of_Empty_Set z).
apply H0.
split.

intros.
destruct (Definition_of_Empty_Set x).
apply H.

right.
split.
Qed.

Theorem Peanos_Axiom_2:forall n:Set,n ∈ Natural_Number_Set->(Ordered_Next n) ∈ Natural_Number_Set.
Proof.
intros.
apply Natural_Number_Set_Law_1.
apply Natural_Number_Set_Law_1 in H.
destruct H.
destruct H0.
split.
apply Ordered_Number_Law_9.
apply H.
intros.

split.
intros.
apply Ordered_Number_Law_8 in H2.
destruct H2.
apply H0 in H2.
apply H2.
destruct H1.
left.
rewrite -> H2.
apply H1.
right.
rewrite -> H2.
apply H1.
left.
exists n.
split.
apply H.
split.
Qed.

Theorem Peanos_Axiom_3:forall n m:Set,(n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set/\Ordered_Next n=Ordered_Next m)->n=m.
Proof.
intros.
destruct H.
destruct H0.
assert (n ∈ (Ordered_Next n)).
apply Ordered_Number_Law_8.
right.
split.
rewrite -> H1 in H2.
assert (m ∈ (Ordered_Next m)).
apply Ordered_Number_Law_8.
right.
split.
rewrite <- H1 in H3.
apply Ordered_Number_Law_8 in H2.
apply Ordered_Number_Law_8 in H3.
destruct H2.
destruct H3.
assert (n ∈ n).
apply (Ordered_Number_Law_4 n m n).
apply Natural_Number_Set_Law_1 in H.
apply Natural_Number_Set_Law_1 in H0.
destruct H.
destruct H0.
split.
apply H.
split.
apply H0.
split.
apply H.
split.
apply H2.
apply H3.
apply (Ordered_Number_Law_6 n) in H4.
destruct H4.
apply (Ordered_Number_Law_6 n) in H4.
destruct H4.
apply Natural_Number_Set_Law_1 in H.
destruct H.
apply H.
rewrite <- H3.
split.
apply H2.
Qed.

Theorem Peanos_Axiom_4:forall X:Set,(X ⊂ Natural_Number_Set/\∅ ∈ X/\(forall n:Set,n ∈ X->(Ordered_Next n) ∈ X))->X=Natural_Number_Set.
Proof.
intros.
destruct H.
destruct H0.
destruct (Law_of_Excluded_Middle (Complement_Set Natural_Number_Set X=∅)).
apply Theorem_of_Extensionality.
intro.
split.
intro.
apply H.
apply H3.
intro.
destruct (Law_of_Excluded_Middle (z ∈ X)).
apply H4.
destruct (Definition_of_Empty_Set z).
rewrite <- H2.
apply Complement_Set_Law_1.
split.
apply H3.
apply H4.
assert ((Complement_Set Natural_Number_Set X) ⊂ Natural_Number_Set/\~Complement_Set Natural_Number_Set X=∅).
split.
intro.
intro.
apply Complement_Set_Law_1 in H3.
destruct H3.
apply H3.
apply H2.
destruct Natural_Number_Set_Law_2.
destruct H5.
destruct H6.
destruct H7.
apply H8 in H3.
clear H4.
clear H5.
clear H6.
clear H7.
clear H8.
destruct H3.
destruct H3.
apply Complement_Set_Law_1 in H3.
destruct H3.
assert (x ∈ Natural_Number_Set).
apply H3.
apply Natural_Number_Set_Law_1 in H3.
destruct H3.
destruct H7.
destruct H8.
destruct H8.
destruct (Law_of_Excluded_Middle (x0 ∈ X)).
destruct H5.
destruct H8.
rewrite <- H8.
apply H1.
apply H9.
assert (x0 ∈(Complement_Set Natural_Number_Set X)).
apply Complement_Set_Law_1.
split.
destruct Natural_Number_Set_Law_2.
apply H10 in H6.
clear H10.
clear H11.
apply H6.
destruct H8.
rewrite <- H10.
apply Ordered_Number_Law_8.
right.
split.
apply H9.
apply H4 in H10.
destruct H10.
destruct H8.
rewrite <- H10.
apply Ordered_Number_Law_8.
right.
split.
destruct H5.
rewrite -> H8.
apply H0.
Qed.

Theorem Peanos_Axiom_5:forall x:Set,~Ordered_Next x=∅.
Proof.
intro.
intro.
apply (Definition_of_Empty_Set x).
rewrite <- H.
apply Ordered_Number_Law_8.
right.
split.
Qed.



Theorem Mathemetical_Induction_1:forall p:Set->Prop,((p (∅))/\(forall n:Set,(n ∈ Natural_Number_Set/\p n)->(p (Ordered_Next n))))->forall n:Set,n ∈ Natural_Number_Set->p n.
Proof.
intros.
destruct H.
assert ((Prop_Set (fun n=>n ∈ Natural_Number_Set/\p n)) ⊂ Natural_Number_Set/\∅ ∈ (Prop_Set (fun n=>n ∈ Natural_Number_Set/\p n))/\(forall n:Set,n ∈ (Prop_Set (fun n=>n ∈ Natural_Number_Set/\p n))->(Ordered_Next n) ∈ (Prop_Set (fun n=>n ∈ Natural_Number_Set/\p n)))).
split.
intro.
intro.
apply (Prop_Set_Law_1 (fun n=>n ∈ Natural_Number_Set/\p n)) in H2.
destruct H2.
apply H2.
exists Natural_Number_Set.
intros.
destruct H4.
apply H4.
split.
apply (Prop_Set_Law_1 (fun n=>n ∈ Natural_Number_Set/\p n)).
exists Natural_Number_Set.
intros.
destruct H2.
apply H2.
split.
apply Peanos_Axiom_1.
apply H.
intros.
apply (Prop_Set_Law_1 (fun n=>n ∈ Natural_Number_Set/\p n)).
exists Natural_Number_Set.
intros.
destruct H3.
apply H3.
apply (Prop_Set_Law_1 (fun n=>n ∈ Natural_Number_Set/\p n)) in H2.
split.
apply Peanos_Axiom_2.
destruct H2.
apply H2.
apply H1 in H2.
apply H2.
exists Natural_Number_Set.
intros.
destruct H4.
apply H4.

apply Peanos_Axiom_4 in H2.
rewrite <- H2 in H0.
apply (Prop_Set_Law_1 (fun n=>n ∈ Natural_Number_Set/\p n)) in H0.
destruct H0.
apply H3.
exists Natural_Number_Set.
intros.
destruct H4.
apply H4.
Qed.



(*加算*)
Definition Nat_Add_n_Map(n:Set):=Well_Defined (fun f=>(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=n)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map f m))=((Culculateion_Map f (Ordered_Next m)))))).

Theorem Nat_Add_n_Map_Law_1:forall n:Set,n ∈ Natural_Number_Set->(Map (Nat_Add_n_Map n) Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map (Nat_Add_n_Map n) (∅)=n)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map (Nat_Add_n_Map n) m))=((Culculateion_Map (Nat_Add_n_Map n) (Ordered_Next m))))).
Proof.
intro.

assert (forall n:Set,n ∈ Natural_Number_Set->exists! f:Set,(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=n)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map f m))=((Culculateion_Map f (Ordered_Next m)))))).
apply (Mathemetical_Induction_1 (fun n0=>exists! f:Set,(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=n0)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map f m))=((Culculateion_Map f (Ordered_Next m))))))).
split.
exists (Identify_Map Natural_Number_Set).
split.
split.
destruct (Identify_Map_Law_2 Natural_Number_Set).
destruct H.
apply H.
split.
assert (∅ ∈ Natural_Number_Set).
apply Peanos_Axiom_1.
apply Identify_Map_Law_3 in H.
rewrite <- H.
split.
intros.
assert (m ∈ Natural_Number_Set).
apply H.
apply Identify_Map_Law_3 in H.
rewrite <- H.
apply Peanos_Axiom_2 in H0.
apply Identify_Map_Law_3 in H0.
rewrite <- H0.
split.
intros.
destruct H.
destruct H0.
apply (Map_Law_4 (Identify_Map Natural_Number_Set) x' Natural_Number_Set Natural_Number_Set).
split.
destruct (Identify_Map_Law_2 Natural_Number_Set).
destruct H2.
apply H2.
split.
apply H.
intros.
assert (x ∈ Natural_Number_Set).
apply H2.
apply Identify_Map_Law_3 in H2.
rewrite <- H2.
assert (forall y:Set,y ∈ Natural_Number_Set->y=Culculateion_Map x' y).
intro.
apply (Mathemetical_Induction_1 (fun z=>z=Culculateion_Map x' z)).
split.
rewrite -> H0.
split.
intros.
destruct H4.
assert (n0 ∈ Natural_Number_Set).
apply H4.
apply H1 in H4.
rewrite <- H4.
rewrite <- H5.
split.
apply H4.
apply H3.

intros.
destruct H.
destruct H0.
destruct H0.
destruct H0.
destruct H2.
exists (Prop_Set (fun x0=>exists n:Set,n ∈ Natural_Number_Set/\x0=(Ordered_Set n (Ordered_Next (Culculateion_Map x n))))).
assert  (forall x1:Set,x1 ∈ Prop_Set (fun x0=>exists n:Set,n ∈ Natural_Number_Set/\x0=(Ordered_Set n (Ordered_Next (Culculateion_Map x n))))<->exists n:Set,n ∈ Natural_Number_Set/\x1=(Ordered_Set n (Ordered_Next (Culculateion_Map x n)))).
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set Natural_Number_Set)).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
destruct H4.
destruct H4.
rewrite -> H7 in H5.
apply Ordered_Set_Law_1 in H5.
destruct H5.
rewrite -> H5 in H6.
apply Pair_Set_Law_1 in H6.
destruct H6.
rewrite -> H6.
apply H4.
rewrite -> H6.
apply Peanos_Axiom_2.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set x2).
split.
apply H0.
apply H4.
rewrite -> H5 in H6.
apply Single_Set_Law_1 in H6.
rewrite -> H6.
apply Peanos_Axiom_2.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set x2).
split.
apply H0.
apply H4.

assert (Map (Prop_Set (fun x0=>exists n:Set,n ∈ Natural_Number_Set/\x0=(Ordered_Set n (Ordered_Next (Culculateion_Map x n))))) Natural_Number_Set Natural_Number_Set).
split.
intros.
apply H4 in H5.
destruct H5.
destruct H5.
exists x0.
exists (Culculateion_Map x (Ordered_Next x0)).
split.
apply H5.
split.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set (Ordered_Next x0)).
split.
apply H0.
apply Peanos_Axiom_2.
apply H5.
apply H3 in H5.
rewrite <- H5.
apply H6.
intros.
exists (Ordered_Next (Culculateion_Map x x0)).
split.
split.
apply H4.
exists x0.
split.
apply H5.
split.
apply Peanos_Axiom_2.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set x0).
split.
apply H0.
apply H5.
intros.
destruct H6.
apply H4 in H6.
destruct H6.
destruct H6.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H8.
rewrite -> H9.
split.

split.
split.
apply H5.
split.
assert ((Ordered_Set (∅) (Ordered_Next n0)) ∈ (Prop_Set(fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0 = Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1))))).
apply H4.
exists (∅).
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
rewrite -> H2.
split.
rewrite -> (Map_Law_3 (Prop_Set(fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0 = Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) Natural_Number_Set Natural_Number_Set (∅) (Ordered_Next n0)).
split.
split.
apply H5.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_2.
apply H.
apply H4.
exists (∅).
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
rewrite -> H2.
split.

intros.
assert ((Ordered_Set (Ordered_Next m) (Ordered_Next (Culculateion_Map x (Ordered_Next m)))) ∈ (Prop_Set(fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0 = Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1))))).
apply H4.
exists (Ordered_Next m).
split.
apply Peanos_Axiom_2.
apply H6.
split.
rewrite <- (Map_Law_3 (Prop_Set(fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0 = Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) Natural_Number_Set Natural_Number_Set (Ordered_Next m) (Ordered_Next (Culculateion_Map x (Ordered_Next m)))).
assert ((Culculateion_Map (Prop_Set (fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0=Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) m)=(Culculateion_Map x (Ordered_Next m))).
assert ((Ordered_Set m (Culculateion_Map x (Ordered_Next m))) ∈ (Prop_Set (fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0=Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1))))).
apply H4.
exists m.
split.
apply H6.
apply H3 in H6.
rewrite -> H6.
split.
rewrite <- (Map_Law_3 (Prop_Set (fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0=Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) Natural_Number_Set Natural_Number_Set m (Culculateion_Map x (Ordered_Next m))).
split.
split.
apply H5.
split.
apply H6.
split.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set (Ordered_Next m)).
split.
apply H0.
apply Peanos_Axiom_2.
apply H6.
apply H4.
exists m.
split.
apply H6.
apply H3 in H6.
rewrite -> H6.
split.
rewrite -> H8.
split.
split.
apply H5.
split.
apply Peanos_Axiom_2.
apply H6.
split.
apply Peanos_Axiom_2.
apply (Map_Law_2 x Natural_Number_Set Natural_Number_Set (Ordered_Next m)).
split.
apply H0.
apply Peanos_Axiom_2.
apply H6.
apply H7.

intros.
apply (Map_Law_4 (Prop_Set (fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0=Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) x' Natural_Number_Set Natural_Number_Set).
destruct H6.
destruct H7.
split.
apply H5.
split.
apply H6.
intros.
rewrite -> (Map_Law_3 (Prop_Set (fun x0=>exists n1:Set,n1 ∈ Natural_Number_Set/\x0=Ordered_Set n1 (Ordered_Next (Culculateion_Map x n1)))) Natural_Number_Set Natural_Number_Set x0 (Culculateion_Map x' x0)).
split.
split.
apply H5.
split.
apply H9.
split.
apply (Map_Law_2 x' Natural_Number_Set Natural_Number_Set x0).
split.
apply H6.
apply H9.
apply H4.
exists x0.
split.
apply H9.
apply Ordered_Set_Law_2.
split.
split.
assert (forall x0:Set,x0 ∈ Natural_Number_Set->Culculateion_Map x' x0=Ordered_Next (Culculateion_Map x x0)).
intro.
apply (Mathemetical_Induction_1 (fun n0=>Culculateion_Map x' n0=Ordered_Next (Culculateion_Map x n0))).
split.
rewrite -> H7.
rewrite -> H2.
split.
intros.
destruct H10.
assert (n1 ∈ Natural_Number_Set).
apply H10.
apply H3 in H10.
rewrite <- H10.
rewrite <- H11.
rewrite <- H8.
split.
apply H12.
apply H10.
apply H9.

intros.
apply H in H0.
apply Well_Defined_1 in H0.
apply H0.
Qed.

Definition Nat_Add:=Prop_Set (fun x=>exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Add_n_Map n1) n2))).

Theorem Nat_Add_Law_1:forall x0:Set,x0 ∈ Nat_Add<->(exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x0=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Add_n_Map n1) n2))).
Proof.
intros.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set ((Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) ∪ Natural_Number_Set))).
intros.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Pair_Union_Set_Law_1.
destruct H.
destruct H.
destruct H.
destruct H2.
rewrite -> H3 in H0.
apply Ordered_Set_Law_1 in H0.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H1.
left.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
rewrite -> H1.
split.
split.
apply H.
apply H2.
right.
rewrite -> H1.
apply (Map_Law_2  (Nat_Add_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
apply H.
apply H2.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
right.
apply (Map_Law_2 (Nat_Add_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
apply H.
apply H2.
Qed.

Theorem Nat_Add_Law_2:Map Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set.
Proof.
split.
intros.
apply Nat_Add_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
exists (Ordered_Set x x0).
exists (Culculateion_Map (Nat_Add_n_Map x) x0).
split.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
split.
split.
apply H.
apply H0.
split.
apply (Map_Law_2  (Nat_Add_n_Map x) Natural_Number_Set Natural_Number_Set x0).
split.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
apply H.
apply H0.
apply H1.

intros.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
exists (Culculateion_Map (Nat_Add_n_Map x0) x1).
split.
split.
apply Nat_Add_Law_1.
exists x0.
exists x1.
split.
apply H0.
split.
apply H1.
apply Ordered_Set_Law_2.
split.
rewrite -> H.
split.
split.
apply (Map_Law_2  (Nat_Add_n_Map x0) Natural_Number_Set Natural_Number_Set x1).
split.
apply Nat_Add_n_Map_Law_1.
apply H0.
apply H1.
intros.
destruct H2.
apply Nat_Add_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H6.
rewrite H5 in H.
apply Ordered_Set_Law_2 in H.
destruct H.
rewrite -> H.
rewrite -> H7.
split.
Qed.

Theorem Nat_Add_Law_3:forall n1 n2:Set,(n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set)->(Culculateion_Map  (Nat_Add_n_Map n1) n2=Culculateion_Map Nat_Add (Ordered_Set n1 n2)).
Proof.
intros.
destruct H.
apply (Map_Law_3 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n2)).
split.
apply Nat_Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
split.
apply (Map_Law_2 (Nat_Add_n_Map n1) Natural_Number_Set Natural_Number_Set n2).
split.
apply Nat_Add_n_Map_Law_1.
apply H.
apply H0.
apply Nat_Add_Law_1.
exists n1.
exists n2.
split.
apply H.
split.
apply H0.
split.
Qed.

Theorem Nat_Add_Law_4:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n (∅))=n.
Proof.
intros.
rewrite -> (Map_Law_3 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n (∅))).
split.
split.
apply Nat_Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists (∅).
split.
split.
split.
apply H.
apply Peanos_Axiom_1.
split.
apply H.
apply Nat_Add_Law_1.
exists n.
exists (∅).
split.
apply H.
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
apply (Map_Law_3 (Nat_Add_n_Map n) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply Nat_Add_n_Map_Law_1.
apply H.
split.
apply Peanos_Axiom_1.
split.
apply H.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
destruct H0.
assert (Ordered_Set (∅) (Culculateion_Map (Nat_Add_n_Map n) (∅)) ∈ Nat_Add_n_Map n).
apply (Map_Law_1 (Nat_Add_n_Map n) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply H.
apply Peanos_Axiom_1.
rewrite -> H0 in H2.
apply H2.
Qed.

Theorem Nat_Add_Law_5:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set (∅) n)=n.
Proof.
intros.
rewrite <- (Map_Law_3 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (∅) n) n).
split.
split.
apply Nat_Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (∅).
exists n.
split.
split.
split.
apply Peanos_Axiom_1.
apply H.
split.
apply H.
apply Nat_Add_Law_1.
exists (∅).
exists n.
split.
apply Peanos_Axiom_1.
split.
apply H.
apply Ordered_Set_Law_2.
split.
split.
destruct (Nat_Add_n_Map_Law_1 (∅)).
apply Peanos_Axiom_1.
destruct H1.
assert (forall n0:Set,n0 ∈ Natural_Number_Set->n0=Culculateion_Map (Nat_Add_n_Map (∅)) n0).
intro.
apply (Mathemetical_Induction_1 (fun n1=>n1=Culculateion_Map (Nat_Add_n_Map (∅)) n1)).
split.
rewrite -> H1.
split.
intros.
destruct H3.
apply H2 in H3.
assert ((Ordered_Next (Culculateion_Map (Nat_Add_n_Map (∅)) n1))=Culculateion_Map (Nat_Add_n_Map (∅)) (Ordered_Next n1)).
rewrite -> H3.
split.
rewrite <- H4 in H5.
apply H5.
apply H3 in H.
apply H.
Qed.

Theorem Nat_Add_Law_6:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Ordered_Next (Culculateion_Map Nat_Add (Ordered_Set n m))=Culculateion_Map Nat_Add (Ordered_Set n (Ordered_Next m)).
Proof.
intros.
destruct H.
rewrite <- Nat_Add_Law_3.
assert (Ordered_Next (Culculateion_Map (Nat_Add_n_Map n) m)=Culculateion_Map (Nat_Add_n_Map n) (Ordered_Next m)).
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
destruct H1.
apply H2 in H0.
apply H0.
rewrite -> H1.
rewrite -> Nat_Add_Law_3.
split.
split.
apply H.
apply Peanos_Axiom_2.
apply H0.
split.
apply H.
apply H0.
Qed.

Theorem Nat_Add_Law_7:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Ordered_Next (Culculateion_Map Nat_Add (Ordered_Set n m))=Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n) m).
Proof.
intros.
destruct H.
assert (forall m0:Set,m0 ∈ Natural_Number_Set->Ordered_Next (Culculateion_Map Nat_Add (Ordered_Set n m0))=Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n) m0)).
intro.
apply (Mathemetical_Induction_1 (fun m0=>Ordered_Next (Culculateion_Map Nat_Add (Ordered_Set n m0))=Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n) m0))).
split.

assert ((Ordered_Next n) ∈ Natural_Number_Set).
apply Peanos_Axiom_2.
apply H.
apply Nat_Add_n_Map_Law_1 in H1.
destruct H1.
destruct H2.
rewrite <- (Nat_Add_Law_3 (Ordered_Next n) (∅)).
rewrite -> H2.
assert (n ∈ Natural_Number_Set).
apply H.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
destruct H5.
rewrite <- Nat_Add_Law_3.
rewrite -> H5.
split.
split.
apply H4.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_2.
apply H.
apply Peanos_Axiom_1.

intros.
destruct H1.
assert (Culculateion_Map Nat_Add (Ordered_Set n (Ordered_Next n0))=Ordered_Next (Culculateion_Map Nat_Add (Ordered_Set n n0))).
rewrite <- Nat_Add_Law_3.
assert (n ∈ Natural_Number_Set).
apply H.
apply Nat_Add_n_Map_Law_1 in H.
destruct H.
destruct H4.
assert (n0 ∈ Natural_Number_Set).
apply H1.
apply H5 in H1.
rewrite <- H1.
rewrite -> Nat_Add_Law_3.
split.
split.
apply H3.
apply H6.
split.
apply H.
apply Peanos_Axiom_2.
apply H1.
rewrite -> H3.
rewrite -> H2.
clear H2.
clear H3.
assert ((Ordered_Next n) ∈ Natural_Number_Set).
apply Peanos_Axiom_2.
apply H.
rewrite <- (Nat_Add_Law_3 (Ordered_Next n) (Ordered_Next n0)).
apply Nat_Add_n_Map_Law_1 in H2.
destruct H2.
destruct H3.
assert (n0 ∈ Natural_Number_Set).
apply H1.
apply H4 in H5.
rewrite <- H5.
rewrite -> (Nat_Add_Law_3 (Ordered_Next n) n0).
split.
split.
apply Peanos_Axiom_2.
apply H.
apply H1.
split.
apply Peanos_Axiom_2.
apply H.
apply Peanos_Axiom_2.
apply H1.
apply H1.
apply H0.
Qed.

Theorem Nat_Add_Law_8:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n m)=Culculateion_Map Nat_Add (Ordered_Set m n).
Proof.
intros.
destruct H.
assert (forall m0:Set,m0 ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n m0)=Culculateion_Map Nat_Add (Ordered_Set m0 n)).
intro.
apply (Mathemetical_Induction_1 (fun m1=>Culculateion_Map Nat_Add (Ordered_Set n m1)=Culculateion_Map Nat_Add (Ordered_Set m1 n))).
split.

assert (Culculateion_Map Nat_Add (Ordered_Set (∅) n)=n).
apply Nat_Add_Law_5.
apply H.
assert (Culculateion_Map Nat_Add (Ordered_Set n (∅))=n).
apply Nat_Add_Law_4.
apply H.
rewrite -> H1.
rewrite -> H2.
split.

intros.
destruct H1.
rewrite <- Nat_Add_Law_6.
rewrite <- Nat_Add_Law_7.
rewrite -> H2.
split.
split.
apply H1.
apply H.
split.
apply H.
apply H1.
apply H1.
apply H0.
Qed.

Theorem Nat_Add_Law_9:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n2 n3)))=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) n3)).
Proof.
intros.
destruct H.
destruct H0.
assert (forall m:Set,m ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n2 m)))=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) m)).
intro.
apply (Mathemetical_Induction_1 (fun m=>Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n2 m)))=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) m))).
split.

rewrite -> Nat_Add_Law_4.
rewrite -> Nat_Add_Law_4.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n2)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
apply H0.

intros.
destruct H2.
rewrite <- Nat_Add_Law_6.
rewrite <- Nat_Add_Law_6.
rewrite <- Nat_Add_Law_6.
rewrite -> H3.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set  (Ordered_Set n1 n2)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
apply H2.
split.
apply H.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n2 n)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n.
split.
split.
split.
apply H0.
apply H2.
split.
apply H0.
apply H2.
apply H2.
apply H1.
Qed.

Theorem Nat_Add_Law_10:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 n3)=Culculateion_Map Nat_Add (Ordered_Set n2 n3)->n1=n2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
assert (forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n1 n) = Culculateion_Map Nat_Add (Ordered_Set n2 n)->n1=n2).
intro.
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Add (Ordered_Set n1 a)=Culculateion_Map Nat_Add (Ordered_Set n2 a)->n1=n2)).
split.
rewrite -> (Nat_Add_Law_4 n1).
rewrite -> (Nat_Add_Law_4 n2).
intro.
apply H4.
apply H0.
apply H.
intros.
destruct H4.
apply H6.
apply (Ordered_Number_Law_13 (Culculateion_Map Nat_Add (Ordered_Set n1 n0)) (Culculateion_Map Nat_Add (Ordered_Set n2 n0))).
split.
apply Natural_Number_Set_Law_1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n0)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n0.
split.
split.
split.
apply H.
apply H4.
split.
apply Natural_Number_Set_Law_1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n2 n0)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n0.
split.
split.
split.
apply H0.
apply H4.
rewrite -> (Nat_Add_Law_6 n1 n0).
rewrite -> (Nat_Add_Law_6 n2 n0).
apply H5.
split.
apply H0.
apply H4.
split.
apply H.
apply H4.
apply H3.
apply (H3 n3).
apply H1.
apply H2.
Qed.

Theorem Nat_Add_Law_11:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 n2)=Culculateion_Map Nat_Add (Ordered_Set n1 n3)->n2=n3.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
rewrite -> (Nat_Add_Law_8 n1 n2) in H2.
rewrite -> (Nat_Add_Law_8 n1 n3) in H2.
apply (Nat_Add_Law_10 n2 n3 n1).
split.
apply H0.
split.
apply H1.
split.
apply H.
apply H2.
split.
apply H.
apply H1.
split.
apply H.
apply H0.
Qed.

Theorem Nat_Add_Law_12:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n1 ∈ n2->(exists n3:Set,n3 ∈ Natural_Number_Set/\n2=Culculateion_Map Nat_Add (Ordered_Set n1 n3)).
Proof.
intros.
destruct H.
destruct H0.
assert (forall a:Set,a ∈ Natural_Number_Set->(a ∈ n2->exists a0:Set,a0 ∈ Natural_Number_Set/\n2 = Culculateion_Map Nat_Add (Ordered_Set a a0))).
apply (Mathemetical_Induction_1 (fun a=>a ∈ n2->exists a0:Set,a0 ∈ Natural_Number_Set/\n2 = Culculateion_Map Nat_Add (Ordered_Set a a0))).
split.
intro.
exists n2.
split.
apply H0.
symmetry.
apply (Nat_Add_Law_5 n2).
apply H0.
intros.
destruct H2.
assert (n ∈ n2).
apply (Ordered_Number_Law_4 n (Ordered_Next n) n2).
split.
apply Natural_Number_Set_Law_1 in H2.
destruct H2.
apply H2.
split.
apply Ordered_Number_Law_9.
apply Natural_Number_Set_Law_1 in H2.
destruct H2.
apply H2.
split.
apply Natural_Number_Set_Law_1 in H0.
destruct H0.
apply H0.
split.
apply Ordered_Number_Law_8.
right.
split.
apply H3.
apply H4 in H5.
destruct H5.
destruct H5.
assert (~x=∅).
intro.
rewrite -> H7 in H6.
rewrite -> (Nat_Add_Law_4 n) in H6.
destruct (Ordered_Number_Law_6 n2).
apply Natural_Number_Set_Law_1 in H0.
destruct H0.
apply H0.
apply (Ordered_Number_Law_4 n2 (Ordered_Next n) n2).
split.
apply Natural_Number_Set_Law_1 in H0.
destruct H0.
apply H0.
split.
apply Ordered_Number_Law_9.
apply Natural_Number_Set_Law_1 in H2.
destruct H2.
apply H2.
split.
apply Natural_Number_Set_Law_1 in H0.
destruct H0.
apply H0.
split.
apply Ordered_Number_Law_8.
right.
apply H6.
apply H3.
apply H2.
assert (x ∈ Natural_Number_Set).
apply H5.
apply Natural_Number_Set_Law_1 in H8.
destruct H8.
destruct H9.
destruct H10.
destruct H10.
destruct H10.
exists x0.
split.
apply (Ordered_Number_Law_4 x0 x Natural_Number_Set).
split.
apply H10.
split.
apply Natural_Number_Set_Law_1 in H5.
destruct H5.
apply H5.
split.
apply Natural_Number_Set_Law_2.
split.
rewrite <- H11.
apply Ordered_Number_Law_8.
right.
split.
apply H5.
rewrite <- (Nat_Add_Law_7 n x0).
rewrite -> (Nat_Add_Law_6 n x0).
rewrite -> H11.
apply H6.
split.
apply H2.
apply (Ordered_Number_Law_4 x0 x Natural_Number_Set).
split.
apply H10.
split.
apply Natural_Number_Set_Law_1 in H5.
destruct H5.
apply H5.
split.
apply Natural_Number_Set_Law_2.
split.
rewrite <- H11.
apply Ordered_Number_Law_8.
right.
split.
apply H5.
split.
apply H2.
apply (Ordered_Number_Law_4 x0 x Natural_Number_Set).
split.
apply H10.
split.
apply Natural_Number_Set_Law_1 in H5.
destruct H5.
apply H5.
split.
apply Natural_Number_Set_Law_2.
split.
rewrite <- H11.
apply Ordered_Number_Law_8.
right.
split.
apply H5.
destruct H7.
apply H10.
apply H2.
apply H.
apply H1.
Qed.

Theorem Nat_Add_Law_13:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n1 n2) ∈ Natural_Number_Set.
Proof.
intros.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n2)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
apply H.
Qed.



(*乗算*)
Definition Nat_Multi_n_Map(n:Set):=Well_Defined (fun f=>(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=(∅))/\(forall m:Set,m ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set n (Culculateion_Map f m))=Culculateion_Map f (Ordered_Next m)))).

Theorem Nat_Multi_n_Map_Law_1:forall n:Set,n ∈ Natural_Number_Set->(Map (Nat_Multi_n_Map n) Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map (Nat_Multi_n_Map n) (∅)=(∅))/\(forall m:Set,m ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set n (Culculateion_Map (Nat_Multi_n_Map n) m))=Culculateion_Map (Nat_Multi_n_Map n) (Ordered_Next m))).
Proof.
intro.
apply (Mathemetical_Induction_1 (fun n=>(Map (Nat_Multi_n_Map n) Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map (Nat_Multi_n_Map n) (∅)=(∅))/\(forall m:Set,m ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set n (Culculateion_Map (Nat_Multi_n_Map n) m))=Culculateion_Map (Nat_Multi_n_Map n) (Ordered_Next m))))).
split.
apply (Well_Defined_1 (fun f=>(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=(∅))/\(forall m:Set,m ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set (∅) (Culculateion_Map f m))=Culculateion_Map f (Ordered_Next m))))).
exists (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=(Ordered_Set n0 (∅)))).

assert (forall a0:Set,a0 ∈ (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=(Ordered_Set n0 (∅))))<->exists n0:Set,n0 ∈ Natural_Number_Set/\a0=(Ordered_Set n0 (∅))).
intro.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set Natural_Number_Set)).
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
apply Peanos_Axiom_1.
rewrite H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
apply Peanos_Axiom_1.

assert (Map (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=(Ordered_Set n0 (∅)))) Natural_Number_Set Natural_Number_Set).
split.
intros.
apply H in H0.
destruct H0.
exists x.
exists (∅).
destruct H0.
split.
apply H0.
split.
apply Peanos_Axiom_1.
apply H1.
intros.
exists (∅).
split.
split.
apply H.
exists x.
split.
apply H0.
split.
apply Peanos_Axiom_1.
intros.
destruct H1.
apply H in H1.
destruct H1.
destruct H1.
apply Ordered_Set_Law_2 in H3.
destruct H3.
rewrite -> H4.
split.
split.

split.
apply H0.
split.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set (∅) (∅)).
split.
apply H0.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply H.
exists (∅).
split.
apply Peanos_Axiom_1.
split.
intros.
assert ((∅)=(Culculateion_Map (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) (Ordered_Next m))).
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set (Ordered_Next m) (∅)).
split.
apply H0.
split.
apply Peanos_Axiom_2.
apply H1.
split.
apply Peanos_Axiom_1.
apply H.
exists (Ordered_Next m).
split.
apply Peanos_Axiom_2.
apply H1.
split.
rewrite <- H2.
clear H2.
rewrite -> Nat_Add_Law_5.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set m (∅)).
split.
apply H0.
split.
apply H1.
split.
apply Peanos_Axiom_1.
apply H.
exists m.
split.
apply H1.
split.
apply (Map_Law_2 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set m).
split.
apply H0.
apply H1.

intros.
destruct H1.
destruct H2.
apply (Map_Law_4 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) x' Natural_Number_Set Natural_Number_Set).
split.
apply H0.
split.
apply H1.
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) a=Culculateion_Map x' a)).
split.
rewrite -> H2.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set (∅) (∅)).
split.
apply H0.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply H.
exists (∅).
split.
apply Peanos_Axiom_1.
split.
intros.
destruct H4.
assert (n0 ∈ Natural_Number_Set).
apply H4.
apply H3 in H4.
rewrite <- H4.
rewrite -> Nat_Add_Law_5.
rewrite <- H5.
assert ((∅)=(Culculateion_Map (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) (Ordered_Next n0))).
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set (Ordered_Next n0) (∅)).
split.
apply H0.
split.
apply Peanos_Axiom_2.
apply H6.
split.
apply Peanos_Axiom_1.
apply H.
exists (Ordered_Next n0).
split.
apply Peanos_Axiom_2.
apply H6.
split.
rewrite <- H7.
apply (Map_Law_3 (Prop_Set (fun a=>exists n0:Set,n0 ∈ Natural_Number_Set/\a=Ordered_Set n0 (∅))) Natural_Number_Set Natural_Number_Set n0 (∅)).
split.
apply H0.
split.
apply H6.
split.
apply Peanos_Axiom_1.
apply H.
exists n0.
split.
apply H6.
split.
apply (Map_Law_2 x' Natural_Number_Set Natural_Number_Set n0).
split.
apply H1.
apply H6.

intros.
destruct H.
destruct H0.
destruct H1.
apply (Well_Defined_1 (fun f=>(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=(∅))/\(forall m:Set,m ∈ Natural_Number_Set->(Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n0) (Culculateion_Map f m))=Culculateion_Map f (Ordered_Next m))))).
exists (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))).

assert (forall a0:Set,a0 ∈ (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1))))))<->exists n1:Set,n1 ∈ Natural_Number_Set/\a0=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1))))).
apply (Prop_Set_Law_1 (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))).
exists (Power_Set (Power_Set Natural_Number_Set)).
intros.
destruct H3.
destruct H3.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H4 in H5.
apply Ordered_Set_Law_1 in H5.
destruct H5.
rewrite -> H5 in H6.
apply Pair_Set_Law_1 in H6.
destruct H6.
rewrite -> H6.
apply H3.
rewrite -> H6.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 (Culculateion_Map (Nat_Multi_n_Map n0) x0))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists (Culculateion_Map (Nat_Multi_n_Map n0) x0).
split.
split.
split.
apply H3.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set x0).
split.
apply H0.
apply H3.
rewrite -> H5 in H6.
apply Single_Set_Law_1 in H6.
rewrite -> H6.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 (Culculateion_Map (Nat_Multi_n_Map n0) x0))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists (Culculateion_Map (Nat_Multi_n_Map n0) x0).
split.
split.
split.
apply H3.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set x0).
split.
apply H0.
apply H3.

assert (Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set).
split.
intros.
apply H3 in H4.
destruct H4.
destruct H4.
exists x.
exists (Culculateion_Map Nat_Add (Ordered_Set x (Culculateion_Map (Nat_Multi_n_Map n0) x))).
split.
apply H4.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x (Culculateion_Map (Nat_Multi_n_Map n0) x))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists (Culculateion_Map (Nat_Multi_n_Map n0) x).
split.
split.
split.
apply H4.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set x).
split.
apply H0.
apply H4.
apply H5.
intros.
exists (Culculateion_Map Nat_Add (Ordered_Set x (Culculateion_Map (Nat_Multi_n_Map n0) x))).
split.
split.
apply H3.
exists x.
split.
apply H4.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x (Culculateion_Map (Nat_Multi_n_Map n0) x))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists (Culculateion_Map (Nat_Multi_n_Map n0) x).
split.
split.
split.
apply H4.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set x).
split.
apply H0.
apply H4.
intros.
destruct H5.
apply H3 in H5.
destruct H5.
destruct H5.
apply Ordered_Set_Law_2 in H7.
destruct H7.
rewrite -> H8.
rewrite -> H7.
split.
split.
split.
apply H4.
split.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set (∅) (∅)).
split.
apply H4.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply H3.
exists (∅).
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
symmetry.
rewrite -> H1.
apply Nat_Add_Law_5.
apply Peanos_Axiom_1.
intros.
assert (Culculateion_Map Nat_Add (Ordered_Set m (Culculateion_Map (Nat_Multi_n_Map n0) m))=Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) m).
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set m (Culculateion_Map Nat_Add (Ordered_Set m (Culculateion_Map (Nat_Multi_n_Map n0) m)))).
split.
apply H4.
split.
apply H5.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set m (Culculateion_Map (Nat_Multi_n_Map n0) m))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists m.
exists (Culculateion_Map (Nat_Multi_n_Map n0) m).
split.
split.
split.
apply H5.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set m).
split.
apply H0.
apply H5.
apply H3.
exists m.
split.
apply H5.
split.
intros.
rewrite <- H6.
clear H6.
assert (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next m) (Culculateion_Map (Nat_Multi_n_Map n0) (Ordered_Next m)))=Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) (Ordered_Next m)).
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set (Ordered_Next m) (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next m) (Culculateion_Map (Nat_Multi_n_Map n0) (Ordered_Next m))))).
split.
apply H4.
split.
apply Peanos_Axiom_2.
apply H5.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (Ordered_Next m) (Culculateion_Map (Nat_Multi_n_Map n0) (Ordered_Next m)))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Next m).
exists (Culculateion_Map (Nat_Multi_n_Map n0) (Ordered_Next m)).
split.
split.
split.
apply Peanos_Axiom_2.
apply H5.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set (Ordered_Next m)).
split.
apply H0.
apply Peanos_Axiom_2.
apply H5.
apply H3.
exists (Ordered_Next m).
split.
apply Peanos_Axiom_2.
apply H5.
split.
rewrite <- H6.
clear H6.
assert (m ∈ Natural_Number_Set).
apply H5.
apply H2 in H6.
rewrite <- H6.
clear H6.
rewrite -> (Nat_Add_Law_9 (Ordered_Next n0) m (Culculateion_Map (Nat_Multi_n_Map n0) m)).
rewrite -> (Nat_Add_Law_9 (Ordered_Next m) n0 (Culculateion_Map (Nat_Multi_n_Map n0) m)).
assert (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n0) m)=Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next m) n0)).
rewrite <- (Nat_Add_Law_7 n0 m).
rewrite <- (Nat_Add_Law_7 m n0).
rewrite -> (Nat_Add_Law_8 m n0).
split.
split.
apply H5.
apply H.
split.
apply H5.
apply H.
split.
apply H.
apply H5.
rewrite -> H6.
split.
split.
apply Peanos_Axiom_2.
apply H5.
split.
apply H.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set m).
split.
apply H0.
apply H5.
split.
apply Peanos_Axiom_2.
apply H.
split.
apply H5.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set m).
split.
apply H0.
apply H5.

intros.
destruct H5.
destruct H6.
apply (Map_Law_4 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) x' Natural_Number_Set Natural_Number_Set).
split.
apply H4.
split.
apply H5.
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) a=Culculateion_Map x' a)).
split.
rewrite -> H6.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set (∅) (∅)).
split.
apply H4.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply H3.
exists (∅).
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
apply (Map_Law_3 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (∅) (Culculateion_Map (Nat_Multi_n_Map n0) (∅))) (∅)).
split.
apply Nat_Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (∅).
exists (Culculateion_Map (Nat_Multi_n_Map n0) (∅)).
split.
split.
split.
apply Peanos_Axiom_1.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply H0.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply Nat_Add_Law_1.
exists (∅).
exists (Culculateion_Map (Nat_Multi_n_Map n0) (∅)).
split.
apply Peanos_Axiom_1.
split.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply H0.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
rewrite -> H1.
assert ((∅) ∈ Natural_Number_Set).
apply Peanos_Axiom_1.
apply Nat_Add_n_Map_Law_1 in H8.
destruct H8.
destruct H9.
rewrite -> H9.
split.
intros.
destruct H8.
assert (n1 ∈ Natural_Number_Set).
apply H8.
apply H7 in H10.
rewrite <- H10.
rewrite <- H9.
symmetry.
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set (Ordered_Next n1) (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n0) (Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) n1)))).
split.
apply H4.
split.
apply Peanos_Axiom_2.
apply H8.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (Ordered_Next n0) (Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) n1))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Next n0).
exists (Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) n1).
split.
split.
split.
apply Peanos_Axiom_2.
apply H.
apply (Map_Law_2 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set n1).
split.
apply H4.
apply H8.
apply H3.
exists (Ordered_Next n1).
split.
apply Peanos_Axiom_2.
apply H8.
apply Ordered_Set_Law_2.
split.
split.
assert (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1))=Culculateion_Map (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) n1).
apply (Map_Law_3 (Prop_Set (fun a=>exists n1:Set,n1 ∈ Natural_Number_Set/\a=(Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))))) Natural_Number_Set Natural_Number_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1)))).
split.
apply H4.
split.
apply H8.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 (Culculateion_Map (Nat_Multi_n_Map n0) n1))).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists (Culculateion_Map (Nat_Multi_n_Map n0) n1).
split.
split.
split.
apply H8.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set n1).
split.
apply H0.
apply H8.
apply H3.
exists n1.
split.
apply H8.
split.
rewrite <- H11.
assert (n1 ∈ Natural_Number_Set).
apply H8.
apply H2 in H12.
rewrite <- H12.
rewrite -> Nat_Add_Law_9.
rewrite -> Nat_Add_Law_9.
assert (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n0) n1)=Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n1) n0)).
rewrite <- Nat_Add_Law_7.
rewrite <- Nat_Add_Law_7.
rewrite -> Nat_Add_Law_8.
split.
split.
apply H.
apply H8.
split.
apply H8.
apply H.
split.
apply H.
apply H8.
rewrite -> H13.
split.
split.
apply Peanos_Axiom_2.
apply H8.
split.
apply H.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set n1).
split.
apply H0.
apply H8.
split.
apply Peanos_Axiom_2.
apply H.
split.
apply H8.
apply (Map_Law_2 (Nat_Multi_n_Map n0) Natural_Number_Set Natural_Number_Set n1).
split.
apply H0.
apply H8.
Qed.

Definition Nat_Multi:=Prop_Set (fun x=>exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Multi_n_Map n1) n2))).

Theorem Nat_Multi_Law_1:forall x0:Set,x0 ∈ Nat_Multi<->(exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x0=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Multi_n_Map n1) n2))).
Proof.
intro.
apply (Prop_Set_Law_1 (fun x1=>exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x1=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Multi_n_Map n1) n2)))).
exists (Power_Set (Power_Set ((Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) ∪ Natural_Number_Set))).
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
rewrite -> H3 in H0.
apply Ordered_Set_Law_1 in H0.
apply Pair_Union_Set_Law_1.
destruct H0.
rewrite -> H0 in H1.
apply Pair_Set_Law_1 in H1.
destruct H1.
rewrite -> H1.
left.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H.
apply H2.
rewrite -> H1.
right.
apply (Map_Law_2 (Nat_Multi_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Nat_Multi_n_Map_Law_1 in H.
destruct H.
destruct H4.
apply H.
apply H2.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
right.
apply (Map_Law_2 (Nat_Multi_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Nat_Multi_n_Map_Law_1 in H.
destruct H.
destruct H4.
apply H.
apply H2.
Qed.

Theorem Nat_Multi_Law_2:Map Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set.
Proof.
split.
intros.
apply Nat_Multi_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
exists (Ordered_Set x x0).
exists (Culculateion_Map (Nat_Multi_n_Map x) x0).
split.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
split.
split.
apply H.
apply H0.
split.
apply (Map_Law_2 (Nat_Multi_n_Map x) Natural_Number_Set Natural_Number_Set x0).
split.
apply Nat_Multi_n_Map_Law_1.
apply H.
apply H0.
apply H1.

intros.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
exists (Culculateion_Map (Nat_Multi_n_Map x0) x1).
split.
split.
apply Nat_Multi_Law_1.
exists x0.
exists x1.
split.
apply H0.
split.
apply H1.
apply Ordered_Set_Law_2.
split.
rewrite -> H.
split.
split.
apply (Map_Law_2 (Nat_Multi_n_Map x0) Natural_Number_Set Natural_Number_Set x1).
split.
apply Nat_Multi_n_Map_Law_1.
apply H0.
apply H1.
intros.
destruct H2.
apply Nat_Multi_Law_1 in H2.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
apply Ordered_Set_Law_2 in H5.
destruct H5.
rewrite -> H6.
rewrite -> H5 in H.
apply Ordered_Set_Law_2 in H.
destruct H.
rewrite -> H.
rewrite -> H7.
split.
Qed.

Theorem Nat_Multi_Law_3:forall n1 n2:Set,(n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set)->(Culculateion_Map  (Nat_Multi_n_Map n1) n2=Culculateion_Map Nat_Multi (Ordered_Set n1 n2)).
Proof.
intros.
destruct H.
apply (Map_Law_3 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n2) (Culculateion_Map (Nat_Multi_n_Map n1) n2)).
split.
apply Nat_Multi_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
split.
apply (Map_Law_2 (Nat_Multi_n_Map n1) Natural_Number_Set Natural_Number_Set n2).
split.
apply Nat_Multi_n_Map_Law_1.
apply H.
apply H0.
apply Nat_Multi_Law_1.
exists n1.
exists n2.
split.
apply H.
split.
apply H0.
split.
Qed.

Theorem Nat_Multi_Law_4:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set n (∅))=(∅).
Proof.
intros.
rewrite <- Nat_Multi_Law_3.
apply Nat_Multi_n_Map_Law_1 in H.
destruct H.
destruct H0.
apply H0.
split.
apply H.
apply Peanos_Axiom_1.
Qed.

Theorem Nat_Multi_Law_5:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set (∅) n)=(∅).
Proof.
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Multi (Ordered_Set (∅) a)=∅)).
split.
assert ((∅) ∈ Natural_Number_Set).
apply Peanos_Axiom_1.
apply Nat_Multi_n_Map_Law_1 in H.
destruct H.
destruct H0.
rewrite <- Nat_Multi_Law_3.
apply H0.
split.
apply Peanos_Axiom_1.
apply Peanos_Axiom_1.

intros.
destruct H.
rewrite <- Nat_Multi_Law_3.
assert ((∅) ∈ Natural_Number_Set).
apply Peanos_Axiom_1.
assert (n0 ∈ Natural_Number_Set).
apply H.
apply Nat_Multi_n_Map_Law_1 in H1.
destruct H1.
destruct H3.
apply H4 in H2.
rewrite <- H2.
rewrite -> Nat_Add_Law_5.
rewrite -> Nat_Multi_Law_3.
apply H0.
split.
apply Peanos_Axiom_1.
apply H.
apply (Map_Law_2 (Nat_Multi_n_Map (∅)) Natural_Number_Set Natural_Number_Set n0).
split.
apply H1.
apply H.
split.
apply Peanos_Axiom_1.
apply Peanos_Axiom_2.
apply H.
Qed.

Theorem Nat_Multi_Law_6:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set m (Culculateion_Map Nat_Multi (Ordered_Set n m)))=Culculateion_Map Nat_Multi (Ordered_Set (Ordered_Next n) m).
Proof.
intros.
destruct H.
assert (forall m0:Set,m0 ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set m0 (Culculateion_Map Nat_Multi (Ordered_Set n m0)))=Culculateion_Map Nat_Multi (Ordered_Set (Ordered_Next n) m0)).
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Add (Ordered_Set a (Culculateion_Map Nat_Multi (Ordered_Set n a)))=Culculateion_Map Nat_Multi (Ordered_Set (Ordered_Next n) a))).
split.
rewrite -> Nat_Add_Law_5.
rewrite -> Nat_Multi_Law_4.
rewrite -> Nat_Multi_Law_4.
split.
apply Peanos_Axiom_2.
apply H.
apply H.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n (∅))).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists (∅).
split.
split.
split.
apply H.
apply Peanos_Axiom_1.

intros.
destruct H1.
assert (Culculateion_Map Nat_Add (Ordered_Set (Ordered_Next n) (Culculateion_Map Nat_Multi (Ordered_Set (Ordered_Next n) n0)))=Culculateion_Map Nat_Multi (Ordered_Set (Ordered_Next n) (Ordered_Next n0))).
rewrite <- (Nat_Multi_Law_3 (Ordered_Next n) (Ordered_Next n0)).
rewrite <- (Nat_Multi_Law_3 (Ordered_Next n) n0).
assert ((Ordered_Next n) ∈ Natural_Number_Set).
apply Peanos_Axiom_2.
apply H.
apply Nat_Multi_n_Map_Law_1 in H3.
destruct H3.
destruct H4.
apply H5.
apply H1.
split.
apply Peanos_Axiom_2.
apply H.
apply H1.
split.
apply Peanos_Axiom_2.
apply H.
apply Peanos_Axiom_2.
apply H1.
rewrite <- H3.
clear H3.
assert (Culculateion_Map Nat_Add (Ordered_Set n (Culculateion_Map Nat_Multi (Ordered_Set n n0)))=Culculateion_Map Nat_Multi (Ordered_Set n (Ordered_Next n0))).
rewrite <- (Nat_Multi_Law_3 n n0).
rewrite <- (Nat_Multi_Law_3 n (Ordered_Next n0)).
assert (n ∈ Natural_Number_Set).
apply H.
apply Nat_Multi_n_Map_Law_1 in H3.
destruct H3.
destruct H4.
apply H5.
apply H1.
split.
apply H.
apply Peanos_Axiom_2.
apply H1.
split.
apply H.
apply H1.
rewrite <- H3.
clear H3.
rewrite <- H2.
clear H2.
rewrite -> (Nat_Add_Law_9 (Ordered_Next n0) n (Culculateion_Map Nat_Multi (Ordered_Set n n0))).
rewrite -> (Nat_Add_Law_9 (Ordered_Next n) n0 (Culculateion_Map Nat_Multi (Ordered_Set n n0))).
rewrite <- (Nat_Add_Law_7 n0 n).
rewrite <- (Nat_Add_Law_7 n n0).
rewrite <- (Nat_Add_Law_8 n n0).
split.
split.
apply H.
apply H1.
split.
apply H.
apply H1.
split.
apply H1.
apply H.
split.
apply Peanos_Axiom_2.
apply H.
split.
apply H1.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n n0)).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n0.
split.
split.
split.
apply H.
apply H1.
split.
apply Peanos_Axiom_2.
apply H1.
split.
apply H.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n n0)).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n0.
split.
split.
split.
apply H.
apply H1.
apply H1.
apply H0.
Qed.

Theorem Nat_Multi_Law_7:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Culculateion_Map Nat_Add (Ordered_Set n (Culculateion_Map Nat_Multi (Ordered_Set n m)))=Culculateion_Map Nat_Multi (Ordered_Set n (Ordered_Next m)).
Proof.
intros.
destruct H.
rewrite <- (Nat_Multi_Law_3 n (Ordered_Next m)).
assert (n ∈ Natural_Number_Set).
apply H.
apply Nat_Multi_n_Map_Law_1 in H.
destruct H.
destruct H2.
assert (m ∈ Natural_Number_Set).
apply H0.
apply H3 in H0.
rewrite <- H0.
rewrite -> (Nat_Multi_Law_3 n m).
split.
split.
apply H1.
apply H4.
split.
apply H.
apply Peanos_Axiom_2.
apply H0.
Qed.

Theorem Nat_Multi_Law_8:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set n m)=Culculateion_Map Nat_Multi (Ordered_Set m n).
Proof.
intros.
destruct H.
assert (forall m0:Set,m0 ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set n m0)=Culculateion_Map Nat_Multi (Ordered_Set m0 n)).
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Multi (Ordered_Set n a)=Culculateion_Map Nat_Multi (Ordered_Set a n))).
split.
rewrite -> Nat_Multi_Law_4.
rewrite -> Nat_Multi_Law_5.
split.
apply H.
apply H.

intros.
destruct H1.
rewrite <- Nat_Multi_Law_6.
rewrite <- Nat_Multi_Law_7.
rewrite -> H2.
split.
split.
apply H.
apply H1.
split.
apply H1.
apply H.
apply H1.
apply H0.
Qed.

Theorem Nat_Multi_Law_9:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set->(Culculateion_Map Nat_Multi (Ordered_Set n1 (Culculateion_Map Nat_Add (Ordered_Set n2 n3)))=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set n1 n2)) (Culculateion_Map Nat_Multi (Ordered_Set n1 n3)))).
Proof.
intros.
destruct H.
destruct H0.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Multi (Ordered_Set a (Culculateion_Map Nat_Add (Ordered_Set n2 n3)))=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set a n2)) (Culculateion_Map Nat_Multi (Ordered_Set a n3))))).
split.
rewrite -> (Nat_Multi_Law_5 (Culculateion_Map Nat_Add (Ordered_Set n2 n3))).
rewrite -> (Nat_Multi_Law_5 n2).
rewrite -> (Nat_Multi_Law_5 n3).
rewrite -> (Nat_Add_Law_4 (∅)).
split.
apply Peanos_Axiom_1.
apply H1.
apply H0.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n3.
split.
split.
split.
apply H0.
apply H1.

intros.
destruct H2.
rewrite <- (Nat_Multi_Law_6 n (Culculateion_Map Nat_Add (Ordered_Set n2 n3))).
rewrite -> H3.
rewrite <- (Nat_Multi_Law_6 n n2).
rewrite <- (Nat_Multi_Law_6 n n3).
rewrite <- (Nat_Add_Law_9 n2 n3 (Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set n n2)) (Culculateion_Map Nat_Multi (Ordered_Set n n3))))).
rewrite <- (Nat_Add_Law_9 n2 (Culculateion_Map Nat_Multi (Ordered_Set n n2)) (Culculateion_Map Nat_Add (Ordered_Set n3 (Culculateion_Map Nat_Multi (Ordered_Set n n3))))).
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Multi (Ordered_Set n n2)) n3 (Culculateion_Map Nat_Multi (Ordered_Set n n3))).
rewrite -> (Nat_Add_Law_8 (Culculateion_Map Nat_Multi (Ordered_Set n n2)) n3).
rewrite -> (Nat_Add_Law_9 n3 (Culculateion_Map Nat_Multi (Ordered_Set n n2)) (Culculateion_Map Nat_Multi (Ordered_Set n n3))).
split.
split.
apply H1.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n3.
split.
split.
split.
apply H2.
apply H1.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
apply H1.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
split.
apply H1.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n3.
split.
split.
split.
apply H2.
apply H1.
split.
apply H0.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n3.
exists (Culculateion_Map Nat_Multi (Ordered_Set n n3)).
split.
split.
split.
apply H1.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n3.
split.
split.
split.
apply H2.
apply H1.
split.
apply H0.
split.
apply H1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Multi (Ordered_Set n n2)).
exists (Culculateion_Map Nat_Multi (Ordered_Set n n3)).
split.
split.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n3.
split.
split.
split.
apply H2.
apply H1.
split.
apply H2.
apply H1.
split.
apply H2.
apply H0.
split.
apply H2.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n3.
split.
split.
split.
apply H0.
apply H1.
apply H.
Qed.

Theorem Nat_Multi_Law_10:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set->(Culculateion_Map Nat_Multi (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) n3)=Culculateion_Map Nat_Add (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set n1 n3)) (Culculateion_Map Nat_Multi (Ordered_Set n2 n3)))).
Proof.
intros.
destruct H.
destruct H0.

rewrite -> (Nat_Multi_Law_8 n1 n3).
rewrite -> (Nat_Multi_Law_8 n2 n3).
rewrite <- (Nat_Multi_Law_9 n3 n1 n2).
rewrite -> (Nat_Multi_Law_8 (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) n3).
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
apply H1.
split.
apply H1.
split.
apply H.
apply H0.
split.
apply H0.
apply H1.
split.
apply H.
apply H1.
Qed.

Theorem Nat_Multi_Law_11:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set->(Culculateion_Map Nat_Multi (Ordered_Set n1 (Culculateion_Map Nat_Multi (Ordered_Set n2 n3)))=Culculateion_Map Nat_Multi (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set n1 n2)) n3)).
Proof.
intros.
destruct H.
destruct H0.

apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Multi (Ordered_Set a (Culculateion_Map Nat_Multi (Ordered_Set n2 n3)))=Culculateion_Map Nat_Multi (Ordered_Set (Culculateion_Map Nat_Multi (Ordered_Set a n2)) n3))).
split.
rewrite -> (Nat_Multi_Law_5 (Culculateion_Map Nat_Multi (Ordered_Set n2 n3))).
rewrite -> (Nat_Multi_Law_5 n2).
rewrite -> (Nat_Multi_Law_5 n3).
split.
apply H1.
apply H0.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n3.
split.
split.
split.
apply H0.
apply H1.
intros.
destruct H2.
rewrite <- (Nat_Multi_Law_6 n (Culculateion_Map Nat_Multi (Ordered_Set n2 n3))).
rewrite -> H3.
rewrite <- (Nat_Multi_Law_6 n n2).
rewrite -> (Nat_Multi_Law_10 n2 (Culculateion_Map Nat_Multi (Ordered_Set n n2)) n3).
split.
split.
apply H0.
split.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists n2.
split.
split.
split.
apply H2.
apply H0.
apply H1.
split.
apply H2.
apply H0.
split.
apply H2.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists n3.
split.
split.
split.
apply H0.
apply H1.
apply H.
Qed.

Theorem Nat_Multi_Law_12:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set/\n3=∅/\Culculateion_Map Nat_Multi (Ordered_Set n1 n3)=Culculateion_Map Nat_Multi (Ordered_Set n2 n3)->n1=n2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
assert (forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set n1 n) = Culculateion_Map Nat_Multi (Ordered_Set n2 n)->n1=n2).
intro.
intro.
apply (Mathemetical_Induction_1 (fun a=>Culculateion_Map Nat_Multi (Ordered_Set n1 a)=Culculateion_Map Nat_Multi (Ordered_Set n2 a)->n1=n2)).
split.

Qed.

Theorem Nat_Multi_Law_13:forall n1 n2 n3:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\n3 ∈ Natural_Number_Set/\n1=∅/\Culculateion_Map Nat_Multi (Ordered_Set n1 n2)=Culculateion_Map Nat_Multi (Ordered_Set n1 n3)->n2=n3.
Proof.

Qed.

Theorem Nat_Multi_Law_14:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Culculateion_Map Nat_Multi (Ordered_Set n1 n2) ∈ Natural_Number_Set.
Proof.
intros.
apply (Map_Law_2 Nat_Multi (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n1 n2)).
split.
apply Nat_Multi_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
apply H.
Qed.