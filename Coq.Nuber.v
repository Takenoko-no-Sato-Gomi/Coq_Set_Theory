Require Export Coq_Basic.



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
apply Ordered_Next_Law_2.
apply H.
intros.

split.
intros.
apply Ordered_Next_Law_1 in H2.
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
Qed.

Theorem Peanos_Axiom_3:forall n m:Set,(n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set/\Ordered_Next n=Ordered_Next m)->n=m.
Proof.
intros.
destruct H.
destruct H0.
assert (n ∈ (Ordered_Next n)).
apply Ordered_Next_Law_1.
right.
split.
rewrite -> H1 in H2.
assert (m ∈ (Ordered_Next m)).
apply Ordered_Next_Law_1.
right.
split.
rewrite <- H1 in H3.
apply Ordered_Next_Law_1 in H2.
apply Ordered_Next_Law_1 in H3.
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
rewrite <- H8.
apply Ordered_Next_Law_1.
right.
split.
apply H9.
apply H4 in H10.
destruct H10.
rewrite <- H8.
apply Ordered_Next_Law_1.
right.
split.
destruct H5.
rewrite -> H8.
apply H0.
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



Definition Add_n_Map(n:Set):=Well_Defined (fun f=>(Map f Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map f (∅)=n)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map f m))=((Culculateion_Map f (Ordered_Next m)))))).

Theorem Add_n_Map_Law_1:forall n:Set,n ∈ Natural_Number_Set->(Map (Add_n_Map n) Natural_Number_Set Natural_Number_Set)/\(Culculateion_Map (Add_n_Map n) (∅)=n)/\(forall m:Set,m ∈ Natural_Number_Set->((Ordered_Next (Culculateion_Map (Add_n_Map n) m))=((Culculateion_Map (Add_n_Map n) (Ordered_Next m))))).
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

Definition Add:=Prop_Set (fun x=>exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Add_n_Map n1) n2))).

Theorem Add_Law_1:forall x0:Set,x0 ∈ Add<->(exists n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\x0=(Ordered_Set (Ordered_Set n1 n2) (Culculateion_Map (Add_n_Map n1) n2))).
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
apply (Map_Law_2  (Add_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Add_n_Map_Law_1 in H.
destruct H.
apply H.
apply H2.
rewrite -> H0 in H1.
apply Single_Set_Law_1 in H1.
rewrite -> H1.
right.
apply (Map_Law_2  (Add_n_Map x1) Natural_Number_Set Natural_Number_Set x2).
split.
apply Add_n_Map_Law_1 in H.
destruct H.
apply H.
apply H2.
Qed.

Theorem Add_Law_2:Map Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set.
Proof.
split.
intros.
apply Add_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
exists (Ordered_Set x x0).
exists (Culculateion_Map (Add_n_Map x) x0).
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
apply (Map_Law_2  (Add_n_Map x) Natural_Number_Set Natural_Number_Set x0).
split.
apply Add_n_Map_Law_1 in H.
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
exists (Culculateion_Map (Add_n_Map x0) x1).
split.
split.
apply Add_Law_1.
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
apply (Map_Law_2  (Add_n_Map x0) Natural_Number_Set Natural_Number_Set x1).
split.
apply Add_n_Map_Law_1.
apply H0.
apply H1.
intros.
destruct H2.
apply Add_Law_1 in H2.
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

Theorem Add_Law_3:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Add (Ordered_Set n (∅))=n.
Proof.
intros.
rewrite -> (Map_Law_3 Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n (∅))).
split.
split.
apply Add_Law_2.
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
apply Add_Law_1.
exists n.
exists (∅).
split.
apply H.
split.
apply Peanos_Axiom_1.
apply Ordered_Set_Law_2.
split.
split.
apply (Map_Law_3 (Add_n_Map n) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply Add_n_Map_Law_1.
apply H.
split.
apply Peanos_Axiom_1.
split.
apply H.
apply Add_n_Map_Law_1 in H.
destruct H.
destruct H0.
assert (Ordered_Set (∅) (Culculateion_Map (Add_n_Map n) (∅)) ∈ Add_n_Map n).
apply (Map_Law_1 (Add_n_Map n) Natural_Number_Set Natural_Number_Set (∅)).
split.
apply H.
apply Peanos_Axiom_1.
rewrite -> H0 in H2.
apply H2.
Qed.

Theorem Add_Law_4:forall n:Set,n ∈ Natural_Number_Set->Culculateion_Map Add (Ordered_Set (∅) n)=n.
Proof.
intros.
rewrite <- (Map_Law_3 Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (∅) n) n).
split.
split.
apply Add_Law_2.
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
apply Add_Law_1.
exists (∅).
exists n.
split.
apply Peanos_Axiom_1.
split.
apply H.
apply Ordered_Set_Law_2.
split.
split.
destruct (Add_n_Map_Law_1 (∅)).
apply Peanos_Axiom_1.
destruct H1.
assert (forall n0:Set,n0 ∈ Natural_Number_Set->n0=Culculateion_Map (Add_n_Map (∅)) n0).
intro.
apply (Mathemetical_Induction_1 (fun n1=>n1=Culculateion_Map (Add_n_Map (∅)) n1)).
split.
rewrite -> H1.
split.
intros.
destruct H3.
apply H2 in H3.
assert ((Ordered_Next (Culculateion_Map (Add_n_Map (∅)) n1))=Culculateion_Map (Add_n_Map (∅)) (Ordered_Next n1)).
rewrite -> H3.
split.
rewrite <- H4 in H5.
apply H5.
apply H3 in H.
apply H.
Qed.

Theorem Add_Law_5:forall n m:Set,n ∈ Natural_Number_Set/\m ∈ Natural_Number_Set->Culculateion_Map Add (Ordered_Set n m)=Culculateion_Map Add (Ordered_Set m n).
Proof.
intros.
destruct H.
assert (forall m0:Set,m0 ∈ Natural_Number_Set->Culculateion_Map Add (Ordered_Set n m0)=Culculateion_Map Add (Ordered_Set m0 n)).
intro.
apply (Mathemetical_Induction_1 (fun m1=>Culculateion_Map Add (Ordered_Set n m1)=Culculateion_Map Add (Ordered_Set m1 n))).
split.
assert (n ∈ Natural_Number_Set).
apply H.
apply Add_Law_3 in H.
apply Add_Law_4 in H1.
rewrite -> H.
rewrite -> H1.
split.
intros.
destruct H1.
assert (Culculateion_Map Add (Ordered_Set n (Ordered_Next n0))=Culculateion_Map (Add_n_Map n) (Ordered_Next n0)).
rewrite -> (Map_Law_3 Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set n (Ordered_Next n0)) (Culculateion_Map (Add_n_Map n) (Ordered_Next n0))).
split.
split.
apply Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists n.
exists (Ordered_Next n0).
split.
split.
split.
apply H.
apply Peanos_Axiom_2.
apply H1.
split.
apply (Map_Law_2 (Add_n_Map n) Natural_Number_Set Natural_Number_Set (Ordered_Next n0)).
split.
apply Add_n_Map_Law_1.
apply H.
apply Peanos_Axiom_2.
apply H1.
apply Add_Law_1.
exists n.
exists (Ordered_Next n0).
split.
apply H.
split.
apply Peanos_Axiom_2.
apply H1.
split.
rewrite -> H3.
assert (Culculateion_Map Add (Ordered_Set (Ordered_Next n0) n)=Culculateion_Map (Add_n_Map (Ordered_Next n0)) n).
rewrite -> (Map_Law_3 Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set (Ordered_Next n0) n) (Culculateion_Map (Add_n_Map (Ordered_Next n0)) n)).
split.
split.
apply Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Next n0).
exists n.
split.
split.
split.
apply Peanos_Axiom_2.
apply H1.
apply H.
split.
apply (Map_Law_2 (Add_n_Map (Ordered_Next n0)) Natural_Number_Set Natural_Number_Set n).
split.
apply Add_n_Map_Law_1.
apply Peanos_Axiom_2.
apply H1.
apply H.
apply Add_Law_1.
exists (Ordered_Next n0).
exists n.
split.
apply Peanos_Axiom_2.
apply H1.
split.
apply H.
split.
rewrite -> H4.
assert (n ∈ Natural_Number_Set).
apply H.
assert (n0 ∈ Natural_Number_Set).
apply H1.
apply Add_n_Map_Law_1 in H.


rewrite <- H5.
Qed. 