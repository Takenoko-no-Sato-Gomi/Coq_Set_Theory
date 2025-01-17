Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.
Require Export Set_Theory_Ordered_Relation.
Require Export Set_Theory_Ordered_Number.
Require Export Set_Theory_Natural_Number.



Definition Integer_Reration:=Prop_Set (fun a=>exists n1 m1 n2 m2:Set,a=Ordered_Set (Ordered_Set n1 m1) (Ordered_Set n2 m2)/\n1 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 m2)=Culculateion_Map Nat_Add (Ordered_Set n2 m1)).

Definition Integer_Number:=Quotient_Set Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set).

Definition Plus_Integer_Number(n:Set):=Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n (∅)).

Definition Minus_Integer_Number(n:Set):=Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) n).

Definition Zero_Integer_Number:=Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) (∅)).

Theorem Integer_Number_Law_1:forall a:Set,a ∈ Integer_Reration<->exists n1 m1 n2 m2:Set,a=Ordered_Set (Ordered_Set n1 m1) (Ordered_Set n2 m2)/\n1 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 m2)=Culculateion_Map Nat_Add (Ordered_Set n2 m1).
Proof.
intro.
apply Prop_Set_Law_1.
exists (Power_Set (Power_Set (Power_Set (Power_Set Natural_Number_Set)))).
intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
apply Power_Set_Law_1.
intro.
intro.
rewrite -> H in H5.
apply Ordered_Set_Law_1 in H5.
destruct H5.
rewrite -> H5 in H6.
apply Pair_Set_Law_1 in H6.
destruct H6.
rewrite -> H6 in H7.
apply Ordered_Set_Law_1 in H7.
destruct H7.
rewrite -> H7 in H8.
apply Pair_Set_Law_1 in H8.
destruct H8.
rewrite -> H8.
apply H0.
rewrite -> H8.
apply H1.
rewrite -> H7 in H8.
apply Single_Set_Law_1 in H8.
rewrite -> H8.
apply H1.
rewrite -> H6 in H7.
apply Ordered_Set_Law_1 in H7.
destruct H7.
rewrite -> H7 in H8.
apply Pair_Set_Law_1 in H8. 
destruct H8.
rewrite -> H8.
apply H2.
rewrite -> H8.
apply H3.
rewrite -> H7 in H8.
apply Single_Set_Law_1 in H8.
rewrite -> H8.
apply H3.
rewrite -> H5 in H6.
apply Single_Set_Law_1 in H6.
rewrite -> H6 in H7.
apply Ordered_Set_Law_1 in H7.
destruct H7.
rewrite -> H7 in H8.
apply Pair_Set_Law_1 in H8.
destruct H8.
rewrite -> H8.
apply H2.
rewrite -> H8.
apply H3.
rewrite -> H7 in H8.
apply Single_Set_Law_1 in H8.
rewrite -> H8.
apply H3.
Qed.

Theorem Integer_Number_Law_2:Equivalenc_Relation Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set).
Proof.
split.
intro.
intro.
apply Integer_Number_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
exists (Ordered_Set x x0).
exists (Ordered_Set x1 x2).
split.
apply H.
split.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
split.
split.
apply H0.
apply H1.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H2.
apply H3.
split.

intro.
intros.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists x0.
exists x1.
split.
rewrite <- H.
split.
split.
apply H0.
split.
apply H1.
split.
apply H0.
split.
apply H1.
split.
split.

intro.
intros.
apply Integer_Number_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
apply Integer_Number_Law_1.
exists x2.
exists x3.
exists x0.
exists x1.
split.
apply Ordered_Set_Law_2.
apply Ordered_Set_Law_2 in H.
destruct H.
split.
apply H5.
apply H.
split.
apply H2.
split.
apply H3.
split.
apply H0.
split.
apply H1.
symmetry.
apply H4.

intro.
intros.
destruct H.
apply Integer_Number_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
apply Ordered_Set_Law_2 in H.
destruct H.
apply Integer_Number_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H7.
destruct H8.
destruct H9.
destruct H10.
apply Ordered_Set_Law_2 in H0.
destruct H0.
rewrite -> H.
rewrite -> H12.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists x6.
exists x7.
split.
split.
split.
apply H1.
split.
apply H2.
split.
apply H9.
split.
apply H10.
apply (Nat_Add_Law_10 (Culculateion_Map Nat_Add (Ordered_Set x0 x7)) (Culculateion_Map Nat_Add (Ordered_Set x6 x1)) (Culculateion_Map Nat_Add (Ordered_Set x3 x4))).
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x7.
split.
split.
split.
apply H1.
apply H10.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x6 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x1.
split.
split.
split.
apply H9.
apply H2.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x4.
split.
split.
split.
apply H4.
apply H7.
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x7)) x3 x4).
rewrite -> (Nat_Add_Law_8 x0 x7).
rewrite <- (Nat_Add_Law_9 x7 x0 x3).
rewrite -> H5.
rewrite -> (Nat_Add_Law_8 x7 (Culculateion_Map Nat_Add (Ordered_Set x2 x1))).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x2 x1)) x7 x4).
rewrite -> (Nat_Add_Law_8 x7 x4).
rewrite -> H11.
rewrite -> H6 in H0.
apply Ordered_Set_Law_2 in H0.
destruct H0.
rewrite -> H0.
rewrite -> H13.
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x4 x1)) x6 x5).
rewrite <- (Nat_Add_Law_9 x4 x1 x6).
rewrite -> (Nat_Add_Law_8 x4 (Culculateion_Map Nat_Add (Ordered_Set x1 x6))).
rewrite -> (Nat_Add_Law_8  x1 x6).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x6 x1)) x4 x5).
rewrite -> (Nat_Add_Law_8  x5 x4).
split.
split.
apply H8.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x6 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x1.
split.
split.
split.
apply H9.
apply H2.
split.
apply H7.
apply H8.
split.
apply H2.
apply H9.
split.
apply H7.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x6.
split.
split.
split.
apply H2.
apply H9.
split.
apply H7.
split.
apply H2.
apply H9.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x1.
split.
split.
split.
apply H7.
apply H2.
split.
apply H9.
apply H8.
split.
apply H10.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x2 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x1.
split.
split.
split.
apply H3.
apply H2.
split.
apply H10.
apply H7.
split.
apply H10.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x2 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x1.
split.
split.
split.
apply H3.
apply H2.
split.
apply H10.
split.
apply H1.
apply H4.
split.
apply H1.
apply H10.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x7.
split.
split.
split.
apply H1.
apply H10.
split.
apply H4.
apply H7.
Qed.

Theorem Integer_Number_Law_3:forall n:Set,n ∈ Integer_Number->(exists n0:Set,n=Plus_Integer_Number n0)\/(exists n0:Set,n=Minus_Integer_Number n0).
Proof.
intros.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H1.
rewrite <- H in H0.
assert (Ordered_Number x0/\Ordered_Number x1).
split.
apply Natural_Number_Set_Law_1 in H1.
apply H1.
apply Natural_Number_Set_Law_1 in H2.
apply H2.
apply Ordered_Number_Law_5 in H3.
destruct H3.

right.
assert (x0 ∈ Natural_Number_Set/\x1 ∈ Natural_Number_Set/\x0 ∈ x1).
split.
apply H1.
split.
apply H2.
apply H3.
apply Nat_Add_Law_12 in H4.
destruct H4.
destruct H4.
exists x2.
rewrite -> H0.
unfold Minus_Integer_Number.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set x0 x1) (Ordered_Set (∅) x2) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H1.
apply H2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (∅).
exists x2.
split.
split.
split.
apply Peanos_Axiom_1.
apply H4.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists (∅).
exists x2.
split.
split.
split.
apply H1.
split.
apply H2.
split.
apply Peanos_Axiom_1.
split.
apply H4.
rewrite -> (Nat_Add_Law_5 x1).
symmetry.
apply H5.
apply H2.

destruct H3.
left.
exists (∅).
rewrite -> H0.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set x0 x1) (Ordered_Set (∅) (∅)) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H1.
apply H2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (∅).
exists (∅).
split.
split.
split.
apply Peanos_Axiom_1.
apply Peanos_Axiom_1.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists (∅).
exists (∅).
split.
split.
split.
apply H1.
split.
apply H2.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_5 x1).
rewrite <- H3.
apply Nat_Add_Law_4.
apply H1.
apply H2.
left.

assert (x1 ∈ Natural_Number_Set/\x0 ∈ Natural_Number_Set/\x1 ∈ x0).
split.
apply H2.
split.
apply H1.
apply H3.
apply Nat_Add_Law_12 in H4.
destruct H4.
destruct H4.
exists x2.
rewrite -> H0.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set x0 x1) (Ordered_Set x2 (∅)) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H1.
apply H2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists (∅).
split.
split.
split.
apply H4.
apply Peanos_Axiom_1.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists x2.
exists (∅).
split.
split.
split.
apply H1.
split.
apply H2.
split.
apply H4.
split.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_4 x0).
rewrite -> (Nat_Add_Law_8 x2 x1).
apply H5.
split.
apply H4.
apply H2.
apply H1.
Qed.



Definition Int_Add:=Prop_Set (fun a=>exists n1 n2 m1 m2:Set,a=(Ordered_Set (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set m1 m2)))))/\n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set).

Theorem Int_Add_Law_1:forall a:Set,a ∈ Int_Add<->exists n1 n2 m1 m2:Set,a=(Ordered_Set (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set m1 m2)))))/\n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number).
intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
rewrite -> H.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x1 x3))).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x1)) (Culculateion_Map Nat_Add (Ordered_Set x2 x3)))).
split.
split.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x1 x3)).
split.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x0 x2).
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x2.
split.
split.
split.
apply H0.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x1 x3).
split.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x3.
split.
split.
split.
apply H1.
apply H3.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x1)) (Culculateion_Map Nat_Add (Ordered_Set x2 x3))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x0 x1)).
exists (Culculateion_Map Nat_Add (Ordered_Set x2 x3)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H0.
apply H1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x2 x3)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x2.
exists x3.
split.
split.
split.
apply H2.
apply H3.
split.
Qed.

Theorem Int_Add_Law_2:Map Int_Add (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number.
Proof.
split.
intros.
apply Int_Add_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
exists (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x x1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2))).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x x0)) (Culculateion_Map Nat_Add (Ordered_Set x1 x2)))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x x1)).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)).
split.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x x1).
split.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x1.
split.
split.
split.
apply H0.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x0 x2).
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x2.
split.
split.
split.
apply H1.
apply H3.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x x0)) (Culculateion_Map Nat_Add (Ordered_Set x1 x2))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x x0)).
exists (Culculateion_Map Nat_Add (Ordered_Set x1 x2)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x x0)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x0.
split.
split.
split.
apply H0.
apply H1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x2)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x2.
split.
split.
split.
apply H2.
apply H3.
split.
apply H.

intros.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H6.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7)))).
split.
split.
apply Int_Add_Law_1.
exists x3.
exists x6.
exists x4.
exists x7.
split.
rewrite <- H.
rewrite -> H2.
rewrite <- H0.
rewrite -> H5.
rewrite <- H1.
split.
split.
apply H3.
split.
apply H6.
split.
apply H4.
apply H7.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x7)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H3.
apply H6.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x7.
split.
split.
split.
apply H4.
apply H7.
split.
intros.
destruct H8.
apply Int_Add_Law_1 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H8.
destruct H8.
destruct H10.
destruct H11.
destruct H12.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H14.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x8 x9)) (Culculateion_Map Nat_Add (Ordered_Set x10 x11))) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x7)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H3.
apply H6.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x7.
split.
split.
split.
apply H4.
apply H7.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x8 x9)).
exists (Culculateion_Map Nat_Add (Ordered_Set x10 x11)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x8 x9)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x8.
exists x9.
split.
split.
split.
apply H10.
apply H11.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x10 x11)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x10.
exists x11.
split.
split.
split.
apply H12.
apply H13.
apply Integer_Number_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x7)).
exists (Culculateion_Map Nat_Add (Ordered_Set x8 x9)).
exists (Culculateion_Map Nat_Add (Ordered_Set x10 x11)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H3.
apply H6.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x7.
split.
split.
split.
apply H4.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x8 x9)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x8.
exists x9.
split.
split.
split.
apply H10.
apply H11.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x10 x11)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x10.
exists x11.
split.
split.
split.
apply H12.
apply H13.
assert (Culculateion_Map Nat_Add (Ordered_Set x3 x10)=Culculateion_Map Nat_Add (Ordered_Set x8 x4)/\Culculateion_Map Nat_Add (Ordered_Set x6 x11)=Culculateion_Map Nat_Add (Ordered_Set x9 x7)).
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x3 x4)=Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x8 x10)/\Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x6 x7)=Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x9 x11)).
apply Ordered_Set_Law_2.
rewrite -> H0.
rewrite -> H1.
rewrite <- H2.
rewrite <- H5.
rewrite -> H.
apply H8.
destruct H15.
split.
assert (Relation_Prop Integer_Reration (Ordered_Set x3 x4) (Ordered_Set x8 x10)).
apply (Equivalence_Class_Law_4 Integer_Reration (Ordered_Set x3 x4) (Ordered_Set x8 x10) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x4.
split.
split.
split.
apply H3.
apply H4.
split.
apply Double_Direct_Product_Set_Law_1.
exists x8.
exists x10.
split.
split.
split.
apply H10.
apply H12.
apply H15.
apply Integer_Number_Law_1 in H17.
destruct H17.
destruct H17.
destruct H17.
destruct H17.
destruct H17.
destruct H18.
destruct H19.
destruct H20.
destruct H21.
apply Ordered_Set_Law_2 in H17.
destruct H17.
apply Ordered_Set_Law_2 in H17.
destruct H17.
apply Ordered_Set_Law_2 in H23.
destruct H23.
rewrite -> H17.
rewrite -> H24.
rewrite -> H23.
rewrite -> H25.
apply H22.
assert (Relation_Prop Integer_Reration (Ordered_Set x6 x7) (Ordered_Set x9 x11)).
apply (Equivalence_Class_Law_4 Integer_Reration (Ordered_Set x6 x7) (Ordered_Set x9 x11) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x7.
split.
split.
split.
apply H6.
apply H7.
split.
apply Double_Direct_Product_Set_Law_1.
exists x9.
exists x11.
split.
split.
split.
apply H11.
apply H13.
apply H16.
apply Integer_Number_Law_1 in H17.
destruct H17.
destruct H17.
destruct H17.
destruct H17.
destruct H17.
destruct H18.
destruct H19.
destruct H20.
destruct H21.
apply Ordered_Set_Law_2 in H17.
destruct H17.
apply Ordered_Set_Law_2 in H17.
destruct H17.
apply Ordered_Set_Law_2 in H23.
destruct H23.
rewrite -> H17.
rewrite -> H24.
rewrite -> H23.
rewrite -> H25.
apply H22.
destruct H15.
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) x10 x11).
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x8 x9)) x4 x7).
rewrite <- (Nat_Add_Law_9 x3 x6 x10).
rewrite <- (Nat_Add_Law_9 x8 x9 x4).
rewrite -> (Nat_Add_Law_8 x6 x10).
rewrite -> (Nat_Add_Law_8 x9 x4).
rewrite -> (Nat_Add_Law_9 x3 x10 x6).
rewrite -> (Nat_Add_Law_9 x8 x4 x9).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x3 x10)) x6 x11).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x8 x4)) x9 x7).
rewrite -> H15.
rewrite -> H16.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x8 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x8.
exists x4.
split.
split.
split.
apply H10.
apply H4.
split.
apply H11.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x10)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x10.
split.
split.
split.
apply H3.
apply H12.
split.
apply H6.
apply H13.
split.
apply H10.
split.
apply H4.
apply H11.
split.
apply H3.
split.
apply H12.
apply H6.
split.
apply H11.
apply H4.
split.
apply H6.
apply H12.
split.
apply H10.
split.
apply H11.
apply H4.
split.
apply H3.
split.
apply H6.
apply H12.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x8 x9)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x8.
exists x9.
split.
split.
split.
apply H10.
apply H11.
split.
apply H4.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H3.
apply H6.
split.
apply H12.
apply H13.
Qed.

Theorem Int_Add_Law_3:forall n1 m1 n2 m2:Set,n1 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set->Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set m1 m2)))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply (Map_Law_3 Int_Add (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set m1 m2))))).
split.
apply Int_Add_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2)).
split.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set n1 m1).
split.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists m1.
split.
split.
split.
apply H.
apply H0.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set n2 m2).
split.
apply Double_Direct_Product_Set_Law_1.
exists n2.
exists m2.
split.
split.
split.
apply H1.
apply H2.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set m1 m2))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set n1 n2)).
exists (Culculateion_Map Nat_Add (Ordered_Set m1 m2)).
split.
split.
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
apply H1.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set m1 m2)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists m1.
exists m2.
split.
split.
split.
apply H0.
apply H2.
split.
apply Int_Add_Law_1.
exists n1.
exists n2.
exists m1.
exists m2.
split.
split.
split.
apply H.
split.
apply H1.
split.
apply H0.
apply H2.
Qed.

Theorem Int_Add_Law_4:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Plus_Integer_Number (Culculateion_Map Nat_Add (Ordered_Set n1 n2))=Culculateion_Map Int_Add (Ordered_Set (Plus_Integer_Number n1) (Plus_Integer_Number n2)).
Proof.
intros.
destruct H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 n2)) (Culculateion_Map Nat_Add (Ordered_Set (∅) (∅))))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 (∅))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 (∅))))).
apply (Int_Add_Law_3 n1 (∅) n2 (∅)).
split.
apply H.
split.
apply Peanos_Axiom_1.
split.
apply H0.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_4 (∅)) in H1.
apply H1.
apply Peanos_Axiom_1.
Qed.

Theorem Int_Add_Law_5:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Minus_Integer_Number (Culculateion_Map Nat_Add (Ordered_Set n1 n2))=Culculateion_Map Int_Add (Ordered_Set (Minus_Integer_Number n1) (Minus_Integer_Number n2)).
Proof.
intros.
destruct H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set (∅) (∅))) (Culculateion_Map Nat_Add (Ordered_Set n1 n2)))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) n1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) n2)))).
apply (Int_Add_Law_3 (∅) n1 (∅) n2).
split.
apply Peanos_Axiom_1.
split.
apply H.
split.
apply Peanos_Axiom_1.
apply H0.
rewrite -> (Nat_Add_Law_4 (∅)) in H1.
apply H1.
apply Peanos_Axiom_1.
Qed.

Theorem Int_Add_Law_6:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 n2)=Culculateion_Map Int_Add (Ordered_Set (Plus_Integer_Number n1) (Minus_Integer_Number n2)).
Proof.
intros.
destruct H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 (∅))) (Culculateion_Map Nat_Add (Ordered_Set (∅) n2)))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 (∅))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) n2)))).
apply (Int_Add_Law_3 n1 (∅) (∅) n2).
split.
apply H.
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
apply H0.
rewrite -> (Nat_Add_Law_4 n1) in H1.
rewrite -> (Nat_Add_Law_5 n2) in H1.
apply H1.
apply H0.
apply H.
Qed.

Theorem Int_Add_Law_7:forall n1 n2:Set,n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set->Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 n1)=Culculateion_Map Int_Add (Ordered_Set (Minus_Integer_Number n1) (Plus_Integer_Number n2)).
Proof.
intros.
destruct H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set (∅) n2)) (Culculateion_Map Nat_Add (Ordered_Set n1 (∅))))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) n1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 (∅))))).
apply (Int_Add_Law_3 (∅) n1 n2 (∅)).
split.
apply Peanos_Axiom_1.
split.
apply H.
split.
apply H0.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_4 n1) in H1.
rewrite -> (Nat_Add_Law_5 n2) in H1.
apply H1.
apply H0.
apply H.
Qed.

Theorem Int_Add_Law_8:forall n1 n2:Set,n1 ∈ Integer_Number/\n2 ∈ Integer_Number->Culculateion_Map Int_Add (Ordered_Set n1 n2) ∈ Integer_Number.
Proof.
intros.
destruct H.
apply (Map_Law_2 Int_Add (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number (Ordered_Set n1 n2)).
split.
apply Int_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists n1.
exists n2.
split.
split.
split.
apply H.
apply H0.
Qed.

Theorem Int_Add_Law_9:forall n1 n2 n3:Set,n1 ∈ Integer_Number/\n2 ∈ Integer_Number/\n3 ∈ Integer_Number->Culculateion_Map Int_Add (Ordered_Set n1 (Culculateion_Map Int_Add (Ordered_Set n2 n3)))=Culculateion_Map Int_Add (Ordered_Set (Culculateion_Map Int_Add (Ordered_Set n1 n2)) n3).
Proof.
intros.
destruct H.
destruct H0.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H3.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H6.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H9.
rewrite -> H2.
rewrite <- H.
rewrite -> H5.
rewrite <- H0.
rewrite -> H8.
rewrite <- H1.
rewrite <- (Int_Add_Law_3 x3 x4 x6 x7).
rewrite <- (Int_Add_Law_3 x0 x1 (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7))).
rewrite <- (Int_Add_Law_3 x0 x1 x3 x4).
rewrite <- (Int_Add_Law_3 (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) (Culculateion_Map Nat_Add (Ordered_Set x1 x4)) x6 x7).
rewrite -> (Nat_Add_Law_9 x0 x3 x6).
rewrite -> (Nat_Add_Law_9 x1 x4 x7).
split.
split.
apply H4.
split.
apply H7.
apply H10.
split.
apply H3.
split.
apply H6.
apply H9.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x3)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x3.
split.
split.
split.
apply H3.
apply H6.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x4.
split.
split.
split.
apply H4.
apply H7.
split.
apply H9.
apply H10.
split.
apply H3.
split.
apply H4.
split.
apply H6.
apply H7.
split.
apply H3.
split.
apply H4.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H6.
apply H9.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x7.
split.
split.
split.
apply H7.
apply H10.
split.
apply H6.
split.
apply H7.
split.
apply H9.
apply H10.
Qed.

Theorem Int_Add_Law_10:forall n:Set,n ∈ Integer_Number->n=Culculateion_Map Int_Add (Ordered_Set n Zero_Integer_Number).
Proof.
intros.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H1.
rewrite -> H0.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 (∅))) (Culculateion_Map Nat_Add (Ordered_Set x1 (∅))))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) (∅))))).
apply (Int_Add_Law_3 x0 x1 (∅) (∅)).
split.
apply H1.
split.
apply H2.
split.
apply Peanos_Axiom_1.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_4 x0) in H3.
rewrite -> (Nat_Add_Law_4 x1) in H3.
rewrite <- H.
apply H3.
apply H2.
apply H1.
Qed.

Theorem Int_Add_Law_11:forall n:Set,n ∈ Integer_Number->n=Culculateion_Map Int_Add (Ordered_Set Zero_Integer_Number n).
Proof.
intros.
intros.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H1.
rewrite -> H0.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set (∅) x0)) (Culculateion_Map Nat_Add (Ordered_Set (∅) x1)))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (∅) (∅))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x1)))).
apply (Int_Add_Law_3 (∅) (∅) x0 x1).
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
split.
apply H1.
apply H2.
rewrite -> (Nat_Add_Law_5 x0) in H3.
rewrite -> (Nat_Add_Law_5 x1) in H3.
rewrite <- H.
apply H3.
apply H2.
apply H1.
Qed.

Theorem Int_Add_Law_12:forall n1 n2 n3:Set,n1 ∈ Integer_Number/\n2 ∈ Integer_Number/\n3 ∈ Integer_Number/\Culculateion_Map Int_Add (Ordered_Set n1 n3)=Culculateion_Map Int_Add (Ordered_Set n2 n3)->n1=n2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H4.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H7.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H10.
rewrite -> H3.
rewrite -> H6.
rewrite <- H.
rewrite <- H0.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set x0 x1) (Ordered_Set x3 x4) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H4.
apply H5.
split.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x4.
split.
split.
split.
apply H7.
apply H8.
apply Integer_Number_Law_1.
exists x0.
exists x1.
exists x3.
exists x4.
split.
split.
split.
apply H4.
split.
apply H5.
split.
apply H7.
split.
apply H8.
apply (Nat_Add_Law_10 (Culculateion_Map Nat_Add (Ordered_Set x0 x4)) (Culculateion_Map Nat_Add (Ordered_Set x3 x1)) (Culculateion_Map Nat_Add (Ordered_Set x6 x7))).
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x4.
split.
split.
split.
apply H4.
apply H8.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x1.
split.
split.
split.
apply H7.
apply H5.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x6 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x7.
split.
split.
split.
apply H10.
apply H11.
assert (Relation_Prop Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) (Culculateion_Map Nat_Add (Ordered_Set x1 x7))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7)))).
apply (Equivalence_Class_Law_4 Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) (Culculateion_Map Nat_Add (Ordered_Set x1 x7))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) (Culculateion_Map Nat_Add (Ordered_Set x4 x7))) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x0 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x1 x7)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x6.
split.
split.
split.
apply H4.
apply H10.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x7.
split.
split.
split.
apply H5.
apply H11.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x7)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H7.
apply H10.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x4 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x4.
exists x7.
split.
split.
split.
apply H8.
apply H11.
rewrite -> H3 in H2.
rewrite <- H in H2.
rewrite -> H6 in H2.
rewrite <- H0 in H2.
rewrite -> H9 in H2.
rewrite <- H1 in H2.
rewrite <- (Int_Add_Law_3 x0 x1 x6 x7) in H2.
rewrite <- (Int_Add_Law_3 x3 x4 x6 x7) in H2.
apply H2.
split.
apply H7.
split.
apply H8.
split.
apply H10.
apply H11.
split.
apply H4.
split.
apply H5.
split.
apply H10.
apply H11.
apply Integer_Number_Law_1 in H12.
destruct H12.
destruct H12.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
destruct H14.
destruct H15.
destruct H16.
apply Ordered_Set_Law_2 in H12.
destruct H12.
apply Ordered_Set_Law_2 in H12.
destruct H12.
apply Ordered_Set_Law_2 in H18.
destruct H18.
rewrite <- H12 in H17.
rewrite <- H19 in H17.
rewrite <- H18 in H17.
rewrite <- H20 in H17.
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x4)) x6 x7).
rewrite <- (Nat_Add_Law_9 x0 x4 x6).
rewrite -> (Nat_Add_Law_8 x4 x6).
rewrite -> (Nat_Add_Law_9 x0 x6 x4).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) x4 x7).
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x3 x1)) x6 x7).
rewrite <- (Nat_Add_Law_9 x3 x1 x6).
rewrite -> (Nat_Add_Law_8 x1 x6).
rewrite -> (Nat_Add_Law_9 x3 x6 x1).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x3 x6)) x1 x7).
apply H17.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x6.
split.
split.
split.
apply H7.
apply H10.
split.
apply H5.
apply H11.
split.
apply H7.
split.
apply H10.
apply H5.
split.
apply H5.
apply H10.
split.
apply H7.
split.
apply H5.
apply H10.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x1.
split.
split.
split.
apply H7.
apply H5.
split.
apply H10.
apply H11.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x6.
split.
split.
split.
apply H4.
apply H10.
split.
apply H8.
apply H11.
split.
apply H4.
split.
apply H10.
apply H8.
split.
apply H8.
apply H10.
split.
apply H4.
split.
apply H8.
apply H10.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x4.
split.
split.
split.
apply H4.
apply H8.
split.
apply H10.
apply H11.
Qed.

Theorem Int_Add_Law_13:forall n1 n2 n3:Set,n1 ∈ Integer_Number/\n2 ∈ Integer_Number/\n3 ∈ Integer_Number/\Culculateion_Map Int_Add (Ordered_Set n1 n2)=Culculateion_Map Int_Add (Ordered_Set n1 n3)->n2=n3.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H4.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H7.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H10.
rewrite -> H3 in H2.
rewrite <- H in H2.
rewrite -> H6 in H2.
rewrite <- H0 in H2.
rewrite -> H9 in H2.
rewrite <- H1 in H2.
rewrite <- (Int_Add_Law_3 x0 x1 x3 x4) in H2.
rewrite <- (Int_Add_Law_3 x0 x1 x6 x7) in H2.
rewrite -> H6.
rewrite -> H9.
rewrite <- H0.
rewrite <- H1.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set x3 x4) (Ordered_Set x6 x7) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x4.
split.
split.
split.
apply H7.
apply H8.
split.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x7.
split.
split.
split.
apply H10.
apply H11.
apply Integer_Number_Law_1.
exists x3.
exists x4.
exists x6.
exists x7.
split.
split.
split.
apply H7.
split.
apply H8.
split.
apply H10.
split.
apply H11.
apply (Nat_Add_Law_11 (Culculateion_Map Nat_Add (Ordered_Set x0 x1)) (Culculateion_Map Nat_Add (Ordered_Set x3 x7)) (Culculateion_Map Nat_Add (Ordered_Set x6 x4))).
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H4.
apply H5.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x3 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x3.
exists x7.
split.
split.
split.
apply H7.
apply H11.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x6 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x6.
exists x4.
split.
split.
split.
apply H10.
apply H8.
assert (Relation_Prop Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) (Culculateion_Map Nat_Add (Ordered_Set x1 x4))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) (Culculateion_Map Nat_Add (Ordered_Set x1 x7)))).
apply (Equivalence_Class_Law_4 Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) (Culculateion_Map Nat_Add (Ordered_Set x1 x4))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) (Culculateion_Map Nat_Add (Ordered_Set x1 x7))) (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set)).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x0 x3)).
exists (Culculateion_Map Nat_Add (Ordered_Set x1 x4)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x3)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x3.
split.
split.
split.
apply H4.
apply H7.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x4)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x4.
split.
split.
split.
apply H5.
apply H8.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x0 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x1 x7)).
split.
split.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x6.
split.
split.
split.
apply H4.
apply H10.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x1 x7)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x7.
split.
split.
split.
apply H5.
apply H11.
apply H2.
apply Integer_Number_Law_1 in H12.
destruct H12.
destruct H12.
destruct H12.
destruct H12.
destruct H12.
destruct H13.
destruct H14.
destruct H15.
destruct H16.
apply Ordered_Set_Law_2 in H12.
destruct H12.
apply Ordered_Set_Law_2 in H12.
destruct H12.
apply Ordered_Set_Law_2 in H18.
destruct H18.
rewrite <- H12 in H17.
rewrite <- H18 in H17.
rewrite <- H19 in H17.
rewrite <- H20 in H17.
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x1)) x3 x7).
rewrite -> (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x1)) x6 x4).
rewrite <- (Nat_Add_Law_9 x0 x1 x3).
rewrite <- (Nat_Add_Law_9 x0 x1 x6).
rewrite -> (Nat_Add_Law_8 x1 x3).
rewrite -> (Nat_Add_Law_8 x1 x6).
rewrite -> (Nat_Add_Law_9 x0 x3 x1).
rewrite -> (Nat_Add_Law_9 x0 x6 x1).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) x1 x7).
rewrite <- (Nat_Add_Law_9 (Culculateion_Map Nat_Add (Ordered_Set x0 x6)) x1 x4).
apply H17.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x6)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x6.
split.
split.
split.
apply H4.
apply H10.
split.
apply H5.
apply H8.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x3)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x3.
split.
split.
split.
apply H4.
apply H7.
split.
apply H5.
apply H11.
split.
apply H4.
split.
apply H10.
apply H5.
split.
apply H4.
split.
apply H7.
apply H5.
split.
apply H5.
apply H10.
split.
apply H5.
apply H7.
split.
apply H4.
split.
apply H5.
apply H10.
split.
apply H4.
split.
apply H5.
apply H7.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H4.
apply H5.
split.
apply H10.
apply H8.
split.
apply (Map_Law_2 Nat_Add (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) Natural_Number_Set (Ordered_Set x0 x1)).
split.
apply Nat_Add_Law_2.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x1.
split.
split.
split.
apply H4.
apply H5.
split.
apply H7.
apply H11.
split.
apply H4.
split.
apply H5.
split.
apply H10.
apply H11.
split.
apply H4.
split.
apply H5.
split.
apply H7.
apply H8.
Qed.

Theorem Int_Add_Law_14:forall n:Set,n ∈ Integer_Number->n=Culculateion_Map Int_Add (Ordered_Set n Zero_Integer_Number).
Proof.
intros.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H1.
rewrite -> H0.
rewrite <- H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 (∅))) (Culculateion_Map Nat_Add (Ordered_Set x1 (∅))))=Culculateion_Map Int_Add (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x1)) Zero_Integer_Number)).
apply (Int_Add_Law_3 x0 x1 (∅) (∅)).
split.
apply H1.
split.
apply H2.
split.
apply Peanos_Axiom_1.
apply Peanos_Axiom_1.
rewrite -> (Nat_Add_Law_4 x0) in H3.
rewrite -> (Nat_Add_Law_4 x1) in H3.
apply H3.
apply H2.
apply H1.
Qed.

Theorem Int_Add_Law_15:forall n:Set,n ∈ Integer_Number->n=Culculateion_Map Int_Add (Ordered_Set Zero_Integer_Number n).
Proof.
intros.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H1.
rewrite -> H0.
rewrite <- H.
assert (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set (∅) x0)) (Culculateion_Map Nat_Add (Ordered_Set (∅) x1)))=Culculateion_Map Int_Add (Ordered_Set Zero_Integer_Number (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x1)))).
apply (Int_Add_Law_3 (∅) (∅) x0 x1).
split.
apply Peanos_Axiom_1.
split.
apply Peanos_Axiom_1.
split.
apply H1.
apply H2.
rewrite -> (Nat_Add_Law_5 x0) in H3.
rewrite -> (Nat_Add_Law_5 x1) in H3.
apply H3.
apply H2.
apply H1.
Qed.

Theorem Int_Add_Law_16:forall n1 n2:Set,n1 ∈ Integer_Number/\n2 ∈ Integer_Number->Culculateion_Map Int_Add (Ordered_Set n1 n2)=Culculateion_Map Int_Add (Ordered_Set n2 n1).
Proof.
intros.
destruct H.
apply Quotient_Set_Law_1 in H.
destruct H.
destruct H.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H2.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H5.
rewrite -> H1.
rewrite <- H.
rewrite -> H4.
rewrite <- H0.
rewrite <- (Int_Add_Law_3 x0 x1 x3 x4).
rewrite <- (Int_Add_Law_3 x3 x4 x0 x1).
rewrite -> (Nat_Add_Law_8 x0 x3).
rewrite -> (Nat_Add_Law_8 x1 x4).
split.
split.
apply H3.
apply H6.
split.
apply H2.
apply H5.
split.
apply H5.
split.
apply H6.
split.
apply H2.
apply H3.
split.
apply H2.
split.
apply H3.
split.
apply H5.
apply H6.
Qed.



Definition Int_Minus:=Prop_Set (fun a=>exists n1 n2 m1 m2:Set,a=(Ordered_Set (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 m2)) (Culculateion_Map Nat_Add (Ordered_Set m1 n2)))))/\n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set).

Theorem Int_Minus_Law_1:forall a:Set,a ∈ Int_Minus<->exists n1 n2 m1 m2:Set,a=(Ordered_Set (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n1 m1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set n2 m2))) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set n1 m2)) (Culculateion_Map Nat_Add (Ordered_Set m1 n2)))))/\n1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set.
Proof.
intros.
apply Prop_Set_Law_1.
exists (Double_Direct_Product_Set (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number).
intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
rewrite -> H.
apply Double_Direct_Product_Set_Law_1.
exists (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x1 x3))).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) (Culculateion_Map Nat_Add (Ordered_Set x2 x1)))).
split.
split.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x1 x3)).
split.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x0 x2).
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x2.
split.
split.
split.
apply H0.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x1 x3).
split.
apply Double_Direct_Product_Set_Law_1.
exists x1.
exists x3.
split.
split.
split.
apply H1.
apply H3.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x0 x3)) (Culculateion_Map Nat_Add (Ordered_Set x2 x1))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x0 x3)).
exists (Culculateion_Map Nat_Add (Ordered_Set x2 x1)).
split.
split.
split.
apply (Nat_Add_Law_13 x0 x3).
split.
apply H0.
apply H3.
apply (Nat_Add_Law_13 x2 x1).
split.
apply H2.
apply H1.
split.
Qed.

Theorem Int_Minus_Law_2:Map Int_Minus (Double_Direct_Product_Set Integer_Number Integer_Number) Integer_Number.
Proof.
split.
intros.
apply Int_Minus_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
exists (Ordered_Set (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x x1)) (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2))).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x x2)) (Culculateion_Map Nat_Add (Ordered_Set x1 x0)))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x x1)).
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set x0 x2)).
split.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x x1).
split.
apply Double_Direct_Product_Set_Law_1.
exists x.
exists x1.
split.
split.
split.
apply H0.
apply H2.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set x0 x2).
split.
apply Double_Direct_Product_Set_Law_1.
exists x0.
exists x2.
split.
split.
split.
apply H1.
apply H3.
split.
split.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x x2)) (Culculateion_Map Nat_Add (Ordered_Set x1 x0))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x x2)).
exists (Culculateion_Map Nat_Add (Ordered_Set x1 x0)).
split.
split.
split.
apply Nat_Add_Law_13.
split.
apply H0.
apply H3.
apply Nat_Add_Law_13.
split.
apply H2.
apply H1.
split.
apply H.

intros.
apply Double_Direct_Product_Set_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H0.
apply Quotient_Set_Law_1 in H0.
destruct H0.
destruct H0.
apply Double_Direct_Product_Set_Law_1 in H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
apply Quotient_Set_Law_1 in H1.
destruct H1.
destruct H1.
apply Double_Direct_Product_Set_Law_1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H6.
exists (Equivalence_Class Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x7)) (Culculateion_Map Nat_Add (Ordered_Set x4 x6)))).
split.
split.
apply Int_Minus_Law_1.
rewrite <- H.
rewrite -> H2.
rewrite -> H5.
rewrite <- H0.
rewrite <- H1.
exists x3.
exists x6.
exists x4.
exists x7.
split.
apply Ordered_Set_Law_2.
split.
split.
split.
split.
apply H3.
split.
apply H6.
split.
apply H4.
apply H7.
apply Quotient_Set_Law_1.
exists (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x7)) (Culculateion_Map Nat_Add (Ordered_Set x4 x6))).
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x7)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x6)).
split.
split.
split.
apply Nat_Add_Law_13.
split.
apply H3.
apply H7.
apply Nat_Add_Law_13.
split.
apply H4.
apply H6.
split.
intros.
destruct H8.
apply Int_Minus_Law_1 in H8.
destruct H8.
destruct H8.
destruct H8.
destruct H8.
destruct H8.
destruct H10.
destruct H11.
destruct H12.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite <- H in H8.
apply Ordered_Set_Law_2 in H8.
destruct H8.
rewrite -> H14.
apply (Equivalence_Class_Law_5 Integer_Reration (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x3 x7)) (Culculateion_Map Nat_Add (Ordered_Set x4 x6))) (Ordered_Set (Culculateion_Map Nat_Add (Ordered_Set x8 x11)) (Culculateion_Map Nat_Add (Ordered_Set x10 x9)))).
split.
apply Integer_Number_Law_2.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x7)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x6)).
split.
split.
split.
apply Nat_Add_Law_13.
split.
apply H3.
apply H7.
apply Nat_Add_Law_13.
split.
apply H4.
apply H6.
split.
apply Double_Direct_Product_Set_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x8 x11)).
exists (Culculateion_Map Nat_Add (Ordered_Set x10 x9)).
split.
split.
split.
apply Nat_Add_Law_13.
split.
apply H10.
apply H13.
apply Nat_Add_Law_13.
split.
apply H12.
apply H11.
apply Integer_Number_Law_1.
exists (Culculateion_Map Nat_Add (Ordered_Set x3 x7)).
exists (Culculateion_Map Nat_Add (Ordered_Set x4 x6)).
exists (Culculateion_Map Nat_Add (Ordered_Set x8 x11)).
exists (Culculateion_Map Nat_Add (Ordered_Set x10 x9)).
split.
split.
split.
apply Nat_Add_Law_13.
split.
apply H3.
apply H7.
split.
apply Nat_Add_Law_13.
split.
apply H4.
apply H6.
split.
apply Nat_Add_Law_13.
split.
apply H10.
apply H13.
split.
apply Nat_Add_Law_13.
split.
apply H12.
apply H11.

Qed.














