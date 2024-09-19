Require Export Set_Theory_Basic.
Require Export Set_Theory_Relation.
Require Export Set_Theory_Map.
Require Export Set_Theory_Ordered_Relation.
Require Export Set_Theory_Ordered_Number.
Require Export Set_Theory_Natural_Number.



Definition Integer_Reration:=Prop_Set (fun a=>exists n1 m1 n2 m2:Set,a=Ordered_Set (Ordered_Set n1 m1) (Ordered_Set n2 m2)/\n1 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 m2)=Culculateion_Map Nat_Add (Ordered_Set n2 m1)).

Definition Integer_Number:=Quotient_Set Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set).

Definition Integer_Number_Plus(n:Set):=Equivalence_Class Integer_Reration Natural_Number_Set (Ordered_Set n (∅)).

Definition Integer_Number_Minus(n:Set):=Equivalence_Class Integer_Reration Natural_Number_Set (Ordered_Set (∅) n).

Theorem Integer_Reration_Law_1:forall a:Set,a ∈ Integer_Reration<->exists n1 m1 n2 m2:Set,a=Ordered_Set (Ordered_Set n1 m1) (Ordered_Set n2 m2)/\n1 ∈ Natural_Number_Set/\m1 ∈ Natural_Number_Set/\n2 ∈ Natural_Number_Set/\m2 ∈ Natural_Number_Set/\Culculateion_Map Nat_Add (Ordered_Set n1 m2)=Culculateion_Map Nat_Add (Ordered_Set n2 m1).
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

Theorem Integer_Reration_Law_2:Equivalenc_Relation Integer_Reration (Double_Direct_Product_Set Natural_Number_Set Natural_Number_Set).
Proof.
split.
intro.
intro.
apply Integer_Reration_Law_1 in H.
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
apply Integer_Reration_Law_1.
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
apply Integer_Reration_Law_1 in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
apply Integer_Reration_Law_1.
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
apply Integer_Reration_Law_1 in H.
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
apply Integer_Reration_Law_1 in H0.
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
apply Integer_Reration_Law_1.
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

Theorem Integer_Reration_Law_3:forall n:Set,n ∈ Integer_Number->(exists n0:Set,n=Integer_Number_Plus n0)\/(exists n0:Set,n=Integer_Number_Minus n0).
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

Qed.



Definition Int_Add:=Prop_Set (fun a=>exists n1 n2 m1 m2:Set,).



