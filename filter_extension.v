(***********************************************************************)
(*   This is part of filter extension, it is distributed under the     *)
(*      terms of the GNU Lesser General Public License version 3       *)
(*                (see file LICENSE for more details)                  *)
(*                                                                     *)
(*                       Copyright 2022-2025                           *)
(*                    Guowei Dou and Wensheng Yu                       *)
(***********************************************************************)

(** filter_extension *)

Require Export filter.

(* 滤基的定义 *)
Definition FilterBase B A := B <> Φ /\ B ⊂ pow(A)
  /\ Φ ∉ B /\ (∀ a b, a ∈ B -> b ∈ B -> (a ∩ b) ∈ B).

(* 集合A上的滤基是一个集合 *)
Corollary FilterBase_is_Set : ∀ A B, Ensemble A -> FilterBase B A -> Ensemble B.
Proof.
  intros. destruct H0 as [H0[]]. apply (MKT33 pow(A)); auto.
  apply MKT38a; auto.
Qed.

(* G具有有限交性 *)
Definition Finite_Intersection G := ∀ A, A ⊂ G -> Finite A -> ∩A <> Φ.

(* 滤基有有限交性 *)
Proposition FilterBase_Property1 : ∀ B A, FilterBase B A
  -> Finite_Intersection B.
Proof.
  intros. destruct H as [H[H0[]]].
  unfold Finite_Intersection; intros.
  destruct (classic (A0 = Φ)). rewrite H5,MKT24. intro.
  destruct MKT135. elim MKT39. rewrite H6. eauto.
  set (p := fun n => (∀ X, X ⊂ B -> X <> Φ -> P[X] = n -> ∩X ∈ B)).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction; unfold p; intros.
    - apply carE in H8. elim H7; auto.
    - apply Inf_P7_Lemma in H10 as [Y[b[H10[H11[H12[]]]]]]; auto.
      destruct (classic (Y = Φ)).
      + rewrite H15,MKT17 in H14. pose proof H11.
        apply MKT44 in H16 as []. rewrite H14,H16.
        apply H8. rewrite H14. apply MKT41; auto.
      + assert (∩Y ∈ B).
        { apply H7; auto. unfold Included; intros.
          apply H8. rewrite H14. apply MKT4; auto. }
        assert (∩X = (∩Y) ∩ b).
        { apply AxiomI; split; intros.
          - apply AxiomII in H17 as []. apply MKT4'; split.
            apply AxiomII; split; intros; auto. apply H18.
            rewrite H14. apply MKT4; auto. apply H18. rewrite H14.
            apply MKT4; right. apply MKT41; auto.
          - apply MKT4' in H17 as []. apply AxiomII; split; eauto.
            intros. apply AxiomII in H17 as [_]. rewrite H14 in H19.
            apply MKT4 in H19 as []; auto. apply MKT41 in H19; auto.
            rewrite H19; auto. }
        rewrite H17. apply H2; auto. apply H8. rewrite H14.
        apply MKT4; right. apply MKT41; auto. }
  apply H6 in H4. assert (∩A0 ∈ B). { apply H4; auto. }
  intro. rewrite H8 in H7; auto.
Qed.

(* 一系列相互包含的滤基, 全体之并也是滤基 *)
Proposition FilterBase_Property2 : ∀ B A, Nest B -> B <> Φ
  -> (∀ b, b ∈ B -> FilterBase b A) -> FilterBase (∪B) A.
Proof.
  intros. repeat split; intros.
  - apply NEexE. apply NEexE in H0 as [b].
    assert (b <> Φ). { apply H1 in H0 as []; auto. }
    apply NEexE in H2 as [x]. exists x. apply AxiomII; split; eauto.
  - unfold Included; intros. apply AxiomII in H2 as [H2[x[]]].
    apply H1 in H4 as [_[]]; auto.
  - intro. apply AxiomII in H2 as [H2[x[]]].
    apply H1 in H4 as [_[_[]]]; auto.
  - apply AxiomII in H2 as [H2[X[]]].
    apply AxiomII in H3 as [H3[Y[]]].
    pose proof H7. apply (H X Y) in H8 as []; auto.
    + pose proof H7. apply H1 in H7 as [_[_[_]]].
      assert ((a ∩ b) ∈ Y); auto. apply AxiomII; split; eauto.
    + pose proof H5. apply H1 in H5 as [_[_[_]]].
      assert ((a ∩ b) ∈ X); auto. apply AxiomII; split; eauto.
Qed.

(* G生成的滤基 *)
Definition FilterBase_from G := \{ λ u, ∃ S, S ⊂ G /\ Finite S /\ u = ∩S \}.

Declare Scope filter_scope.
Open Scope filter_scope.

Notation "〈 G 〉→ᵇ" := (FilterBase_from G) : filter_scope.

Corollary FilterBase_from_Corollary : ∀ G, G ⊂ (〈G〉→ᵇ).
Proof.
  unfold Included; intros. apply AxiomII; split; eauto.
  exists [z]. split. unfold Included; intros.
  apply MKT41 in H0; eauto. rewrite H0; auto.
  assert (Ensemble z). eauto. split. apply finsin; auto.
  apply MKT44 in H0 as [H0 _]. rewrite H0; auto.
Qed.

(* 任何具有有限交性的A上的子类族G都可扩张成为一个滤基 *)
Lemma Filter_Extension1 : ∀ G A, G <> Φ -> G ⊂ pow(A)
  -> Finite_Intersection G -> G ⊂ (〈G〉→ᵇ) /\ FilterBase (〈G〉→ᵇ) A.
Proof.
  intros. repeat split; intros.
  - unfold Included; intros. apply AxiomII; split; eauto.
    exists [z]. split. unfold Included; intros. apply MKT41 in H3;
    eauto. rewrite H3; auto. assert (Ensemble z). eauto. split.
    apply finsin; auto. apply MKT44 in H3 as [H3 _].
    rewrite H3; auto.
  - apply NEexE in H as [a]. assert (a ∈ (〈 G 〉→ᵇ)).
    { apply AxiomII; split; eauto. assert (Ensemble a); eauto.
      exists [a]. repeat split. unfold Included; intros.
      apply MKT41 in H3; auto. rewrite H3; auto. apply finsin; auto.
      apply MKT44 in H2 as []; auto. }
    intro. rewrite H3 in H2. elim (@ MKT16 a); auto.
  - unfold Included; intros. apply AxiomII in H2 as [H2[A0[H3[]]]].
    apply AxiomII; split; auto. destruct (classic (A0 = Φ)).
    rewrite H5,H6,MKT24 in H2. elim MKT39; auto.
    apply NEexE in H6 as []. pose proof H6.
    apply H3,H0,AxiomII in H6 as []. unfold Included; intros.
    rewrite H5 in H9. apply AxiomII in H9 as [_].
    apply H9 in H7; auto.
  - intro. apply AxiomII in H2 as [_[A0[H2[]]]].
    apply H1 in H3; auto.
  - apply AxiomII in H2 as [H2[A0[H4[]]]].
    apply AxiomII in H3 as [H3[B0[H7[]]]].
    assert (Ensemble (a ∩ b)).
    { apply (MKT33 a); eauto. unfold Included; intros.
      apply MKT4' in H10 as []; auto. }
    apply AxiomII; split; auto. exists (A0 ∪ B0).
    repeat split; unfold Included; intros.
    apply AxiomII in H11 as [_[|]]; auto. apply MKT168; auto.
    rewrite H6,H9. apply AxiomI; split; intros.
    + apply MKT4' in H11 as []. apply AxiomII in H11 as [].
      apply AxiomII in H12 as []. apply AxiomII; split; auto.
      intros. apply MKT4 in H15 as []; auto.
    + apply AxiomII in H11 as []. apply MKT4'; split;
      apply AxiomII; split; auto; intros; apply H12;
      apply MKT4; auto.
Qed.

(* A上的滤基B生成的滤子 *)
Definition Filter_from_FilterBase B A := \{ λ u, u ⊂ A /\ ∃ b, b ∈ B /\ b ⊂ u \}.

Notation "〈 B ∣ A 〉ᵇ→ᶠ" := (Filter_from_FilterBase B A) : filter_scope.

(* 集合A上的任何滤基都可扩张成为一个滤子 *)
Lemma Filter_Extension2 : ∀ B A, Ensemble A -> FilterBase B A
  -> B ⊂ (〈B∣A〉ᵇ→ᶠ) /\ Filter (〈B∣A〉ᵇ→ᶠ) A.
Proof.
  intros B A J H. destruct H as [H[H0[]]]. repeat split; unfold Included; intros.
  - apply AxiomII; repeat split. eauto. apply H0,AxiomII in H3; tauto.
    exists z. split; auto.
  - apply AxiomII in H3 as [H3[]]. apply AxiomII; auto.
  - intro. apply AxiomII in H3 as [_[_[x[]]]].
    assert (Φ = x). { apply AxiomI; split; intros; elim (@ MKT16 z); auto. }
    elim H1. rewrite H5; auto.
  - apply AxiomII; repeat split; auto. apply NEexE in H as []. exists x.
    split; auto. apply H0,AxiomII in H; tauto.
  - apply AxiomII in H3 as [H3[H5[x[]]]], H4 as [H4[H8[y[]]]].
    apply AxiomII; repeat split; [apply (MKT33 a); eauto| | ];
    try (unfold Included; intros; apply MKT4' in H11 as []; auto).
    exists (x ∩ y). split; auto. unfold Included; intros.
    apply MKT4' in H11 as []. apply MKT4'; auto.
  - apply AxiomII in H5 as [H5[H6[x[]]]]. apply AxiomII; repeat split; auto.
    apply (MKT33 A); auto. exists x. split; unfold Included; intros; auto.
Qed.

(* A的子集族G生成的滤子 *)
Definition Filter_from G A := \{ λ u, u ⊂ A
  /\ ∃ S, S ⊂ G /\ Finite S /\ ∩S ⊂ u \}.

Notation "〈 G ∣ A 〉→ᶠ" := (Filter_from G A) : filter_scope.

Fact Filter_Extension_Fact : ∀ G A, 〈(〈G〉→ᵇ) ∣ A〉ᵇ→ᶠ = 〈G ∣ A〉→ᶠ.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as [H[H0[x[]]]]. apply AxiomII in H1 as [H1[x0[H3[]]]].
    apply AxiomII; repeat split; auto. exists x0. rewrite <-H5; auto.
  - apply AxiomII in H as [H[H0[x[H1[]]]]]. apply AxiomII; repeat split; auto.
    exists (∩x). split; auto. apply AxiomII; split; eauto.
    apply (MKT33 z); auto.
Qed.

(* 任何具有有限交性的A上的子集族G都可扩张成为一个滤子, 这里要求A是一个集合 *)
Lemma Filter_Extension_1_and_2 : ∀ G A, G <> Φ -> G ⊂ pow(A) -> Ensemble A
  -> Finite_Intersection G -> G ⊂ (〈G ∣ A〉→ᶠ) /\ Filter (〈G ∣ A〉→ᶠ) A.
Proof.
  intros. rewrite <-Filter_Extension_Fact.
  apply (Filter_Extension1 G A) in H2 as []; auto.
  New H3. apply (Filter_Extension2 _ A) in H4 as []; auto.
  split; unfold Included; intros; auto.
Qed.

(* 滤子扩张原则: 任何滤子可以扩张成为超滤 *)
Lemma Filter_Extension3 : ∀ F A, Filter F A
  -> (∃ F1, F ⊂ F1 /\ ultraFilter F1 A).
Proof.
  intros. assert (Ensemble F /\ Ensemble A) as [].
  { split; [apply (Filter_is_Set_Co2 F A)|
    apply (Filter_is_Set_Co1 F A)]; auto. }
  set (M := \{ λ u, F ⊂ u /\ Filter u A \}).
  assert (Ensemble M).
  { apply (MKT33 (pow(pow(A)))). apply MKT38a,MKT38a; auto.
    unfold Included; intros. apply AxiomII in H2 as [H2[H3[]]].
    apply AxiomII; split; auto. }
  pose proof H2. apply MKT143 in H3 as [X[[]]].
  assert (F ∈ X).
  { apply NNPP; intro. assert ((X ∪ [F]) ⊂ M).
    { unfold Included; intros. apply MKT4 in H7 as []; auto.
      apply MKT41 in H7; auto. rewrite H7. apply AxiomII; auto. }
    apply H5 in H7. apply H6. rewrite <-H7.
    apply MKT4; right. apply MKT41; auto.
    unfold Nest; intros. apply MKT4 in H8 as [], H9 as [].
    apply H3; auto. apply MKT41 in H9; auto.
    apply H4,AxiomII in H8 as [_[]]. rewrite H9; auto.
    apply MKT41 in H8; auto. apply H4,AxiomII in H9 as [_[]].
    rewrite H8; auto. apply MKT41 in H8,H9; auto.
    rewrite H8,H9; auto. unfold Included; intros.
    apply MKT4; auto. }
  assert (F ⊂ (∪X)).
  { unfold Included; intros. apply AxiomII; split; eauto. }
  assert (ultraFilter (∪X) A).
  { apply ultraFilter_Equ_maxFilter. repeat split; intros.
    - unfold Included; intros. apply AxiomII in H8 as [H8[x[]]].
      apply H4,AxiomII in H10 as [H10[H11[]]]; auto.
    - intro. apply AxiomII in H8 as [H8[x[]]].
      apply H4,AxiomII in H10 as [_[_[_[]]]]; auto.
    - apply AxiomII; split; auto. exists F. split; auto.
      destruct H as [_[_[]]]; auto.
    - apply AxiomII in H8 as [H8[x[]]], H9 as [H9[y[]]].
      apply AxiomII; split. apply (MKT33 a); eauto.
      unfold Included; intros. apply MKT4' in H14; tauto.
      New H11. New H13.
      apply H4,AxiomII in H14 as [_[_[_[_[_[H14 _]]]]]],
      H15 as [_[_[_[_[_[H15 _]]]]]].
      New H11. apply (H3 x y) in H16 as []; eauto.
    - apply AxiomII in H10 as [H10[x[]]].
      apply AxiomII; split. apply (MKT33 A); auto.
      New H12. apply H4,AxiomII in H13
      as [_[_[_[_[_[]]]]]]; eauto.
    - assert (∀ x, x ∈ X -> x ⊂ G).
      { unfold Included; intros. apply H9,AxiomII; split; eauto. }
      apply AxiomI; split; intros; auto.
      apply AxiomII; split; eauto. exists G. split; auto.
      assert (Ensemble G). { apply Filter_is_Set_Co2 in H8; auto. }
      apply NNPP; intro. assert ((X ∪ [G]) ⊂ M).
      { unfold Included; intros. apply MKT4 in H14 as []; auto. 
        apply MKT41 in H14; auto. rewrite H14.
        apply AxiomII; auto. }
      apply H5 in H14; auto. apply H13. rewrite <-H14.
      apply MKT4; right. apply MKT41; auto. unfold Nest; intros.
      apply MKT4 in H15 as [], H16 as []. apply H3; auto.
      apply MKT41 in H16; auto. rewrite H16; auto.
      apply MKT41 in H15; auto. rewrite H15; auto.
      apply MKT41 in H15,H16; auto. rewrite H15,H16; auto. }
  eauto.
Qed.

(* 任何具有有限交性的A上的子集族都可扩张成为一个超滤 *)
Theorem Filter_Extension_Principle : ∀ G A, G <> Φ -> G ⊂ pow(A)
  -> Ensemble A -> Finite_Intersection G -> ∃ F, G ⊂ F /\ ultraFilter F A.
Proof.
  intros.
  apply (Filter_Extension_1_and_2 G A) in H2 as []; auto.
  apply Filter_Extension3 in H3 as [F[]]; auto.
  exists F. split; unfold Included; auto.
Qed.

(* 任意无限集上存在自由超滤 *)
Theorem Existence_of_free_ultraFilter : ∀ A, Ensemble A
  -> ~ Finite A -> ∃ F0, free_ultraFilter F0 A.
Proof.
  intros. pose proof H. apply Fσ_is_just_Filter in H1 as [H1 _]; auto.
  apply Filter_Extension3 in H1 as [x[]]. exists x.
  apply Fσ_and_free_ultrafilter; auto.
Qed.
