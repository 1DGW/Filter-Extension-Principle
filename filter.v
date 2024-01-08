(**********************************************************************)
(*   This is part of filter, it is distributed under the terms of     *)
(*          the GNU Lesser General Public License version 3           *)
(*               (see file LICENSE for more details)                  *)
(*                                                                    *)
(*                      Copyright 2022-2025                           *)
(*                   Guowei Dou and Wensheng Yu                       *)
(**********************************************************************)

(** filter *)

Require Export infinite_set.

(* A上的滤子和超滤 *)
(* 定义 滤子：设A的子集族F⊂pow(A)满足：
            1. Φ∉F 且 A∈F
            2. 若a∈F,b∈F, 则a∩b∈F (对交封闭)
            3. 若a⊂b⊂W 且 a∈F, 则b∈F (大集性质)
            则F叫A上的滤子. *)
Definition Filter F A := F ⊂ pow(A) /\ Φ ∉ F /\ A ∈ F
  /\ (∀ a b, a ∈ F -> b ∈ F -> (a ∩ b) ∈ F)
  /\ (∀ a b, a ⊂ b -> b ⊂ A -> a ∈ F -> b ∈ F).

(*滤子是集*)
Corollary Filter_is_Set_Co1 : ∀ F A, Filter F A -> Ensemble A.
Proof.
  intros. destruct H as [_[_[]]]; eauto.
Qed.

Corollary Filter_is_Set_Co2 : ∀ F A, Filter F A -> Ensemble F.
Proof.
  intros. pose proof H. apply Filter_is_Set_Co1 in H.
  destruct H0. apply MKT33 in H0; auto. apply MKT38a; auto.
Qed.

Global Hint Resolve Filter_is_Set_Co1 Filter_is_Set_Co2 : Fi.



(* 定义 超滤：在滤子的条件下,如果F满足极大性：
            任意A的子集a都有 a∈F 或者 (A~a)∈F
            则F叫A上的超滤. *)
Definition ultraFilter F A := Filter F A
  /\ (∀ a, a ⊂ A -> a ∈ F \/ (A ~ a) ∈ F).

(* 定义 极大滤子：若G和F都是A上的滤子,并且由F⊂G可以推出G=F,
               则称F为A上的极大滤子. *)
Definition maxFilter F A := Filter F A
  /\ (∀ G, Filter G A -> F ⊂ G -> G = F).

(* 超滤和极大滤子等价 *)
Corollary ultraFilter_Equ_maxFilter :
  ∀ F A, ultraFilter F A <-> maxFilter F A.
Proof.
  split; intros; destruct H; split; auto; intros.
  - apply MKT27; split; auto. red; intros.
    assert (z ⊂ A).
    { destruct H1. apply H1,AxiomII in H3; tauto. }
    pose proof H4. apply H0 in H5 as []; auto.
    destruct H1 as [_[H1[H6[]]]]. apply H2,(H7 z) in H5; auto.
    elim H1. replace Φ with (z ∩ (A ~ z)); auto.
    apply AxiomI; split; intros; elim (@ MKT16 z0); auto.
    apply MKT4' in H9 as []. apply MKT4' in H10 as [].
    apply AxiomII in H11 as []. contradiction.
  - apply NNPP; intro. apply notandor in H2 as [].
    assert (∀ b, b ∈ F -> a ∩ b <> Φ).
    { intros. intro. assert (b ⊂ (A ~ a)).
      { red; intros. destruct H. apply H,AxiomII in H4 as [].
        apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. elim (@ MKT16 z). rewrite <-H5. apply MKT4'; auto. }
      elim H3. destruct H as [_[_[_[]]]]. apply (H7 b); auto.
      red; intros. apply MKT4' in H8; tauto. }
    assert (Filter (\{ λ u, u ∈ F \/ (∃ v, v ∈ F
      /\ (u = a ∩ v \/ ((a ∩ v) ⊂ u /\ u ⊂ A))) \}) A).
    { destruct H as [H[H5[H6[]]]]. repeat split; intros.
      - red; intros. apply AxiomII in H9 as [H9[]]; auto.
        destruct H10 as [v[H10[H11|[]]]].
        apply AxiomII; split; eauto. rewrite H11. red; intros.
        apply MKT4' in H12 as []; auto. apply AxiomII; auto.
      - intro. apply AxiomII in H9 as [H9[]]. contradiction.
        destruct H10 as [v[H10[H11|[]]]]; apply H4 in H10; auto.
        elim H10. apply MKT27; auto.
      - apply AxiomII; split; eauto.
      - apply AxiomII in H9 as [],H10 as [].
        assert (Ensemble (a0 ∩ b)).
        { apply (MKT33 a0); auto. red; intros.
          apply MKT4' in H13; tauto. }
        apply AxiomII. split; auto. destruct H11,H12; auto;
        try destruct H11 as [u[]]; try destruct H12 as [v[]].
        + destruct H14 as [H14|[]]. right. exists (a0 ∩ v).
          split. apply H7; auto. left. rewrite H14.
          rewrite <-MKT7',(MKT6' a0 a),MKT7'; auto.
          right. exists (a0 ∩ v). split. apply H7; auto.
          right. split; unfold Included; intros.
          apply MKT4' in H16 as []. apply MKT4' in H17 as [].
          apply MKT4'; split; auto. apply H14,MKT4'; auto.
          apply MKT4' in H16 as []; auto.
        + destruct H14 as [H14|[]]. right. exists (u ∩ b).
          split. apply H7; auto. left. rewrite H14,MKT7'; auto.
          right. exists (u ∩ b). split. apply H7; auto. right.
          split; unfold Included; intros. apply MKT4' in H16 as [].
          apply MKT4' in H17 as []. apply MKT4'; split; auto.
          apply H14,MKT4'; auto. apply MKT4' in H16 as []; auto.
        + destruct H14 as [H14|[]],H15 as [H15|[]];
          right; exists (u ∩ v); split; auto.
          * left. rewrite H14,H15. rewrite (MKT6' a u),MKT7',
            <-(MKT7' a a v),MKT5',<-MKT7',(MKT6' u a),MKT7'; auto.
          * right. split; unfold Included; intros.
            rewrite H14. apply MKT4' in H17 as [].
            apply MKT4' in H18 as []; auto. apply MKT4'; split.
            apply MKT4'; auto. apply H15,MKT4'; auto.
            apply MKT4' in H17 as []; auto.
          * right. split; unfold Included; intros.
            apply MKT4' in H17 as []. apply MKT4' in H18 as [].
            apply MKT4'; split. apply H14,MKT4'; auto.
            rewrite H15. apply MKT4'; auto.
            apply MKT4' in H17 as []; auto.
          * right. split; unfold Included; intros.
            apply MKT4' in H18 as []. apply MKT4' in H19 as [].
            apply MKT4'; split. apply H14,MKT4'; auto.
            apply H15,MKT4'; auto. apply MKT4' in H18 as []; auto.
      - apply AxiomII in H11 as []. apply AxiomII; split.
        apply (MKT33 A); eauto. destruct H12.
        + left. apply (H8 a0 b); auto.
        + destruct H12 as [v[H12[]]]; right; exists v;
          split; auto; right; [rewrite <-H13|split]; auto.
          destruct H13. eapply MKT28; eauto. }
    assert ((\{ λ u, u ∈ F \/ (∃ v, v ∈ F
      /\ (u = a ∩ v \/ ((a ∩ v) ⊂ u /\ u ⊂ A))) \}) = F).
    { apply H0; auto. unfold Included; intros.
      apply AxiomII; split. eauto. left; auto. }
    assert (Ensemble a). { apply (MKT33 A); eauto with Fi. }
    elim H2. rewrite <-H6. apply AxiomII; split; auto.
    right. exists A. destruct H as [_[_[]]]. split; auto.
    left. symmetry. apply MKT30; auto.
Qed.

(* 单点集[A]是A上的滤子 *)
Example Example1 : ∀ A, Ensemble A -> A <> Φ -> Filter ([A]) A.
Proof.
  intros. repeat split; intros.
  - unfold Included; intros. apply MKT41 in H1; eauto.
    apply AxiomII; split. rewrite H1; eauto. rewrite H1.
    unfold Included; auto.
  - intro. apply MKT41 in H1; eauto.
  - apply MKT41; auto.
  - apply MKT41 in H1,H2; eauto. rewrite H1,H2,MKT5'.
    apply MKT41; auto.
  - apply MKT41 in H3; auto. rewrite H3 in H1.
    apply MKT41; auto. apply MKT27; auto.
Qed.

(* 定理1 超滤的一个性质 *)
Theorem FT1 : ∀ F A a1 a2, ultraFilter F A -> (a1 ∪ a2) ∈ F
  -> a1 ∈ F \/ a2 ∈ F.
Proof.
  intros. destruct H as [[H[H1[H2[]]]]].
  assert ((A ~ (a1 ∪ a2)) ∉ F).
  { intro. assert (((a1 ∪ a2) ∩ (A ~ (a1 ∪ a2))) ∈ F).
    apply H3; auto. unfold Setminus in H7.
    rewrite (MKT6' A _),<-MKT7' in H7.
    replace ((a1 ∪ a2) ∩ (¬ (a1 ∪ a2))) with Φ in H7.
    rewrite MKT17' in H7; auto.
    apply AxiomI; split; intros. elim (@ MKT16 z); auto.
    apply MKT4' in H8 as []. apply AxiomII in H9 as [].
    contradiction. }
  replace (A ~ (a1 ∪ a2)) with ((A ~ a1) ∩ (A ~ a2)) in H6.
  assert ((A ~ a1) ∉ F \/ (A ~ a2) ∉ F).
  { apply NNPP; intro. apply notandor in H7 as [].
    apply (NNPP ((A ~ a1) ∈ F)) in H7.
    apply (NNPP ((A ~ a2) ∈ F)) in H8.
    elim H6. apply H3; auto. }
  assert (a1 ⊂ A /\ a2 ⊂ A) as [].
  { apply H in H0. apply AxiomII in H0 as []. split.
    assert (a1 ⊂ (a1 ∪ a2)). unfold Included; intros.
    apply MKT4; auto. eapply MKT28; eauto.
    assert (a2 ⊂ (a1 ∪ a2)). unfold Included; intros.
    apply MKT4; auto. eapply MKT28; eauto. }
  apply H5 in H8; apply H5 in H9. destruct H7;[destruct H8;
  [auto|contradiction]|destruct H9;[auto|contradiction]].
  apply AxiomI; split; intros.
  - apply MKT4' in H7 as []. apply MKT4' in H7 as [].
    apply MKT4' in H8 as []. apply MKT4'. split; auto.
    apply AxiomII; split. eauto. intro.
    apply AxiomII in H9 as []; apply AxiomII in H10 as [].
    apply MKT4 in H11 as []; contradiction.
  - apply MKT4' in H7 as []. apply AxiomII in H8 as [].
    apply MKT4'; split. apply MKT4'; split; auto.
    apply AxiomII; split; auto. intro. elim H9. apply MKT4; auto.
    apply MKT4'; split; auto. apply AxiomII; split; auto.
    intro; elim H9. apply MKT4; auto.
Qed.

(* 定理1的推广 *)
Corollary FT1_Corollary : ∀ F A B, ultraFilter F A
  -> Finite B -> ∪B ∈ F -> ∃ b, b ∈ B /\ b ∈ F.
Proof.
  intros. set (Q := fun n => ∀ D, P[D] = n
    -> ∪D ∈ F -> ∃ d, d ∈ D /\ d ∈ F).
  assert (∀ n, n ∈ ω -> Q n).
  { apply Mathematical_Induction.
    - unfold Q; intros. assert (D = Φ).
      { assert (P[Φ] = Φ).
        { pose proof MKT152a. pose proof MKT152b.
          pose proof MKT152c. assert (Φ ∈ dom(P)).
          { rewrite H5. apply MKT19. eauto. }
          apply Property_Value in H7; auto. destruct H4.
          apply (H8 Φ); auto. apply AxiomII'; repeat split.
          apply MKT49a; eauto. apply MKT145.
          apply MKT164; auto. }
        rewrite <-H4 in H2. apply MKT154 in H2;
        try split; eauto; try apply Property_Finite.
        apply AxiomI; split; intros; elim (@ MKT16 z); auto.
        destruct H2 as [f[[][]]]. rewrite <-H7 in H5.
        apply Property_Value,Property_ran in H5; auto.
        rewrite H8 in H5. elim (@ MKT16 (f[z])); auto.
        unfold Finite. rewrite H2,H4; auto. }
      rewrite H4,MKT24' in H3. destruct H as [[H[]]]. elim H5; auto.
    - intros. unfold Q; intros. pose proof H4.
      apply Inf_P7_Lemma in H6 as [D'[d[H6[H7[H8[]]]]]]; auto.
      assert (∪D = (∪D') ∪ d).
      { apply AxiomI; split; intros.
        - apply AxiomII in H11 as [H11[x[]]]. rewrite H10 in H13.
          apply MKT4 in H13 as [].
          + apply MKT4; left. apply AxiomII; split; eauto.
          + apply MKT4; right. apply MKT41 in H13; auto.
            rewrite <-H13; auto.
        - apply AxiomII; split; eauto. apply MKT4 in H11 as [].
          + apply AxiomII in H11 as [H11[x[]]]. exists x.
            split; auto. rewrite H10. apply MKT4; auto.
          + exists d. split; auto. rewrite H10. apply MKT4; right.
            apply MKT41; auto. }
      rewrite H11 in H5. apply (FT1 F A) in H5 as []; auto.
      + apply H3 in H5 as [x[]]; auto. exists x. split; auto.
        rewrite H10. apply MKT4; auto.
      + exists d. split; auto. rewrite H10. apply MKT4; right.
        apply MKT41; auto. }
  apply H2 in H0. apply H0; auto.
Qed.

(* 定义 自由超滤：在超滤的条件下,如果A的任意有限子集都不属于F,则F为A上的自由超滤.
   换言之,F中的元素集均为无限的,因而自由超滤是针对无限集而言的.    *)
Definition free_ultraFilter F A := ultraFilter F A
  /\ (∀ a, a ⊂ A -> Finite a -> a ∉ F).

(* 自由超滤中的元素集都是无限的 *)
Corollary free_ultraFilter_Co1 : ∀ F A, free_ultraFilter F A
  -> (∀ x, x ∈ F -> ~ Finite x).
Proof.
  intros. intro. destruct H. destruct H as [[H[H3[H4[]]]]].
  pose proof H0. apply H in H8. apply AxiomII in H8 as [].
  eapply H2; eauto.
Qed.

(* 对于任意一个有限集, 不存在其上的自由超滤 *)
Corollary free_ultraFilter_Co2 : ∀ A, Finite A ->
  ~ ∃ F, free_ultraFilter F A.
Proof.
  intros. intro. destruct H0 as [F[[[H0[H1[H2[]]]]]]].
  apply (H6 A); auto.
Qed.

(* 定义 一个特殊滤子Fσ,不满足超滤的条件，但是满足自由超滤的附加条件
      Fσ叫做余有限子集滤子 或者 叫做Fréchet滤子 *)
Definition Fσ A := \{ λ a, a ⊂ A /\ Finite (A ~ a) \}.

(* Fréchet滤子也需要对无限集讨论, 否则意义不大 *)
Corollary Fσ_Co1_a : ∀ A, Finite A -> Fσ A = pow(A).
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as [H0[]]. apply AxiomII; auto.
  - apply AxiomII in H0 as []. apply AxiomII; repeat split; auto.
    apply (@ finsub A); auto. red; intros. apply MKT4' in H2; tauto.
Qed.

Corollary Fσ_Co1_b : ∀ A, Finite A -> ~ Filter (Fσ A) A.
Proof.
  intros. intro. destruct H0 as [_[]]. rewrite Fσ_Co1_a in H0; auto.
  apply H0,AxiomII; split; auto.
Qed.

(* 这里有 Ensemble 的条件, 不必讨论真类 *)
Corollary Fσ_Co2 : ∀ A, ~ Finite A -> Ensemble A
  -> (Fσ A) ⊂ pow(A) /\ (Fσ A) <> pow(A).
Proof.
  intros. split. red; intros.
  apply AxiomII in H1 as [H1[]]. apply AxiomII; auto. intro.
  New H0. apply Inf_P8 in H2 as [A1[A2[H2[H3[H4[H5[]]]]]]]; auto.
  assert (A1 ∈ pow(A)).
  { apply AxiomII; split; auto; rewrite <-H6; unfold Included;
    intros; apply MKT4; auto. }
  rewrite <-H1 in H8. apply AxiomII in H8 as [H8[]].
  assert (A ~ A1 = A2).
  { apply AxiomI; split; intros. apply MKT4' in H11 as [].
    rewrite <-H6 in H11. apply MKT4 in H11 as []; auto.
    apply AxiomII in H12 as []. contradiction.
    apply MKT4'; split. rewrite <-H6. apply MKT4; auto.
    apply AxiomII; split; eauto. intro. apply (@ MKT16 z).
    rewrite <-H7. apply MKT4'; auto. }
  rewrite H11 in H10; auto.
Qed.

Lemma Finite_Φ : Finite Φ.
Proof.
  destruct MKT135. apply MKT164,MKT156 in H as [].
  unfold Finite. rewrite H1; auto.
Qed.

(* Fσ是滤子, 但不是超滤, 并且Fσ中的集都是无限的(否则不属于Fσ) *)
Corollary Fσ_is_just_Filter : ∀ A, ~ Finite A -> Ensemble A
  -> Filter (Fσ A) A /\ ~ ultraFilter (Fσ A) A
    /\ (∀ a, a ⊂ A -> Finite a -> a ∉ (Fσ A)).
Proof.
  intros. assert (Filter (Fσ A) A).
  { repeat split; intros.
    - unfold Included; intros. apply AxiomII; split; eauto.
      apply AxiomII in H1 as [H1[]]; auto.
    - intro. apply AxiomII in H1 as [H1[]].
      assert (A ~ Φ = A).
      { apply AxiomI; split; intros. apply MKT4' in H4 as []; auto.
        apply MKT4'; split; auto. apply AxiomII; split. eauto.
        intro. pose proof (@ MKT16 z); auto. }
      rewrite H4 in H3; auto.
    - apply AxiomII; repeat split; auto.
      assert (A ~ A = Φ).
      { apply AxiomI; split; intros; elim (@ MKT16 z); auto.
        apply MKT4' in H1 as []. apply AxiomII in H2 as [].
        contradiction. }
      rewrite H1. apply Finite_Φ.
    - apply AxiomII in H1 as [H1[]], H2 as [H2[]].
      assert ((a ∩ b) ⊂ a).
      { unfold Included; intros. apply MKT4' in H7; tauto. }
      apply AxiomII; repeat split. apply (MKT33 a); auto.
      unfold Included; intros; auto.
      assert ((A ~ (a ∩ b)) = ((A ~ a) ∪ (A ~ b))).
      { apply AxiomI; split; intros.
        apply MKT4' in H8 as []. apply AxiomII in H9 as [].
        apply MKT4. apply NNPP; intro. apply notandor in H11 as [].
        elim H10. apply MKT4'. apply NNPP; intro.
        apply notandor in H13 as []; [elim H11|elim H12];
        apply AxiomII; repeat split; auto; apply AxiomII; auto.
        apply MKT4'; split. apply MKT4 in H8 as []; apply MKT4' in H8; tauto.
        apply AxiomII; split; eauto. intro. apply MKT4' in H9 as [].
        apply MKT4 in H8 as []; apply MKT4' in H8 as [];
        apply AxiomII in H11 as []; auto. }
      rewrite H8. apply MKT168; auto.
    - apply AxiomII; repeat split; auto. apply (MKT33 A); auto.
      apply AxiomII in H3 as [H3[]]. apply (@ finsub ((A ~ a))); auto.
      unfold Included; intros. apply MKT4' in H6 as [].
      apply AxiomII in H7 as []. apply MKT4'; split; auto.
      apply AxiomII; split; auto. intro. apply H1 in H9; auto. }
  split; auto. split. intro.
  - destruct H2 as [_]. destruct H1 as [H1[H3[H4[]]]].
    New H0. apply Inf_P8 in H7 as [A1[A2[H7[H8[H9[H10[]]]]]]]; auto.
    assert (A1 ⊂ A).
    { rewrite <-H11. unfold Included; intros. apply MKT4; auto. }
    New H13. apply H2 in H14 as []; apply AxiomII in H14 as [H14[]].
    assert (A ~ A1 = A2).
    { apply AxiomI; split; intros. apply MKT4' in H17 as [].
      rewrite <-H11 in H17. apply MKT4 in H17 as []; auto.
      apply AxiomII in H18 as []. contradiction.
      apply MKT4'; split. rewrite <-H11. apply MKT4; auto.
      apply AxiomII; split; eauto. intro. elim (@ MKT16 z).
      rewrite <-H12. apply MKT4'; auto. }
    rewrite H17 in H16; auto.
    assert (A ~ (A ~ A1) = A1).
    { apply AxiomI; split; intros. apply MKT4' in H17 as [].
      apply AxiomII in H18 as []. apply NNPP; intro. elim H19.
      apply MKT4'; split; auto. apply AxiomII; auto.
      apply MKT4'; split. rewrite <-H11. apply MKT4; auto.
      apply AxiomII; split; eauto. intro.
      apply MKT4' in H18 as []. apply AxiomII in H19 as []; auto. }
    rewrite H17 in H16. auto.
  - intros. intro. apply AxiomII in H4 as [H4[]].
    assert ((A ~ a) ∪ a = A).
    { apply AxiomI; split; intros. apply MKT4 in H7 as []; auto.
      apply MKT4' in H7 as []; auto. apply MKT4.
      TF (z ∈ a). auto. left. apply MKT4'; split; auto.
      apply AxiomII; split; eauto. }
    elim H. rewrite <-H7. apply MKT168; auto.
Qed.

(* 在超滤的前提下, 自由超滤 等价于 包含了Fσ *)
Proposition Fσ_and_free_ultrafilter : ∀ F A, Ensemble A -> ~ Finite A
  -> ultraFilter F A -> free_ultraFilter F A <-> (Fσ A) ⊂ F.
Proof.
  split; intros.
  - destruct H2 as [[[H2[H3[H4[]]]]]]. unfold Included; intros.
    apply AxiomII in H9 as [H9[]]. apply H7 in H10 as []; auto.
    apply H8 in H11. contradiction. unfold Included; intros.
    apply MKT4' in H12; tauto.
  - split; auto. intros. intro.
    assert ((A ~ a) ∈ (Fσ A)).
    { apply AxiomII. assert ((A ~ a) ⊂ A).
      { unfold Included; intros. apply MKT4' in H6; tauto. }
      repeat split; auto. apply (MKT33 A); auto.
      assert (A ~ (A ~ a) = a).
      { apply AxiomI; split; intros. apply MKT4' in H7 as [].
        apply AxiomII in H8 as []. apply NNPP; intro. elim H9.
        apply MKT4'; split; auto. apply AxiomII; split; auto.
        apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. apply MKT4' in H8 as []. apply AxiomII in H9 as []; auto. }
      rewrite H7; auto. }
    apply H2 in H6. destruct H1 as [[H1[H7[H8[]]]]].
    assert ((a ∩ (A ~ a)) ∈ F). { apply H9; auto. }
    replace (a ∩ (A ~ a)) with Φ in H12; auto.
    apply AxiomI; split; intros. elim (@ MKT16 z); auto.
    apply MKT4' in H13 as []. apply MKT4' in H14 as [].
    apply AxiomII in H15 as []. contradiction.
Qed.

(* 定义 A上的主超滤Fa
       只有a∈A时，Fa才有意义，否则Fa为空.
       至此, 找到了确切能够构造出来的一类超滤: 主超滤. *)
Definition F A a := \{ λ u, u ⊂ A /\ a ∈ u \}.

Corollary Fn_Corollary1 : ∀ A a, F A a = Φ <-> a ∉ A.
Proof.
  split; intros.
  - intro. assert ([a] ∈ (F A a)).
    { apply AxiomII; repeat split. eauto. unfold Included; intros.
      apply MKT41 in H1; eauto. rewrite H1; auto.
      apply MKT41; eauto. }
    apply (@ MKT16 [a]). rewrite <-H; auto.
  - apply AxiomI; split; intros; elim (@ MKT16 z); auto.
    apply AxiomII in H0 as [H0[]]. apply H1 in H2. elim H; auto.
Qed.

Corollary Fn_Corollary2_a : ∀ A a, ultraFilter (F A a) A -> a ∈ A.
Proof.
  intros. apply NNPP; intro. apply Fn_Corollary1 in H0. rewrite H0 in H.
  destruct H as [[H[H1[]]]]. elim (@ MKT16 A); auto.
Qed.

Corollary Fn_Corollary2_b : ∀ A a, Ensemble A -> a ∈ A
  -> ultraFilter (F A a) A.
Proof.
  repeat split; intros.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII; split; auto.
  - intro. apply AxiomII in H1 as [H1[]]. apply (@ MKT16 a); auto.
  - apply AxiomII; repeat split; auto.
  - apply AxiomII in H1 as [H1[]], H2 as [H2[]].
    apply AxiomII. assert ((a0 ∩ b) ⊂ A).
    { unfold Included; intros. apply MKT4' in H7 as []; auto. }
    repeat split; auto. apply (MKT33 A); auto. apply MKT4'; auto.
  - apply AxiomII. apply AxiomII in H3 as [H3[]].
    repeat split; auto. apply (MKT33 A); auto.
  - TF (a ∈ a0).
    + left. apply AxiomII; split; auto. apply (MKT33 A); auto.
    + right. assert ((A ~ a0) ⊂ A).
      { unfold Included; intros. apply MKT4' in H3; tauto. }
      apply AxiomII; repeat split; auto. apply (MKT33 A); auto.
Qed.
(* a∈A时, Fa 称为A上的主超滤 *)

(* 关于主超滤的两个例子 *)
Example Example2 : ∀ A u v, u ∈ A -> v ∈ A
  -> u <> v <-> F A u <> F A v.
Proof.
  intros. split; intros; intro.
  - assert ([u] ∈ (F A u)).
    { apply AxiomII. repeat split. eauto. unfold Included; intros.
      apply MKT41 in H3; eauto. rewrite H3; auto. apply MKT41; eauto. }
    assert ([u] ∉ (F A v)).
    { intro. apply AxiomII in H4 as [H4[]].
      apply MKT41 in H6; eauto. }
    rewrite H2 in H3; auto.
  - elim H1. apply AxiomI; split; intros;
    apply AxiomII in H3 as [H3[]]; apply AxiomII;
    repeat split; auto; [rewrite <-H2|rewrite H2]; auto.
Qed.

Example Example3_a : ∀ A A0 a, A0 ⊂ A -> a ∈ A -> A0 ∈ (F A a) -> a ∈ A0.
Proof.
  intros. apply AxiomII in H1 as [H1[]]; auto.
Qed.

Example Example3_b : ∀ A A0 a, Ensemble A0 -> A0 ⊂ A -> a ∈ A0
  -> A0 ∈ (F A a).
Proof.
  intros. apply AxiomII; auto.
Qed.

(* 定理2a 每个主超滤 都是 非自由的超滤 *)
Theorem FT2_a : ∀ A a, Ensemble A -> a ∈ A
  -> ultraFilter (F A a) A /\ ~ free_ultraFilter (F A a) A.
Proof.
  intros. split. apply Fn_Corollary2_b; auto.
  intro. destruct H1. assert ([a] ⊂ A).
  { unfold Included; intros.
    apply MKT41 in H3; eauto. rewrite H3; auto. }
  assert (Ensemble a); eauto. New H4. apply finsin in H4.
  New H3. apply H2 in H6; auto. apply H6,AxiomII. repeat split; auto.
Qed.

Lemma FT2_b_Lemma1 : ∀ x y, ∩(x ∪ y) = (∩x) ∩ (∩y).
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H as []. apply MKT4'; split;
    apply AxiomII; split; auto; intros; apply H0,MKT4; auto.
  - apply MKT4' in H as []. apply AxiomII; split; eauto; intros.
    apply AxiomII in H as [], H0 as [].
    apply MKT4 in H1 as []; auto.
Qed.

Lemma FT2_b_Lemma2 : ∀ F0 A B, Filter F0 A -> Finite B -> B <> Φ
  -> (∀ b, b ∈ B -> b ∈ F0) -> ∩B ∈ F0.
Proof.
  intros. generalize dependent B.
  set (p := fun m => (∀ B, P[B] = m -> B <> Φ
    -> (∀ b, b ∈ B -> b ∈ F0) -> ∩B ∈ F0)).
  assert (∀ n, n ∈ ω -> p n).
  { apply Mathematical_Induction; unfold p; intros.
    - apply carE in H0. contradiction.
    - New H2. apply Inf_P7_Lemma in H5
      as [B1[b[H5[H6[H7[]]]]]]; auto.
      New H6. apply MKT44 in H10 as [H10 _].
      rewrite H9,FT2_b_Lemma1,H10.
      assert (b ∈ F0).
      { apply H4. rewrite H9. apply MKT4; right.
        apply MKT41; auto. }
      TF (B1 = Φ). rewrite H12,MKT24,MKT6',MKT20'; auto.
      destruct H as [H[H13[H14[]]]]. apply H15; auto.
      apply H1; auto. intros. apply H4. rewrite H9.
      apply MKT4; auto. }
  intros. apply (H0 (P[B])); auto.
Qed.

(* 定理2b 每个非自由的超滤 也是 某个主超滤 *)
Theorem FT2_b : ∀ F0 A, ultraFilter F0 A
  -> ~ free_ultraFilter F0 A -> (∃ a, a ∈ A /\ F0 = F A a).
Proof.
  intros. assert (∃ A1, A1 ∈ F0 /\ Finite A1) as [A1[]].
  { apply NNPP; intro. elim H0. split;
    auto. intros. intro. elim H1. eauto. }
  assert ((A ~ A1) ∉ F0).
  { destruct H as [[H[H3[H4[]]]]]. intro.
    apply (H5 A1) in H8; auto. apply H3.
    replace (A1 ∩ (A ~ A1)) with Φ in H8; auto.
    apply AxiomI; split; intros. elim (@ MKT16 z); auto.
    apply MKT4' in H9 as []. apply MKT4' in H10 as [].
    apply AxiomII in H11 as []. contradiction. }
  assert (Ensemble A) as HA.
  { apply (Filter_is_Set_Co1 F0 A). destruct H; auto. }
  assert (A ~ A1 = ∩(\{ λ v, ∃ a, a ∈ A1 /\ v = A ~ [a] \})).
  { apply AxiomI; split; intros.
    - apply AxiomII; split. eauto. intros.
      apply AxiomII in H5 as [H5[a[]]].
      assert ((A ~ A1) ⊂ (A ~ [a])).
      { unfold Included; intros. apply MKT4' in H8 as [].
        apply AxiomII in H9 as []. apply MKT4'; split; auto.
        apply AxiomII; split; auto. intro. apply MKT41 in H11; eauto.
        rewrite <-H11 in H6; auto. }
      apply H8 in H4. rewrite H7; auto.
    - apply AxiomII in H4 as []. destruct (classic (A1 = Φ)).
      rewrite H6 in H1. destruct H as [[H[H7[H8[]]]]].
      contradiction. apply NEexE in H6 as [a].
      assert ((A ~ [a]) ∈ \{ λ u, ∃ a, a ∈ A1 /\ u = A ~ [a] \}).
      { apply AxiomII; split; eauto. apply (MKT33 A); eauto. }
      apply H5 in H7. destruct H as [[]]. apply H in H1.
      assert (z ∈ A). { apply MKT4' in H7; tauto. }
      apply AxiomII in H1 as []. apply NNPP; intro.
      assert (z ∈ A1).
      { apply NNPP; intro. elim H12.
        apply MKT4'; split; auto. apply AxiomII; auto. }
      assert ((A ~ [z]) ∈ \{ λ u, ∃ a, a ∈ A1 /\ u = A ~ [a] \}).
      { apply AxiomII; split; eauto. apply (MKT33 A); eauto. }
      apply H5 in H14. apply MKT4' in H14 as [].
      apply AxiomII in H15 as []. elim H16. apply MKT41; auto. }
  assert (∃ u, u ∈ \{ λ v, ∃ a, a ∈ A1 /\ v = A ~ [a] \}
    /\ u ∉ F0) as [u[]].
  { apply NNPP; intro.
    assert (∀ u, u ∈ \{ λ v, ∃ a, a ∈ A1 /\ v = A ~ [a] \}
      -> u ∈ F0).
    { intros. apply AxiomII in H6 as [H6[a[]]]. apply NNPP; intro.
      elim H5. exists u. split; auto. apply AxiomII; split; eauto. }
    apply H3. rewrite H4. apply (FT2_b_Lemma2 _ A); auto.
    destruct H; auto.
    - set (f := \{\ λ u v, u ∈ A1 /\ v = A ~ [u] \}\).
      assert (Function f /\ dom(f) = A1
        /\ ran(f) = \{ λ v, ∃ a, a ∈ A1 /\ v = A ~ [a] \}) as [H7[]].
      { repeat split; try (apply AxiomI; split); unfold Relation; intros.
        - apply AxiomII in H7 as [_[x[y[]]]]; eauto.
        - apply AxiomII' in H7 as [_[]], H8 as [_[]].
          rewrite H9,H10; auto.
        - apply AxiomII in H7 as [_[]].
          apply AxiomII' in H7; tauto.
        - apply AxiomII; split. eauto. exists (A ~ [z]).
          apply AxiomII'; split; auto. apply MKT49a; eauto.
          apply (MKT33 A); eauto.
        - apply AxiomII in H7 as [H7[]]. apply AxiomII; split; auto.
          apply AxiomII' in H8 as [H8[]]; eauto.
        - apply AxiomII in H7 as [H7[x[]]].
          apply AxiomII; split; auto. exists x.
          apply AxiomII'; split; auto. apply MKT49a; eauto. }
      assert (Ensemble f). { apply MKT75; [ |rewrite H8]; eauto. }
      apply MKT160 in H10; auto. rewrite H8 in H10. rewrite <-H9.
      destruct H10. New MKT138. apply AxiomII in H11 as [_[]].
      apply H12 in H2. apply H2 in H10; auto.
      unfold Finite. rewrite H10; auto.
    - assert (A1 <> Φ).
      { intro. rewrite H7 in H1. destruct H as [[_[]]]; auto. }
      apply NEexE in H7 as []. apply NEexE. exists (A ~ [x]).
      apply AxiomII; split; eauto. apply (MKT33 A); eauto. }
  apply AxiomII in H5 as [H5[x[]]]. rewrite H8 in *. destruct H.
  assert ([x] ⊂ A).
  { destruct H. unfold Included; intros. apply MKT41 in H11; eauto.
    rewrite H11. apply H,AxiomII in H1 as []; auto. }
  apply H9 in H10 as []; [ |contradiction]. exists x.
  assert (x ∈ A).
  { destruct H. apply H,AxiomII in H10 as [].
    apply H12. apply MKT41; eauto. }
  split; auto. destruct H as [H[H12[H13[]]]].
  apply AxiomI; split; intros. apply AxiomII; split; eauto.
  split. unfold Included; intros. apply H,AxiomII in H16 as []; auto.
  apply NNPP; intro. apply (H14 z) in H10; auto.
  replace (z ∩ [x]) with Φ in H10; auto.
  apply AxiomI; split; intros; elim (@ MKT16 z0); auto.
  apply MKT4' in H18 as []. apply MKT41 in H19; eauto.
  rewrite H19 in H18. contradiction. apply AxiomII in H16 as [H16[]].
  apply (H15 _ z) in H10; auto. unfold Included; intros.
  apply MKT41 in H19; eauto. rewrite H19; auto.
Qed.

