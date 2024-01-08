(***********************************************************************)
(*   This is part of algebra operation on ω, it is distributed under   *)
(*    the terms of the GNU Lesser General Public License version 3     *)
(*               (see file LICENSE for more details)                   *)
(*                                                                     *)
(*                      Copyright 2022-2025                            *)
(*                   Guowei Dou and Wensheng Yu                        *)
(***********************************************************************)

(** alge_operation *)

Require Export mk_theorems.

Declare Scope ω_scope.
Delimit Scope ω_scope with ω.
Open Scope ω_scope.

(* 下面三个个记号为定义偶数和奇数做准备 *)
Notation "0" := Φ : ω_scope.
Notation "1" := [Φ] : ω_scope.
Notation "2" := ([Φ] ∪ [[Φ]]) : ω_scope.

Fact in_ω_0 : 0 ∈ ω.
Proof. destruct MKT135; auto. Qed.

Fact in_ω_1 : 1 ∈ ω.
Proof.
  pose proof in_ω_0. apply MKT134 in H.
  replace 1 with (PlusOne 0); auto. apply MKT17.
Qed.

Fact in_ω_2 : 2 ∈ ω.
Proof.
  pose proof in_ω_1. pose proof H. apply MKT134 in H; auto.
Qed.

(* 递归定理 *)
Theorem Recursion : ∀ x a h, Ensemble a
  -> Function h -> dom(h) = a -> ran(h) ⊂ a -> x ∈ a
  -> (exists ! f, Function f /\ dom(f) = ω /\ ran(f) ⊂ a
    /\ f[0] = x /\ (∀ n, n ∈ ω -> f[PlusOne n] = h[(f[n])])).
Proof.
  intros. set (Ind r := r ⊂ (ω × a) /\ [0,x] ∈ r
    /\ (∀ n x, n ∈ ω -> x ∈ a -> [n,x] ∈ r
      -> [(PlusOne n),h[x]] ∈ r)).
  set (f := \{\ λ u v, [u,v] ∈ (ω × a)
    /\ (∀ r, Ind r -> [u,v] ∈ r) \}\).
  assert (Ensemble x); eauto. destruct MKT135.
  assert (Ensemble 0); eauto.
  assert (∀ r, Ind r -> f ⊂ r).
  { unfold Included; intros. apply AxiomII in H9
    as [_[x1[y1[H9[]]]]]. rewrite H9; auto. }
  assert ([0,x] ∈ f).
  { apply AxiomII'. assert (Ensemble ([0,x])); auto. repeat
    split; [|apply AxiomII'|intros]; auto. destruct H10; tauto. }
  assert (Ind f).
  { repeat split; unfold Included; intros; auto.
    - apply AxiomII in H10 as [_[x1[y1[H10[]]]]]. rewrite H10; auto.
    - pose proof H10. apply MKT134 in H13. pose proof H11.
      rewrite <-H1 in H14. apply Property_Value,Property_ran in H14;
      auto. assert (Ensemble ([(PlusOne n),(h[x0])])).
      { apply MKT49a; eauto. } apply AxiomII'; repeat split; intros;
      auto. apply AxiomII'; split; auto. pose proof H16.
      apply H8 in H16. apply H16 in H12.
      destruct H17 as [_[]]. apply H18; auto. }
  assert (∀ m, m ∈ ω -> exists ! x, x ∈ a /\ [m,x] ∈ f).
  { apply Mathematical_Induction.
    - exists x. split; auto. intros x1 []. apply NNPP; intro.
      set(f' := f ~ [[0,x1]]). assert (Ind f').
      { repeat split; unfold Included; intros.
        - destruct H10. apply MKT4' in H14 as []; auto.
        - apply MKT4'; split; auto. apply AxiomII; split; auto.
          intro. apply MKT41 in H14; eauto. apply MKT55 in H14
          as []; auto.
        - apply MKT4' in H16 as []. destruct H10 as [H10[]].
          apply H19 in H16; auto. apply MKT4'; split; auto.
          apply AxiomII; split; eauto. intro.
          apply MKT41 in H20; eauto.
          assert (Ensemble ([(PlusOne n),(h[x0])])); eauto.
          apply MKT49b in H21 as []. apply MKT55 in H20 as []; auto.
          elim (H6 n); auto. }
      apply H8 in H14. apply H14 in H12. apply MKT4' in H12 as [_].
      apply AxiomII in H12 as []. elim H15. apply MKT41; eauto.
    - intros m H11 [x0[[]]]. assert (h[x0] ∈ a).
      { apply H2,(@ Property_ran x0),Property_Value;
        [ |rewrite H1]; auto. }
      pose proof H11. apply MKT134 in H16. exists (h[x0]).
      assert ([(PlusOne m),(h[x0])] ∈ f).
      { destruct H10 as [H10[]]. apply H18; auto. }
      repeat split; auto. intros x1 []. apply NNPP; intro.
      set(f' := f ~ [[(PlusOne m),x1]]).
      assert (Ind f').
      { repeat split; unfold Included; intros.
        - apply MKT4' in H21 as []. destruct H10; auto.
        - apply MKT4'; split; auto. apply AxiomII; split;
          eauto. intro. apply MKT41 in H21; eauto.
          apply MKT55 in H21 as []; auto. elim (H6 m); auto.
        - apply MKT4' in H23 as []. destruct H10 as [H10[]].
          pose proof H23. apply H26 in H23; auto. apply MKT4';
          split; auto. apply AxiomII; split; eauto. intro.
          apply MKT41 in H28; eauto.
          assert (Ensemble ([(PlusOne n),(h[x2])])); eauto.
          apply MKT49b in H29 as []. apply MKT55 in H28 as []; auto.
          apply MKT136 in H28; auto. rewrite H28 in H27.
          assert (x0 = x2). { apply H14; auto. }
          elim H20. rewrite H32; auto. }
      apply H8 in H21. apply H21 in H19. apply MKT4' in H19 as [_].
      apply AxiomII in H19 as []. elim H22. apply MKT41; eauto. }
  assert (Function f).
  { split; unfold Relation; intros.
    apply AxiomII in H12 as [_[x1[y1[]]]]; eauto.
    assert (x0 ∈ ω /\ y ∈ a /\ z ∈ a) as [H14[]].
    { apply AxiomII' in H12 as [_[]].
      apply AxiomII' in H13 as [_[]].
      apply AxiomII' in H12 as [_[]].
      apply AxiomII' in H13 as [_[]]; auto. }
    pose proof H14. apply H11 in H17 as [x1[_]].
    assert (x1 = y /\ x1 = z) as []. { split; apply H17; auto. }
    rewrite <-H18,<-H19; auto. }
  assert (∀ m, m ∈ ω -> ∃ y, [m,y] ∈ f).
  { apply Mathematical_Induction; eauto. intros m H13 [].
    destruct H10 as [H10[]]. apply H16 in H14; eauto.
    apply AxiomII' in H14 as [_[]]. apply AxiomII' in H14; tauto. }
  assert (dom(f) = ω).
  { apply AxiomI; split; intros.
    - apply AxiomII in H14 as [_[]]. apply AxiomII' in H14 as [_[]].
      apply AxiomII' in H14; tauto.
    - apply AxiomII; split; eauto. }
  assert (ran(f) ⊂ a).
  { unfold Included; intros. apply AxiomII in H15 as [_[]].
    apply AxiomII' in H15 as [_[]]. apply AxiomII' in H15; tauto. }
  assert (∀ n, n ∈ ω -> f[PlusOne n] = h[f[n]]).
  { intros. destruct H10 as [H10[]]. pose proof H16.
    rewrite <-H14 in H16. apply Property_Value in H16; auto.
    pose proof H16. apply Property_ran in H16. apply (H18 n) in H20;
    auto. pose proof H20. apply Property_dom,Property_Value in H21;
    auto. destruct H12. eapply H22; eauto. }
  assert (f[0] = x).
  { pose proof H9. apply Property_dom,Property_Value in H17; auto.
    destruct H12. apply (H18 0); auto. }
  exists f. split; auto. intros f1 [H18[H19[H20[]]]].
  apply MKT71; auto. intros. destruct (classic (x0 ∈ ω)).
  - generalize dependent x0. apply Mathematical_Induction.
    rewrite H17,H21; auto. intros. pose proof H23.
    apply H22 in H23. apply H16 in H25. rewrite H23,H25,H24; auto.
  - pose proof H23. rewrite <-H14 in H23. rewrite <-H19 in H24.
    apply MKT69a in H23; apply MKT69a in H24. rewrite H23,H24; auto.
Qed.

(* 加法函数预定理 对于任意一个整数m, 都有唯一函数f使得 f[0]=m 并且 f[n']=(f[n])' *)
Theorem Pre_PlusFunction : ∀ m, m ∈ ω
  -> exists ! f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω
    /\ f[0] = m /\ (∀ n, n ∈ ω -> f[PlusOne n] = PlusOne (f[n])).
Proof.
  intros. assert (Function (\{\ λ u v, u ∈ ω /\ v = PlusOne u \}\)).
  { split; intros. unfold Relation; intros. apply AxiomII in H0 as
    [H0[u[v[H1[]]]]]; eauto. apply AxiomII' in H0 as [H0[]].
    apply AxiomII' in H1 as [H1[]]. rewrite H3,H5; auto. }
  apply (Recursion m ω _) in H0 as [f[[H0[H1[H2[]]]]]]; auto.
  - exists f. split; auto. split; auto. repeat split; auto.
    + intros. pose proof H6 as H6'. apply H4 in H6.
      rewrite H6. apply AxiomI; split; intros.
      * apply AxiomII in H7 as []. apply H8.
        assert (Ensemble (PlusOne f[n])).
        { rewrite <-H1 in H6'. apply Property_Value,Property_ran,
          H2,MKT134 in H6'; eauto. }
        apply AxiomII; split; auto. apply AxiomII'.
        assert (f[n] ∈ ω).
        { rewrite <-H1 in H6'. apply Property_Value,
          Property_ran,H2 in H6'; auto. }
        split; auto. apply MKT49a; eauto.
      * apply AxiomII; split. eauto. intros. apply AxiomII in
        H8 as []. apply AxiomII' in H9 as [H9[]]. rewrite H11; auto.
    + intros g [H6[H7[H8[]]]]. apply H5; split; auto.
       repeat split; auto. intros. pose proof H11 as H11'.
       apply H10 in H11. rewrite H11. apply AxiomI; split; intros.
      * apply AxiomII; split. eauto. intros. apply AxiomII in H13
        as []. apply AxiomII' in H14 as [H14[]]. rewrite H16; auto.
      * apply AxiomII in H12 as []. apply H13. apply AxiomII.
        assert (Ensemble (PlusOne g[n])).
        { rewrite <-H7 in H11'. apply Property_Value,Property_ran,
          H8,MKT134 in H11'; eauto. }
        split; auto. apply AxiomII'.
        assert (g[n] ∈ ω).
        { rewrite <-H7 in H11'. apply Property_Value,
          Property_ran,H8 in H11'; auto. }
        split; auto. apply MKT49a; eauto.
  - pose proof MKT138; eauto.
  - apply AxiomI; split; intros.
    apply AxiomII in H1 as [H1[y]]. apply AxiomII' in H2 as [H2[]];
    auto. apply AxiomII; split. eauto. exists (PlusOne z).
    apply AxiomII'. split; auto. apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]]. apply
    AxiomII' in H2 as [H2[]]. apply MKT134 in H3. rewrite H4; auto.
Qed.

(* 该推论是对加法函数定义合理性的进一步说明, 也是对加法函数唯一性的另一种表达.
   根据该推论,加法函数定义中, {}里的元素只有一个, 从而对于任意一个整数m, 关于
   m的加法函数唯一确定 *)
Corollary PlusFunction_uni : ∀ m, m ∈ ω
  -> ∃ f, Ensemble f /\ (\{ λ f, Function f
    /\ dom(f) = ω /\ ran(f) ⊂ ω /\ m ∈ ω /\ f[0] = m
    /\ (∀ n, n ∈ ω -> f[PlusOne n] = PlusOne f[n]) \}) = [f].
Proof.
  intros. pose proof H as H'. apply Pre_PlusFunction in H
  as [f[[H[H0[H1[]]]]]]. exists f.
  assert (Ensemble f).
  { apply MKT75; auto. rewrite H0. pose proof (MKT138); eauto. }
  split; auto. apply AxiomI; split; intros.
  - apply AxiomII in H6 as [H6[H7[H8[H9[H10[]]]]]].
    apply MKT41; auto. symmetry. apply H4; auto.
  - apply MKT41 in H6; auto. rewrite H6. apply AxiomII.
    destruct H. repeat split; auto.
Qed.

(* 定义 关于整数m的加法函数, 该函数的唯一性是由上一条定理所保证的*)
Definition PlusFunction m := ∩(\{ λ f, Function f
  /\ dom(f) = ω /\ ran(f) ⊂ ω /\ m ∈ ω /\ f[0] = m
  /\ (∀ n, n ∈ ω -> f[PlusOne n] = PlusOne f[n]) \}).

(* 定义 加法 该定义仅用于m n均为W的元的情况(即 自然数上的加法) *)
Definition Plus m n := (PlusFunction m)[n].

Notation "m + n" := (Plus m n) : ω_scope.

Fact ω_Plus_in_ω : ∀ m n, m ∈ ω -> n ∈ ω -> (m + n) ∈ ω.
Proof.
  intros. unfold Plus. pose proof H as H'.
  apply PlusFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((PlusFunction m) = f).
  { unfold PlusFunction. rewrite H1. apply MKT44; auto. }
  rewrite H3. rewrite <-H1 in H2.
  apply AxiomII in H2 as [H2[H4[H5[]]]].
  assert (f[n] ∈ ran(f)).
  { apply (@ Property_ran n),Property_Value; auto.
    rewrite H5; auto. } apply H6; auto.
Qed.

(* 乘法函数预定理 对于任意一个整数m, 都有唯一函数f使得 f[0]=0 并且 f[n'] = f[n]+m *)
Theorem Pre_MultiFunction : ∀ m, m ∈ ω
  -> (exists ! f, Function f /\ dom(f) = ω /\ ran(f) ⊂ ω
    /\ f[0] = 0 /\ (∀ n, n ∈ ω -> f[PlusOne n] = f[n] + m)).
Proof.
  intros. assert (Function (\{\ λ u v, u ∈ ω /\ v = u + m \}\)).
  { split; intros. unfold Relation; intros. apply AxiomII in H0 as
    [H0[u[v[H1[]]]]]; eauto. apply AxiomII' in H0 as [H0[]].
    apply AxiomII' in H1 as [H1[]]. rewrite H3,H5; auto. }
  apply (Recursion 0 ω _) in H0 as [f[[H0[H1[H2[]]]]]]; auto.
  - exists f. split; auto. split; auto. repeat split; auto.
    + intros. pose proof H6 as H6'. apply H4 in H6.
      rewrite H6. apply AxiomI; split; intros.
      * apply AxiomII in H7 as []. apply H8.
        assert (Ensemble (f[n] + m)).
        { assert ((f[n] + m) ∈ ω).
          { apply ω_Plus_in_ω; auto. apply H2,(@ Property_ran n),
            Property_Value; auto. rewrite H1; auto. } eauto. }
        apply AxiomII; split; auto. apply AxiomII'.
        assert (f[n] ∈ ω).
        { apply H2,(@ Property_ran n),Property_Value; auto.
          rewrite H1; auto. } split; auto. apply MKT49a; eauto.
      * apply AxiomII; split. eauto. intros. apply AxiomII in
        H8 as []. apply AxiomII' in H9 as [H9[]]. rewrite H11; auto.
    + intros g [H6[H7[H8[]]]]. apply H5. split; auto.
      repeat split; auto. intros. pose proof H11 as H11'.
      apply H10 in H11. rewrite H11. apply AxiomI; split; intros.
      * apply AxiomII; split. eauto. intros. apply AxiomII in H13
        as []. apply AxiomII' in H14 as [H14[]]. rewrite H16; auto.
      * apply AxiomII in H12 as []. apply H13. apply AxiomII.
        assert (Ensemble (g[n] + m)).
        { assert ((g[n] + m) ∈ ω).
          { apply ω_Plus_in_ω; auto. apply H8,(@ Property_ran n),
            Property_Value; auto. rewrite H7; auto. } eauto. }
        split; auto. apply AxiomII'.
        assert (g[n] ∈ ω).
        { rewrite <-H7 in H11'. apply Property_Value,
          Property_ran,H8 in H11'; auto. }
        split; auto. apply MKT49a; eauto.
  - pose proof MKT138; eauto.
  - apply AxiomI; split; intros.
    apply AxiomII in H1 as [H1[y]]. apply AxiomII' in H2 as [H2[]];
    auto. apply AxiomII; split. eauto. exists (z + m).
    apply AxiomII'. split; auto. apply MKT49a; eauto.
    assert ((z + m) ∈ ω). { apply ω_Plus_in_ω; auto. } eauto.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]]. apply
    AxiomII' in H2 as [H2[]]. rewrite H4. apply ω_Plus_in_ω; auto.
Qed.

(* 该推论是对乘法函数定义合理性的进一步说明, 也是对乘法函数唯一性的另一种表达.
   根据该推论,乘法函数定义中, {}里的元素只有一个, 从而对于任意一个整数m, 关于
   m的乘法函数唯一确定 *)
Corollary MultiFunction_uni : ∀ m, m ∈ ω
  -> ∃ f, Ensemble f /\ \{ λ f, Function f
    /\ dom(f) = ω /\ ran(f) ⊂ ω /\ m ∈ ω /\ f[0] = 0
    /\ (∀ n, n ∈ ω -> f[PlusOne n] = f[n] + m) \} = [f].
Proof.
  intros. pose proof H as H'. apply Pre_MultiFunction in H
  as [f[[H[H0[H1[]]]]]]. exists f.
  assert (Ensemble f).
  { apply MKT75; auto. rewrite H0. pose proof (MKT138); eauto. }
  split; auto. apply AxiomI; split; intros.
  - apply AxiomII in H6 as [H6[H7[H8[H9[H10[]]]]]].
    apply MKT41; auto. symmetry. apply H4; auto.
  - apply MKT41 in H6; auto. rewrite H6. apply AxiomII.
    destruct H. repeat split; auto.
Qed.

(* 定义 关于整数m的乘法函数, 该函数的唯一性是由上一条定理所保证的 *)
Definition MultiFunction m := ∩(\{ λ f, Function f
  /\ dom(f) = ω /\ ran(f) ⊂ ω /\ m ∈ ω /\ f[0] = 0
  /\ (∀ n, n ∈ ω -> f[PlusOne n] = f[n] + m) \}).

(* 定义 乘法 该定义仅用于m n均为W的元的情况(即 自然数上的乘法) *)
Definition Mult m n := (MultiFunction m)[n].

Notation "m · n" := (Mult m n)(at level 10) : ω_scope.

Corollary ω_Mult_in_ω : ∀ m n, m ∈ ω -> n ∈ ω -> (m · n) ∈ ω.
Proof.
  intros. unfold Mult. pose proof H as H'.
  apply MultiFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((MultiFunction m) = f).
  { unfold MultiFunction. rewrite H1. apply MKT44; auto. }
  rewrite H3. rewrite <-H1 in H2.
  apply AxiomII in H2 as [H2[H4[H5[]]]].
  assert (f[n] ∈ ran(f)).
  { apply (@ Property_ran n),Property_Value; auto.
    rewrite H5; auto. } apply H6; auto.
Qed.

(* 验证:  m + 0 = m  /  0 + m = m *)
Fact Plus_Property1_a : ∀ m, m ∈ ω -> m + 0 = m.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as []. apply H1. apply AxiomII; split.
    eauto. apply AxiomII. destruct MKT135. split.
    apply MKT49a; eauto. intros. apply AxiomII
    in H4 as [H4[H5[H6[H7[H8[]]]]]]. rewrite <-H9.
    apply Property_Value; auto. rewrite H6; auto.
  - apply AxiomII; split. eauto. intros. apply AxiomII in H1 as [].
    apply AxiomII in H2 as []. pose proof H as H'.
    apply Pre_PlusFunction in H as [f[[H[H4[H5[]]]]]].
    assert ([0,y] ∈ f).
    { apply H3. apply AxiomII. destruct H. repeat split; auto. apply
      MKT75. split; auto. rewrite H4. pose proof MKT138; eauto. }
    pose proof H9 as H9'. apply Property_dom,Property_Value in H9;
    auto. assert (f[0] = y). { destruct H. apply (H10 0); auto. }
    rewrite <-H10,H6; auto.
Qed.

Fact Plus_Property2_a : ∀ m n, m ∈ ω -> n ∈ ω
  -> m + (PlusOne n) = PlusOne (m + n).
Proof.
  intros. pose proof H as H'. apply PlusFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  rewrite <-H1 in H2. apply AxiomII in H2 as [H2[H3[H4[H5[H6[]]]]]].
  apply MKT44 in H2 as []. unfold Plus,PlusFunction. rewrite H1,
  H2. apply H8; auto.
Qed.

Fact Plus_Property1_b : ∀ m, m ∈ ω -> 0 + m = m.
Proof.
  destruct MKT135. apply Mathematical_Induction.
  - apply Plus_Property1_a; auto.
  - intros. rewrite Plus_Property2_a; auto. rewrite H2; auto.
Qed.

Fact Plus_Property2_b : ∀ m n, m ∈ ω -> n ∈ ω
  -> (PlusOne m) + n = PlusOne (m + n).
Proof.
  intros. generalize dependent n. apply Mathematical_Induction.
  - rewrite Plus_Property1_a,Plus_Property1_a; auto.
  - intros. rewrite Plus_Property2_a,Plus_Property2_a; auto.
    rewrite H1; auto.
Qed.

Fact Plus_Commutation : ∀ m n, m ∈ ω -> n ∈ ω -> m + n = n + m.
Proof.
  intros. generalize dependent n. apply Mathematical_Induction.
  - rewrite Plus_Property1_a,Plus_Property1_b; auto.
  - intros. rewrite Plus_Property2_a,Plus_Property2_b,H1; auto.
Qed.

Fact Plus_Association : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> (m + n) + k = m + (n + k).
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Plus_Property1_b,Plus_Property1_b; auto.
    apply ω_Plus_in_ω; auto.
  - intros. rewrite Plus_Property2_b,Plus_Property2_b,
    Plus_Property2_b; try apply ω_Plus_in_ω; auto.
    rewrite H2; auto.
Qed.

Fact Plus_Cancellation : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> m + n = m + k <-> n = k.
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Plus_Property1_b,Plus_Property1_b; auto. split; auto.
  - intros. rewrite Plus_Property2_b,Plus_Property2_b; auto.
    split; intros. apply H2. apply MKT136 in H3; try apply
    ω_Plus_in_ω; auto. apply H2 in H3. rewrite H3; auto.
Qed.

Lemma Plus_PrOrder_Lemma : ∀ m n, m ∈ ω -> n ∈ ω
  -> (PlusOne m) ∈ (PlusOne n) <-> m ∈ n.
Proof.
  split; intros.
  - apply MKT4 in H1 as [].
    + apply AxiomII in H0 as [H0[[]]]. apply H3 in H1. apply H1.
      apply MKT4; right. apply MKT41; eauto.
    + apply MKT41 in H1; eauto. rewrite <-H1.
      apply MKT4; right. apply MKT41; eauto.
  - apply MKT4. destruct (classic (LastMember m E n)).
    + right. assert (n = PlusOne m).
      { apply MKT133; auto. apply AxiomII
        in H0 as [H0[]]. apply AxiomII; auto. }
      apply MKT41; eauto.
    + left. assert (Ordinal n /\ Ordinal (PlusOne m)) as [].
      { apply MKT134,AxiomII in H as [H[]].
        apply AxiomII in H0 as [H0[]]; auto. }
        apply (@ MKT110 n _) in H4 as [H4|[|]]; auto.
        apply MKT4 in H4 as []. elim (MKT102 m n); auto.
        apply MKT41 in H4; eauto. rewrite H4 in H1.
        elim (MKT101 m); auto. elim H2. split; auto. intros. intro.
        apply AxiomII' in H6 as []. apply AxiomII' in H7 as [].
        rewrite H4 in H5. apply MKT4 in H5 as [].
        elim (MKT102 m y); auto. apply MKT41 in H5; eauto.
        rewrite H5 in H8. elim (MKT101 m); auto.
Qed.

Fact Plus_PrOrder : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> (m + n) ∈ (m + k) <-> n ∈ k.
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Plus_Property1_b,Plus_Property1_b; auto. split; auto.
  - intros. rewrite Plus_Property2_b,Plus_Property2_b; auto.
    split; intros. apply H2. apply Plus_PrOrder_Lemma; try apply
    ω_Plus_in_ω; auto. apply H2 in H3. apply Plus_PrOrder_Lemma;
    try apply ω_Plus_in_ω; auto.
Qed.

Corollary Plus_PrOrder_Corollary : ∀ m n, m ∈ ω -> n ∈ ω
  -> n ∈ m <-> (exists ! k, k ∈ ω /\ 0 ∈ k /\ n + k = m).
Proof.
  split.
  - generalize dependent m.
    set (P := fun x => ∀ m, m ∈ ω -> x ∈ m
      -> exists ! k, k ∈ ω /\ 0 ∈ k /\ x + k = m).
    assert (∀ n, n ∈ ω -> P n).
    { apply Mathematical_Induction; unfold P; intros.
      - exists m. repeat split; auto.
        rewrite Plus_Property1_b; auto. intros x1 [H2[]].
        rewrite Plus_Property1_b in H4; auto.
      - pose proof H2. apply AxiomII in H4 as [H4[H5[]]].
        assert (m ⊂ m /\ m ≠ 0) as [].
        { split; unfold Included; intros; auto. intro.
          rewrite H8 in H3. elim (@ MKT16 (PlusOne k)); auto. }
        apply H7 in H8 as [m0]; auto. clear H9.
        assert (m ∈ R /\ LastMember m0 E m) as [].
        { split; auto. apply AxiomII in H2 as [H2[]].
          apply AxiomII; auto. }
        apply MKT133 in H10; auto.
        clear H5 H6 H7 H8 H9. rewrite H10 in H3.
        assert (∀ m, m ∈ ω -> PlusOne m = m + 1).
        { intros. replace 1 with (PlusOne 0).
          rewrite Plus_Property2_a,Plus_Property1_a;
          destruct MKT135; auto. unfold PlusOne. apply MKT17. }
        assert (m0 ∈ ω).
        { assert (m0 ∈ m).
          { rewrite H10. apply MKT4; right; apply MKT41; auto.
            apply (MKT33 (PlusOne m0)). rewrite <-H10; auto.
            unfold Included; intros; apply MKT4; auto. }
          pose proof MKT138. apply AxiomII in H7 as [H7[]].
          apply H9 in H2. apply H2; auto. }
        pose proof in_ω_1. rewrite H5,H5,Plus_Commutation,
        (Plus_Commutation m0) in H3; auto. apply Plus_PrOrder
        in H3; auto. apply H1 in H6 as [k0[[H6[]]]]; auto.
        exists k0. repeat split; auto.
        rewrite Plus_Property2_b,H10,H9; auto. intros x1 [H12[]].
        rewrite Plus_Property2_b in H14; auto. rewrite H10 in H14.
        apply MKT136 in H14; auto. apply ω_Plus_in_ω; auto.
        rewrite <-H9. apply ω_Plus_in_ω; auto. }
    apply H in H0; auto.
  - intros [k[[H1[]]]].
    assert (∀ m, m ∈ ω -> ~ (m + k) ∈ m /\ m + k <> m).
    { intros. assert ((m0 + 0) ∈ (m0 + k)).
      { apply Plus_PrOrder; destruct MKT135; auto. }
      rewrite Plus_Property1_a in H6; auto. split; intro.
      elim (MKT102 m0 (m0 + k)); auto.
      rewrite H7 in H6. elim (MKT101 m0); auto. }
    assert (Ordinal m /\ Ordinal n) as [].
    { apply AxiomII in H as [H[]];
      apply AxiomII in H0 as [H0[]]; auto. }
    apply (@ MKT110 _ n) in H6 as [H6|[]]; auto. clear H7.
    assert ((k + m) ∈ (k + n)). { apply Plus_PrOrder; auto. }
    rewrite Plus_Commutation,(Plus_Commutation _ n),H3 in H7; auto.
    apply H5 in H as []; contradiction. rewrite H6 in H3.
    apply H5 in H0. destruct H0; contradiction.
Qed.

(* 验证:  m·0 = 0  /  0·m = 0 *)
Fact Mult_Property1_a : ∀ m, m ∈ ω -> m · 0 = 0.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as []. apply H1. destruct MKT135.
    apply AxiomII; split. eauto. apply AxiomII; split.
    apply MKT49a; eauto. intros. apply AxiomII in H4 as
    [H4[H5[H6[H7[H8[]]]]]]. replace ([0,0]) with ([0,y[0]]).
    apply Property_Value; auto. rewrite H6; auto. rewrite H9; auto.
  - pose proof (@ MKT16 z). contradiction.
Qed.

Fact Mult_Property2_a : ∀ m n, m ∈ ω -> n ∈ ω
  -> m · (PlusOne n) = (m · n) + m.
Proof.
  intros. unfold Mult. pose proof H.
  apply MultiFunction_uni in H1 as [f[]].
  assert ((MultiFunction m) = f).
  { unfold MultiFunction. rewrite H2. apply MKT44; auto. }
  rewrite H3. assert (f ∈ [f]). { apply MKT41; auto. }
  rewrite <-H2 in H4. apply AxiomII in H4 as [H4[H5[H6[H7[H8[]]]]]].
  rewrite H10; auto.
Qed.

Fact Mult_Property1_b : ∀ m, m ∈ ω -> 0 · m = 0.
Proof.
  destruct MKT135. apply Mathematical_Induction.
  - rewrite Mult_Property1_a; auto.
  - intros. rewrite Mult_Property2_a; auto.
    rewrite H2,Plus_Property1_a; auto.
Qed.

Fact Mult_Property2_b : ∀ m n, m ∈ ω -> n ∈ ω
  -> (PlusOne m) · n = (m · n) + n.
Proof.
  intros. generalize dependent n. apply Mathematical_Induction.
  - repeat rewrite Mult_Property1_a; auto.
    rewrite Plus_Property1_a; auto.
  - intros. rewrite Mult_Property2_a,Mult_Property2_a,H1,
    Plus_Property2_a,Plus_Property2_a,Plus_Association,
    Plus_Association,(Plus_Commutation k);
    try apply ω_Plus_in_ω; try apply ω_Mult_in_ω; auto.
Qed.

Fact Mult_Commutation : ∀ m n, m ∈ ω -> n ∈ ω -> m · n = n · m.
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Mult_Property1_a,Mult_Property1_b; auto.
  - intros. rewrite Mult_Property2_a,Mult_Property2_b,H1; auto.
Qed.

Fact Mult_Distribution : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> m · (n + k) = (m · n) + (m · k).
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Mult_Property1_b,Mult_Property1_b,Mult_Property1_b,
    Plus_Property1_b; auto. apply ω_Plus_in_ω; auto.
  - intros. rewrite Mult_Property2_b,Mult_Property2_b,
    Mult_Property2_b,H2,(Plus_Association _ n),
    <-(Plus_Association n),(Plus_Commutation n (k0 · k)),
    (Plus_Association _ n),<-(Plus_Association (k0 · n));
    try apply ω_Plus_in_ω; try apply ω_Mult_in_ω; auto.
Qed.

Fact Mult_Association : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> (m · n) · k = m · (n · k).
Proof.
  intros. generalize dependent m. apply Mathematical_Induction.
  - rewrite Mult_Property1_b,Mult_Property1_b,Mult_Property1_b;
    try apply ω_Mult_in_ω; auto.
  - intros. rewrite Mult_Property2_b,Mult_Property2_b,<-H2,
    (Mult_Commutation _ k),Mult_Distribution,
    (Mult_Commutation k),(Mult_Commutation k);
    try apply ω_Plus_in_ω; try apply ω_Mult_in_ω; auto.
Qed.

(* 此引理说明了W中无零因子 *)
Lemma Mult_Cancellation_Lemma : ∀ m n, m ∈ ω -> n ∈ ω
  -> m <> 0 -> m · n = 0 -> n = 0.
Proof.
  intros. pose proof MKT138. pose proof H. pose proof H0.
  apply AxiomII in H4 as [H4[H6[]]].
  apply AxiomII in H5 as [H5[H9[]]].
  assert (m ⊂ m /\ m ≠ 0) as []. { split; auto. }
  apply H8 in H12 as [m0]; auto. clear H13.
  assert (m = PlusOne m0).
  { apply MKT133; auto. apply AxiomII; auto. }
  assert (m0 ∈ ω).
  { apply AxiomII in H3 as [H3[]]. apply H15 in H. apply H.
    rewrite H13. apply MKT4; right. apply MKT41; auto.
    apply (MKT33 m); auto. unfold Included; intros.
    rewrite H13. apply MKT4; auto. }
  rewrite H13,Mult_Property2_b in H2; auto. apply NNPP; intro.
  assert (n ⊂ n /\ n ≠ 0) as []. { split; auto. }
  apply H11 in H16 as [n0]; auto. clear H17.
  assert (n = PlusOne n0).
  { apply MKT133; auto. apply AxiomII; auto. }
  assert (n0 ∈ ω).
  { apply AxiomII in H3 as [H3[]]. apply H19 in H0. apply H0.
    rewrite H17. apply MKT4; right. apply MKT41; auto.
    apply (MKT33 n); auto. unfold Included; intros.
    rewrite H17. apply MKT4; auto. }
  assert ((m0 · n) ∈ ω). { apply ω_Mult_in_ω; auto. }
  rewrite H17,Plus_Property2_a in H2; auto. destruct MKT135.
  assert (((m0 · (PlusOne n0)) + n0) ∈ ω).
  { rewrite <-H17. apply ω_Plus_in_ω; auto. }
  apply H21 in H22; auto. rewrite <-H17; auto.
Qed.

Fact Mult_Cancellation : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> m <> 0 -> m · n = m · k -> n = k.
Proof.
  intros. generalize dependent n.
  set (p := fun x => ∀ k n, k ∈ ω -> n ∈ ω -> x <> 0
    -> x · n = x · k -> n = k).
  assert (∀ x, x ∈ ω -> p x).
  { apply Mathematical_Induction. unfold p. intros; elim H4; auto.
    unfold p. intros m0 H3. intros. generalize dependent k.
    set (p1 := fun x => ∀ k, k ∈ ω
      -> (PlusOne m0) · x = (PlusOne m0) · k -> x = k).
    assert (∀ x, x ∈ ω -> p1 x).
    { apply Mathematical_Induction. unfold p1. intros.
      rewrite Mult_Property1_a in H8. symmetry in H8.
      apply (Mult_Cancellation_Lemma (PlusOne m0)) in H8; auto.
      apply MKT134; auto. intros n0 H1 H8. unfold p1 in *. intros.
      set (p2 := fun x => (PlusOne m0) · (PlusOne n0)
        = (PlusOne m0) · x -> (PlusOne n0) = x).
      assert (∀ x, x ∈ ω -> p2 x).
      { apply Mathematical_Induction. unfold p2; intros.
        rewrite Mult_Property1_a in H11; auto. apply
        (Mult_Cancellation_Lemma (PlusOne m0)) in H11; auto. intros.
        assert (((PlusOne m0) · n0) ∈ ω
          /\ ((PlusOne m0) · k1) ∈ ω) as [].
        { split; apply ω_Mult_in_ω; try apply MKT134; auto. }
        unfold p2 in *. intros. rewrite Mult_Property2_a,
        Mult_Property2_a,Plus_Commutation,
        (Plus_Commutation _ (PlusOne m0)) in H15; auto.
        apply Plus_Cancellation in H15; auto.
        apply H8 in H15; auto. rewrite H15; auto. }
      apply H11; auto. }
    intros. apply H1; auto. }
  intros. apply (H0 m); auto.
Qed.

Fact Mult_PrOrder : ∀ m n k, m ∈ ω -> n ∈ ω -> k ∈ ω
  -> m <> 0 -> (m · n) ∈ (m · k) <-> n ∈ k.
Proof.
  pose proof Plus_PrOrder_Lemma. split; intros.
  assert (k <> 0).
  { intro. rewrite H5 in H4. rewrite Mult_Property1_a in H4; auto.
    elim (@ MKT16 (m · n)); auto. }
  - generalize dependent n. generalize dependent k.
    set (q := (fun a => ∀ n k, k ∈ ω -> k <> 0 -> a <> 0
      -> n ∈ ω -> (a · n) ∈ (a · k) -> n ∈ k)).
    assert (∀ a, a ∈ ω -> q a).
    { apply Mathematical_Induction. unfold q; intros.
      elim H4; auto. intros k H1 H2. unfold q in *. intros.
      rewrite Mult_Property2_b,Mult_Property2_b in H8; auto.
      generalize dependent k0.
      set (q1 := (fun a => ∀ k0, k0 ∈ ω -> k0 <> 0
        -> ((k · a) + a) ∈ ((k · k0) + k0) -> a ∈ k0)).
      assert (∀ a, a ∈ ω -> q1 a).
      { apply Mathematical_Induction.
        unfold q1; intros. destruct MKT135.
        assert (Ordinal k0 /\ Ordinal 0) as [].
        { apply AxiomII in H4 as [H4[]].
          apply AxiomII in H9 as [H9[]]; auto. }
        apply (@ MKT110 k0 0) in H11 as [H11|[|]];
        try contradiction; auto; clear H12. elim (@ MKT16 k0); auto.
        intros k1 H4 H5. unfold q1 in *. intros.
        set (q2 := fun a => ((k · (PlusOne k1)) + (PlusOne k1))
           ∈ ((k · a) + a) -> a <> 0 -> (PlusOne k1) ∈ a).
        assert (∀ a, a ∈ ω -> q2 a).
        { apply Mathematical_Induction. unfold q2; intros.
          elim H12; auto. intros k2 H11 H12.
          unfold q2 in *; intros. apply (H k1 k2); auto.
          assert ((PlusOne k) ∈ ω /\ (PlusOne k1) ∈ ω
            /\ (PlusOne k2) ∈ ω) as [H15[]].
          { repeat split; apply MKT134; auto. }
          assert (((PlusOne k) · k1) ∈ ω
            /\ ((PlusOne k) · k2) ∈ ω) as [].
          { split; apply ω_Mult_in_ω; auto. }
          rewrite <-Mult_Property2_b,<-Mult_Property2_b in H13; auto.
          rewrite Mult_Property2_a,Mult_Property2_a in H13; auto.
          rewrite Plus_Commutation,(Plus_Commutation _ (PlusOne k))
          in H13; auto. apply Plus_PrOrder in H13; auto.
          assert (k2 <> 0).
          { intro. rewrite H20 in H13. rewrite Mult_Property1_a
            in H13; auto. elim (@ MKT16 ((PlusOne k) · k1)); auto. }
          rewrite Mult_Property2_b,Mult_Property2_b in H13; auto. }
        apply H11 in H8. apply H8; auto. }
      apply H4 in H7; auto. }
    apply H1 in H0; auto.
  - set (q := fun a => a <> 0 -> n ∈ k -> (a · n) ∈ (a · k)).
    assert (∀ a, a ∈ ω -> q a).
    { apply Mathematical_Induction. unfold q; intros.
      elim H5; auto. intros k0 H5 H6. unfold q in *; intros.
      rewrite Mult_Property2_b,Mult_Property2_b; auto.
      destruct (classic (k0 = 0)).
      - rewrite H9,Mult_Property1_b,Mult_Property1_b,
        Plus_Property1_b,Plus_Property1_b; auto.
      - assert ((k0 · n) ∈ ω /\ (k0 · k) ∈ ω) as [].
        { split; apply ω_Mult_in_ω; auto. }
        assert (((k0 · n) + n) ∈ ((k0 · k) + n)).
        { rewrite Plus_Commutation,(Plus_Commutation _ n); auto.
          apply Plus_PrOrder; auto. }
        assert (((k0 · k) + n) ∈ ((k0 · k) + k)).
        { apply Plus_PrOrder; auto. }
        assert (((k0 · k) + k) ∈ ω). { apply ω_Plus_in_ω; auto. }
        apply AxiomII in H14 as [H14[[]]]. apply H16 in H13.
        apply H13; auto. }
    apply H5 in H0; auto.
Qed.

(* 定义 偶数 *)
Definition Even m := ∃ k, k ∈ ω /\ m = 2 · k.

(* 定义 偶数类 *)
Definition ω_E := \{ λ u, Even u \}.

(* 偶数类是集 *)
Corollary ω_E_is_Set : Ensemble (ω_E).
Proof.
  apply (MKT33 ω). pose proof MKT138; eauto.
  unfold Included; intros. apply AxiomII in H as [H[m[]]].
  rewrite H1. apply ω_Mult_in_ω; try apply in_ω_2; auto.
Qed.

(* 定义 奇数 *)
Definition Odd m := ∃ k, k ∈ ω /\ m = (2 · k) + 1.

(* 定义 奇数类 *)
Definition ω_O := \{ λ u, Odd u \}.

(* 奇数类是集 *)
Corollary ω_O_is_Set : Ensemble (ω_O).
Proof.
  apply (MKT33 ω). pose proof MKT138; eauto.
  unfold Included; intros. apply AxiomII in H as [H[m[]]].
  rewrite H1. apply ω_Plus_in_ω; try apply in_ω_1; auto.
  apply ω_Mult_in_ω; try apply in_ω_2; auto.
Qed.

(* 偶数集是自然数集的真子集 *)
Fact ω_E_properSubset_ω : ω_E ⊂ ω /\ ω_E <> ω.
Proof.
  split. unfold Included; intros. apply AxiomII in H as [H[x[]]].
  rewrite H1. apply ω_Mult_in_ω; auto. apply in_ω_2.
  intro. pose proof in_ω_1. rewrite <-H in H0.
  apply AxiomII in H0 as [H0[x[]]]. destruct (classic (x=0)).
  rewrite H3,Mult_Property1_a in H2.
  assert (0 ∈ 1). { rewrite H3 in H1. apply MKT41; eauto. }
  rewrite H2 in H4. pose proof (@ MKT16 0); auto. apply in_ω_2.
  assert (1 ∈ (2 · x)).
  { pose proof in_ω_2. pose proof in_ω_1. pose proof in_ω_0.
    assert (1 ∈ 2). { apply MKT4. right. apply MKT41; auto. }
    assert (1 = PlusOne 0). { unfold PlusOne. rewrite MKT17; auto. }
    assert (x ∈ (2 · x)).
    { apply (Mult_PrOrder x) in H7; auto. rewrite H8,
      Mult_Property2_a,Mult_Property1_a,Plus_Property1_b,
      Mult_Commutation in H7; rewrite <-H8 in H7; auto.
      rewrite <-H8; auto. }
    rewrite <-H2 in H9. apply MKT41 in H9; auto. elim H3; auto. }
  rewrite <-H2 in H4. elim (MKT101 1); auto.
Qed.

(* 偶数集和自然数集等势 *)
Fact ω_E_Equivalent_ω : ω_E ≈ ω.
Proof.
  apply MKT146. unfold Equivalent.
  set (f := \{\ λ u v, u ∈ ω /\ v = 2 · u \}\).
  exists f. repeat split.
  - unfold Relation; intros.
    apply AxiomII in H as [H[a[b[]]]]; eauto.
  - intros. apply AxiomII' in H as [H[]].
    apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
  - unfold Relation; intros.
    apply AxiomII in H as [H[a[b[]]]]; eauto.
  - intros. apply AxiomII' in H as []. apply AxiomII' in H0 as [].
    apply AxiomII' in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
    rewrite H4 in H6. pose proof in_ω_1. pose proof in_ω_2.
    assert (2 <> 0).
    { destruct MKT135. assert (0 ∈ 2).
      { apply MKT4; left. apply MKT41; eauto. }
      intro. rewrite H12 in H11. pose proof (@ MKT16 0); auto. }
    apply (Mult_Cancellation 2); auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as [H[]].
      apply AxiomII' in H0 as [H0[]]; auto.
    + apply AxiomII; split. eauto. exists (2 · z).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      assert ((2 · z) ∈ ω).
      { apply ω_Mult_in_ω; auto. apply in_ω_2. } eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]].
      apply AxiomII; split; auto. unfold Even; eauto.
    + apply AxiomII in H as [H[x[]]]. apply AxiomII; split; auto.
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

(* 奇数集是自然数集的真子集 *)
Fact ω_O_properSubset_ω : ω_O ⊂ ω /\ ω_O <> ω.
Proof.
  split. unfold Included; intros. apply AxiomII in H as [H[x[]]].
  rewrite H1. apply ω_Plus_in_ω; try apply ω_Mult_in_ω; auto.
  apply in_ω_2. apply in_ω_1. intro. destruct MKT135.
  pose proof H0 as Ha. rewrite <-H in H0.
  apply AxiomII in H0 as [H0[x[]]].
  assert (1 = PlusOne 0). { unfold PlusOne. rewrite MKT17; auto. }
  assert ((2 · x) ∈ ω). { apply ω_Mult_in_ω; auto. apply in_ω_2. }
  rewrite H4,Plus_Property2_a,Plus_Property1_a in H3;
  try rewrite <-H4; auto. apply H1 in H5. rewrite <-H4 in H3; auto.
Qed.

(* 奇数集和自然数集等势 *)
Fact ω_O_Equivalent_ω : ω_O ≈ ω.
Proof.
  set (f := \{\ λ u v, u ∈ ω /\ v = (2 · u) + 1 \}\).
  apply MKT146. exists f. repeat split; intros.
  - unfold Relation; intros.
    apply AxiomII in H as [H[a[b[]]]]; eauto.
  - apply AxiomII' in H as [H[]].
    apply AxiomII' in H0 as [H0[]]. rewrite H2,H4; auto.
  - unfold Relation; intros.
    apply AxiomII in H as [H[a[b[]]]]; eauto.
  - apply AxiomII' in H as []. apply AxiomII' in H0 as [].
    apply AxiomII' in H1 as [H1[]]. apply AxiomII' in H2 as [H2[]].
    pose proof in_ω_1; pose proof in_ω_2.
    assert ((2 · y) ∈ ω). { apply ω_Mult_in_ω; auto. }
    assert ((2 · z) ∈ ω). { apply ω_Mult_in_ω; auto. }
    rewrite H4 in H6. rewrite Plus_Commutation,
    (Plus_Commutation _ 1) in H6; auto.
    apply Plus_Cancellation,Mult_Cancellation in H6; auto. intro.
    assert (0 ∈ 2).
    { apply MKT4; left. rewrite H11 in H8. apply MKT41; eauto. }
    rewrite H11 in H12. pose proof (@ MKT16 0); auto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as [H[]].
      apply AxiomII' in H0 as [H0[]]; auto.
    + apply AxiomII; split. eauto. exists ((2 · z) + 1).
      apply AxiomII'. split; auto. apply MKT49a; eauto.
      pose proof in_ω_1; pose proof in_ω_2.
      assert ((((2 · z) + 1) ∈ ω)).
      { apply ω_Plus_in_ω; auto. apply ω_Mult_in_ω; auto. } eauto.
  - apply AxiomI; split; intros.
    + apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [H0[]].
      apply AxiomII; split; auto. exists x; auto.
    + apply AxiomII in H as [H[x[]]]. apply AxiomII; split; auto.
      exists x. apply AxiomII'; split; auto. apply MKT49a; eauto.
Qed.

(* 偶数集和奇数集等势 *)
Fact ω_O_Equivalent_ω_E : ω_O ≈ ω_E.
Proof.
  pose proof ω_E_Equivalent_ω; pose proof ω_O_Equivalent_ω.
  apply (MKT147 ω); auto. apply MKT146; auto.
Qed.

(* 以下几条验证了偶数集与奇数集互余 *)
Fact ω_E_Union_ω_O : ω_E ∪ ω_O = ω.
Proof.
  apply AxiomI; split; intros.
  - pose proof ω_E_properSubset_ω; pose proof ω_O_properSubset_ω.
    destruct H0,H1. apply MKT4 in H as [];[apply H0|apply H1];auto.
  - generalize dependent z. apply Mathematical_Induction.
    + apply MKT4; left. destruct MKT135.
      apply AxiomII; split. eauto. exists 0. split; auto.
      rewrite Mult_Property1_a; try apply in_ω_2; auto.
    + intros. apply MKT4 in H0 as [].
      * apply MKT4; right. apply AxiomII in H0 as [H0[x[]]].
        apply AxiomII; split. apply MKT134 in H; eauto.
        exists x. split; auto. replace ((2 · x) + 1)
        with ((2 · x) + (PlusOne 0)). rewrite Plus_Property2_a,
        Plus_Property1_a; try rewrite <-H2; auto.
        destruct MKT135; auto. unfold PlusOne. rewrite MKT17; auto.
      * apply MKT4; left. apply AxiomII in H0 as [H0[x[]]].
        apply AxiomII; split. apply MKT134 in H; eauto.
        assert ((2 · x) ∈ ω).
        { pose proof in_ω_2. apply ω_Mult_in_ω; auto. }
        pose proof in_ω_1; pose proof in_ω_2.
        rewrite H2,<-Plus_Property2_a; auto. replace (PlusOne 1)
        with (2 · 1). rewrite <-Mult_Distribution; auto.
        exists (x + 1); split; auto. apply ω_Plus_in_ω; auto.
        replace (PlusOne 1) with 2; auto.
        assert (PlusOne 0 = 1).
        { unfold PlusOne. rewrite MKT17; auto. }
        rewrite <-H6,Mult_Property2_a,Mult_Property1_a,
        Plus_Property1_b; try rewrite H6; auto.
Qed.

Fact ω_E_Intersection_ω_O : ω_E ∩ ω_O = Φ.
Proof.
  set (A := \{ λ u, u ∈ (ω_E ∩ ω_O) \}).
  destruct (classic (A = 0)).
  - apply NNPP; intro. apply NEexE in H0 as [].
    assert (x ∈ A). { apply AxiomII; eauto. }
    rewrite H in H1. pose proof (@ MKT16 x); auto.
  - assert (A ⊂ ω).
    { unfold Included; intros. apply AxiomII in H0 as [].
      apply MKT4' in H1 as []. apply AxiomII in H1 as [H1[x[]]].
      rewrite H4. apply ω_Mult_in_ω; try apply in_ω_2; auto. }
    assert (WellOrdered E A).
    { apply (wosub ω); auto. pose proof MKT138.
      apply AxiomII in H1 as []. apply MKT107; auto. }
    destruct H1. assert (A ⊂ A /\ A ≠ 0) as []. { split; auto. }
    apply H2 in H3 as [x[]]; auto. clear H4.
    apply AxiomII in H3 as []. apply MKT4' in H4 as [].
    assert (1 = PlusOne 0).
    { unfold PlusOne. rewrite MKT17; auto. }
    destruct MKT135. destruct (classic (x=0)).
    + rewrite H10 in H6. apply AxiomII in H6 as [H6[m[]]].
      assert (((2 · m)) ∈ ω).
      { apply ω_Mult_in_ω; try apply in_ω_2; auto. }
      rewrite H7,Plus_Property2_a,Plus_Property1_a in H12;
      try rewrite <-H7; auto. rewrite <-H7 in H12.
      apply H9 in H13. contradiction.
    + assert (x ∈ ω).
      { apply AxiomII in H4 as [H4[x0[]]]. rewrite H12.
        apply ω_Mult_in_ω; try apply in_ω_2; auto. }
      pose proof H11 as Ha. apply AxiomII in H11 as [H11[H12[]]].
      assert (x ⊂ x /\ x ≠ 0) as []. { split; auto. }
      apply H14 in H15 as [x0]; auto. clear H16.
      assert (x = PlusOne x0).
      { apply MKT133; auto. apply AxiomII; auto. }
      assert (x0 ∈ x).
      { rewrite H16. apply MKT4; right. apply MKT41; auto.
        apply (MKT33 (x)); auto. unfold Included; intros.
        rewrite H16. apply MKT4; auto. }
      assert (x0 ∈ ω).
      { pose proof MKT138. apply AxiomII in H18 as [H18[]].
        eapply H20; eauto. }
      assert (x = x0 + 1).
      { rewrite H7. rewrite Plus_Property2_a,
        Plus_Property1_a; auto. }
      pose proof in_ω_1; pose proof in_ω_2.
      assert (x0 ∈ ω_E).
      { apply AxiomII; split. eauto. apply AxiomII in H6
        as [H6[m[]]]. rewrite H23 in H19.
        assert ((2 · m) ∈ ω). { apply ω_Mult_in_ω; auto. }
        rewrite Plus_Commutation,(Plus_Commutation _ 1)
        in H19; auto. apply Plus_Cancellation in H19; auto.
        exists m; auto. }
      assert (x0 ∈ ω_O).
      { apply AxiomII in H4 as [H4[m[]]].
        destruct (classic (m = 0)).
        - rewrite H25 in H24. rewrite Mult_Property1_a in H24; auto.
          rewrite H24 in H16. apply H9 in H18. contradiction.
        - pose proof H23 as Hb. apply AxiomII in Hb as [H26[H27[]]].
          assert (m ⊂ m /\ m ≠ 0) as []. { split; auto. }
          apply H29 in H30 as [m0]; auto. clear H31.
          assert (m = PlusOne m0).
          { apply MKT133; auto. apply AxiomII; auto. }
          assert (m0 ∈ ω).
          { destruct H30. pose proof MKT138. apply AxiomII in H33
            as [H33[]]. apply H35 in H23. apply H23; auto. }
          assert (m = m0 + 1).
          { rewrite H7,Plus_Property2_a,Plus_Property1_a; auto. }
          rewrite H33,Mult_Distribution in H24; auto.
          assert ((2 · m0) ∈ ω). { apply ω_Mult_in_ω; auto. }
          replace (2 · 1) with (1 + 1) in H24.
          rewrite H19,<-Plus_Association in H24; auto.
          assert (((2 · m0) + 1) ∈ ω). { apply ω_Plus_in_ω; auto. }
          rewrite Plus_Commutation,(Plus_Commutation _ 1) in H24;
          auto. apply Plus_Cancellation in H24; auto.
          apply AxiomII; split. eauto. exists m0; auto.
          rewrite H7. rewrite Plus_Property2_a,Plus_Property1_a;
          try rewrite <-H7; auto.
          rewrite H7,Mult_Property2_a,Mult_Property1_a,
          Plus_Property1_b; try rewrite <-H7; auto. }
      assert (x0 ∈ A).
      { apply AxiomII; split. eauto. apply MKT4'; auto. }
      apply H5 in H24. elim H24. apply AxiomII'; split; auto.
      apply MKT49a; eauto.
Qed.

Fact ω_Setminus_ω_E : ω ~ ω_E = ω_O.
Proof.
  apply AxiomI; split; intros.
  - apply MKT4' in H as []. rewrite <-ω_E_Union_ω_O in H.
    apply MKT4 in H as []; auto. apply AxiomII in H0 as [].
    contradiction.
  - destruct ω_O_properSubset_ω. apply MKT4'; split.
    apply H0; auto. apply AxiomII; split; eauto. intro.
    pose proof ω_E_Intersection_ω_O.
    assert (z ∈ 0). { rewrite <-H3. apply MKT4'; auto. }
    pose proof (@ MKT16 z); auto.
Qed.

Fact ω_Setminus_ω_O : ω ~ ω_O = ω_E.
Proof.
  apply AxiomI; split; intros.
  - apply MKT4' in H as []. rewrite <-ω_E_Union_ω_O in H.
    apply MKT4 in H as []; auto. apply AxiomII in H0 as [].
    contradiction.
  - destruct ω_E_properSubset_ω. apply MKT4'; split.
    apply H0; auto. apply AxiomII; split; eauto. intro.
    pose proof ω_E_Intersection_ω_O.
    assert (z ∈ 0). { rewrite <-H3. apply MKT4'; auto. }
    pose proof (@ MKT16 z); auto.
Qed.

Close Scope ω_scope.
