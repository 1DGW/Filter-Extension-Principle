(***********************************************************************)
(*   This is part of infinite set, it is distributed under the terms   *)
(*         of the GNU Lesser General Public License version 3          *)
(*                (see file LICENSE for more details)                  *)
(*                                                                     *)
(*                       Copyright 2022-2025                           *)
(*                    Guowei Dou and Wensheng Yu                       *)
(***********************************************************************)

(** infinite_set *)

Require Export alge_operation.

(* 关于无限集的补充性质 *)

Proposition Inf_P1 : P[ω] = ω.
Proof.
  pose proof MKT165. apply MKT156 in H; tauto.
Qed.

Proposition Inf_P2 : P[Φ] = Φ.
Proof.
  apply MKT156. destruct MKT135. apply MKT164; auto.
Qed.

Hint Rewrite Inf_P1 Inf_P2 : inf.

Proposition Inf_P3 : ∀ A, ~ Finite A <-> ω ∈ P[A] \/ ω = P[A].
Proof.
  split; intros.
  - TF (Ensemble A).
    + assert (P[A] ∈ R).
      { apply Property_PClass,AxiomII in H0 as [_[]]; auto. }
      New MKT138. apply AxiomII in H1 as [_], H2 as [_].
      apply (@ MKT110 ω) in H1 as [H1|[]]; auto. contradiction.
    + assert (A ∉ dom(P)).
      { rewrite MKT152b. intro. apply H0,MKT19; auto. }
      apply MKT69a in H1. rewrite H1. left. New MKT138. apply MKT19; eauto.
  - intro. unfold Finite in H0. destruct H.
    apply (MKT102 ω P[A]); auto. rewrite H in H0.
    apply (MKT101 P[A]); auto.
Qed.

Proposition Inf_P4 : ∀ A B, Finite B -> A ≈ B -> Finite A.
Proof.
  intros. New H. apply Property_Finite in H1.
  New H0. apply eqvp in H2; auto. apply MKT154 in H0; auto.
  unfold Finite. rewrite H0; auto.
Qed.

Proposition Inf_P5 : ∀ A B, ~ Finite B -> A ≈ B -> ~ Finite A.
Proof.
  intros. intro. apply MKT146,Inf_P4 in H0; auto.
Qed.

Lemma Inf_P6_Lemma : ∀ f A, Function1_1 f -> Function1_1 (f|(A)).
Proof.
  intros f A []. split. apply MKT126a; auto.
  split; unfold Relation; intros.
  apply AxiomII in H1 as [_[x[y[]]]]; eauto.
  apply AxiomII' in H1 as [], H2 as [].
  apply MKT4' in H3 as [H3 _], H4 as [H4 _].
  assert ([x,y] ∈ f⁻¹ /\ [x,z] ∈ f⁻¹) as [].
  { split; apply AxiomII'; split; auto. }
  destruct H0. apply (H7 x); auto.
Qed.

Proposition Inf_P6 : ∀ A, A ≈ ω
  -> ∃ A1 A2, Ensemble A1 /\ Ensemble A2 /\ A1 ≈ ω /\ A2 ≈ ω
    /\ A1 ∪ A2 = A /\ A1 ∩ A2 = Φ.
Proof.
  intros. apply MKT146 in H as [f[[][]]].
  New ω_E_Equivalent_ω. New ω_O_Equivalent_ω.
  New ω_E_Union_ω_O. New ω_E_Intersection_ω_O.
  destruct ω_E_properSubset_ω. destruct ω_O_properSubset_ω.
  exists ran(f|(ω_E)),ran(f|(ω_O)).
  assert (Function1_1 (f|(ω_E)) /\ Function1_1 (f|(ω_O))) as [].
  { split; apply Inf_P6_Lemma; split; auto. }
  assert (dom(f|(ω_E)) = ω_E /\ dom(f|(ω_O)) = ω_O) as [].
  { split; rewrite MKT126b; auto; rewrite H1; apply MKT30; auto. }
  assert (ran(f|(ω_E)) ≈ dom(f|(ω_E)) /\ ran(f|(ω_O)) ≈ dom(f|(ω_O))) as [].
  { split; apply MKT146; [exists (f|(ω_E))|exists (f|(ω_O))]; auto. }
  rewrite H13 in H15. rewrite H14 in H16.
  split; [|split]; [apply eqvp in H15|apply eqvp in H16| ]; auto;
  [apply ω_E_is_Set|apply ω_O_is_Set| ].
  split; [|split]; try eapply MKT147; eauto. destruct H11,H12.
  split; apply AxiomI; split; intros; [ | | |elim (@ MKT16 z); auto].
  - apply MKT4 in H19 as []; apply Einr in H19 as [x[]]; auto;
    [rewrite H13 in H19|rewrite H14 in H19]; rewrite MKT126c in H20;
    try rewrite H13; try rewrite H14; auto;
    [apply H7 in H19|apply H9 in H19]; rewrite <-H1 in H19;
    apply Property_Value,Property_ran in H19; auto; rewrite H20,<-H2; auto.
  - rewrite <-H2 in H19. apply Einr in H19 as [x[]]; auto.
    rewrite H1,<-H5 in H19. apply MKT4 in H19 as [];
    pose proof H19 as H19a; [rewrite <-H13 in H19|rewrite <-H14 in H19];
    apply Property_Value in H19; auto; rewrite MKT126c,<-H20 in H19;
    try rewrite H13; try rewrite H14; auto; apply Property_ran in H19;
    apply MKT4; auto.
  - apply MKT4' in H19 as []. apply Einr in H19 as [x1[]], H20 as [x2[]]; auto.
    rewrite MKT126c in H21,H22; auto. rewrite H21 in H22.
    rewrite H13 in H19. rewrite H14 in H20. apply f11inj in H22;
    try rewrite H1; auto. rewrite H22 in H19. elim (@ MKT16 x2).
    rewrite <-H6. apply MKT4'; auto.
Qed.

Lemma Inf_P7_Lemma : ∀ m A, m ∈ ω -> P[A] = PlusOne m
  -> ∃ B b, Ensemble B /\ Ensemble b /\ P[B] = m /\ b ∉ B /\ A = B ∪ [b].
Proof.
  intros. assert ((PlusOne m) ∈ ω). { apply MKT134,H. }
  assert (Finite A). { rewrite <-H0 in H1; auto. }
  assert (Ensemble A). { apply Property_Finite,H2. }
  assert (A <> Φ).
  { intro. assert (P[Φ] = Φ). { apply MKT156,MKT164; auto. }
    rewrite H4,H5 in H0. destruct MKT135. elim (H7 m); auto. }
  assert (A ≈ PlusOne m).
  { apply MKT154; try split; eauto. rewrite H0.
    symmetry. apply MKT156,MKT164,H1. }
  apply NEexE in H4 as []. set (B := A ~ [x]).
  assert (x ∉ B).
  { intro. apply MKT4' in H6 as []. apply AxiomII
    in H7 as []. elim H8. apply MKT41; auto. }
  assert (A = B ∪ [x]).
  { apply AxiomI; split; intros.
    - apply MKT4. destruct (classic (z = x)).
      + right. apply MKT41; eauto.
      + left. apply MKT4'; split; auto. apply AxiomII; split;
        eauto. intro. apply MKT41 in H9; eauto.
    - apply MKT4 in H7 as []. apply MKT4' in H7; tauto.
      apply MKT41 in H7; eauto. rewrite H7; auto. }
  assert (P[B] = m).
  { replace m with (P[m]); try apply MKT156,MKT164,H.
    apply MKT154; try split; eauto.
    apply (MKT33 A); auto. unfold Included; intros.
    rewrite H7. apply MKT4; auto. destruct H5 as [f[[][]]].
    destruct (classic (f[x] = m)).
    - set (f1 := f ~ [[x,f[x]]]). exists f1.
      assert (Function1_1 f1).
      { repeat split; unfold Relation; intros.
        - apply MKT4' in H12 as []. rewrite MKT70 in H12; auto.
          apply AxiomII in H12 as [_[a[b[]]]]; eauto.
        - apply MKT4' in H12 as []. apply MKT4' in H13 as [].
          destruct H5. apply (H16 x0); auto.
        - apply AxiomII in H12 as [_[a[b[]]]]; eauto.
        - apply AxiomII' in H12 as []. apply AxiomII' in H13 as [].
          apply MKT4' in H14 as []. apply MKT4' in H15 as [].
          destruct H8. apply (H18 x0); apply AxiomII'; auto. }
      split; auto. destruct H12. split; apply AxiomI; split; intros.
      + apply AxiomII in H14 as [H14[]]. apply MKT4' in H15 as [].
        pose proof H15. apply Property_dom in H15.
        rewrite H9 in H15. apply AxiomII in H16 as [].
        apply MKT4'; split; auto. apply AxiomII; split; auto. intro.
        apply MKT41 in H19; eauto. elim H18. rewrite <-H9 in H4.
        apply Property_Value in H4; auto. apply MKT41; eauto.
        apply MKT49b in H16 as []. apply MKT55; auto. split; auto.
        destruct H5. apply (H21 x); auto. rewrite <-H19; auto.
      + apply AxiomII; split; eauto.
        assert (z ∈ A). { rewrite H7. apply MKT4; auto. }
        assert (z <> x). { intro. rewrite H16 in H14; auto. }
        exists f[z]. apply MKT4'; split.
        apply Property_Value; auto. rewrite H9; auto.
        rewrite <-H9 in H15. apply Property_Value in H15; auto.
        apply AxiomII; split; eauto. intro. rewrite <-H9 in H4.
        apply Property_Value in H4; auto. apply MKT41 in H17; eauto.
        assert (Ensemble ([z,f[z]])); eauto.
        apply MKT49b in H18 as []. apply MKT55 in H17 as []; auto.
      + apply AxiomII in H14 as [H14[]]. apply MKT4' in H15 as [].
        pose proof H15. apply Property_ran in H15.
        rewrite H10 in H15. apply MKT4 in H15 as []; auto.
        apply MKT41 in H15; eauto.
        apply AxiomII in H16 as []. elim H18. rewrite <-H9 in H4.
        apply Property_Value in H4; auto. apply MKT41; eauto.
        rewrite H15,<-H11. rewrite H11,<-H15. apply MKT55; auto.
        apply MKT49b in H16; tauto. split; auto. pose proof H15.
        rewrite H15,<-H11 in H17. destruct H8.
        apply (H20 f[x]); apply AxiomII'; split; auto;
        rewrite H11,<-H15; apply MKT49a; auto.
        apply MKT49b in H16; tauto. apply Property_dom in H4; eauto.
      + apply AxiomII; split; eauto.
        assert (z ∈ ran(f)). { rewrite H10. apply MKT4; auto. }
        apply AxiomII in H15 as [H15[]]. exists x0.
        apply MKT4'; split; auto. apply AxiomII; split; eauto.
        intro. pose proof H4. rewrite <-H9 in H18.
        apply Property_Value in H18; auto. apply MKT41 in H17; eauto.
        apply MKT55 in H17 as []; eauto. rewrite H19,H11 in H14.
        elim (MKT101 m); auto. assert (Ensemble ([x0,z])); eauto.
        apply MKT49b in H20; tauto.
    - set (f1 := ((f ~ [[x,f[x]]]) ~ [[f⁻¹[m],m]])
         ∪ [[f⁻¹[m],f[x]]]).
      exists f1. assert (Function1_1 f1).
      { pose proof H4. rewrite <-H9 in H12. apply Property_Value,
        Property_ran in H12; auto. assert (m ∈ ran(f)).
        { rewrite H10. apply MKT4. right. apply MKT41; eauto. }
        rewrite reqdi in H13. apply Property_Value,Property_ran
        in H13; auto. repeat split; unfold Relation; intros.
        - apply MKT4 in H14 as []. repeat apply MKT4' in H14 as [].
          rewrite MKT70 in H14; auto. apply AxiomII in H14 as
          [_[x0[y0[]]]]; eauto. apply MKT41 in H14; eauto.
          apply MKT49a; eauto.
        - apply MKT4 in H14 as []; apply MKT4 in H15 as [];
          repeat apply MKT4' in H14 as []; repeat apply MKT4'
          in H15 as [].
          + destruct H5. apply (H20 x0); auto.
          + apply AxiomII in H16 as []. elim H18. apply MKT41.
            apply MKT49a; eauto. apply MKT49b in H16 as [].
            apply MKT55; auto. pose proof H15.
            apply AxiomII in H15 as [H15 _].
            apply MKT41 in H20; try (apply MKT49a; eauto).
            apply MKT49b in H15 as []. apply MKT55 in H20 as [];
            auto. split; auto. rewrite MKT70 in H14; auto.
            apply AxiomII' in H14 as []. rewrite H23,H20,f11vi; auto.
            rewrite H10. apply MKT4; right; apply MKT41; eauto.
          + pose proof H14. apply AxiomII in H14 as [H14 _].
            apply MKT41 in H18; try (apply MKT49a; eauto).
            apply MKT49b in H14 as [].
            apply MKT55 in H18 as []; auto.
            apply AxiomII in H16 as []. elim H21. apply MKT41.
            apply MKT49a; eauto. apply MKT55; auto.
            assert (Ensemble ([x0,z])); eauto.
            apply MKT49b in H22; tauto. split; auto.
            rewrite MKT70 in H15; auto. apply AxiomII' in H15 as [].
            rewrite H22,H18,f11vi; auto. rewrite H10.
            apply MKT4; right; apply MKT41; eauto.
          + pose proof H14; pose proof H15.
            apply AxiomII in H16 as [H16 _].
            apply AxiomII in H17 as [H17 _].
            apply MKT41 in H14; try (apply MKT49a; eauto).
            apply MKT41 in H15; try (apply MKT49a; eauto).
            apply MKT49b in H16 as []; apply MKT49b in H17 as [].
            apply MKT55 in H14; apply MKT55 in H15; auto.
            destruct H14,H15. rewrite H20,H21; auto.
        - apply AxiomII in H14 as [_[x0[y0[]]]]; eauto.
        - apply AxiomII' in H14 as []; apply AxiomII' in H15 as [].
          apply MKT4 in H16 as []; apply MKT4 in H17 as [];
          repeat apply MKT4' in H16 as [];
          repeat apply MKT4' in H17 as [].
          + assert ([x0,y] ∈ f⁻¹ /\ [x0,z] ∈ f⁻¹) as [].
            { split; apply AxiomII'; auto. }
            destruct H8. apply (H24 x0); auto.
          + apply MKT41 in H17; try (apply MKT49a; eauto).
            apply MKT49b in H15 as []. apply MKT55 in H17 as [];
            auto. pose proof H16. pose proof H4.
            apply Property_dom in H22. rewrite <-H9 in H23.
            rewrite MKT70 in H16; auto. apply AxiomII' in H16 as [].
            assert (y = x).
            { rewrite <-(f11iv f),<-(f11iv f y),<-H24,<-H21; auto. }
            apply AxiomII in H19 as []. elim H26. apply MKT41.
            apply MKT49a; eauto. apply MKT55; eauto.
          + apply MKT41 in H16; try (apply MKT49a; eauto).
            apply MKT49b in H14 as [].
            apply MKT55 in H16 as []; auto. pose proof H17.
            apply Property_dom in H22. rewrite MKT70 in H17; auto.
            apply AxiomII' in H17 as [].
            assert (x = z).
            { rewrite <-(f11iv f),<-(f11iv f x),<-H21,<-H23; auto.
              rewrite H9; auto. }
            apply AxiomII in H19 as []. elim H25. apply MKT41.
            apply MKT49a; eauto. apply MKT55; eauto.
          + apply MKT41,MKT55 in H16 as [];
            apply MKT41,MKT55 in H17 as [];
            try (apply MKT49a; eauto); apply MKT49b in H14 as [];
            apply MKT49b in H15 as []; auto. rewrite H16,H17; auto. }
      split; auto. destruct H12.
      assert (m ∈ ran(f)).
      { rewrite H10. apply MKT4; right; apply MKT41; eauto. }
      assert ((f⁻¹)[m] ∈ dom(f)).
      { rewrite reqdi in H14. apply Property_Value,Property_ran
        in H14; auto. rewrite <-deqri in H14; auto. }
      assert (x ∈ dom(f)). { rewrite H9; auto. }
      assert (f[x] ∈ ran(f)).
      { apply Property_Value,Property_ran in H16; auto. }
      split; apply AxiomI; split; intros.
      + apply AxiomII in H18 as [H18[y]]. apply MKT4 in H19 as [].
        * repeat apply MKT4' in H19 as []. apply MKT4'; split.
          apply Property_dom in H19. rewrite <-H9; auto.
          apply AxiomII; split; auto. intro.
          apply MKT41 in H22; eauto. apply AxiomII in H21 as [].
          elim H23. apply MKT41; try (apply MKT49a; eauto).
          apply MKT49b in H21 as []. apply MKT55; eauto. split; auto.
          rewrite MKT70 in H19; auto. apply AxiomII' in H19 as [].
          rewrite H25,H22; auto.
        * assert (Ensemble ([z,y])); eauto. apply MKT41 in H19;
          try (apply MKT49a; eauto). apply MKT49b in H20 as [].
          apply MKT55 in H19 as []; auto. apply MKT4'; split.
          rewrite H19,<-H9; auto. apply AxiomII; split; auto.
          intro. apply MKT41 in H23; eauto. rewrite H23 in H19.
          elim H11. rewrite H19,f11vi; auto.
      + apply MKT4' in H18 as []. rewrite <-H9 in H18.
        destruct (classic (z = (f⁻¹)[m])).
        * apply AxiomII; split; eauto. exists (f[x]).
          apply MKT4; right. apply MKT41. apply MKT49a; eauto.
          apply MKT55; eauto.
        * apply AxiomII; split; eauto. exists (f[z]).
          apply MKT4; left. pose proof H18.
          apply Property_Value in H21; auto.
          assert (Ensemble ([z,f[z]])); eauto.
          apply MKT49b in H22 as []. apply MKT4'; split.
          apply MKT4'; split; auto. apply AxiomII; split; eauto.
          intro. apply MKT41 in H24; try (apply MKT49a; eauto).
          apply MKT55 in H24 as []; auto. apply AxiomII in H19 as [].
          elim H26. rewrite <-H24. apply MKT41; auto.
          apply AxiomII; split; eauto. intro. apply MKT41 in H24;
          try (apply MKT49a; eauto). apply MKT55 in H24 as []; auto.
      + apply AxiomII in H18 as [H18[x0]]. apply MKT4 in H19 as [].
        * repeat apply MKT4' in H19 as []. pose proof H19.
          apply Property_ran in H19. rewrite H10 in H19.
          apply MKT4 in H19 as []; auto. apply MKT41 in H19; eauto.
          assert ([z,x0] ∈ f⁻¹).
          { apply AxiomII'; split; auto.
            assert (Ensemble ([x0,z])); eauto.
            apply MKT49b in H23 as []. apply MKT49a; auto. }
          rewrite MKT70 in H23; auto. apply AxiomII' in H23 as [].
          apply AxiomII in H20 as []. elim H25.
          apply MKT41; try (apply MKT49a; eauto).
          apply MKT49b in H20 as []. apply MKT55; auto.
          rewrite <-H19; auto.
        * assert (Ensemble ([x0,z])); eauto.
          apply MKT41 in H19; try (apply MKT49a; eauto).
          apply MKT49b in H20 as []. apply MKT55 in H19 as []; auto.
          rewrite <-H22,H10 in H17. apply MKT4 in H17 as []; auto.
          apply MKT41 in H17; eauto. rewrite H17 in H22.
          elim H11; auto.
      + assert (z ∈ ran(f)). { rewrite H10. apply MKT4; auto. }
        apply AxiomII in H19 as [H19[]]. apply AxiomII; split; auto.
        destruct (classic (z = f[x])).
        * exists ((f⁻¹)[m]). apply MKT4; right. apply MKT41;
          try (apply MKT49a; eauto). apply MKT55; eauto.
        * assert (Ensemble ([x0,z])); eauto.
          apply MKT49b in H22 as []. exists x0. apply MKT4; left.
          apply MKT4'; split. apply MKT4'; split; auto.
          apply AxiomII; split; eauto. intro. apply MKT41 in H24;
          try (apply MKT49a; eauto). apply MKT55 in H24 as []; auto.
          apply AxiomII; split; eauto. intro.
          apply MKT41 in H24; try (apply MKT49a; eauto).
          apply MKT55 in H24 as []; try apply MKT49a; eauto.
          rewrite H25 in H18. elim (MKT101 m); auto. }
  assert (Ensemble B /\ Ensemble x) as [].
  { split; [ |eauto]. apply (MKT33 A); auto.
    unfold Included; intros. rewrite H7. apply MKT4; auto. }
  exists B,x. auto.
Qed.

Proposition Inf_P7 : ∀ A B, P[A] = ω -> P[B] ≼ ω -> P[A ∪ B] = ω.
Proof.
  intros. destruct H0.
  - set (p := fun n => (∀ B0, P[B0] = n -> P[A ∪ B0] = ω)).
    assert (∀ n, n ∈ ω -> p n).
    { apply Mathematical_Induction; unfold p; intros.
      apply carE in H1. rewrite H1,MKT6,MKT17; auto. pose proof H3.
      apply Inf_P7_Lemma in H4 as [B1[b[H4[H5[H6[]]]]]]; auto.
      destruct (classic (b ∈ A)).
      assert (A ∪ B0 = A ∪ B1).
      { apply AxiomI; split; intros. apply MKT4. apply MKT4 in H10
        as []; auto. rewrite H8 in H10. apply MKT4 in H10 as []; auto.
        apply MKT41 in H10; auto. rewrite H10; auto. apply MKT4.
        apply MKT4 in H10 as []; auto. right. rewrite H8.
        apply MKT4; auto. }
      rewrite H10. apply H2; auto. rewrite H8,<-MKT7.
      pose proof H6. apply H2 in H10.
      assert (Ensemble (A ∪ B1)).
      { apply MKT19. apply NNPP; intro. rewrite <-MKT152b in H11.
        apply MKT69a in H11. pose proof MKT138.
        rewrite <-H10,H11 in H12. elim MKT39; eauto. }
      pose proof MKT165. apply MKT156 in H12 as [].
      rewrite <-H13 in H10. symmetry in H10.
      apply MKT154 in H10; auto. destruct H10 as [f[[][]]].
      assert ((PlusOne ω) ≈ (A ∪ B1) ∪ [b]).
      { exists (f ∪ [[ω,b]]). split. split. apply fupf; auto.
        rewrite H15. apply MKT101. rewrite uiv,siv; auto.
        apply fupf; auto. rewrite <-reqdi,H16. intro.
        apply MKT4 in H17 as []; auto.
        split; apply AxiomI; split; intros.
        - apply AxiomII in H17 as [H17[x]]. apply MKT4 in H18 as [].
          apply Property_dom in H18. rewrite H15 in H18.
          apply MKT4; auto. pose proof H18. apply MKT41 in H19; auto.
          apply MKT55 in H19 as []; auto. apply MKT4; right.
          apply MKT41; auto. assert (Ensemble ([z,x])); eauto.
          apply MKT49b in H21; tauto.
        - apply AxiomII; split; eauto. apply MKT4 in H17 as [].
          rewrite <-H15 in H17. apply Property_Value in H17; auto.
          exists f[z]. apply MKT4; auto. pose proof H17.
          apply MKT41 in H18; auto. exists b. apply MKT4; right.
          rewrite H18. apply MKT41; auto.
        - apply AxiomII in H17 as [H17[x]]. apply MKT4 in H18 as [].
          apply Property_ran in H18. rewrite H16 in H18.
          apply MKT4; auto. apply MKT4; right. apply MKT41; auto.
          assert (Ensemble x). { apply Property_dom in H18; eauto. }
          apply MKT41 in H18; auto. apply MKT55 in H18; tauto.
        - apply AxiomII; split; eauto. apply MKT4 in H17 as [].
          rewrite <-H16 in H17. apply AxiomII in H17 as [H17[x]].
          exists x. apply MKT4; auto. apply MKT41 in H17; auto.
          exists ω. apply MKT4; right. rewrite H17.
          apply MKT41; auto. }
      apply MKT154 in H17; try apply AxiomIV; auto.
      assert (P[PlusOne ω] = P[ω]).
      { apply MKT174. apply MKT4'; split. apply MKT138.
        apply AxiomII; split; auto. apply MKT101. }
      rewrite <-H17,H18; auto. }
    apply H1 in H0; auto.
  - pose proof MKT165. apply MKT156 in H1 as [].
    assert (Ensemble A /\ Ensemble B) as [].
    { split; apply MKT19,NNPP; intro;
      rewrite <-MKT152b in H3; apply MKT69a in H3;
      elim MKT39; [rewrite <-H3,H|rewrite <-H3,H0]; auto. }
    assert (ω_E ≈ A /\ ω_O ≈ B) as [[f[[][]]][g[[][]]]].
    { split; apply (MKT147 ω). apply ω_E_Equivalent_ω.
      apply MKT154; auto. rewrite H2; auto. apply ω_O_Equivalent_ω.
      apply MKT154; auto. rewrite H2; auto. }
    assert (Function (f ∪ g) /\ dom(f ∪ g) = ω
      /\ ran(f ∪ g) = A ∪ B) as [H13[]].
    { rewrite <-ω_E_Union_ω_O,undom,H7,H11,unran,H8,H12.
      split; auto. split; unfold Relation; intros.
      apply MKT4 in H13 as []; rewrite MKT70 in H13; auto;
      apply AxiomII in H13 as [_[x[y[]]]]; eauto.
      apply MKT4 in H13 as [], H14 as []. destruct H5.
      apply (H15 x); auto. apply Property_dom in H13,H14.
      rewrite H7 in H13. rewrite H11 in H14. elim (@ MKT16 x).
      rewrite <-ω_E_Intersection_ω_O. apply MKT4'; auto.
      apply Property_dom in H13,H14. rewrite H7 in H14.
      rewrite H11 in H13. elim (@ MKT16 x).
      rewrite <-ω_E_Intersection_ω_O. apply MKT4'; auto.
      destruct H9. apply (H15 x); auto. }
    apply MKT160 in H13; [ |apply AxiomIV; apply MKT75; auto;
    [rewrite H7; apply ω_E_is_Set|rewrite H11; apply ω_O_is_Set]].
    rewrite H14,H15,H2 in H13.
    assert (A ⊂ (A ∪ B)).
    { unfold Included; intros. apply MKT4; auto. }
    apply MKT158 in H16. rewrite H in H16. destruct H13,H16; auto.
    elim (MKT102 ω P[A ∪ B]); auto.
Qed.

Proposition Inf_P8 : ∀ A, ~ Finite A -> Ensemble A
  -> ∃ A1 A2, Ensemble A1 /\ Ensemble A2 /\ ~ Finite A1 /\ ~ Finite A2
    /\ A1 ∪ A2 = A /\ A1 ∩ A2 = Φ.
Proof.
  intros. New H. apply Inf_P3 in H1 as [].
  - New H0. apply MKT153 in H2 as [f[[][]]].
    assert (ω ⊂ P[A]).
    { apply Property_PClass,AxiomII in H0 as [_[]].
      apply AxiomII in H0 as [_[]]; auto. }
    exists ran(f|(P[A] ~ ω)),ran(f|(ω)).
    assert (Ensemble (dom(f))).
    { rewrite H4. apply Property_PClass in H0; eauto. }
    assert (dom(f|(P[A] ~ ω)) = P[A] ~ ω /\ dom(f|(ω)) = ω) as [].
    { split; rewrite MKT126b; auto; rewrite H4; apply MKT30; auto.
      unfold Included; intros. apply MKT4' in H8 as []; auto. }
    split; [ |split]; try apply AxiomV; try apply MKT126a; auto;
    [rewrite H8|rewrite H9| ]; try apply (MKT33 dom(f)); auto;
    try rewrite H4; auto. unfold Included; intros; apply MKT4' in H10; tauto.
    assert (~ Finite (P[A] ~ ω)).
    { intro. New (MKT155 A). New Inf_P1.
      apply (Inf_P7 ω (P[A] ~ ω)) in H12.
      assert (ω ∪ (P[A] ~ ω) = P[A]).
      { apply AxiomI; split; intros. TF (z ∈ ω).
        apply MKT4 in H13 as []; auto. apply MKT4 in H13 as []; auto.
        apply MKT4' in H13; tauto. TF (z ∈ ω); apply MKT4; auto. }
      rewrite H13,H11 in H12. rewrite H12 in H1. apply (MKT101 ω); auto.
      left; auto. }
    assert (~ Finite ω).
    { intro. unfold Finite in H11. elim (MKT101 ω).
      rewrite Inf_P1 in H11; auto. }
    assert (dom(f|(P[A] ~ ω)) ≈ ran(f|(P[A] ~ ω))
      /\ dom(f|(ω)) ≈ ran(f|(ω))) as [].
    { split; [exists (f|(P[A] ~ ω))|exists (f|(ω))];
      split; auto; apply Inf_P6_Lemma; split; auto. }
    apply MKT146 in H12,H13. rewrite H8 in H12. rewrite H9 in H13.
    apply Inf_P5 in H12,H13; auto. split; [ |split]; auto.
    split; apply AxiomI; split; intros; [ | | |elim (@ MKT16 z); auto].
    + apply MKT4 in H14 as []; apply AxiomII in H14 as [H14[]];
      apply MKT4' in H15 as []; rewrite <-H5;
      apply Property_ran in H15; auto.
    + apply MKT4. rewrite <-H5 in H14. apply AxiomII in H14 as [H14[]].
      TF (x ∈ ω). right. apply AxiomII; split; auto. exists x.
      apply MKT4'; split; auto. apply AxiomII'; split; auto.
      apply MKT49a; eauto. left. apply AxiomII; split; auto.
      exists x. apply MKT4'; split; auto. apply AxiomII'; split; eauto.
      split. apply MKT4'; split. apply Property_dom in H15.
      rewrite H4 in H15; auto. apply AxiomII; split; auto.
      assert (Ensemble ([x,z])). eauto. apply MKT49b in H17; tauto.
      apply MKT19; auto.
    + apply MKT4' in H14 as []. apply Einr in H14 as [x[]];
      [ |apply MKT126a]; auto. apply Einr in H15 as [y[]];
      [ |apply MKT126a]; auto. rewrite MKT126c in H16,H17; auto.
      rewrite H16 in H17. rewrite MKT126b in H14,H15; auto.
      apply MKT4' in H14 as [], H15 as []. apply f11inj in H17; auto.
      rewrite H17 in H14. apply MKT4' in H14 as [].
      apply AxiomII in H20 as []. elim H21; auto.
  - rewrite <-Inf_P1 in H1. New MKT138. apply MKT154 in H1; eauto.
    apply MKT146,Inf_P6 in H1 as [A1[A2[H1[H3[H4[H5[]]]]]]].
    assert (~ Finite A1 /\ ~ Finite A2) as [].
    { apply MKT154 in H4,H5; eauto. unfold Finite; split; intro;
      [rewrite H4 in H8|rewrite H5 in H8]; rewrite Inf_P1 in H8;
      elim (MKT101 ω); auto. }
    exists A1,A2. auto 6.
Qed.
