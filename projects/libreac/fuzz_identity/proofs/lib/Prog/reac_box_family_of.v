From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import bcmp_c reac_box_family_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma famof_memcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> map bv_unsigned l = map bv_unsigned r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model map] in *; try discriminate.
  - injection H as <-. split; [lia| tauto].
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|]. rewrite Hi, E.
      split; [intros ->; reflexivity | intros Hc; injection Hc as Hc; exact Hc].
    + injection H as <-. split; [lia|]. split; [lia | intros Hc; injection Hc as Hc _; contradiction].
Qed.

Lemma famof_firstn1 : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  induction l as [|x l IH]; intros [|k] d H; cbn [length firstn skipn nth] in *; try lia; [reflexivity | apply IH; lia].
Qed.

Lemma famof_sub : forall m A (bs : list byte) k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma famof_bv : forall m A (bs : list byte), bytes_at rsegs m A bs -> A < 2^64 ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 A)) bs.
Proof. intros m A bs H HA. pose proof (bytes_at_bound rsegs m A bs H). rewrite unsigned_lit by lia. exact H. Qed.

Lemma famof_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  apply unsigned_lit. lia.
Qed.

Lemma famof_row1 : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x105dc (map (Z_to_bv 8) FAMOF_HW1).
Proof.
  intros m HI. apply ro_bytes_at; [exact HI | lia | vm_compute; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

Lemma famof_row2 : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x105e8 (map (Z_to_bv 8) FAMOF_HW2).
Proof.
  intros m HI. apply ro_bytes_at; [exact HI | lia | vm_compute; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

Lemma famof_row3 : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x105f4 (map (Z_to_bv 8) FAMOF_HW3).
Proof.
  intros m HI. apply ro_bytes_at; [exact HI | lia | vm_compute; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

Local Ltac famof_bcmp BC HR ROW HV :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply BC;
        [ apply famof_bv; [ exact HR | lia ]
        | apply famof_bv; [ apply ROW; assumption | lia ]
        | exact HV
        | assumption ]
      | post_call segs mm ];
      repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end
  end.

Local Ltac famof_dec :=
  repeat match goal with
  | |- context [list_eq_dec Z.eq_dec ?x ?y] => destruct (list_eq_dec Z.eq_dec x y); try contradiction
  end; try reflexivity.

Local Ltac famof_fam NZ HC E36 Eraw :=
  unfold FAMOF_FAM; rewrite <- E36, <- Eraw; cbv zeta;
  rewrite (proj2 (Z.eqb_neq _ _) NZ), (proj2 (Z.eqb_neq _ _) HC);
  famof_dec.

Local Ltac famof_exit EF MU WM ST :=
  apply evt_done; cbv beta; rewrite EF;
  do 14 eexists; eexists; split; [ reflexivity | ];
  split; [ exact MU | ]; split; [ exact WM | ]; split; [ exact ST | assumption ].

Theorem reac_box_family_of_holds : bcmp_contract -> reac_box_family_of_contract.
Proof.
  intros BC.
  unfold reac_box_family_of_contract, REAC_BOX_FAMILY_OF, REAC_BOX_FAMILY_OF_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo idb
    ST LO HI HA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  pose proof ST as (Slo & Shi & _).
  destruct (Z.eq_dec (bv_unsigned a0) 0) as [Z0|NZ].
  - assert (EA : a0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity).
    subst a0.
    step. if_true. step.
    apply evt_done; cbv beta.
    do 14 eexists; eexists; split; [ reflexivity | ].
    split; [ apply munch_refl | ]; split; [ apply wmono_refl | ]; split; [ exact ST | exact HI ].
  - destruct HA as [HA | (HB & HL & HD)]; [ contradiction | ].
    pose proof (bytes_at_bound rsegs m _ _ HB) as HBb. rewrite HL in HBb. change (Z.of_nat 38) with 38 in HBb.
    assert (R36 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 36)) 1 = Some [nth 36 idb (Z_to_bv 8 0)]).
    { rewrite (bytes_at_read rsegs m (bv_unsigned a0) idb 36 1 HB) by (rewrite ?HL; lia).
      change (Z.to_nat 36) with 36%nat. rewrite (famof_firstn1 idb 36 (Z_to_bv 8 0)) by (rewrite ?HL; lia). reflexivity. }
    assert (HR : bytes_at rsegs m (bv_unsigned a0 + 28) (firstn 8 (skipn 28 idb))).
    { change (bv_unsigned a0 + 28) with (bv_unsigned a0 + Z.of_nat 28). apply famof_sub; [ exact HB | rewrite HL; lia ]. }
    assert (LR : length (firstn 8 (skipn 28 idb)) = 8%nat) by (rewrite length_firstn, length_skipn, HL; reflexivity).
    clear HB.
    remember (firstn 8 (skipn 28 idb)) as raw eqn:Eraw.
    remember (nth 36 idb (Z_to_bv 8 0)) as b36 eqn:E36.
    step. if_false.
    step. step.
    if_cases HC.
    + zify_cond HC. rewrite ?famof_ub in HC.
      assert (EF : FAMOF_FAM (bv_unsigned a0) idb = 0).
      { unfold FAMOF_FAM. rewrite <- E36, HC. destruct (bv_unsigned a0 =? 0); reflexivity. }
      step. step.
      apply evt_done; cbv beta. rewrite EF.
      do 14 eexists; eexists; split; [ reflexivity | ].
      split; [ apply munch_refl | ]; split; [ apply wmono_refl | ]; split; [ exact ST | exact HI ].
    + zify_cond HC. rewrite ?famof_ub in HC.
      clear R36.
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 32%nat ST.
      step. step. step. step. step.
      step. step. step. step. step. step. step. step.
      destruct (memcmp_model_total raw (map (Z_to_bv 8) FAMOF_HW1) 8 ltac:(lia) (Nat.le_refl 8)) as [v1 Hv1].
      destruct (famof_memcmp 8 raw (map (Z_to_bv 8) FAMOF_HW1) v1 LR eq_refl Hv1) as [Rv1 Iv1].
      change (map bv_unsigned (map (Z_to_bv 8) FAMOF_HW1)) with FAMOF_HW1 in Iv1.
      famof_bcmp BC HR famof_row1 Hv1.
      step.
      if_cases HC1; zify_cond HC1; rewrite ?unsigned_lit_wrap in HC1.
      * assert (V1 : v1 = 0) by (clear - HC1 Rv1; Z.div_mod_to_equations; lia).
        apply Iv1 in V1.
        assert (EF : FAMOF_FAM (bv_unsigned a0) idb = 1) by (famof_fam NZ HC E36 Eraw).
        step. step. step. step. step. step. step.
        release_frame FR ST (bv_unsigned sp).
        famof_exit EF MU WM ST.
      * assert (V1 : v1 <> 0) by (clear - HC1 Rv1; Z.div_mod_to_equations; lia).
        assert (M1 : map bv_unsigned raw <> FAMOF_HW1) by (intros E; apply Iv1 in E; lia).
        step. step. step. if_true.
        step. step. step. step.
        destruct (memcmp_model_total raw (map (Z_to_bv 8) FAMOF_HW2) 8 ltac:(lia) (Nat.le_refl 8)) as [v2 Hv2].
        destruct (famof_memcmp 8 raw (map (Z_to_bv 8) FAMOF_HW2) v2 LR eq_refl Hv2) as [Rv2 Iv2].
        change (map bv_unsigned (map (Z_to_bv 8) FAMOF_HW2)) with FAMOF_HW2 in Iv2.
        famof_bcmp BC HR famof_row2 Hv2.
        step.
        if_cases HC2; zify_cond HC2; rewrite ?unsigned_lit_wrap in HC2.
        -- assert (V2 : v2 = 0) by (clear - HC2 Rv2; Z.div_mod_to_equations; lia).
           apply Iv2 in V2.
           assert (EF : FAMOF_FAM (bv_unsigned a0) idb = 2) by (famof_fam NZ HC E36 Eraw).
           step. step. step. step. step. step. step.
           release_frame FR ST (bv_unsigned sp).
           famof_exit EF MU WM ST.
        -- assert (V2 : v2 <> 0) by (clear - HC2 Rv2; Z.div_mod_to_equations; lia).
           assert (M2 : map bv_unsigned raw <> FAMOF_HW2) by (intros E; apply Iv2 in E; lia).
           step. step. step. if_true.
           step. step. step. step.
           destruct (memcmp_model_total raw (map (Z_to_bv 8) FAMOF_HW3) 8 ltac:(lia) (Nat.le_refl 8)) as [v3 Hv3].
           destruct (famof_memcmp 8 raw (map (Z_to_bv 8) FAMOF_HW3) v3 LR eq_refl Hv3) as [Rv3 Iv3].
           change (map bv_unsigned (map (Z_to_bv 8) FAMOF_HW3)) with FAMOF_HW3 in Iv3.
           famof_bcmp BC HR famof_row3 Hv3.
           step.
           if_cases HC3; zify_cond HC3; rewrite ?unsigned_lit_wrap in HC3.
           ++ assert (V3 : v3 = 0) by (clear - HC3 Rv3; Z.div_mod_to_equations; lia).
              apply Iv3 in V3.
              assert (EF : FAMOF_FAM (bv_unsigned a0) idb = 3) by (famof_fam NZ HC E36 Eraw).
              step. step. step. step. step. step. step.
              release_frame FR ST (bv_unsigned sp).
              famof_exit EF MU WM ST.
           ++ assert (V3 : v3 <> 0) by (clear - HC3 Rv3; Z.div_mod_to_equations; lia).
              assert (M3 : map bv_unsigned raw <> FAMOF_HW3) by (intros E; apply Iv3 in E; lia).
              assert (EF : FAMOF_FAM (bv_unsigned a0) idb = 0) by (famof_fam NZ HC E36 Eraw).
              step. step. step. if_false.
              step. step. step. step. step. step. step. step.
              release_frame FR ST (bv_unsigned sp).
              famof_exit EF MU WM ST.
Qed.
