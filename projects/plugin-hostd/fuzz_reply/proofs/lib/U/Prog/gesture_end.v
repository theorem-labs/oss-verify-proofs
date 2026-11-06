From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import strlen_c send_line_c gesture_end_c.
Import ListNotations.
Open Scope Z_scope.

Lemma off_nz : forall cl br n, n <> 0 -> send_off cl br n = (cl <? 0) || (br =? 1).
Proof. intros cl br n Hn. unfold send_off. rewrite (proj2 (Z.eqb_neq n 0) Hn). apply orb_false_r. Qed.

Lemma live_nz : forall cl br dd n, n <> 0 -> send_live cl br dd n = negb ((cl <? 0) || (br =? 1)) && (dd =? 0).
Proof. intros cl br dd n Hn. unfold send_live. rewrite (off_nz cl br n Hn). reflexivity. Qed.

Lemma bytes_at_trunc : forall m A (s t : list byte) n,
  bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A (s ++ firstn n t).
Proof.
  intros m A s t n H. apply bytes_at_app in H. destruct H as [H1 H2]. apply bytes_at_app. split; [exact H1|].
  rewrite <- (firstn_skipn n t) in H2. apply bytes_at_app in H2. exact (proj1 H2).
Qed.

Lemma bytes_at_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma bytes_at_nul : forall m A (s t : list byte) (b : byte), bytes_at rsegs m A (s ++ b :: t) ->
  bytes_at rsegs m (A + Z.of_nat (length s)) [b].
Proof.
  intros m A s t b H. apply bytes_at_app in H. destruct H as [_ H].
  change (b :: t) with ([b] ++ t) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma rw_cells_at : forall m A B cs, rw_cells rsegs m A cs -> A = B -> rw_cells rsegs m B cs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_CB_eq : forall m A n n' bs bs', rw_cells rsegs m A [CB n bs] -> n = n' -> bs = bs' ->
  rw_cells rsegs m A [CB n' bs'].
Proof. intros; subst; assumption. Qed.

Lemma end5_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 66387 END5.
Proof.
  intros m MI.
  pose proof (ro_cells_image rsegs m 66387 END5 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Theorem gesture_end_nogrow_holds : strlen_contract -> send_line_nogrow_contract -> gesture_end_nogrow_contract.
Proof.
  intros SLEN SL.
  unfold send_line_nogrow_contract, SEND_LINE, SEND_LINE_FRAME, G_CLIENT, G_RELAY_LO, G_BROKEN, G_DEAD, G_EINTR,
    G_OUTV, G_RELAY_HI, ERRNO_OFF in SL.
  cbv zeta in SL.
  unfold gesture_end_nogrow_contract, GESTURE_END, GESTURE_END_FRAME, END5_ADDR, SEND_LINE_FRAME, G_CLIENT,
    G_RELAY_LO, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, G_RELAY_HI, ERRNO_OFF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    x slack junk cl br dd ei mx nout cap out ev.
  cbv zeta.
  intros ST LO HE1 HE2 ERRM HA0 HXL HLV MI HX NZ PAD XL1 SEPR SEPE SEPS Hcl Hbr Hdd Hei CCL CBR CDD CEI COUT CERR HOUT.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (bv_unsigned_in_range 64 nout) as RNO. unfold bv_modulus in RNO. cbn in RNO.
  pose proof (bv_unsigned_in_range 64 cap) as RCA. unfold bv_modulus in RCA. cbn in RCA.
  pose proof (bv_unsigned_in_range 64 out) as ROU. unfold bv_modulus in ROU. cbn in ROU.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (- (bv_unsigned a0 + Z.of_nat (length x) + 1)) 8 ltac:(lia)) as R8.
  remember (Z.to_nat ((- (bv_unsigned a0 + Z.of_nat (length x) + 1)) mod 8)) as k eqn:Ek.
  assert (KZ : Z.of_nat k = (- (bv_unsigned a0 + Z.of_nat (length x) + 1)) mod 8) by (rewrite Ek; apply Z2Nat.id; lia).
  clear Ek.
  assert (HS : bytes_at rsegs m (bv_unsigned a0) (x ++ Z_to_bv 8 0 :: firstn k slack)).
  { replace (x ++ Z_to_bv 8 0 :: firstn k slack) with ((x ++ [Z_to_bv 8 0]) ++ firstn k slack)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_trunc. rewrite <- app_assoc. exact HX. }
  assert (KL : length (firstn k slack) = k) by (apply firstn_length_le; lia).
  clear HX.
  assert (XL0 : Z.of_nat (length x) + 5 <> 0) by lia.
  rewrite !(off_nz _ _ _ XL0), !(live_nz _ _ _ _ XL0).
  rewrite (live_nz _ _ _ _ XL0) in HOUT, HLV.
  destruct (negb ((cl <? 0) || (br =? 1)) && (dd =? 0)) eqn:LV.
  - assert (cl = 3 /\ br = 0 /\ dd = 0) as (-> & -> & ->)
      by (destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->]; vm_compute in LV; first [discriminate | lia]).
    specialize (HOUT LV). destruct HOUT as (HO1 & HO2 & HO3 & HO4 & HO5 & HO6).
    specialize (HLV LV). destruct HLV as [HLV1 HLV2].
    change ((3 <? 0) || (0 =? 1)) with false. change (0 =? 1) with false. cbv beta iota.
    apply (rw_cells_split_CB rsegs m _ [] _ junk [] [length x; 5%nat]) in HO1; [| cbn [sum_nat]; lia].
    cbn [mk_CB_cells app] in HO1.
    destruct (rw_cells_cut _ _ [_] [_] HO1) as [Q1 Q2]. clear HO1. cbn [cells_size csize] in Q2.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160);
      (0x318a4, 0x318a5); (0x318b0, 0x318b1); (0x318e0, 0x318e8);
      (bv_unsigned out + bv_unsigned nout, bv_unsigned out + bv_unsigned nout + (Z.of_nat (length x) + 5))] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    step. step. step. step. step.
    call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x (firstn k slack)).
    1: eassumption.
    1: exact NZ.
    1: rewrite KL; lia.
    1: assumption.
    cbv delta [mkR].
    pose proof (bytes_at_nul _ _ _ _ _ HS) as Z0.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo x (firstn (length x) junk) 3 0 0 ei mx nout cap out ev)
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        rewrite Nat2Z.id in PO;
        rewrite (off_nz 3 0 (Z.of_nat (length x))) in PO by lia;
        rewrite (live_nz 3 0 0 (Z.of_nat (length x))) in PO by lia;
        try change ((3 <? 0) || (0 =? 1)) with false in PO;
        try change (0 =? 1) with false in PO;
        try change (negb false && (0 =? 0)) with true in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-25: rewrite ?unsigned_lit by lia.
    8: intros _; split; lia.
    1-23: first [ eassumption | lia | (left; reflexivity) | (right; reflexivity)
                | (eapply bytes_at_pre; eassumption) ].
    1: intros _; rewrite Nat2Z.id; split; [exact Q1 | lia].
    match goal with H : true = true -> _ |- _ => specialize (H eq_refl) end.
    step. step. step. step. step. step. step.
    release_frame FR MI (bv_unsigned sp).
    pose proof (end5_at _ PC) as E5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo END5 (firstn 5 (skipn (length x) junk)) 3 0 0 0 mx
                 (Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length x))) cap out
                 (if ei =? 1 then Z_to_bv 64 EINTR_V else ev))
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        try change (send_off 3 0 5) with false in PO;
        try change (send_live 3 0 0 5) with true in PO;
        try change (0 =? 1) with false in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-25: rewrite ?unsigned_lit by lia.
    8: intros _; split; lia.
    1-23: first [ eassumption | reflexivity | lia | (left; reflexivity) | (right; reflexivity) ].
    1: intros _; split; [eapply rw_cells_at; [exact Q2 | lia] | lia].
    match goal with H : true = true -> _ |- _ => specialize (H eq_refl) end.
    finish.
    1: apply bytes_at_app; split; assumption.
    1: rewrite Z.add_assoc; assumption.
    1: intros _;
       match goal with
       | P1 : rw_cells _ ?mm ?A [CB (length x) x], P2 : rw_cells _ ?mm _ [CB _ END5] |- _ =>
           pose proof (rw_cells_merge rsegs mm A [] [CB (length x) x; CB 5 END5] []
                         (rw_cells_join _ _ _ [CB (length x) x] [CB 5 END5] P1 P2
                            ltac:(cbn [cells_size csize]; lia))) as P;
           cbn [app] in P;
           eapply rw_cells_CB_eq;
           [ exact P | cbn [cells_size csize]; lia | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity ]
       end.
  - cbv beta iota. clear HOUT HLV.
    assert (OFF2 : (cl <? 0) || ((if (cl <? 0) || (br =? 1) then br else dd) =? 1) = true)
      by (destruct Hcl as [-> | ->], Hbr as [-> | ->], Hdd as [-> | ->]; vm_compute in LV |- *;
          first [reflexivity | discriminate LV]).
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160);
      (0x318a4, 0x318a5); (0x318b0, 0x318b1); (0x318e0, 0x318e8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    step. step. step. step. step.
    call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x (firstn k slack)).
    1: eassumption.
    1: exact NZ.
    1: rewrite KL; lia.
    1: assumption.
    cbv delta [mkR].
    pose proof (bytes_at_nul _ _ _ _ _ HS) as Z0.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo x junk cl br dd ei mx nout cap out ev)
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        rewrite (off_nz cl br (Z.of_nat (length x))) in PO by lia;
        rewrite (live_nz cl br dd (Z.of_nat (length x))) in PO by lia;
        rewrite LV in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-25: rewrite ?unsigned_lit by lia.
    8: rewrite (live_nz cl br dd (Z.of_nat (length x))) by lia; rewrite LV; intros H; discriminate H.
    1-23: first [ eassumption | lia | (eapply bytes_at_pre; eassumption) ].
    1: rewrite (live_nz cl br dd (Z.of_nat (length x))) by lia; rewrite LV; intros H; discriminate H.
    step. step. step. step. step. step. step.
    release_frame FR MI (bv_unsigned sp).
    pose proof (end5_at _ PC) as E5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo END5 junk cl (if (cl <? 0) || (br =? 1) then br else dd) dd
                 (if (cl <? 0) || (br =? 1) then ei else 0) mx nout cap out
                 (if (cl <? 0) || (br =? 1) then ev
                  else if dd =? 1 then Z_to_bv 64 EPIPE_V else if ei =? 1 then Z_to_bv 64 EINTR_V else ev))
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        rewrite (off_nz cl (if (cl <? 0) || (br =? 1) then br else dd) 5) in PO by lia;
        rewrite (live_nz cl (if (cl <? 0) || (br =? 1) then br else dd) dd 5) in PO by lia;
        rewrite OFF2 in PO;
        try change (negb true && (dd =? 0)) with false in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-25: rewrite ?unsigned_lit by lia.
    8: rewrite (live_nz cl (if (cl <? 0) || (br =? 1) then br else dd) dd 5) by lia; rewrite OFF2;
       intros H; cbv in H; discriminate H.
    1-23: first [ eassumption | reflexivity | lia
                | (destruct ((cl <? 0) || (br =? 1)); first [ assumption | (left; reflexivity) ]) ].
    1: rewrite (live_nz cl (if (cl <? 0) || (br =? 1) then br else dd) dd 5) by lia; rewrite OFF2;
       intros H; cbv in H; discriminate H.
    finish.
    1: apply bytes_at_app; split; assumption.
    1: intros H; discriminate H.
Qed.
