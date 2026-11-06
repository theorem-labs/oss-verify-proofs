From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  strlen_c send_line_c relay_event_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_trunc : forall m A (s t : list byte) n,
  bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A (s ++ firstn n t).
Proof.
  intros m A s t n H. apply bytes_at_app in H. destruct H as [H1 H2]. apply bytes_at_app. split; [exact H1|].
  rewrite <- (firstn_skipn n t) in H2. apply bytes_at_app in H2. exact (proj1 H2).
Qed.

Lemma bytes_at_pre : forall m A (s t : list byte), bytes_at rsegs m A (s ++ t) -> bytes_at rsegs m A s.
Proof. intros m A s t H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma bytes_at_str : forall m A (s t : list byte) (b : byte), bytes_at rsegs m A (s ++ b :: t) ->
  bytes_at rsegs m A (s ++ [b]).
Proof. intros m A s t b H. apply (bytes_at_pre _ _ _ t). rewrite <- app_assoc. exact H. Qed.

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

Theorem relay_event_nogrow_holds : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract -> strlen_contract ->
  send_line_nogrow_contract -> relay_event_nogrow_contract.
Proof.
  intros SPL SPU SLEN SL.
  unfold send_line_nogrow_contract, SEND_LINE, SEND_LINE_FRAME, G_CLIENT, G_RELAY_LO, G_BROKEN, G_DEAD, G_EINTR,
    G_OUTV, G_RELAY_HI, ERRNO_OFF in SL.
  cbv zeta in SL.
  unfold relay_event_nogrow_contract, RELAY_EVENT, RELAY_EVENT_FRAME, G_LOCK, G_LOCK_HI, SEND_LINE_FRAME, G_CLIENT,
    G_RELAY_LO, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, G_RELAY_HI, ERRNO_OFF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    e slack junk cl br dd ei mx nout cap out ev.
  cbv zeta.
  intros ST LO HE1 HE2 MI HX NZ PAD SEPR SEPE SEPS GL Hcl Hbr Hdd Hei CCL CBR CDD CEI COUT CERR HOUT.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. rewrite length_app in XB. cbn [length] in XB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (bv_unsigned_in_range 64 nout) as RNO. unfold bv_modulus in RNO. cbn in RNO.
  pose proof (bv_unsigned_in_range 64 cap) as RCA. unfold bv_modulus in RCA. cbn in RCA.
  pose proof (bv_unsigned_in_range 64 out) as ROU. unfold bv_modulus in ROU. cbn in ROU.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (- (bv_unsigned a0 + Z.of_nat (length e) + 1)) 8 ltac:(lia)) as R8.
  remember (Z.to_nat ((- (bv_unsigned a0 + Z.of_nat (length e) + 1)) mod 8)) as k eqn:Ek.
  assert (KZ : Z.of_nat k = (- (bv_unsigned a0 + Z.of_nat (length e) + 1)) mod 8) by (rewrite Ek; apply Z2Nat.id; lia).
  clear Ek.
  assert (HS : bytes_at rsegs m (bv_unsigned a0) (e ++ Z_to_bv 8 0 :: firstn k slack)).
  { replace (e ++ Z_to_bv 8 0 :: firstn k slack) with ((e ++ [Z_to_bv 8 0]) ++ firstn k slack)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_trunc. rewrite <- app_assoc. exact HX. }
  assert (KL : length (firstn k slack) = k) by (apply firstn_length_le; lia).
  clear HX.
  destruct (rw_cells_cut _ _ [_] [_; _] GL) as [GL0 GL12]. clear GL.
  destruct (rw_cells_cut _ _ [_] [_] GL12) as [GL1 GL2]. clear GL12.
  assert (TB : bytes_at rsegs m 200728 [hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0))]).
  { pose proof (proj2 (proj1 GL0)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    rewrite <- (firstn_skipn 1 (le4 (Z_to_bv 64 0))) in B. exact (bytes_at_pre _ _ _ _ B). }
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (200732, 200736)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  step. step. step. step. step. step. step. step. step.
  call (SPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            200728 (hd (Z_to_bv 8 0) (le4 (Z_to_bv 64 0)))).
  1: reflexivity.
  1: exact TB.
  1: reflexivity.
  1: exact GL1.
  1: assumption.
  cbv delta [mkR].
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 16)] |- _ => rename H into L16 end.
  step. step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e (firstn k slack)).
  1: eassumption.
  1: exact NZ.
  1: rewrite KL; lia.
  1: assumption.
  cbv delta [mkR].
  pose proof (bytes_at_str _ _ _ _ _ HS) as LB.
  step. step. step.
  destruct (send_live cl br dd (Z.of_nat (length e) + 1)) eqn:LV.
  - specialize (HOUT eq_refl). destruct HOUT as (HO1 & HO2 & HO3 & HO4 & HO5 & HO6).
    cbv beta iota.
    match goal with MU0 : munch ?W m ?mm, WM0 : wmono _ m ?mm |- _ =>
      pose proof (rw_cells_transport rsegs W m mm _ _ HO1 MU0 WM0
                    ltac:(cbn [disjoint_from cells_size csize]; lia)) as HO1';
      assert (MU1 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160);
                           (200732, 200736); (200644, 200645); (200656, 200657); (200704, 200712);
                           (bv_unsigned out + bv_unsigned nout,
                            bv_unsigned out + bv_unsigned nout + (Z.of_nat (length e) + 1))] m mm)
        by (eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MU0 HO1
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo (e ++ [Z_to_bv 8 0]) junk cl br dd ei mx nout cap out ev)
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        rewrite LV in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-21: rewrite ?unsigned_lit by lia.
    1-20: first [ eassumption | lia | (rewrite length_app; cbn [length]; lia) ].
    1: intros _; split; [exact HO1' | lia].
    match goal with H : true = true -> _ |- _ => specialize (H eq_refl) end.
    step. step. step. step. step. step.
    match goal with S : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FR S (bv_unsigned sp) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 200728 lo)
      | post_call rsegs mm ]
    end.
    1: reflexivity.
    1: exact (rw_cells_join _ _ _ [_] [_; _] GL0 (rw_cells_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl).
    1: eassumption.
    1: lia.
    1: lia.
    1: assumption.
    finish.
    intros _; assumption.
  - cbv beta iota. clear HOUT.
    match goal with MU0 : munch ?W m ?mm |- _ =>
      assert (MU1 : munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160);
                           (200732, 200736); (200644, 200645); (200656, 200657); (200704, 200712)] m mm)
        by (eapply munch_weaken; [| exact MU0]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MU0
    end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 lo (e ++ [Z_to_bv 8 0]) junk cl br dd ei mx nout cap out ev)
      | intros ms' PO;
        rewrite ?unsigned_lit in PO by lia;
        rewrite LV in PO;
        cbv beta iota in PO;
        cbn [app] in PO;
        revert ms' PO; post_call rsegs mm ]
    end.
    1-21: rewrite ?unsigned_lit by lia.
    1-20: first [ eassumption | lia | (rewrite length_app; cbn [length]; lia) ].
    1: rewrite LV; intros H; discriminate H.
    step. step. step. step. step. step.
    match goal with S : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FR S (bv_unsigned sp) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SPU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 200728 lo)
      | post_call rsegs mm ]
    end.
    1: reflexivity.
    1: exact (rw_cells_join _ _ _ [_] [_; _] GL0 (rw_cells_join _ _ _ [_] [_] L16 GL2 eq_refl) eq_refl).
    1: eassumption.
    1: lia.
    1: lia.
    1: assumption.
    finish.
    intros H; discriminate H.
Qed.
