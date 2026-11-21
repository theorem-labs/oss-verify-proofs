(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rstep lem := aflat; eapply RES2_step2; [apply lem | apply lem |]; cbv beta iota.
Ltac rstepr := aflat; eapply RES2_step2; [reflexivity | reflexivity |]; cbv beta iota.
Ltac rfin_run := cbn [RES2]; split; [reflexivity|].

Ltac rlast := unfold us, uc, ur; cbv beta iota delta [w_s w_c w_r wset_s wset_c wset_r]; rfin_run.
Ltac uw0 W5 F0 := apply UW_intro0; unfold fixedtables; sacc; [exact W5 | exact F0 | first [reflexivity | match goal with H : is_mode ?s = _ |- _ => rewrite H; reflexivity end]].
Ltac wmid E W5 F0 := apply WMID_mk; [ieq_close E | uw0 W5 F0].
Ltac notHB HU E W5 F0 := destruct (UW_notHB _ _ _ HU ltac:(rewrite E; first [discriminate | congruence]) ltac:(rewrite E; first [discriminate | congruence])) as [W5 F0].

Ltac lits := repeat (first [ progress change (Z.land 5 4 =? 0) with false | progress change (Z.land 5 2 =? 0) with true
                            | progress change (Z.land 5 1 =? 0) with false | progress change (5 =? 0) with false
                            | progress change (0 =? 0) with true ]); cbn [negb andb orb].
Ltac nrm s1 s2 W5 F0 := unfold fixedtables; sacc; ieq_rw s1 s2; rewrite ?W5, ?F0; lits.

Ltac rlock SF := eapply RES2_bind_lock; [apply SFREE_LOCK; apply SF | | |].

Section Simple.
  Variable iv : ivariant.
  Variable flush : Z.

  Lemma arm_BAD_cong : forall F, arm_cong BAD F arm_BAD.
  Proof.
    intros F s1 s2 c r _ E HQ HU. unfold arm_BAD. apply RES2_sfree; [|exact HQ|exact HU].
    apply SFREE_bind; [apply SFREE_ur; intros; split; reflexivity | intros; apply SFREE_leave].
  Qed.
  Lemma arm_DONE_cong : forall M F, arm_cong M F arm_DONE.
  Proof.
    intros M F s1 s2 c r _ E HQ HU. unfold arm_DONE. apply RES2_sfree; [|exact HQ|exact HU].
    apply SFREE_bind; [apply SFREE_ur; intros; split; reflexivity | intros; apply SFREE_leave].
  Qed.
  Lemma arm_MEM_cong : forall F, arm_cong MEM F arm_MEM.
  Proof. intros F s1 s2 c r _ E HQ HU. unfold arm_MEM. apply RES2_return. apply WMID_mk; assumption. Qed.
  Lemma arm_SYNC_cong : forall F, arm_cong SYNC F arm_SYNC.
  Proof. intros F s1 s2 c r _ E HQ HU. unfold arm_SYNC. apply RES2_return. apply WMID_mk; assumption. Qed.

  Lemma arm_LIT_cong : arm_cong LIT FTrue arm_LIT.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LIT.
    rstep gr_eq. destruct (ir_left r =? 0).
    { apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU]. }
    rstep gs_eq. ieq_rw s1 s2.
    rstep uc_eq. rstep ur_eq. unfold set_mode, us. cbn [w_s w_c w_r wset_s]. rfin_run. wmid E W5 F0.
  Qed.

  Lemma arm_LENGTH_cong : forall M F, M <> HEAD -> M <> BAD -> arm_cong M F arm_LENGTH.
  Proof.
    intros M F NH NB s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. unfold arm_LENGTH.
    rstep gs_eq. ieq_rw s1 s2. rewrite W5, F0. cbn [Z.eqb negb andb].
    rstep aret_eq. unfold set_mode. rstep us_eq.
    apply (arm_DONE_cong DONE FTrue); [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_CHECK_cong : arm_cong CHECK FTrue arm_CHECK.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0.
    pose proof HQ as HQ0. ieq_open HQ E. specialize (Qcheck F0). unfold arm_CHECK.
    rstep gs_eq. nrm s1 s2 W5 F0.
    aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta. aflat.
    rstep gr_eq. rstep ur_eq. rstep uc_eq. rstep us_eq. rstep gs_eq. unfold UPDATE_CHECK_bytes. nrm s1 s2 W5 F0.
    destruct (wrap32 (ir_out r1 - ir_left r1) =? 0); cbn [negb].
    - rstep aret_eq. rstep ur_eq. unfold HOLD. rstep gr_eq. rstep gs_eq. nrm s1 s2 W5 F0.
      destruct (ZSWAP32 _ =? is_check s1); cbn [negb].
      + unfold INITBITS. rstep ur_eq. rstep aret_eq. unfold set_mode. rstep us_eq.
        apply (arm_LENGTH_cong LENGTH FTrue); [discriminate | discriminate | exact I | reflexivity | ieq_close E | uw0 W5 F0].
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
    - rstepr. unfold set_adler_check. rstep us_eq. rstep uc_eq. rstep ur_eq. unfold HOLD. rstep gr_eq. rstep gs_eq. nrm s1 s2 W5 F0.
      match goal with |- context [if ?cnd then _ else _] => destruct cnd end.
      + unfold go_bad, set_msg, set_mode. rstep uc_eq. rstep us_eq. rstep aret_eq. apply RES2_ret. wmid E W5 F0.
      + unfold INITBITS. rstep ur_eq. rstep aret_eq. unfold set_mode. rstep us_eq.
        apply (arm_LENGTH_cong LENGTH FTrue); [discriminate | discriminate | exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_TYPEDO_cong : forall M, M = TYPE \/ M = TYPEDO -> arm_cong M FTrue (arm_TYPEDO iv flush).
  Proof.
    intros M HM s1 s2 c r _ E HQ HU.
    assert (NH : M <> HEAD) by (destruct HM as [-> | ->]; discriminate).
    assert (NB : M <> BAD) by (destruct HM as [-> | ->]; discriminate).
    notHB HU E W5 F0. pose proof HQ as HQ0.
    assert (E' : is_mode s1 = TYPE \/ is_mode s1 = TYPEDO) by (rewrite E; exact HM).
    clear E HM. destruct E' as [E|E]; ieq_open HQ E; unfold arm_TYPEDO.
    all: rstep gs_eq; nrm s1 s2 W5 F0.
    all: destruct (negb (is_last s1 =? 0)).
    1,3: rlock SFREE_BYTEBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta;
         unfold set_mode; rlast; wmid E W5 F0.
    all: rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    all: unfold BITS at 1; rstep gr_eq; rstep us_eq; unfold DROPBITS at 1; rstep ur_eq; unfold BITS at 1; rstep gr_eq.
    all: destruct (BITSv _ 2 =? 0); [|destruct (BITSv _ 2 =? 1); [|destruct (BITSv _ 2 =? 2)]].
    all: unfold set_mode, go_bad, set_msg, set_mode, DROPBITS.

    1,5: rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.

    1,4: rstep us_eq; rstep us_eq; destruct (iv_flush_exits iv && (flush =? Z_TREES));
         [ rstep ur_eq; apply RES2_leave; wmid E W5 F0 | rstep aret_eq; rlast; wmid E W5 F0 ].

    1,3: rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.

    all: rstep uc_eq; rstep us_eq; rstep aret_eq; rlast; wmid E W5 F0.
  Qed.

  Lemma arm_TYPE_cong : arm_cong TYPE FTrue (arm_TYPE iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. unfold arm_TYPE.
    destruct (iv_flush_exits iv && ((flush =? Z_BLOCK) || (flush =? Z_TREES))).
    - apply RES2_leave. apply WMID_mk; assumption.
    - apply (arm_TYPEDO_cong TYPE (or_introl eq_refl) s1 s2 c r I E HQ HU).
  Qed.

  Lemma arm_COPY_cong : arm_cong COPY FTrue arm_COPY.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_COPY.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (negb (is_length s1 =? 0)).
    - rstep gr_eq.
      match goal with |- context [if ?cnd then aleave else _] => destruct cnd end.
      + apply RES2_leave. apply WMID_mk; [exact HQ0 | exact HU].
      + rstep uc_eq. rstep ur_eq. rlast. wmid E W5 F0.
    - unfold set_mode. rlast. wmid E W5 F0.
  Qed.

  Lemma arm_COPY__cong : arm_cong COPY_ FTrue arm_COPY_.
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_COPY_, set_mode.
    rstep us_eq. apply arm_COPY_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_STORED_cong : arm_cong STORED FTrue (arm_STORED iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_STORED.
    rlock SFREE_BYTEBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    rlock SFREE_NEEDBITS; [exact HQ0 | exact HU1 |]; intros [] r2 HU2 _; cbv beta.
    unfold HOLD. rstep gr_eq.
    match goal with |- context [if ?cnd then _ else _] => destruct cnd end.
    - unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. wmid E W5 F0.
    - rstep us_eq. unfold INITBITS. rstep ur_eq. unfold set_mode at 1. rstep us_eq.
      destruct (iv_flush_exits iv && (flush =? Z_TREES)).
      + apply RES2_leave. wmid E W5 F0.
      + apply arm_COPY__cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_DICT_cong : arm_cong DICT FTrue (arm_DICT iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DICT.
    rstep gs_eq. nrm s1 s2 W5 F0.
    destruct (is_havedict s1 =? 0).
    - rstep amodify_eq. unfold RESTORE. cbn [w_s w_c w_r]. apply RES2_return. wmid E W5 F0.
    - unfold set_adler_check. rstep us_eq. rstep uc_eq. unfold set_mode at 1. rstep us_eq.
      apply arm_TYPE_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.

  Lemma arm_DICTID_cong : arm_cong DICTID FTrue (arm_DICTID iv flush).
  Proof.
    intros s1 s2 c r _ E HQ HU. notHB HU E W5 F0. pose proof HQ as HQ0. ieq_open HQ E. unfold arm_DICTID.
    rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]; intros [] r1 HU1 _; cbv beta.
    unfold HOLD. rstep gr_eq. unfold set_adler_check. rstep us_eq. rstep uc_eq. unfold INITBITS. rstep ur_eq.
    unfold set_mode at 1. rstep us_eq.
    apply arm_DICT_cong; [exact I | reflexivity | ieq_close E | uw0 W5 F0].
  Qed.
End Simple.

Lemma UW_bad : forall s s' c r r', UW s c r -> is_wrap s' = is_wrap s -> is_flags s' = is_flags s -> is_mode s' = BAD ->
  ir_put r' = ir_put r -> ir_out r' = ir_out r -> UW s' c r'.
Proof.
  intros s s' c r r' (W & G & F) Ew Ef Em Ep Eo. split; [rewrite Ew; exact W|]. rewrite Em. split; [reflexivity|].
  rewrite Ef, Ep, Eo. destruct F as [F|(F & _ & P & O)]; [left; exact F | right]. repeat split; try assumption. right; reflexivity.
Qed.

Section Head.
  Variable iv : ivariant.

  Lemma arm_HEAD_cong : arm_cong HEAD FTrue (arm_HEAD iv).
  Proof.
    intros s1 s2 c r _ E HQ HU. pose proof HQ as HQ0. pose proof HU as [W5 HF]. ieq_open HQ E. unfold arm_HEAD.
    rstep gs_eq. nrm s1 s2 W5 W5.
    aflat. rlock SFREE_NEEDBITS; [exact HQ0 | exact HU |]. intros [] r1 HU1 _. cbv beta.
    pose proof HU1 as [_ HF1].
    assert (PO : ir_put r1 = ir_put r1 /\ ir_out r1 = ir_out r1) by (split; reflexivity).
    unfold HOLD. rstep gr_eq. lits.
    unfold BITS at 1. aflat. rstep gr_eq.
    match goal with |- context [if ?cnd then go_bad _ else _] => destruct cnd end.
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }
    unfold BITS at 1. rstep gr_eq.
    destruct (negb (BITSv (ir_hold r1) 4 =? Z_DEFLATED)).
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }
    unfold DROPBITS at 1. rstep ur_eq. unfold BITS at 1. rstep gr_eq.

    (* zlib 1.4: the window-size check comes first, the wbits store after it *)
    rstep gs_eq. sacc. ieq_rw s1 s2.
    match goal with |- context [if ?cnd then go_bad _ else _] => destruct cnd end.
    { unfold go_bad, set_msg, set_mode. rstep uc_eq. rlast. apply WMID_mk; [ieq_close E | eapply (UW_bad s1); [exact HU1 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]]. }

    assert (STEP : forall (K : AM unit) ,
      (forall s1' s2', IEQ s1' s2' -> is_wrap s1' = 5 -> is_flags s1' = is_flags s1 -> is_mode s1' = HEAD ->
         RES2 (K (mkW s1' c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))
              (K (mkW s2' c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))) ->
      RES2 (((if is_wbits s1 =? 0 then us (fun s : inflate_state => iset_wbits s (BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8)) else aret tt);; K)%am
              (mkW s1 c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))
           (((if is_wbits s1 =? 0 then us (fun s : inflate_state => iset_wbits s (BITSv (Z.shiftr (ir_hold r1) 4) 4 + 8)) else aret tt);; K)%am
              (mkW s2 c (irset_bits (irset_hold r1 (Z.shiftr (ir_hold r1) 4)) (wrap32 (ir_bits r1 - 4)))))).
    { intros K HK. destruct (is_wbits s1 =? 0).
      - rstep us_eq. apply HK; [ieq_close E | sacc; exact W5 | reflexivity | sacc; exact E].
      - rstep aret_eq. apply HK; [exact HQ0 | exact W5 | reflexivity | exact E]. }
    sacc. apply STEP. clear STEP. intros s1' s2' HQ' W5' EF' E'. clear Qmode Qlast Qwrap Qhavedict Qflags Qdmax Qtotal Qhead Qwbits Qwsize Qwhave Qwnext Qwblk Qhold Qbits Qlencode Qdistcode Qnext Qsane Qback Qself QLwin QLlens QLwork QLcodes Qcheck Qwin.
    pose proof HQ' as HQ1. ieq_open HQ' E'.
    unfold aux. destruct (iv_aux iv); cbv iota; [rstep us_eq|rstep aret_eq]; rstep us_eq; unfold set_adler_check; aflat; rstep us_eq; rstep uc_eq;
      unfold HOLD; rstep gr_eq; unfold set_mode; rstep us_eq; unfold INITBITS; rlast;
      match goal with |- context [if ?cnd then DICTID else TYPE] => destruct cnd end;
      (apply WMID_mk; [ ieq_close E' | apply UW_intro0; sacc; [exact W5' | reflexivity | reflexivity] ]).
  Qed.
End Head.

Lemma arm_gz_cong : forall M F (arm : AM unit), gzb M = true -> arm_cong M F arm.
Proof.
  intros M F arm HM s1 s2 c r _ E HQ HU. exfalso. pose proof (UW_gz _ _ _ HU) as G. rewrite E, HM in G. discriminate G.
Qed.
