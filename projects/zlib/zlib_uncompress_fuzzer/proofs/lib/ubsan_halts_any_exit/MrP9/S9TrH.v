(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec StdModel ShapeAlg ShapeLaws Spec S9TargetPre S9World S9LibStmt S9Atexit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PlainS9 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom MrRulesS9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require Import S9HeapPre S9HBase S9HConv S9SoDefs S9TrTail S9TrInv S9TrRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9TargetPre.
Module OSA := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Module OSp := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Spec.
Module OAX := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.S9Atexit.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma t_target_run : forall (content : list byte) (fs : Fs.Fs),
  6 + OT.hdr_cfglen content <= Z.of_nat (length content) ->
  OSA.t_eq (T_run fs (OT.hdr_paylen content) (OT.hdr_b1 content)
                  (calls_n (OT.hdr_cfglen content) (bv_unsigned (nth 2 content (Z_to_bv 8 0)))))
           (OT.t_target content fs).
Proof.
  intros content fs LEN6. unfold OT.t_target, T_run, calls_n.
  set (c2 := bv_unsigned (nth 2 content (Z_to_bv 8 0))).
  pose proof (byte_range (nth 2 content (Z_to_bv 8 0))) as C2. fold c2 in C2.
  pose proof (byte_range (nth 0 content (Z_to_bv 8 0))) as B0.
  pose proof (byte_range (nth 1 content (Z_to_bv 8 0))) as B1.
  unfold OT.hdr_paylen, OT.hdr_cfglen, OT.hdr_cfg, OT.hdr_b0, OT.hdr_b1 in *.
  set (b0 := bv_unsigned (nth 0 content (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 1 content (Z_to_bv 8 0))) in *.
  set (cfg := b0 + 256 * b1) in *.
  assert (CL : 0 <= cfg mod 32768 < 32768) by (apply Z.mod_pos_bound; lia).
  assert (EC : match Z.to_nat (cfg mod 32768) with 0%nat => 1%nat | S _ => S (Z.to_nat (c2 mod 4)) end
               = S (if cfg mod 32768 =? 0 then 0%nat else Z.to_nat (Z.land c2 3))).
  { destruct (Z.eqb_spec (cfg mod 32768) 0) as [E|E].
    - rewrite E. reflexivity.
    - destruct (Z.to_nat (cfg mod 32768)) eqn:EN; [lia|]. f_equal. f_equal.
      change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. }
  rewrite EC. set (n := if cfg mod 32768 =? 0 then 0%nat else Z.to_nat (Z.land c2 3)).
  assert (ES : OSA.t_eq (ShapeAlg.t_emit (Spec.W 1 [Z_to_bv 8 48; Z_to_bv 8 10])
                           (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines n)) (ShapeAlg.t_exit (Spec.exit_code 0) fs)))
                        (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines (S n))) (ShapeAlg.t_exit (Spec.exit_code 0) fs))).
  { exact (ShapeLaws.t_emit_W_app 1 [Z_to_bv 8 48; Z_to_bv 8 10] (Spec.zero_lines n) _). }
  destruct (Z.eqb_spec (Z.of_nat (length content) - 6 - cfg mod 32768) 0) as [EP|NP].
  - replace (length content - 6 - Z.to_nat (cfg mod 32768))%nat with 0%nat by lia. exact ES.
  - destruct (length content - 6 - Z.to_nat (cfg mod 32768))%nat eqn:EN; [lia|].
    assert (EX : OSA.t_eq (ShapeAlg.t_emit (Spec.W 1 (Spec.zero_lines 0)) (ShapeAlg.t_exit (Spec.exit_code (if b1 <? 128 then 2 else 0)) fs))
                          (ShapeAlg.t_exit (Spec.exit_code (if 32768 <=? cfg then 0 else 2)) fs)).
    { replace (if 32768 <=? cfg then 0 else 2) with (if b1 <? 128 then 2 else 0).
      2:{ destruct (Z.ltb_spec b1 128); destruct (Z.leb_spec 32768 cfg); unfold cfg in *; lia. }
      apply ShapeAlg.t_emit_nil_eq. left. apply is_prefix_nil. }
    eapply OSA.t_eq_trans; [apply ShapeLaws.t_alt2_congr_l; exact EX | apply ShapeLaws.t_alt2_congr_r; exact ES].
Qed.

Section S0.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.

Ltac forget_regsR R :=
  repeat match goal with |- context [reg_get R ?k] => let x := fresh "x" in set (x := reg_get R k); clearbody x end.

Theorem target_phase_h : S9LibStmt.zlib_u2_contract_S9 -> target_phase_h_stmt.
Proof.
  intros C7 sp0 buf cap content R M mo H. destruct H.
  destruct th_heap as (s & pb & HH & HOWN & HDRV & HROOM).
  destruct th_sp0 as [SP0 SP16]. destruct th_len as [[LEN6 LENB] LENC].
  destruct th_tid as (tid & TID & TIDC). destruct th_errno as [errv ERR].
  assert (CFGR : 0 <= OT.hdr_cfglen content < 32768) by (unfold OT.hdr_cfglen; apply Z.mod_pos_bound; lia).
  pose proof (byte_range (nth 1 content (Z_to_bv 8 0))) as B1R. fold (OT.hdr_b1 content) in B1R.
  pose proof (byte_range (nth 2 content (Z_to_bv 8 0))) as C2R.
  pose proof (RHEAP_block_range_proof _ _ _ (pb, buf, cap) HH ltac:(left; reflexivity)) as (BR1 & BR2 & BR3 & BR4 & BR5).
  cbn [blk_addr blk_size fst snd] in *.
  eapply ShapeAlg.rz_conseq; [| apply (t_target_run content (m_fs mo) LEN6)].
  apply rz_mkR. unfold mkR_of.
  rewrite (th_ra : reg_get R (Z_to_bv 5 1) = _), (th_sp : reg_get R (Z_to_bv 5 2) = _),
          (th_tp : reg_get R (Z_to_bv 5 4) = _), (th_a0 : reg_get R (Z_to_bv 5 10) = _), (th_a1 : reg_get R (Z_to_bv 5 11) = _),
          (th_a2 : reg_get R (Z_to_bv 5 12) = _), (th_a3 : reg_get R (Z_to_bv 5 13) = _), (th_s1 : reg_get R (Z_to_bv 5 9) = _),
          (th_s5 : reg_get R (Z_to_bv 5 21) = _).
  forget_regsR R. clear th_ra th_sp th_gp th_tp th_a0 th_a1 th_a2 th_a3 th_s1 th_s5.
  pose proof (stk_of_stack_writable M sp0 (sp0 - 120) ltac:(lia) ltac:(lia) ltac:(lia) th_stack) as ST0.
  destruct (stk_carve (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 8%nat ST0 ltac:(lia)) as [ST (junk & FR0)].
  replace (sp0 - 120 - Z.of_nat 8) with (sp0 - 128) in * by lia.
  assert (SOK : forall a, sp0 - 6144513 <= a -> a + 8 <= sp0 -> store_ok (run_segments psegs rc_inp rc_sp rc_mb) M (wa a) 8 = true).
  { intros a A1 A2. specialize (th_stack (a - (sp0 - 6144513)) 8%nat ltac:(lia) ltac:(lia)).
    replace (sp0 - 6144513 + (a - (sp0 - 6144513))) with a in th_stack by lia. exact th_stack. }
  assert (FRM : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128)
                  [CB 8 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sp0 + 32));
                   C8 (Z_to_bv 64 0x148cc); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (sp0 + 8)); C8 (Z_to_bv 64 0x18c08)]).
  { destruct th_frame as [F_ra F_s0 F_s1 F_s2 F_s3 F_s4 F_s5 F_s6 F_s7].
    apply rw_cells_cons; [exact FR0|]. cbn [csize].
    Ltac cell8 F SOK := apply rw_cells_cons; [apply rw_cell8_of_cell; [ | apply SOK; lia | lia | lia];
                         match goal with |- S9World.cell _ ?a _ _ => replace a with ltac:(let t := type of F in match t with S9World.cell _ ?b _ _ => exact b end) by lia end; exact F |]; cbn [csize].
    cell8 F_s7 SOK. cell8 F_s6 SOK. cell8 F_s5 SOK. cell8 F_s4 SOK. cell8 F_s3 SOK. cell8 F_s2 SOK. cell8 F_s1 SOK. cell8 F_s0 SOK.
    apply rw_cell8_of_cell; [ | apply SOK; lia | lia | lia].
    match goal with |- S9World.cell _ ?a _ _ => replace a with (sp0 - 56) by lia end. exact F_ra. }
  pose proof (pristine_word M 0x32e59 0x32e90 (fun a Ha => th_img 0x32e59 0x32e90 a ltac:(cbn; tauto) Ha)) as NONE1.
  pose proof (pristine_word M 0x21000 0x21be8 (fun a Ha => th_img 0x21000 0x21be8 a ltac:(cbn; tauto) Ha)) as NONE2.
  rimg_chunk NONE1 M 0x32e60%Z [C1 (Z_to_bv 8 0)] FL.
  rimg_chunk NONE2 M 0x21bb0%Z [C8 (Z_to_bv 64 0)] GOT.
  rimg_chunk NONE1 M 0x32e64%Z [C1 (Z_to_bv 8 0)] ICB.
  pose proof (pristine_word M 0x92fa0 0x931c8 (fun a Ha => th_img 0x92fa0 0x931c8 a ltac:(cbn; tauto) Ha)) as NONE3.
  assert (AX0 : OAX.atx_cells0 M).
  { apply OAX.atx_cells0_init. intros a Ha. unfold OAX.atx_addr, OAX.PATX, OAX.PATX_N, OAX.PAEF_INCB in Ha.
    destruct Ha as [Ha|Ha]; [apply NONE3; lia | apply NONE1; lia]. }
  pose proof (bytes_at_of_rdn _ M buf content th_content ltac:(lia) ltac:(lia)) as CT.
  assert (CBY : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 2) [Z_to_bv 8 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))]).
  { replace (Z_to_bv 8 (bv_unsigned (nth 2 content (Z_to_bv 8 0)))) with (nth 2 content (Z_to_bv 8 0))
      by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range).
    rewrite <- (firstn_skipn 2 content) in CT. apply bytes_at_app in CT. destruct CT as [_ X].
    rewrite length_firstn in X. replace (Z.of_nat (Nat.min 2 (length content))) with 2 in X by lia.
    destruct (skipn 2 content) as [|c rest] eqn:SK.
    { exfalso. pose proof (f_equal (@length _) SK) as SL. rewrite length_skipn in SL. cbn in SL. lia. }
    assert (EC : nth 2 content (Z_to_bv 8 0) = c).
    { rewrite <- (firstn_skipn 2 content) at 1. rewrite app_nth2 by (rewrite length_firstn; lia).
      rewrite length_firstn, SK. replace (2 - Nat.min 2 (length content))%nat with 0%nat by lia. reflexivity. }
    rewrite EC. change (c :: rest) with ([c] ++ rest) in X. apply bytes_at_app in X. exact (proj1 X). }
  assert (PBY : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M (buf + 6 + OT.hdr_cfglen content) (skipn (Z.to_nat (6 + OT.hdr_cfglen content)) content)).
  { rewrite <- (firstn_skipn (Z.to_nat (6 + OT.hdr_cfglen content)) content) in CT. apply bytes_at_app in CT. destruct CT as [_ X].
    rewrite length_firstn in X.
    replace (buf + Z.of_nat (Nat.min (Z.to_nat (6 + OT.hdr_cfglen content)) (length content))) with (buf + 6 + OT.hdr_cfglen content) in X by lia.
    exact X. }
  assert (CLI : cli_inv sp0 M tid).
  { constructor; [exact th_aux | | exact TIDC | do 9 eexists; exact FRM].
    intros lo hi a IN Ha. unfold exit_ivs in IN. cbn [In] in IN.
    destruct IN as [IN|[IN|[IN|[IN|[IN|[IN|[IN|[]]]]]]]]; injection IN as <- <-.
    - apply (th_img 0x21000 0x21be8); [cbn; tauto | lia].
    - apply (th_img 0x21bf0 0x22e10); [cbn; tauto | lia].
    - apply (th_img 0x21bf0 0x22e10); [cbn; tauto | lia].
    - apply (th_img 0x22e11 0x22e59); [cbn; tauto | lia].
    - apply (th_img 0x92fa0 0x931c8); [cbn; tauto | lia].
    - apply (th_img 0x92fa0 0x931c8); [cbn; tauto | lia].
    - apply (th_img 0x93608 0x94000); [cbn; tauto | lia]. }
  assert (SOP : so_pristine M).
  { intros i [Hi|Hi]; [apply (th_img 0x21bf0 0x22e10) | apply (th_img 0x93608 0x94000)]; first [cbn; tauto | lia]. }
  eapply (trun_rz sp0 (conj (proj1 SP0) (proj2 SP0)) SP16 th_atop pb buf cap (m_fs mo) (OT.hdr_paylen content) (OT.hdr_b1 content) tid
            (sp0 - 6144513) B1R TID ltac:(lia) ltac:(lia) ltac:(unfold OT.hdr_paylen; lia) C7
            (OT.hdr_cfglen content) (bv_unsigned (nth 2 content (Z_to_bv 8 0))) (buf + 6 + OT.hdr_cfglen content) M s mo
            (skipn (Z.to_nat (6 + OT.hdr_cfglen content)) content) errv);
    try eassumption; try lia.
  - unfold OT.hdr_paylen. lia.
  - rewrite length_skipn. unfold OT.hdr_paylen. lia.
Qed.

End S0.

