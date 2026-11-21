(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit Z_flushpend Z_defl_arms Z_defl_pend Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate FillWinModel DeflateSafe RefDeflFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Section PENDG.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma defl_pendg : forall (Q : machine_state -> Prop) (d : deflate_state)
    (y1 y5 y6 y7 y12 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  DINV L rest0 lo r me d m ->
  (flush = 0 \/ flush = 4 \/ flush = 5) ->
  0 <= cs_avail_out (ds_strm d) < 2^31 -> 0 <= cs_avail_in (ds_strm d) < 2^31 -> - 2 <= ds_last_flush d <= 5 ->
  0 <= ds_pending d <= 65536 -> ds_lit_bufsize d = 16384 -> 0 <= ds_status d < 1000 ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> fp_ok (set_last_flush d flush)) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> 0 <= ds_status (flush_pending (set_last_flush d flush)) < 1000) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> Box (length (cs_out_rev (ds_strm (flush_pending (set_last_flush d flush)))) <= length rest0)%nat) ->
  (cs_avail_out (ds_strm d) = 0 -> DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return d Z_BUF_ERROR))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) = 0 ->
   DKL L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d <> 0 -> cs_avail_out (ds_strm (flush_pending (set_last_flush d flush))) <> 0 ->
   DKB L flush rest0 lo r F fc me Q (flush_pending (set_last_flush d flush))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> rank_err d flush ->
   DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return (set_last_flush d flush) Z_BUF_ERROR))) ->
  (cs_avail_out (ds_strm d) <> 0 -> ds_pending d = 0 -> ~ rank_err d flush -> DKB L flush rest0 lo r F fc me Q (set_last_flush d flush)) ->
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) y12 (wz (ds_status d)) (wz (cs_avail_in (ds_strm d))) y15 y16 y17
                       (r_s2 r) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x17328) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) HFL RAO RAI RLF RP LBS RST FPOK RST2 ROOMF KBUF KLF KB1 KRK KB0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof DR as DR0.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU. unfold DKL, DK, Z_DEFL_LF, deflR in KLF. unfold DKB, Z_DEFL_DISP, deflR in KB1, KB0.
  zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  -
    eapply (defl_buferr L inp rest0 lo r F fc me CTX Q d 0x17364); [left; reflexivity| |apply KBUF; lia].
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
    zs. zs. zs. name_mem mA. zstep. zstep.
    tr_groups MUf WMf.
    remember (set_last_flush d flush) as s1 eqn:Es1.
    assert (ST1 : DST mA L s1).
    { rewrite Es1. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1]. }
    assert (DOUT1 : dout mA L rest0 (ds_strm s1)).
    { rewrite Es1. dsred. apply (dout_munch _ m mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia. }
    assert (DI1 : DINV L rest0 lo r me s1 mA).
    { split; [split; [rewrite Es1; dsred; do 4 eexists; exact ZS| exact ST1]|]. split; [exact DOUT1|]. split; [rewrite Es1; dsred; exact ROOM|].
      split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia.
    +
      assert (P0 : ds_pending d = 0) by lia.
      specialize (KRK ltac:(lia) P0). specialize (KB0 ltac:(lia) P0). clear KLF KB1 KBUF FPOK ROOMF RST2.
      assert (C_DISP : forall (a12 a14 a15 : word), ~ rank_err d flush ->
        evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz (dl_S L)) (wz (dl_S L)) (wz flush) a12 (wz (ds_status d)) a14 a15 y16 y17
                       (wz flush) (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x1738c) fc None mA (seg_rom usegs))).
      { intros a12 a14 a15 NR. specialize (KB0 NR).
        replace (wz (ds_status d)) with (wz (ds_status s1)) by (rewrite Es1; reflexivity).
        eapply KB0. exact DI1. }
      clear KB0.
      zstep. if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
      *
        assert (HLF : ds_last_flush d = -2 \/ ds_last_flush d = -1 \/ ds_last_flush d = 0 \/ ds_last_flush d = 1 \/ ds_last_flush d = 2
                      \/ ds_last_flush d = 3 \/ ds_last_flush d = 4 \/ ds_last_flush d = 5) by lia.
        destruct HFL as [F0|[F4|F5]]; rewrite ?F0, ?F4, ?F5 in *;
          destruct HLF as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
          do 3 zstep; closed_br; do 7 zstep; closed_br; do 2 zstep; closed_br;
          try (do 8 zstep; closed_br).
        all: first [ apply C_DISP; unfold rank_err, RANK, Z_FINISH; rewrite ?E; cbn; lia
                   | eapply (defl_buferr L inp rest0 lo r F fc me CTX Q s1 0x17764); [right; right; reflexivity| exact DI1| apply KRK; unfold rank_err, RANK, Z_FINISH; rewrite E; cbn; lia] ].
      * apply C_DISP. unfold rank_err. lia.
    +
      assert (PN0 : ds_pending d <> 0) by lia.
      specialize (FPOK ltac:(lia) PN0). specialize (ROOMF ltac:(lia) PN0). specialize (RST2 ltac:(lia) PN0).
      specialize (KLF ltac:(lia) PN0). specialize (KB1 ltac:(lia) PN0). clear KRK KB0 KBUF.
      assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
      assert (ESS : ds_strm s1 = ds_strm d) by (rewrite Es1; reflexivity).
      assert (LB1 : ds_lit_bufsize s1 * 4 = 65536) by (rewrite Es1; dsred; lia).
      assert (RAO1 : 0 <= cs_avail_out (ds_strm s1) < 2^31) by (rewrite ESS; lia).
      assert (DR1 : DREP mA L s1) by exact (proj1 DI1).
      clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf ZS ST1.
      zstep. zstep.
      call (flush_pending_spec HTFB L s1 rest0 (zlength inp) lo).
      1:{ exact DR1. } 1:{ exact DOUT1. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. }
      1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
      1:{ exact FPOK. } 1:{ exact LB1. } 1:{ exact RAO1. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. }
      name_mem mC.
      lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKC end.
      lazymatch goal with H : DREP mC L _ |- _ => rename H into DRC end.
      lazymatch goal with H : dout mC L rest0 _ |- _ => rename H into DOUTC end.
      lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIC end.
      assert (DIC : DINV L rest0 lo r me (flush_pending s1) mC).
      { split; [exact DRC|]. split; [exact DOUTC|]. split; [exact ROOMF|]. split; [eexists; exact FR|]. split; [exact STKC|]. split; [exact MU|]. split; [exact WM| exact MIC]. }
      remember (flush_pending s1) as X' eqn:EX'.
      pose proof DRC as DRC0. destruct DRC as [ZS' ST']. open_zs ZS'. destruct ST' as [GA' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA'.
      assert (RAO' : 0 <= cs_avail_out (ds_strm X') < 2^31) by (rewrite EX'; pose proof (fp_avail_out s1 ltac:(lia)); lia).
      zs. zstep. if_cases KA'; zify_cond KA'; rewrite ?unsigned_lit in KA' by lia.
      * eapply (KLF ltac:(lia)). exact DIC.
      * zstep. zs. zstep. zstep. eapply (KB1 ltac:(lia)). exact DIC.
Qed.
End PENDG.
