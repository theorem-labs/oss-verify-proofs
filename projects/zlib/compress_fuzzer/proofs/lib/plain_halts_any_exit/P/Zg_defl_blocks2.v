(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_model Z_defl_kit
     Z_flushpend Z_defl_arms Z_adler32 Zg_adler32_iface Zg_defl_iface Zg_defl_iface2 Z_defl_path Zg_defl_path Zg_defl_path2 Zg_defl_blocks.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast6 RefDeflSlow6 RefDeflSafeS DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma cfg_cell_fast_at : forall m a, relro_clean m ->
  (a = 0x293a0 \/ a = 0x293b0 \/ a = 0x293c0) ->
  rw_cells psegs m a [C8 (wz Z_DEFLATE_FAST)].
Proof.
  intros m a RC Ha. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold Z_DEFLATE_FAST.
  pose (cs := [C8 (wz 0x18f8c)]).
  destruct Ha as [-> |[-> | ->]];
  (lazymatch goal with |- rw_cells _ _ ?b _ =>
     apply (InitMem.rw_cells_recast psegs m b [CB 8 (cells_bytes cs)] cs);
     [ apply (InitMem.rw_cells_image0 psegs m b (cells_bytes cs));
       [ intros x Hx; apply RC; change (Z.of_nat (length (cells_bytes cs))) with 8 in Hx; lia
       | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with 8; lia ]
     | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ] end).
Qed.

Lemma cfg_cell_fast : forall m lv, relro_clean m -> 1 <= lv <= 3 -> rw_cells psegs m (Z_CFG_TABLE + 16 * lv + 8) [C8 (wz Z_DEFLATE_FAST)].
Proof.
  intros m lv RC H. apply cfg_cell_fast_at; [exact RC|]. unfold Z_CFG_TABLE.
  assert (C : lv = 1 \/ lv = 2 \/ lv = 3) by lia.
  destruct C as [-> |[-> | ->]]; cbn; tauto.
Qed.

Section BLOCKSG2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HSTO : deflate_stored_stmt.
Hypothesis HFAST : deflate_fast_stmtg.
Hypothesis HSLOW : deflate_slow_stmtg.

Lemma defl_rung2 : forall (Q : machine_state -> Prop) (X : deflate_state),
  (flush = 0 \/ flush = 4 \/ flush = 5) -> 0 <= ds_level X <= 9 -> 0 <= ds_strategy X <= 1 ->
  din_tie inp X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 -> ds_wrap X <> 2 -> ds_wrap X <> 0 -> - 2 <= ds_wrap X <= 2 ->
  cs_avail_in (ds_strm X) < 2^31 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (ds_level X = 0 -> st_entry X /\ ds_pending_buf_size X = 65536) ->
  (1 <= ds_level X <= 3 -> fast_safe X flush) ->
  (4 <= ds_level X -> slow_safe X flush) ->
  Box (length (cs_out_rev (ds_strm (fst (dblk2 X flush)))) <= length rest0)%nat ->
  0 <= cs_avail_out (ds_strm (fst (dblk2 X flush))) < 2^31 ->
  (snd (dblk2 X flush) = need_more -> cs_avail_out (ds_strm (fst (dblk2 X flush))) = 0 -> DKL L flush rest0 lo r F fc me Q (fst (dblk2 X flush))) ->
  (snd (dblk2 X flush) = need_more -> cs_avail_out (ds_strm (fst (dblk2 X flush))) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (fst (dblk2 X flush))) ->
  (snd (dblk2 X flush) = finish_started -> cs_avail_out (ds_strm (fst (dblk2 X flush))) = 0 -> DKL L flush rest0 lo r F fc me Q (set_status (fst (dblk2 X flush)) FINISH_STATE)) ->
  (snd (dblk2 X flush) = finish_started -> cs_avail_out (ds_strm (fst (dblk2 X flush))) <> 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_status (fst (dblk2 X flush)) FINISH_STATE)) ->
  (snd (dblk2 X flush) = finish_done -> DK L flush rest0 lo r F fc me Q 0x17b88 (set_status (fst (dblk2 X flush)) FINISH_STATE)) ->
  (snd (dblk2 X flush) = block_done -> flush = 5 /\ fp_ok (fst (dblk2 X flush)) /\ ds_lit_bufsize (fst (dblk2 X flush)) = 16384
     /\ Box (length (cs_out_rev (ds_strm (flush_pending (fst (dblk2 X flush))))) <= length rest0)%nat
     /\ 0 <= cs_avail_out (ds_strm (flush_pending (fst (dblk2 X flush)))) < 2^31
     /\ (cs_avail_out (ds_strm (flush_pending (fst (dblk2 X flush)))) = 0 -> DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush (flush_pending (fst (dblk2 X flush))) (-1)))
     /\ (cs_avail_out (ds_strm (flush_pending (fst (dblk2 X flush)))) <> 0 -> DK L flush rest0 lo r F fc me Q 0x17b88 (flush_pending (fst (dblk2 X flush))))) ->
  DK L flush rest0 lo r F fc me Q 0x17a10 X.
Proof.
  intros Q X HFL LV SG TIE WS HS LBS WR W0 WRG RAI RAO SE SAFEF SAFES ROOMF RAO2 KNM0 KNM1 KFS0 KFS1 KFD KBD.
  unfold DK. intros until m'. intros DI. pose proof DI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI). rename m' into m.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp.
  assert (RL : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  assert (DINm : din m L inp) by (apply (defl_din L inp rest0 lo r me CTX); exact MU).
  pose proof DR as DR0. destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  assert (RLV : - 2^31 <= ds_level X < 2^31) by lia. assert (RSG : - 2^31 <= ds_strategy X < 2^31) by lia.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -64)) = bv_unsigned (r_sp r) + -64) by (apply unsigned_lit; lia).
  assert (F05 : 0 <= flush <= 5) by lia.

  assert (AFTER : forall (mA : mem) (y1' y5' y6' y7' y11' y12' y13' y14' y15' y16' y17' y28' y29' y30' y31' : word),
    DINV L rest0 lo r me (fst (dblk2 X flush)) mA ->
    evt psegs Q (MS (deflR L flush r y1' y5' y6' y7' (wz (bs_code (snd (dblk2 X flush)))) y11' y12' y13' y14' y15' y16' y17' y18 y19 y21 y22 y28' y29' y30' y31')
                    F (wz 0x17a80) fc None mA (seg_rom psegs))).
  { intros. eapply defl_bstate; eassumption. }
  zs. zstep. if_cases KL; zify_cond KL; rewrite ?signed_wz in KL by lia.
  -
    destruct (SE ltac:(lia)) as [SEN PBS].
    rewrite (dblk2_stored X flush ltac:(lia)) in *.
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
    zs. zstep. call (HSTO L X flush inp rest0 lo).
    1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. }
    1:{ rewrite ESP. unfold Z_STORED_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
    1:{ exact IO. } 1:{ exact SEN. } 1:{ exact F05. } 1:{ exact WS. } 1:{ exact LBS. } 1:{ exact PBS. } 1:{ exact WR. }
    1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
    name_mem mA.
    lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
    lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
    lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
    zstep. apply AFTER.
    split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption].
  -
    zs. zs. zstep. if_cases KS3; zify_cond KS3; rewrite ?signed_wz in KS3 by lia; [exfalso; lia|].
    zs. zstep. if_cases KS2; zify_cond KS2; rewrite ?signed_wz in KS2 by lia; [| exfalso; lia].
    zs. zs. zs. zs.
    rewrite (Z.shiftl_mul_pow2 (ds_level X) 4) by lia. change (2^4) with 16.
    destruct (Z_lt_le_dec (ds_level X) 4) as [LF|LS].
    +
      specialize (SAFEF ltac:(lia)).
      rewrite (dblk2_fast X flush ltac:(lia)) in *.
      pose proof (cfg_cell_fast m (ds_level X) RL ltac:(lia)) as CFG. unfold Z_CFG_TABLE, Z_DEFLATE_FAST in CFG.
      replace (168840 + 16 * ds_level X + 8) with (168840 + ds_level X * 16 + 8) in CFG by lia.
      zs. zs.
      clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend CFG.
      zstep. call (HFAST L X flush inp rest0 lo).
      1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. }
      1:{ rewrite ESP. unfold Z_FAST_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
      1:{ exact IO. } 1:{ exact SAFEF. } 1:{ exact F05. } 1:{ exact WS. } 1:{ exact HS. } 1:{ exact LBS. } 1:{ exact WR. } 1:{ exact W0. } 1:{ exact WRG. }
      1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
      name_mem mA.
      lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
      lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
      lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
      apply AFTER.
      split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption].
    +
      specialize (SAFES ltac:(lia)).
      rewrite (dblk2_slow X flush ltac:(lia)) in *.
      pose proof (cfg_cell m (ds_level X) RL ltac:(lia)) as CFG. unfold Z_CFG_TABLE, Z_DEFLATE_SLOW in CFG.
      replace (168840 + 16 * ds_level X + 8) with (168840 + ds_level X * 16 + 8) in CFG by lia.
      zs. zs.
      clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend CFG.
      zstep. call (HSLOW L X flush inp rest0 lo).
      1:{ exact DR0. } 1:{ exact DINm. } 1:{ exact TIE. } 1:{ exact DOUT. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. }
      1:{ rewrite ESP. unfold Z_SLOW_STACK. lia. } 1:{ rewrite ESP. Z.div_mod_to_equations. lia. } 1:{ rewrite ESP. unfold dlay_below. lia. }
      1:{ exact IO. } 1:{ exact SAFES. } 1:{ exact F05. } 1:{ exact WS. } 1:{ exact HS. } 1:{ exact LBS. } 1:{ exact WR. } 1:{ exact W0. } 1:{ exact WRG. }
      1:{ exact RAI. } 1:{ exact RAO. } 1:{ exact (unbox _ ROOMF). } 1:{ reflexivity. } 1:{ reflexivity. }
      name_mem mA.
      lazymatch goal with H : stk psegs mA _ _ |- _ => rename H into STKA end. rewrite ESP in STKA.
      lazymatch goal with H : DREP mA L _ |- _ => rename H into DRA end.
      lazymatch goal with H : dout mA L _ _ |- _ => rename H into DOA end.
      apply AFTER.
      split; [exact DRA|]. split; [exact DOA|]. split; [exact ROOMF|]. split; [exact FR|]. split; [exact STKA|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End BLOCKSG2.
