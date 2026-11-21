(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit.

Module Z_slow_fbA.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Z_flushpend Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel DeflateSafe DeflateOverlay RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 RefDeflSafeLF RefDeflSafeFB.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma fbo_fp : forall X last, flush_block_only X last = flush_pending (fbo2 X last).
Proof. intros X last. unfold flush_block_only, fbo2, fbo1, fb_buf, fb_len. reflexivity. Qed.

Lemma fbo2_facts : forall X last, flush_ok X last -> ds_lit_bufsize X = 16384 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  fp_ok (fbo2 X last) /\ ds_lit_bufsize (fbo2 X last) * 4 = 65536 /\ 0 <= cs_avail_out (ds_strm (fbo2 X last)) < 2^31
  /\ ds_strm (fbo2 X last) = ds_strm (fbo1 X last) /\ ds_strstart (fbo1 X last) = ds_strstart X
  /\ cs_out_rev (ds_strm (fbo1 X last)) = cs_out_rev (ds_strm X).
Proof.
  intros X last FOK LBS RAO.
  destruct (flush_ok_fbo X last FOK LBS) as (_ & _ & _ & _ & _ & _ & _ & BI9 & PB10 & RP10 & RPO10 & RPOL & RTO).
  destruct (tfb_keep X last) as (E1 & _ & EO & EAO).
  pose proof (PF_fields _ _ (PF_tfb X (fb_buf X) (fb_len X) last)) as (_ & _ & (_ & Elb & _) & _).
  assert (ELB2 : ds_lit_bufsize (fbo2 X last) = 16384) by (unfold fbo2, fbo1; dsred; rewrite Elb; exact LBS).
  assert (ES2 : ds_strm (fbo2 X last) = ds_strm (fbo1 X last)) by (unfold fbo2; dsred; reflexivity).
  split; [|split; [lia| split; [rewrite ES2, EAO; exact RAO| split; [exact ES2| split; [exact E1| exact EO]]]]].
  unfold fp_ok. rewrite ELB2. change (16384 * 4) with 65536. cbv zeta. fold (fbo3 X last).
  split; [exact BI9|]. split; [exact RP10|]. split; [exact PB10|]. split; [exact RPO10|]. split; [exact RPOL| exact RTO].
Qed.

Section SITE.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmtE.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_fbA : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  flush_ok X 0 -> fb_entry X 0 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 0))) <= length rest0)%nat ->
  SK L flush rest0 lo r fj F fc me Q 0x1a2b0 (flush_block_only X 0) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 (wz (ds_strstart X)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a230) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & FR & STK & MU & WM & MI) FOK FE LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 0); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 0 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 0 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & _).
  destruct (fbo2_facts X 0 FOK LBS RAO) as (FP2 & LB2 & RAO2 & ES2 & E1 & EO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  zs. zstep.
  eapply (evt_cut usegs (fun ms' => exists v10 v13 v14, ms' = MS (slowR L flush r x1 x5 x6 x7 v10 (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) (wz (fb_len X))
                                                                   v13 v14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a294) fc None m (seg_rom usegs))).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. zstep. zstep.
      rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia. gF.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBN NEG).
      replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
        by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
      reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zs. zs. zstep. rewrite ?Z.mod_small by lia.
      replace (Z.land (ds_block_start X) 4294967295) with (ds_block_start X)
        by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      zstep. gF. zstep. zstep. zstep. gX.
      zstep. zstep. rewrite ?Z.mod_small by lia. zstep. zstep. zstep.
      first [rewrite (sub_guard_pos (ds_strstart X) (ds_block_start X)) by lia | rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia]. gT.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBP POS).
      replace (wz (ds_strstart X - ds_block_start X)) with (wz (fb_len X)) by (f_equal; rewrite ELEN; reflexivity).
      reflexivity. }
  intros ms' (v10 & v13 & v14 & ->). unfold slowR.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  zstep. zstep. zstep.
  call (HTFBLK L X (fb_buf X) (fb_len X) 0 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. rewrite ESP. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact FE. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 0) with (fbo1 X 0) in POST.
  remember (fbo1 X 0) as X1 eqn:EX1.
  assert (DOUT1 : u8arr usegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. rewrite ?Z.mod_small by lia. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (EF2 : fbo2 X 0 = X2) by (rewrite EX2, EX1; reflexivity). rewrite EF2 in FP2, LB2, RAO2, ES2.
  assert (DR2 : DREP mB L X2).
  { split.
    - rewrite ES2. do 4 eexists. exact ZS.
    - rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  assert (DOUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES2; exact DOUT1).
  assert (RM2 : (length (cs_out_rev (ds_strm (flush_pending X2))) <= length rest0)%nat) by (rewrite <- EF2, <- fbo_fp; exact (unbox _ ROOM)).
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ZS DOUT1.
  zstep.
  call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI0. } 1:{ rewrite ESP. exact PC. } 1:{ rewrite ESP. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact FP2. } 1:{ exact LB2. } 1:{ exact RAO2. } 1:{ exact RM2. } 1:{ reflexivity. }
  name_mem mC.
  lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKF end.
  lazymatch goal with H : DREP mC L _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DRF end.
  lazymatch goal with H : dout mC L rest0 _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DOUTF end.
  lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIF end.
  eapply HK.
  split; [exact DRF|]. split; [exact DOUTF|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| exact MIF].
Qed.
End SITE.
End Z_slow_fbA.


Module Z_slow_fbB.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Z_flushpend Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fbA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel DeflateSafe DeflateOverlay RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 RefDeflSafeLF RefDeflSafeFB.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section SITE.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmtE.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_fbB : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  flush_ok X 0 -> fb_entry X 0 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 0))) <= length rest0)%nat ->
  SK L flush rest0 lo r fj F fc me Q Z_SLOW_LTAIL (flush_block_only X 0) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a1d8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & FR & STK & MU & WM & MI) FOK FE LBS WSX RAO ROOM HK. unfold SK, Z_SLOW_LTAIL in HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 0); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 0 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 0 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & _).
  destruct (fbo2_facts X 0 FOK LBS RAO) as (FP2 & LB2 & RAO2 & ES2 & E1 & EO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  zs. zstep.
  eapply (evt_cut usegs (fun ms' => exists v10 v13 v14, ms' = MS (slowR L flush r x1 x5 x6 x7 v10 (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) (wz (fb_len X))
                                                                   v13 v14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a2d4) fc None m (seg_rom usegs))).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zstep. zs. rewrite ?Z.mod_small by lia. zstep. zstep. zstep.
      rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia. gF.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBN NEG).
      replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
        by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
      reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zs. zs. zstep. rewrite ?Z.mod_small by lia.
      replace (Z.land (ds_block_start X) 4294967295) with (ds_block_start X)
        by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      zstep. gF. zstep. zstep. zstep. gX.
      zs. rewrite ?Z.mod_small by lia. zstep. zstep. zstep.
      first [rewrite (sub_guard_pos (ds_strstart X) (ds_block_start X)) by lia | rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia]. gT.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBP POS).
      replace (wz (ds_strstart X - ds_block_start X)) with (wz (fb_len X)) by (f_equal; rewrite ELEN; reflexivity).
      reflexivity. }
  intros ms' (v10 & v13 & v14 & ->). unfold slowR.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  zstep. zstep. zstep.
  call (HTFBLK L X (fb_buf X) (fb_len X) 0 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. rewrite ESP. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact FE. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 0) with (fbo1 X 0) in POST.
  remember (fbo1 X 0) as X1 eqn:EX1.
  assert (DOUT1 : u8arr usegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. rewrite ?Z.mod_small by lia. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (EF2 : fbo2 X 0 = X2) by (rewrite EX2, EX1; reflexivity). rewrite EF2 in FP2, LB2, RAO2, ES2.
  assert (DR2 : DREP mB L X2).
  { split.
    - rewrite ES2. do 4 eexists. exact ZS.
    - rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  assert (DOUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES2; exact DOUT1).
  assert (RM2 : (length (cs_out_rev (ds_strm (flush_pending X2))) <= length rest0)%nat) by (rewrite <- EF2, <- fbo_fp; exact (unbox _ ROOM)).
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ZS DOUT1.
  zstep.
  call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI0. } 1:{ rewrite ESP. exact PC. } 1:{ rewrite ESP. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact FP2. } 1:{ exact LB2. } 1:{ exact RAO2. } 1:{ exact RM2. } 1:{ reflexivity. }
  name_mem mC.
  lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKF end.
  lazymatch goal with H : DREP mC L _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DRF end.
  lazymatch goal with H : dout mC L rest0 _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DOUTF end.
  lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIF end.
  eapply HK.
  split; [exact DRF|]. split; [exact DOUTF|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| exact MIF].
Qed.
End SITE.
End Z_slow_fbB.


Module Z_slow_fbC.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Z_flushpend Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_flushpend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fbA.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel DeflateSafe DeflateOverlay RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 RefDeflSafeLF RefDeflSafeFB.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section SITE.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmtE.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_fbC : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  flush_ok X 1 -> fb_entry X 1 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 1))) <= length rest0)%nat ->
  SK L flush rest0 lo r fj F fc me Q 0x1a4ec (flush_block_only X 1) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 (wz (ds_strstart X)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a434) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & FR & STK & MU & WM & MI) FOK FE LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 1); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 1 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 1 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & _).
  destruct (fbo2_facts X 1 FOK LBS RAO) as (FP2 & LB2 & RAO2 & ES2 & E1 & EO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  zs. zstep.
  eapply (evt_cut usegs (fun ms' => exists v10 v13 v14, ms' = MS (slowR L flush r x1 x5 x6 x7 v10 (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) (wz (fb_len X))
                                                                   v13 v14 x15 x16 x17 x28 x29 x30 x31) F (wz 0x1a4d0) fc None m (seg_rom usegs))).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. zstep.
      rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia. gF.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBN NEG).
      replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
        by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
      reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      zs. zs. zstep. rewrite ?Z.mod_small by lia.
      replace (Z.land (ds_block_start X) 4294967295) with (ds_block_start X)
        by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
      zstep. gF. zstep. zstep. zstep. gX.
      zstep. zstep. zstep.
      first [rewrite (sub_guard_pos (ds_strstart X) (ds_block_start X)) by lia | rewrite (sub_guard (ds_strstart X) (ds_block_start X)) by lia]. gT.
      apply evt_done. do 3 eexists. unfold slowR. rewrite (EBP POS).
      replace (wz (ds_strstart X - ds_block_start X)) with (wz (fb_len X)) by (f_equal; rewrite ELEN; reflexivity).
      reflexivity. }
  intros ms' (v10 & v13 & v14 & ->). unfold slowR.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  zstep. zstep. zstep.
  call (HTFBLK L X (fb_buf X) (fb_len X) 1 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. rewrite ESP. lia. }
  1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact FE. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 1) with (fbo1 X 1) in POST.
  remember (fbo1 X 1) as X1 eqn:EX1.
  assert (DOUT1 : u8arr usegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. rewrite ?Z.mod_small by lia. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (EF2 : fbo2 X 1 = X2) by (rewrite EX2, EX1; reflexivity). rewrite EF2 in FP2, LB2, RAO2, ES2.
  assert (DR2 : DREP mB L X2).
  { split.
    - rewrite ES2. do 4 eexists. exact ZS.
    - rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  assert (DOUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES2; exact DOUT1).
  assert (RM2 : (length (cs_out_rev (ds_strm (flush_pending X2))) <= length rest0)%nat) by (rewrite <- EF2, <- fbo_fp; exact (unbox _ ROOM)).
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ZS DOUT1.
  zstep.
  call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact DOUT2. } 1:{ exact MI0. } 1:{ rewrite ESP. exact PC. } 1:{ rewrite ESP. lia. }
  1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. }
  1:{ exact FP2. } 1:{ exact LB2. } 1:{ exact RAO2. } 1:{ exact RM2. } 1:{ reflexivity. }
  name_mem mC.
  lazymatch goal with H : stk usegs mC lo _ |- _ => rewrite ?ESP in H; rename H into STKF end.
  lazymatch goal with H : DREP mC L _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DRF end.
  lazymatch goal with H : dout mC L rest0 _ |- _ => rewrite <- EF2, <- fbo_fp in H; rename H into DOUTF end.
  lazymatch goal with H : mem_inv usegs mC |- _ => rename H into MIF end.
  eapply HK.
  split; [exact DRF|]. split; [exact DOUTF|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STKF|]. split; [exact MU|]. split; [exact WM| exact MIF].
Qed.
End SITE.
End Z_slow_fbC.


Module Z_slow_fill.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FILL.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmt.

Lemma slow_fill : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_ok 32768 32768 X flush -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  ds_insert X = 0 -> ds_wrap X <> 2 -> cs_avail_in (ds_strm X) <= 1 -> din_tie inp X ->
  - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  (forall X1, st_fill X flush = (X1, Some (LRet need_more)) -> SKret L flush rest0 lo r fj F fc me Q 0 X1) ->
  (forall X1, st_fill X flush = (X1, Some LBreak) -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_TAIL X1) ->
  (forall X1, st_fill X flush = (X1, None) -> 3 <= ds_lookahead X1 -> KH L flush rest0 lo r fj F fc me Q X1) ->
  (forall X1, st_fill X flush = (X1, None) -> ds_lookahead X1 < 3 -> KD L flush rest0 lo r fj F fc me Q (prev_st X1)) ->
  evt usegs Q (MS (slowR L flush r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) F (wz Z_SLOW_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) (RLA & FWOK & RLA1 & HOK) HFL INS WRAP AIN TIE RBS KRET KBRK KHASH KLO.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. apply box in SP16.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR, Z_SLOW_HEAD. unfold slow_frame in FR. unfold slow_W in MU. unfold KH, SK, Z_SLOW_HASH in KHASH. unfold KD, Z_SLOW_DECIDE in KLO.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  change MIN_LOOKAHEAD with 262 in *. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  zs. zstep.
  if_cases KLA; zify_cond KLA; rewrite ?unsigned_lit in KLA by lia.
  -
    assert (EF : st_fill X flush = (X, None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    unfold slowR in KHASH. eapply (KHASH X EF ltac:(lia)).
    split; [exact DR0|]. split; [exact DOUT|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  -
    assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
    pose proof (fill_window_keep X) as KEEP. unfold fw_keep in KEEP.
    assert (EO : cs_out_rev (ds_strm (fill_window X)) = cs_out_rev (ds_strm X)) by (decompose [and] KEEP; assumption).
    clear KEEP.
    pose proof (unbox _ ROOM) as OL0.
    unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) OL0) as OL.
    clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
    zstep. zstep.
    call (HFW L X inp (Z.of_nat (length rest0)) lo).
    1:{ exact DR0. } 1:{ apply (slow_din L inp rest0 lo r me CTX). unfold slow_W. exact MU. } 1:{ exact TIE. } 1:{ exact MI. }
    1:{ rewrite ESP. exact STK. } 1:{ unfold Z_FILLWIN_STACK. rewrite ESP. lia. } 1:{ rewrite ESP. pose proof (unbox _ SP16). clear - H RSP LOsp. Z.div_mod_to_equations. lia. }
    1:{ unfold dlay_below. rewrite ESP. lia. } 1:{ exact IO. } 1:{ apply FWOK. lia. } 1:{ exact INS. } 1:{ exact WRAP. } 1:{ exact AIN. } 1:{ exact RBS. } 1:{ reflexivity. }
    name_mem mA.
    lazymatch goal with H : stk usegs mA lo _ |- _ => rewrite ?ESP in H; rename H into STK1 end.
    lazymatch goal with H : DREP _ _ (fill_window X) |- _ => rename H into DR1 end.
    lazymatch goal with H : mem_inv usegs mA |- _ => rename H into MI1 end.
    assert (SI1 : SINV L flush rest0 lo r fj me (fill_window X) mA).
    { split; [exact DR1|]. split; [unfold dout, outv; rewrite EO; exact DOUT|]. split; [rewrite EO; exact ROOM|].
      split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| exact MI1]. }
    remember (fill_window X) as X1 eqn:EX1.
    assert (EFm : st_fill X flush = (X1, if (ds_lookahead X1 <? 262) && (flush =? Z_NO_FLUSH) then Some (LRet need_more)
                                        else if ds_lookahead X1 =? 0 then Some LBreak else None)).
    { unfold st_fill. change MIN_LOOKAHEAD with 262. replace (ds_lookahead X <? 262) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite <- EX1. destruct (_ && _); [reflexivity|]. destruct (_ =? 0); reflexivity. }
    rewrite EFm in RLA1. cbn [fst] in RLA1.
    destruct DR1 as [ZS ST]. open_DST ST. open_A GA.
    clear DR0 DOUT OL OL0 EO.
    zs.
    unfold Z_NO_FLUSH, Z_FINISH in *.
    assert (CONT : (ds_lookahead X1 <? 262) && (flush =? 0) = false ->
      forall a1 a5 a6 a7 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31,
      evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 (wz (ds_lookahead X1)) a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31)
          F (wz 0x19d30) fc None mA (seg_rom usegs))).
    { intros EC. intros. unfold slowR. rewrite EC in EFm.
      zstep. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
      -
        replace (ds_lookahead X1 =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        unfold SK in KBRK. eapply (KBRK X1 EFm). exact SI1.
      - replace (ds_lookahead X1 =? 0) with false in EFm by (symmetry; apply Z.eqb_neq; lia).
        assert (Hsnd : snd (st_fill X flush) = None) by (rewrite EFm; reflexivity).
        pose proof (proj1 (HOK Hsnd)) as SV1. rewrite EFm in SV1. cbn [fst] in SV1. clear Hsnd.
        pose proof (si_ml _ SV1) as Rml. pose proof (si_ms _ SV1) as Rms.
        zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
        +
          pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
          destruct SI1 as (_ & DOUT1 & ROOM1 & _).
          zstep. zs. zs. zstep. zs. zs. zs. name_mem mB.
          zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; [| exfalso; lia].
          tr_groups MUf WMf.
          unfold slowR in KLO. replace (wz 2) with (wz (ds_match_length (prev_st X1))) by reflexivity.
          eapply (KLO X1 EFm ltac:(lia)).
          split; [split|].
          * exact ZS.
          * unfold prev_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac; apply le4_sx32_wz; lia]
                 | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS0 | exact LAY1].
          * split; [apply (dout_munch _ mA mB L rest0 _ DOUT1 ROOM1 MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM1|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| eassumption].
        +
          unfold slowR in KHASH. eapply (KHASH X1 EFm ltac:(lia)). exact SI1. }
    zstep. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
    +
      eapply CONT. replace (flush =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
    + zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      *
        replace (flush =? 0) with true in EFm by (symmetry; apply Z.eqb_eq; lia).
        replace (ds_lookahead X1 <? 262) with true in EFm by (symmetry; apply Z.ltb_lt; lia).
        zstep. zstep. unfold SKret, Z_SLOW_EPI, slowR in KRET. eapply (KRET X1 EFm). exact SI1.
      * eapply CONT. replace (ds_lookahead X1 <? 262) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

End FILL.
End Z_slow_fill.


Module Z_slow_hash.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_lmatch Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel LmatchModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HASH.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Definition KLM (Q : machine_state -> Prop) (s : deflate_state) (hh : Z) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me s m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz 2) (wz hh) (wz (ds_prev_length s)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x19e20) fc None m' (seg_rom usegs)).

Lemma slow_hash : forall (Q : machine_state -> Prop) (X : deflate_state),
  strip_inv X -> 3 <= ds_lookahead X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 ->
  KLM Q (hash_st X) (hash_hh X) ->
  KH L flush rest0 lo r fj F fc me Q X.
Proof.
  intros Q X SV LA3 WS HS HK. unfold KH, SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_u16 Gprev. open_u16 Ghead.
  pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_h _ LAY) as BKh. unfold blk_ok in BKh. pose proof (lo_p _ LAY) as BKp. unfold blk_ok in BKp.
  unfold slowR, Z_SLOW_HASH. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. gF. zs. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
  zs.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 2) ltac:(apply Rwb; lia).
  zs. zs. zs. zs. zs.
  rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) by lia.
  pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)) ltac:(lia)) as Rhv.
  remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) as h eqn:Eh.
  zstep. zstep. rewrite (shl32_shr31 h) by lia. zstep. zs.
  gF. zstep. zstep. zstep. gX. gF. zstep.
  assert (ALh : (dl_Ah L + 2 * h) mod 2 = 0) by (clear - BKh Rhv; Z.div_mod_to_equations; lia).
  first [rewrite (land1_mod2 _ ALh) | replace (2 * h + dl_Ah L) with (dl_Ah L + 2 * h) by lia; rewrite (land1_mod2 _ ALh)]. gF.
  zs. zs. zstep. zstep. zstep.
  rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X)), ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite ?(Z.mul_comm _ 2).
  pose proof (LmatchModel.land_upper_both (ds_strstart X) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
  remember (Z.land (ds_strstart X) (ds_w_mask X)) as pi eqn:Epi.
  gF. zstep. zstep. zstep. gX. gF. zstep.
  assert (ALp : (dl_Ap L + 2 * pi) mod 2 = 0) by (clear - BKp Rpi; Z.div_mod_to_equations; lia).
  first [rewrite (land1_mod2 _ ALp) | replace (2 * pi + dl_Ap L) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp) | replace (dl_Ap L + pi * 2) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp)]. gF.
  ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
  st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
  gF.
  st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
  zstep.
  zs. zs. rewrite (sx32_wz (ds_match_length X)) by lia. zstep. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  subst h pi. unfold KLM in HK. unfold slowR in HK.
  replace (wz (ds_match_length X)) with (wz (ds_prev_length (hash_st X))) by reflexivity.
  change (arr_get (ds_head X) (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)))) with (hash_hh X).
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold hash_st, ins_str. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac; apply le4_sx32_wz; lia]
      | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_lm : forall (Q : machine_state -> Prop) (s : deflate_state) (hh : Z),
  0 <= ds_prev_length s <= 258 -> 0 <= ds_max_lazy_match s < 2^31 -> ds_w_size s = 32768 -> 0 <= ds_strstart s <= 65536 ->
  ds_match_length s = 2 -> 0 <= hh < 65536 -> 0 <= ds_strategy s <= 4 ->
  (sl_lm_cond s hh = true -> lm_ok s hh) -> strip_inv (st_lm s hh) ->
  KD L flush rest0 lo r fj F fc me Q (st_lm s hh) ->
  KLM Q s hh.
Proof.
  intros Q s hh Rpl Rlazy WS Rss ML2 Rhh Rstrat LMOK SVF HK. unfold KLM. intros until m'. intros SI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KD in HK. unfold slowR in *. unfold Z_SLOW_DECIDE in HK.
  pose proof SI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  unfold slow_frame in FR. unfold slow_W in MU.
  assert (RWS : 0 <= ds_w_size s < 2^31) by lia.
  zstep. if_cases KH0; zify_cond KH0; rewrite ?unsigned_lit in KH0 by lia.
  -
    assert (EST : st_lm s hh = s) by (apply st_lm_false; unfold sl_lm_cond; replace (hh =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
    rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
  - zs. zstep. if_cases KLZ; zify_cond KLZ; rewrite ?unsigned_lit in KLZ by lia.
    +
      assert (EST : st_lm s hh = s).
      { apply st_lm_false. unfold sl_lm_cond. replace (ds_prev_length s <? ds_max_lazy_match s) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity. }
      rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
    + zs. zs. zs. zs. zstep.
      if_cases KD0; zify_cond KD0; rewrite ?WS in KD0.
      *
        assert (EST : st_lm s hh = s).
        { apply st_lm_false. unfold sl_lm_cond. rewrite WS.
          replace (wrap32 (ds_strstart s - hh) <=? 32768 - 262) with false; [rewrite andb_false_r; reflexivity|].
          symmetry. apply Z.leb_gt. rewrite wrap32_mod. change (2^32) with 4294967296.
          Z.div_mod_to_equations. lia. }
        rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
      * assert (CND : sl_lm_cond s hh = true).
        { unfold sl_lm_cond. rewrite WS.
          replace (hh =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          replace (ds_prev_length s <? ds_max_lazy_match s) with true by (symmetry; apply Z.ltb_lt; lia).
          replace (wrap32 (ds_strstart s - hh) <=? 32768 - 262) with true; [reflexivity|].
          symmetry. apply Z.leb_le. rewrite wrap32_mod. change (2^32) with 4294967296.
          Z.div_mod_to_equations. lia. }
        pose proof (LMOK CND) as LM.
        assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
        pose proof SI as (DR0 & _). destruct DR0 as [_ ST0].
        name_mem mA.
        pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -128); (dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
        clear GA.
        zstep. zstep.
        call (longest_match_spec L s hh lo).
        1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
        1:{ exact LM. } 1:{ exact WS. } 1:{ reflexivity. } 1:{ reflexivity. }
        name_mem mB.
        lazymatch goal with H : stk usegs mB lo _ |- _ => rewrite ?ESP in H; rename H into STK1 end.
        lazymatch goal with H : DST mB L _ |- _ => rename H into POST end.
        lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
        assert (Rrl : 0 <= snd (longest_match s hh) <= 258) by (unfold lm_ok in LM; decompose [and] LM; lia).
        destruct (longest_match_ms s hh) as (ms & Ems).
        pose proof (st_lm_true s hh CND) as EST. cbv zeta in EST. rewrite Ems in EST, POST.
        remember (snd (longest_match s hh)) as rl eqn:Erl. clear Erl Ems.
        rewrite sl_filter_eq in EST.
        assert (Rms : 0 <= ms < 2^32) by (pose proof (si_ms _ SVF) as R0; rewrite EST in R0; destruct (_ && _) in R0; exact R0).
        destruct POST as [GA' GB' GC' GD' Glt' Gdt' Gbt' Gblc' Gheap' Gdep' Gwin' Gprev' Ghead' Gpend' LENS' LAY'].
        clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ST0 LENS LAY1.
        tr_groups MUf WMf.
        assert (DOUTB : dout mB L rest0 (ds_strm s)) by (apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
        clear MUf WMf DOUT.
        open_A GA'. dsred in GA'.
        pose proof (munch_refl [(dl_As L, dl_As L + 212)] mB) as MUf. pose proof (wmono_refl usegs mB) as WMf.
        zs. name_mem mC.
        tr_groups MUf WMf.
        assert (DOUTC : dout mC L rest0 (ds_strm s)) by (apply (dout_munch _ mB mC L rest0 _ DOUTB ROOM MUf WMf); cbn [disjoint_from]; slia).
        clear MUf WMf DOUTB.
        remember (set_match_length (set_match_start s ms) rl) as s1 eqn:Es1.
        assert (SI1 : SINV L flush rest0 lo r fj me s1 mC).
        { rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTC|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| exact MI1]. }
        assert (C550 : (rl <=? 5) && ((ds_strategy s =? 1) || (rl =? 3) && (4096 <? wrap32 (ds_strstart s - ms))) = true ->
          forall (a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31 : word),
          evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31) F (wz 0x19e60) fc None mC (seg_rom usegs))).
        { intros CT. intros. unfold slowR. rewrite CT in EST.
          pose proof (munch_refl [(dl_As L, dl_As L + 212)] mC) as MUf. pose proof (wmono_refl usegs mC) as WMf.
          zstep. zs. name_mem mD. zstep.
          tr_groups MUf WMf.
          assert (DOUTD : dout mD L rest0 (ds_strm s)) by (apply (dout_munch _ mC mD L rest0 _ DOUTC ROOM MUf WMf); cbn [disjoint_from]; slia).
          rewrite EST in HK. replace (wz 2) with (wz (ds_match_length (set_match_length s1 2))) at 1 by reflexivity.
          eapply HK.
          rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTD|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        pose proof (si_strat _ SVF) as Rst0.
        zstep. zstep. if_cases KF1; zify_cond KF1; rewrite ?unsigned_lit in KF1 by lia.
        --
           replace (rl <=? 5) with false in EST by (symmetry; apply Z.leb_gt; lia). cbn [andb] in EST.
           rewrite EST in HK. rewrite Es1 in HK. replace (wz rl) with (wz (ds_match_length (set_match_length (set_match_start s ms) rl))) by reflexivity.
           eapply HK. rewrite <- Es1. exact SI1.
        -- zs. zstep. zstep. if_cases KF2; zify_cond KF2; rewrite ?unsigned_lit in KF2 by lia.
           ++
              zstep. if_cases KF3; zify_cond KF3; rewrite ?unsigned_lit in KF3 by lia.
              **
                 replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 replace (rl =? 3) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 cbn [andb orb] in EST. rewrite andb_false_r in EST.
                 rewrite EST in HK. rewrite Es1 in HK. replace (wz rl) with (wz (ds_match_length (set_match_length (set_match_start s ms) rl))) by reflexivity.
                 eapply HK. rewrite <- Es1. exact SI1.
              **
                 zs. zs. zs. zs. zstep.
                 if_cases KF4; zify_cond KF4.
                 ---
                     eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
                     replace (rl =? 3) with true by (symmetry; apply Z.eqb_eq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with true; [rewrite orb_true_r; reflexivity|].
                     symmetry. apply Z.ltb_lt. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia.
                 --- zstep.
                     replace (rl <=? 5) with true in EST by (symmetry; apply Z.leb_le; lia).
                     replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with false in EST.
                     2:{ symmetry. apply Z.ltb_ge. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia. }
                     rewrite andb_false_r in EST. cbn [andb orb] in EST.
                     assert (E3 : rl = 3) by lia. subst rl.
                     rewrite EST in HK. rewrite Es1 in HK. replace (wz 3) with (wz (ds_match_length (set_match_length (set_match_start s ms) 3))) at 1 by reflexivity.
                     eapply HK. rewrite <- Es1. exact SI1.
           ++
              eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
              replace (ds_strategy s =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
Qed.
End HASH.
End Z_slow_hash.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_slow_dist.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_slow_dist.

Module Z_slow_lit.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section LIT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Ltac sym_step := zs; zs.
Ltac sym_guards := zstep; zstep; zs; gF; zstep; zstep; zstep; gX; gF.

Lemma slow_tlit : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> 1 <= ds_strstart X -> ds_strstart X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (ds_sym_next X + 3 <> ds_sym_end X -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_LTAIL (slit1 X)) ->
  (ds_sym_next X + 3 = ds_sym_end X -> SK L flush rest0 lo r fj F fc me Q 0x1a1d8 (slit1 X)) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a0f0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) SV SS1 SS2 WS LBS K1 K2.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold SK, Z_SLOW_LTAIL, slowR in K1, K2.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
  sym_step.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + -1) ltac:(apply Rwb; lia).
  pose proof (Rwb (ds_strstart X + -1) ltac:(lia)) as Rc.
  sym_guards.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  remember (arr_get (ds_window X) (ds_strstart X + -1)) as c eqn:Ec.
  assert (Ewc : wrap8 c = c) by (apply wrap8_id; lia).
  zstep.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 c)) ltac:(rewrite unsigned_lit by lia; rewrite !Ewc; reflexivity).
  rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  gF. zstep.
  replace (wz (dl_As L + 212 + c * 4)) with (wz (dl_As L + 212 + 4 * c)) by (f_equal; lia).
  pose proof (u16arr_read usegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * wrap8 c)
                (wz (arr_get (ds_dyn_ltree_fc X) (wrap8 c))) (wa (dl_As L + 212 + 4 * c)) Glt
                (avct_nth_fc _ _ 573 (wrap8 c) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zstep.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r fj me (slit1 X) mB).
  { subst c. unfold slit1. cbv zeta. replace (ds_strstart X - 1) with (ds_strstart X + -1) by lia.
    split; [split|].
    - exact ZS.
    - constructor; [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (K1 ltac:(lia)). exact SI'.
  - eapply (K2 ltac:(lia)). exact SI'.
Qed.
End LIT.
End Z_slow_lit.


Module Z_slow_litT.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section LITT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Ltac sym_step := zs; zs.
Ltac sym_guards := zstep; zstep; zs; gF; zstep; zstep; zstep; gX; gF.

Lemma slow_tlitT : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> 1 <= ds_strstart X -> ds_strstart X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  SK L flush rest0 lo r fj F fc me Q 0x1a414 (break1_st X) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a334) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) SV SS1 SS2 WS LBS HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold SK, slowR in HK.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
  sym_step.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + -1) ltac:(apply Rwb; lia).
  pose proof (Rwb (ds_strstart X + -1) ltac:(lia)) as Rc.
  sym_guards.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0) ltac:(reflexivity).
  sym_step. sym_guards.
  remember (arr_get (ds_window X) (ds_strstart X + -1)) as c eqn:Ec.
  assert (Ewc : wrap8 c = c) by (apply wrap8_id; lia).
  zstep.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 c)) ltac:(rewrite unsigned_lit by lia; rewrite !Ewc; reflexivity).
  rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  gF. zstep.
  replace (wz (dl_As L + 212 + c * 4)) with (wz (dl_As L + 212 + 4 * c)) by (f_equal; lia).
  pose proof (u16arr_read usegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * wrap8 c)
                (wz (arr_get (ds_dyn_ltree_fc X) (wrap8 c))) (wa (dl_As L + 212 + 4 * c)) Glt
                (avct_nth_fc _ _ 573 (wrap8 c) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zstep.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  zs. name_mem mB.
  tr_groups MUf WMf.
  eapply HK.
  subst c. unfold break1_st, slit1. cbv zeta. replace (ds_strstart X - 1) with (ds_strstart X + -1) by lia.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End LITT.
End Z_slow_litT.


Module Z_slow_misc.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section MISC.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_avail : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= ds_strstart X < 2^31 -> 0 <= ds_lookahead X < 2^31 ->
  SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD (avail0_st X) ->
  SK L flush rest0 lo r fj F fc me Q Z_SLOW_AVAIL X.
Proof.
  intros Q X Rss Rla HK. unfold SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR, Z_SLOW_AVAIL. unfold slow_frame in FR. unfold slow_W in MU. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  do 8 zs. name_mem mB.
  tr_groups MUf WMf.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold avail0_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_ltail : forall (Q : machine_state -> Prop) (Y : deflate_state),
  0 <= ds_strstart Y < 2^31 -> 0 <= ds_lookahead Y < 2^31 -> 0 <= cs_avail_out (ds_strm Y) < 2^31 ->
  (cs_avail_out (ds_strm Y) = 0 -> SKret L flush rest0 lo r fj F fc me Q 0 (ltail_st Y)) ->
  (cs_avail_out (ds_strm Y) <> 0 -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD (ltail_st Y)) ->
  SK L flush rest0 lo r fj F fc me Q Z_SLOW_LTAIL Y.
Proof.
  intros Q Y Rss Rla Rao KR KH0. unfold SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0. pose proof (lo_S _ LAY) as BKS.
  unfold slowR, Z_SLOW_LTAIL. unfold slow_frame in FR. unfold slow_W in MU. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  do 7 zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r fj me (ltail_st Y) mB).
  { split; [split|].
    - do 4 eexists. exact ZS.
    - unfold ltail_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  gF. zstep. al8 (dl_S L). gF.
  zs. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold Z_SLOW_HEAD in KH0. eapply (KH0 KB). exact SI'.
  - zstep. unfold SKret in KR. unfold Z_SLOW_EPI, slowR in KR.
    replace (wz (cs_avail_out (ds_strm Y))) with (wz 0) by (f_equal; lia).
    eapply (KR KB). exact SI'.
Qed.

Lemma slow_aexit : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 ->
  (cs_avail_out (ds_strm Z0) = 0 -> SKret L flush rest0 lo r fj F fc me Q 0 Z0) ->
  (cs_avail_out (ds_strm Z0) <> 0 -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD Z0) ->
  SK L flush rest0 lo r fj F fc me Q 0x1a2b0 Z0.
Proof.
  intros Q Z0 Rao KR KH0. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  pose proof (sc_lay _ _ _ _ _ _ CTX) as LAY. lay_open LAY. pose proof (lo_S _ LAY) as BKS.
  open_zs ZS. open_A GA. unfold slowR. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  zs. gT. zstep. al8 (dl_S L). gF.
  zs. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold Z_SLOW_HEAD in KH0. eapply (KH0 KB). exact SI.
  - zstep. unfold SKret in KR. unfold Z_SLOW_EPI, slowR in KR.
    replace (wz (cs_avail_out (ds_strm Z0))) with (wz 0) by (f_equal; lia).
    eapply (KR KB). exact SI.
Qed.

Lemma slow_fin : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 -> ds_wrap Z0 <> 0 -> - 2^31 <= ds_wrap Z0 < 2^31 ->
  SKret L flush rest0 lo r fj F fc me Q (if cs_avail_out (ds_strm Z0) =? 0 then 2 else 3) Z0 ->
  SK L flush rest0 lo r fj F fc me Q 0x1a4ec Z0.
Proof.
  intros Q Z0 Rao W0 Rw KR. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  pose proof (sc_lay _ _ _ _ _ _ CTX) as LAY. lay_open LAY. pose proof (lo_S _ LAY) as BKS.
  open_zs ZS. open_A GA. unfold slowR. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  unfold SKret in KR. unfold Z_SLOW_EPI, slowR in KR.
  zs. gF. zstep. al8 (dl_S L). gF.
  (* 1.4 UBSan: FLUSH_BLOCK(s, 1)'s return reads avail_out, then pending and wrap: finish_started (2) unless all three
     allow finish_done (3); wrap <> 0 here, so avail_out = 0 gives 2 *)
  zs. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - replace (cs_avail_out (ds_strm Z0) =? 0) with true in KR by (symmetry; apply Z.eqb_eq; lia).
    zs. zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + eapply KR. exact SI.
    + zs. zstep. if_cases K3; zify_cond K3.
      * eapply KR. exact SI.
      * exfalso. apply W0. Z.div_mod_to_equations. lia.
  - replace (cs_avail_out (ds_strm Z0) =? 0) with false in KR by (symmetry; apply Z.eqb_neq; lia).
    zs. zstep. eapply KR. exact SI.
Qed.

Lemma slow_tail2 : forall (Q : machine_state -> Prop) (Y : deflate_state),
  0 <= ds_strstart Y <= 65536 -> flush = Z_FINISH ->
  (forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me (tail_st Y) m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart (tail_st Y))) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a434) fc None m' (seg_rom usegs))) ->
  SK L flush rest0 lo r fj F fc me Q 0x1a414 Y.
Proof.
  intros Q Y Rss HF HK. unfold SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold Z_FINISH in HF. subst flush.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zstep. zstep. zstep.
  eapply (evt_cut usegs (fun ms' => ms' = MS (slowR L 4 r y1 y5 y6 y7 (wz (ds_strstart Y)) (wz (if ds_strstart Y <? 2 then ds_strstart Y else 2)) (wz 2)
                                                  y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a428) fc None mA (seg_rom usegs))).
  { if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    - apply evt_done. unfold slowR. replace (ds_strstart Y <? 2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - zstep. apply evt_done. unfold slowR. replace (ds_strstart Y <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  intros ms' ->. unfold slowR.
  assert (Rins : 0 <= (if ds_strstart Y <? 2 then ds_strstart Y else 2) <= 2) by (destruct (Z.ltb_spec (ds_strstart Y) 2); lia).
  zstep. zs. name_mem mB. zstep.
  if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia; [exfalso; lia|].
  tr_groups MUf WMf.
  replace (wz (ds_strstart Y)) with (wz (ds_strstart (tail_st Y))) by reflexivity.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold tail_st. change (MIN_MATCH - 1) with 2. constructor; [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_decide : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= ds_prev_length X <= 258 -> 0 <= ds_match_length X <= 258 -> 0 <= ds_match_available X <= 1 ->
  (dist_cond X = true ->
   forall (y1 y5 y6 y7 y11 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me X m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_match_length X)) y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x19e94) fc None m' (seg_rom usegs))) ->
  (dist_cond X = false -> ds_match_available X <> 0 -> SK L flush rest0 lo r fj F fc me Q 0x1a0f0 X) ->
  (dist_cond X = false -> ds_match_available X = 0 -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_AVAIL X) ->
  KD L flush rest0 lo r fj F fc me Q X.
Proof.
  intros Q X Rpl Rml Rma KDI KLI KAV. unfold KD. intros until m'. intros SI. unfold slowR, Z_SLOW_DECIDE.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  assert (C70C : dist_cond X = false ->
    forall (a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31 : word),
    evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31) F (wz 0x1a0e8) fc None m' (seg_rom usegs))).
  { intros DC. intros. pose proof SI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    unfold slowR. zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
    - unfold SK, Z_SLOW_AVAIL in KAV. eapply (KAV DC KM). exact SI.
    - eapply (KLI DC KM). exact SI. }
  pose proof SI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  zs. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  - eapply C70C. unfold dist_cond. replace (3 <=? ds_prev_length X) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + eapply C70C. unfold dist_cond. replace (ds_match_length X <=? ds_prev_length X) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
    + eapply KDI; [|exact SI]. unfold dist_cond. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
End MISC.
End Z_slow_misc.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_frame OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fbA OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fbB OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fbC OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_fill OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_hash OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_dist.Z_slow_dist2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_dist OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_lit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_litT OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow.Z_slow_misc OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma st_bflush_true : forall s,
  st_bflush s true = (flush_block_only s 0, if cs_avail_out (ds_strm (flush_block_only s 0)) =? 0 then LRet need_more else LCont).
Proof. intros s. unfold st_bflush, flush_block. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof. reflexivity. Qed.

Lemma fst_pr : forall {A B} (a : A) (b : B), fst (a, b) = a. Proof. reflexivity. Qed.
Lemma snd_pr : forall {A B} (a : A) (b : B), snd (a, b) = b. Proof. reflexivity. Qed.

Lemma deflate_tail_finish_eq : forall t,
  deflate_tail t Z_FINISH = (flush_block_only t 1, if cs_avail_out (ds_strm (flush_block_only t 1)) =? 0 then finish_started else finish_done).
Proof. intros t. unfold deflate_tail, flush_block. change (Z_FINISH =? Z_FINISH) with true. cbv iota zeta. destruct (_ =? 0); reflexivity. Qed.

Section SLOW.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmt.
Hypothesis HTFBLK : tr_flush_block_stmtE.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Local Notation SKq := (SK L flush rest0 lo r fj F fc me).
Local Notation SKr := (SKret L flush rest0 lo r fj F fc me).
Local Notation ROOM s := (Box (OUT s <= length rest0)%nat).

Lemma room_OUT : forall s, ROOM s -> (length (cs_out_rev (ds_strm s)) <= length rest0)%nat.
Proof. intros s [H]. exact H. Qed.

Lemma slow_dec : forall (Q : machine_state -> Prop) (X4 : deflate_state),
  SCFG inp X4 -> sdec_ok 32768 X4 -> sdec_fe X4 -> ROOM (fst (st_decide X4)) ->
  (snd (st_decide X4) = LCont -> SKq Q Z_SLOW_HEAD (fst (st_decide X4))) ->
  (forall bs, snd (st_decide X4) = LRet bs -> SKr Q (bs_code bs) (fst (st_decide X4))) ->
  KD L flush rest0 lo r fj F fc me Q X4.
Proof.
  intros Q X4 C (SV & RLA & D) [FED FEL] RM KC KR.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  pose proof C as [Cws Chs Clbs Cins Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  apply (slow_decide L flush rest0 lo r fj F fc me HFL); [exact Rpl| exact Rml| exact Rma| | |].
  -
    intros DC. rewrite DC in D. pose proof D as (PLLA & SL3 & DD & RLA' & FOK).
    pose proof (SCFG_SF _ _ _ (SF_st_sdist' X4) C) as C'.
    assert (ED : st_decide X4 = st_bflush (fst (st_sdist X4)) (snd (st_sdist X4))) by (unfold st_decide; rewrite DC; reflexivity).
    rewrite ED in RM, KC, KR. clear ED.
    intros until m'. intros SI.
    eapply (slow_dist L flush inp rest0 lo r fj F fc me CTX HFL Q X4); [exact SI| exact SV| exact DC| exact D| lia| exact Cws| exact Chs| exact Clbs| |].
    + intros B. rewrite B in KC. rewrite st_bflush_false in KC. rewrite fst_pr, snd_pr in KC. exact (KC eq_refl).
    + intros B. specialize (FOK B). pose proof (FED DC B) as FE. rewrite B in RM, KC, KR. rewrite st_bflush_true in RM, KC, KR. rewrite ?fst_pr, ?snd_pr in RM, KC, KR.
      pose proof (SCFG_fbo _ _ _ C' FOK) as CF.
      unfold KA. intros until m'0. intros SI'.
      eapply (slow_fbA L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI'| exact FOK| exact FE| exact (c_lbs _ _ C')| exact (c_ws _ _ C')| exact (c_aout _ _ C')| exact (room_OUT _ RM)|].
      apply (slow_aexit L flush inp rest0 lo r fj F fc me CTX); [exact (c_aout _ _ CF)| |].
      * intros A0. rewrite A0 in KR. exact (KR need_more eq_refl).
      * intros A0. replace (cs_avail_out (ds_strm (flush_block_only (fst (st_sdist X4)) 0)) =? 0) with false in KC by (symmetry; apply Z.eqb_neq; exact A0).
        exact (KC eq_refl).
  -
    intros DC MA. rewrite DC in D. replace (negb (ds_match_available X4 =? 0)) with true in D by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MA).
    destruct D as (SS1 & FOK & S2).
    unfold st_decide in RM, KC, KR. rewrite DC in RM, KC, KR.
    replace (negb (ds_match_available X4 =? 0)) with true in RM, KC, KR by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact MA).
    rewrite st_slit_eq in RM, KC, KR. cbv zeta in RM, KC, KR, S2. cbn [fst snd] in RM, KC, KR.
    pose proof (SCFG_SF _ _ _ (SF_slit1 X4) C) as C1.
    assert (LT : forall Y, SCFG inp Y -> 0 <= ds_strstart Y -> 1 <= ds_lookahead Y -> ds_strstart Y + ds_lookahead Y <= 2 * 32768 ->
              ROOM (ltail_st Y) ->
              ((if cs_avail_out (ds_strm (ltail_st Y)) =? 0 then LRet need_more else LCont) = LCont -> SKq Q Z_SLOW_HEAD (ltail_st Y)) ->
              (forall bs, (if cs_avail_out (ds_strm (ltail_st Y)) =? 0 then LRet need_more else LCont) = LRet bs -> SKr Q (bs_code bs) (ltail_st Y)) ->
              SKq Q Z_SLOW_LTAIL Y).
    { intros Y CY Y1 Y2 Y3 RY KCY KRY. apply (slow_ltail L flush inp rest0 lo r fj F fc me CTX Q Y); [lia| lia| exact (c_aout _ _ CY)| |].
      - intros A0. replace (cs_avail_out (ds_strm (ltail_st Y))) with (cs_avail_out (ds_strm Y)) in KRY by reflexivity.
        rewrite A0 in KRY. exact (KRY need_more eq_refl).
      - intros A0. replace (cs_avail_out (ds_strm (ltail_st Y))) with (cs_avail_out (ds_strm Y)) in KCY by reflexivity.
        replace (cs_avail_out (ds_strm Y) =? 0) with false in KCY by (symmetry; apply Z.eqb_neq; exact A0). exact (KCY eq_refl). }
    intros until m'. intros SI.
    eapply (slow_tlit L flush inp rest0 lo r fj F fc me CTX Q X4); [exact SI| exact SV| exact SS1| lia| exact Cws| exact Clbs| |].
    + intros B. apply Z.eqb_neq in B. rewrite B in RM, KC, KR, S2. destruct S2 as (Y1 & Y2 & Y3).
      apply LT; [exact C1| exact Y1| exact Y2| exact Y3| exact RM| exact KC| exact KR].
    + intros B. apply Z.eqb_eq in B. pose proof (FEL DC MA B) as FE. rewrite B in RM, KC, KR, S2. destruct S2 as (Y1 & Y2 & Y3). specialize (FOK B).
      pose proof (SCFG_fbo _ _ _ C1 FOK) as CF.
      intros until m'0. intros SI'.
      eapply (slow_fbB L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI'| exact FOK| exact FE| exact (c_lbs _ _ C1)| exact (c_ws _ _ C1)| exact (c_aout _ _ C1)| |].
      * apply room_OUT. destruct RM as [RM]. constructor. rewrite (OUT_SF _ _ (SF_ltail_st _)) in RM. exact RM.
      * apply LT; [exact CF| exact Y1| exact Y2| exact Y3| exact RM| exact KC| exact KR].
  -
    intros DC MA. unfold st_decide in RM, KC, KR. rewrite DC in RM, KC, KR.
    replace (negb (ds_match_available X4 =? 0)) with false in RM, KC, KR by (symmetry; apply negb_false_iff; apply Z.eqb_eq; exact MA).
    rewrite st_avail_eq in RM, KC, KR. cbn [fst snd] in RM, KC, KR.
    apply (slow_avail L flush inp rest0 lo r fj F fc me CTX Q X4); [lia| lia| exact (KC eq_refl)].
Qed.

Lemma slow_trip : forall (Q : machine_state -> Prop) (X : deflate_state),
  SCFG inp X -> strip_ok 32768 32768 X flush -> - 2 ^ 62 <= ds_block_start X < 2 ^ 62 -> strip_fe X flush -> ROOM (fst (st_sbody X flush)) ->
  (snd (st_sbody X flush) = LCont -> SKq Q Z_SLOW_HEAD (fst (st_sbody X flush))) ->
  (snd (st_sbody X flush) = LBreak -> SKq Q Z_SLOW_TAIL (fst (st_sbody X flush))) ->
  (forall bs, snd (st_sbody X flush) = LRet bs -> SKr Q (bs_code bs) (fst (st_sbody X flush))) ->
  SKq Q Z_SLOW_HEAD X.
Proof.
  intros Q X C TOK RBS SFE RM KC KB KR. pose proof TOK as (_ & FW & _ & HOK). unfold strip_fe in SFE.
  destruct (fill_frame inp X flush C FW) as [CF1 _].
  pose proof C as [Cws Chs Clbs Cins Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  unfold SK. intros until m'. intros SI.
  eapply (slow_fill L flush inp rest0 lo r fj F fc me CTX HFW Q X); [exact SI| exact TOK| exact HFL| exact Cins| exact Cwrap| exact Cain| exact Ctie| exact RBS| | | |].
  -
    intros X1 EF.
    assert (ES : st_sbody X flush = (X1, LRet need_more)) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite ES in KR. rewrite fst_pr, snd_pr in KR. exact (KR need_more eq_refl).
  -
    intros X1 EF.
    assert (ES : st_sbody X flush = (X1, LBreak)) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite ES in KB. rewrite fst_pr, snd_pr in KB. exact (KB eq_refl).
  -
    intros X1 EF LA3.
    assert (ES : st_sbody X flush = st_srest X1) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite (st_srest_hi X1 LA3) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1, SFE. rewrite fst_pr in CF1. rewrite fst_pr, snd_pr in HOK, SFE.
    destruct (shash_ok_hi _ _ (HOK eq_refl) LA3) as (SV1 & RLA1 & LMOK & DOK). pose proof (shash_fe_hi _ (SFE eq_refl) LA3) as DFE.
    pose proof SV1 as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
    pose proof (SCFG_SF _ _ _ (SF_hash_st X1) CF1) as CH.
    assert (E4 : SF (st_lm (hash_st X1) (hash_hh X1)) = SF X1) by (rewrite SF_st_lm; apply SF_hash_st).
    apply (slow_hash L flush inp rest0 lo r fj F fc me CTX Q X1 SV1 LA3 (c_ws _ _ CF1) (c_hs _ _ CF1)).
    apply (slow_lm L flush inp rest0 lo r fj F fc me CTX Q (hash_st X1) (hash_hh X1)).
    + exact Rml.
    + exact Rlazy.
    + exact (c_ws _ _ CH).
    + rewrite (c_ws _ _ CF1) in Rsl. unfold hash_st, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str. dsred. lia.
    + reflexivity.
    + unfold hash_hh. rewrite (c_hs _ _ CF1) in Rhb, Rhm.
      pose proof (update_hash_range X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2)) ltac:(lia)) as RH.
      pose proof (Rhb (update_hash X1 (ds_ins_h X1) (arr_get (ds_window X1) (ds_strstart X1 + 2))) ltac:(lia)) as RHH. lia.
    + exact Rstrat.
    + exact LMOK.
    + exact (proj1 DOK).
    + apply slow_dec; [exact (SCFG_SF _ _ _ E4 CF1)| exact DOK| exact DFE| exact RM| exact KC| exact KR].
  -
    intros X1 EF LA3.
    assert (ES : st_sbody X flush = st_srest X1) by (unfold st_sbody; rewrite EF; reflexivity).
    rewrite (st_srest_lo X1 LA3) in ES. rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in ES. rewrite ES in RM, KC, KR. clear ES KB.
    rewrite EF in HOK, CF1, SFE. rewrite fst_pr in CF1. rewrite fst_pr, snd_pr in HOK, SFE.
    destruct (shash_ok_lo _ _ (HOK eq_refl) LA3) as (_ & _ & _ & DOK). rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in DOK.
    pose proof (shash_fe_lo _ (SFE eq_refl) LA3) as DFE. rewrite (st_lm_false _ 0 (sl_lm_cond_0 _)) in DFE.
    apply slow_dec; [exact (SCFG_SF _ _ _ (SF_prev_st X1) CF1)| exact DOK| exact DFE| exact RM| exact KC| exact KR].
Qed.

Lemma slow_tail1 : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  0 <= ds_match_available X1 <= 1 ->
  (ds_match_available X1 = 0 -> SKq Q 0x1a414 X1) ->
  (ds_match_available X1 <> 0 -> SKq Q 0x1a334 X1) ->
  SKq Q Z_SLOW_TAIL X1.
Proof.
  intros Q X1 Rma K0 K1. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA. unfold slowR, Z_SLOW_TAIL. unfold SK, slowR in K0, K1.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
  - eapply (K0 KM). exact SI.
  - eapply (K1 KM). exact SI.
Qed.

Lemma slow_tailall : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  SCFG inp X1 -> stail_ok 32768 X1 flush -> stail_fe X1 -> flush = Z_FINISH -> ROOM (fst (slow_tailres X1 flush)) ->
  SKr Q (bs_code (snd (slow_tailres X1 flush))) (fst (slow_tailres X1 flush)) ->
  SKq Q Z_SLOW_TAIL X1.
Proof.
  intros Q X1 C (SV & RSS & MA1 & S2) TFE HF RM KR.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  pose proof C as [Cws Chs Clbs Cins Cwrap Cwrap0 Cwrng Cain Caout Ctie].
  assert (ETL : slow_tailres X1 flush = deflate_tail (tail_st (if negb (ds_match_available X1 =? 0) then break1_st X1 else X1)) Z_FINISH)
    by (unfold slow_tailres; rewrite HF; reflexivity).
  rewrite ETL in RM, KR. clear ETL. rewrite deflate_tail_finish_eq in RM, KR. rewrite fst_pr in RM, KR. rewrite snd_pr in KR.
  cbv zeta in S2.
  assert (T2 : forall s2, s2 = (if negb (ds_match_available X1 =? 0) then break1_st X1 else X1) -> SCFG inp s2 -> SKq Q 0x1a414 s2).
  { intros s2 E2 C2. unfold stail_fe in TFE. rewrite <- E2 in RM, KR, S2, TFE. clear E2. destruct S2 as (RS2 & RSN & FOK & _). specialize (FOK HF).
    pose proof (TFE 1 ltac:(lia)) as FE.
    apply (slow_tail2 L flush inp rest0 lo r fj F fc me CTX HFL Q s2); [lia| exact HF|].
    intros until m'. intros SI.
    assert (CT : ds_lit_bufsize (tail_st s2) = 16384 /\ ds_w_size (tail_st s2) = 32768 /\ 0 <= cs_avail_out (ds_strm (tail_st s2)) < 2^31)
      by (split; [exact (c_lbs _ _ C2)| split; [exact (c_ws _ _ C2)| exact (c_aout _ _ C2)]]).
    destruct CT as (CT1 & CT2 & CT3).
    eapply (slow_fbC L flush inp rest0 lo r fj F fc me CTX HTFBLK HTFB Q); [exact SI| exact FOK| exact FE| exact CT1| exact CT2| exact CT3| exact (room_OUT _ RM)|].
    assert (WF : ds_wrap (flush_block_only (tail_st s2) 1) = ds_wrap s2).
    { rewrite fbo_wrap. reflexivity. }
    apply (slow_fin L flush inp rest0 lo r fj F fc me CTX); [| rewrite WF; exact (c_nraw _ _ C2)| rewrite WF; pose proof (c_wrng _ _ C2); lia|].
    2:{ destruct (cs_avail_out (ds_strm (flush_block_only (tail_st s2) 1)) =? 0); exact KR. }
    pose proof (fbo_avail_out (tail_st s2) 1 FOK CT1 CT3). lia. }
  apply slow_tail1; [exact Rma| |].
  - intros M0. apply T2; [|exact C]. replace (ds_match_available X1 =? 0) with true by (symmetry; apply Z.eqb_eq; exact M0). reflexivity.
  - intros M1. specialize (MA1 M1). rewrite Cws in Rsl.
    intros until m'. intros SI.
    eapply (slow_tlitT L flush inp rest0 lo r fj F fc me CTX Q X1); [exact SI| exact SV| exact MA1| lia| exact Cws| exact Clbs|].
    apply T2; [|exact (SCFG_SF _ _ _ (SF_break1_st X1) C)].
    replace (ds_match_available X1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact M1). reflexivity.
Qed.

Lemma slow_loop : forall (f : nat) (X : deflate_state),
  SCFG inp X -> sloop_ok 32768 32768 f X flush -> tail_safe flush f X -> ROOM (fst (slow_res flush f X)) -> sbs_ok f X flush ->
  sloop_fe f X flush -> tail_fe flush f X ->
  SKq (slow_post_gen r F fc L (fst (slow_res flush f X)) (bs_code (snd (slow_res flush f X))) inp rest0 lo me) Z_SLOW_HEAD X.
Proof.
  induction f as [|f IH]; intros X C LOK TS RM SBS LFE TFE; [destruct LOK|].
  rewrite sloop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite tail_safe_S in TS. rewrite sbs_ok_S in SBS. destruct SBS as [RBS SBS].
  rewrite sloop_fe_S in LFE. destruct LFE as [SFE LFE]. rewrite tail_fe_S in TFE.
  destruct (sbody_frame inp X flush C TOK) as [C' O'].
  rewrite slow_res_S in RM |- *.
  remember (snd (st_sbody X flush)) as o eqn:ES. symmetry in ES. destruct o as [| |bs].
  -
    apply slow_trip; [exact C| exact TOK| exact RBS| exact SFE| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply (OUT_res inp flush f _ C' LOK)| exact RM].
    + intros _. apply IH; assumption.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs E'. rewrite ES in E'. discriminate.
  -
    assert (HF : flush = Z_FINISH) by (destruct HFL as [H0|H4]; [exfalso; exact (sbody_break_flush X flush ES H0)| exact H4]).
    apply slow_trip; [exact C| exact TOK| exact RBS| exact SFE| | | |].
    + destruct RM as [RM]. constructor. eapply Nat.le_trans; [apply OUT_tailres| exact RM].
    + intros E'. rewrite ES in E'. discriminate.
    + intros _. apply slow_tailall; [exact C'| exact TS| exact TFE| exact HF| exact RM|]. apply (slow_epi L flush inp rest0 lo r fj F fc me CTX).
    + intros bs E'. rewrite ES in E'. discriminate.
  -
    rewrite fst_pr, snd_pr. rewrite fst_pr in RM.
    apply slow_trip; [exact C| exact TOK| exact RBS| exact SFE| exact RM| | |].
    + intros E'. rewrite ES in E'. discriminate.
    + intros E'. rewrite ES in E'. discriminate.
    + intros bs' E'. rewrite ES in E'. injection E' as <-. apply (slow_epi L flush inp rest0 lo r fj F fc me CTX).
Qed.
End SLOW.


Theorem deflate_slow_spec : fill_window_stmt -> tr_flush_block_stmtE -> tr_flush_bits_stmt -> deflate_slow_stmt.
Proof.
  intros HFW HTFBLK HTFB. unfold deflate_slow_stmt.
  intros until m. intros DR DIN TIE DOUT MI RELRO STK LO SP16 BEL IO SAFE HFL WS HS LBS INS WRAP WRAP0 WRNG AIN RAO ROOM SBS [LFE TFE] -> ->.
  unfold Z_DEFLATE_SLOW.
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : slow_ctx L inp rest0 lo r m) by (constructor; assumption).
  destruct SAFE as (DW & LOK & TSAFE). rewrite WS, HS in LOK. rewrite WS in TSAFE.
  assert (C : SCFG inp d) by (constructor; assumption).
  rewrite deflate_slow_res in ROOM.
  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_SLOW_STACK in LO.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  pose proof (munch_refl (slow_W L rest0 lo r) m) as MU. unfold slow_W in MU. cbn [r_sp r] in MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  carve_frame 128%nat STK.
  do 14 zs.
  gF. zs. zstep. al8 (dl_As L). gF. zs.
  do 19 zs.
  rewrite ?(zb_lxor_ones (dl_As L + 212)) by lia. rewrite ?(zb_lxor_ones (dl_As L + 2047 + 457)) by lia. rewrite ?(zb_lxor_ones (dl_As L + 2504)) by lia.
  name_mem mP.
  replace (wz (-1)) with (wz 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
  replace (wz (dl_As L + 2047 + 457)) with (wz (dl_As L + 2504)) by (f_equal; lia).
  replace (wz (18446744073709551615 - (dl_As L + 2047 + 457))) with (wz (18446744073709551615 - (dl_As L + 2504))) by (f_equal; lia).
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?x :: _) => set (fj := x) in FR end.
  assert (RM0 : Box (OUT (fst (slow_res flush (lz_fuel d) d)) <= length rest0)%nat) by (constructor; exact ROOM).
  assert (RMd : Box (length (cs_out_rev (ds_strm d)) <= length rest0)%nat).
  { constructor. eapply Nat.le_trans; [apply (OUT_res inp flush (lz_fuel d) d C LOK)| exact ROOM]. }
  assert (SI : SINV L flush rest0 lo r fj m d mP).
  { split.
    { apply (DREP_agree m mP L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [apply (dout_munch _ m mP L rest0 _ DOUT RMd MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact RMd|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  eapply evt_mono.
  { eapply (slow_loop L flush inp rest0 lo r fj F fc m CTX HFW HTFBLK HTFB HFL (lz_fuel d) d C LOK TSAFE RM0 SBS LFE TFE). exact SI. }
  intros ms' P. unfold deflate_slow_post. rewrite deflate_slow_res. exact P.
Qed.
