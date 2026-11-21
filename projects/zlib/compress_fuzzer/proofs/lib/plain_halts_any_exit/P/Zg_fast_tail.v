(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Zg_fast_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_FAST_SYMC : Z := 0x19448.
Definition Z_FAST_FINB : Z := 0x19504.
Definition Z_FAST_FINC : Z := 0x195c8.

Section FTAIL.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma fast_aexit : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 ->
  (cs_avail_out (ds_strm Z0) = 0 -> FKret L flush rest0 lo r F fc me Q 0 Z0) ->
  (cs_avail_out (ds_strm Z0) <> 0 -> FK L flush rest0 lo r F fc me Q Z_FAST_HEAD Z0) ->
  FK9 L flush rest0 lo r F fc me Q Z_FAST_AOUT Z0.
Proof.
  intros Q Z0 Rao KR KH0. unfold FK9. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  open_zs ZS. open_A GA. unfold Z_FAST_AOUT.
  unfold FKret, Z_FAST_EPI in KR. unfold FK, fastR, Z_FAST_HEAD in KH0.
  zs. zs. zs. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - replace (wz (cs_avail_out (ds_strm Z0))) with (wz 0) by (f_equal; lia).
    eapply (KR KB). exact SI.
  - eapply (KH0 KB). exact SI.
Qed.

Lemma fast_tail1 : forall (Q : machine_state -> Prop) (Y : deflate_state),
  0 <= ds_strstart Y <= 65536 -> 0 <= flush <= 5 ->
  (flush = Z_FINISH -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
     FINV L flush rest0 lo r me (tail_st Y) m' ->
     evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz (ds_strstart (tail_st Y))) y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_FBB) fc None m' (seg_rom psegs))) ->
  (flush <> Z_FINISH -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
     FINV L flush rest0 lo r me (tail_st Y) m' ->
     evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz (ds_strstart (tail_st Y))) y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_SYMC) fc None m' (seg_rom psegs))) ->
  FK L flush rest0 lo r F fc me Q Z_FAST_TAIL Y.
Proof.
  intros Q Y Rss HFL HK HKD. unfold FK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR, Z_FAST_TAIL. unfold fast_frame in FR. unfold slow_W in MU. unfold Z_FINISH in HK, HKD.
  unfold fastR, Z_FAST_FBB, Z_FAST_SYMC in HK, HKD.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. zs. zs. zstep.
  eapply (evt_cut psegs (fun ms' => ms' = MS (fastR L r y1 y5 y6 y7 (wz (ds_strstart Y)) (wz (if ds_strstart Y <? 2 then ds_strstart Y else 2)) (wz 2)
                                                  y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz 0x1941c) fc None mA (seg_rom psegs))).
  { if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    - apply evt_done. unfold fastR. replace (ds_strstart Y <? 2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - zs. apply evt_done. unfold fastR. replace (ds_strstart Y <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  intros ms' ->. unfold fastR.
  assert (Rins : 0 <= (if ds_strstart Y <? 2 then ds_strstart Y else 2) <= 2) by (destruct (Z.ltb_spec (ds_strstart Y) 2); lia).
  zs. zs. name_mem mB. zs. zstep.
  assert (SI : FINV L flush rest0 lo r me (tail_st Y) mB).
  { tr_groups MUf WMf.
    split; [split|].
    - exact ZS.
    - unfold tail_st. change (MIN_MATCH - 1) with 2. constructor; [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  replace (wz (ds_strstart Y)) with (wz (ds_strstart (tail_st Y))) by reflexivity.
  if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by lia.
  - eapply (HKD ltac:(lia)). exact SI.
  - eapply (HK ltac:(lia)). exact SI.
Qed.

Lemma fast_symC : forall (Q : machine_state -> Prop) (Z1 : deflate_state),
  0 <= ds_sym_next Z1 < 2^31 ->
  (ds_sym_next Z1 = 0 -> FKret L flush rest0 lo r F fc me Q 1 Z1) ->
  (ds_sym_next Z1 <> 0 -> forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
     FINV L flush rest0 lo r me Z1 m' ->
     evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz (ds_strstart Z1)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_FBC) fc None m' (seg_rom psegs))) ->
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me Z1 m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz (ds_strstart Z1)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31) F (wz Z_FAST_SYMC) fc None m' (seg_rom psegs)).
Proof.
  intros Q Z1 Rsn K0 KC. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [_ ST]. destruct ST as [GA _ _ GD _ _ _ _ _ _ _ _ _ _ _ LAY1]. open_D GD. unfold fastR, Z_FAST_SYMC.
  unfold FKret, Z_FAST_EPI in K0. unfold fastR, Z_FAST_FBC in KC.
  zs. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
  -
    zs. eapply (K0 ltac:(lia)). exact SI.
  - eapply (KC ltac:(lia)). exact SI.
Qed.

(* 1.4 (zl14-cmp): FLUSH_BLOCK(s, 1)'s finish test is `avail_out == 0 && (pending != 0 || wrap != 0)` for
   finish_started (2), else finish_done (3) (0x19490..0x194b8; 1.3.1 computed `avail_out == 0 ? 2 : 3` branch-free).
   Under wrap <> 0 the two agree, so the statement keeps the code and takes wrap <> 0 as a premise (as slow_fin). *)
Lemma fast_finB : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 -> ds_wrap Z0 <> 0 -> - 2^31 <= ds_wrap Z0 < 2^31 ->
  FKret L flush rest0 lo r F fc me Q (if cs_avail_out (ds_strm Z0) =? 0 then 2 else 3) Z0 ->
  FKs L flush rest0 lo r F fc me Q Z_FAST_FINB Z0.
Proof.
  intros Q Z0 Rao W0 Rw KR. unfold FKs. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  open_zs ZS. open_A GA. unfold Z_FAST_FINB. unfold FKret, Z_FAST_EPI in KR.
  zs. zs. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* avail_out = 0: pending, then wrap *)
    replace (cs_avail_out (ds_strm Z0) =? 0) with true in KR by (symmetry; apply Z.eqb_eq; lia).
    zs. zs. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* pending <> 0: finish_started *) eapply KR. exact SI.
    + zs. zstep. if_cases K3; zify_cond K3.
      * (* wrap <> 0: finish_started *) eapply KR. exact SI.
      * exfalso. apply W0. Z.div_mod_to_equations. lia.
  - (* avail_out <> 0 *)
    replace (cs_avail_out (ds_strm Z0) =? 0) with false in KR by (symmetry; apply Z.eqb_neq; lia).
    zs. zstep. eapply KR. exact SI.
Qed.

Lemma fast_finC : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 ->
  FKret L flush rest0 lo r F fc me Q (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1) Z0 ->
  FKs L flush rest0 lo r F fc me Q Z_FAST_FINC Z0.
Proof.
  intros Q Z0 Rao KR. unfold FKs. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  open_zs ZS. open_A GA. unfold Z_FAST_FINC. unfold FKret, Z_FAST_EPI in KR.
  zs. zs. zstep. if_cases KAO; zify_cond KAO; rewrite ?unsigned_lit in KAO by lia.
  - replace (wz (cs_avail_out (ds_strm Z0))) with (wz (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1))
      by (replace (cs_avail_out (ds_strm Z0) =? 0) with true by (symmetry; apply Z.eqb_eq; lia); f_equal; lia).
    eapply KR. exact SI.
  - zs. replace (wz 1) with (wz (if cs_avail_out (ds_strm Z0) =? 0 then 0 else 1))
      by (replace (cs_avail_out (ds_strm Z0) =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    eapply KR. exact SI.
Qed.
End FTAIL.
