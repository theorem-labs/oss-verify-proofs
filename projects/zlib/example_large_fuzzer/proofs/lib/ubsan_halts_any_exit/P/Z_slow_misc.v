(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section MISC.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma slow_avail : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= ds_strstart X < 2^31 -> 0 <= ds_lookahead X < 2^31 ->
  SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (avail0_st X) ->
  SK L flush rest0 lo r F fc me Q 0x19c9c X.
Proof.
  intros Q X Rss Rla HK. unfold SK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 9 zs. name_mem mB.
  tr_groups MUf WMf.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold avail0_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_ltail : forall (Q : machine_state -> Prop) (Y : deflate_state),
  0 <= ds_strstart Y < 2^31 -> 0 <= ds_lookahead Y < 2^31 -> 0 <= cs_avail_out (ds_strm Y) < 2^31 ->
  (cs_avail_out (ds_strm Y) = 0 -> SKret L flush rest0 lo r F fc me Q 0 (ltail_st Y)) ->
  (cs_avail_out (ds_strm Y) <> 0 -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (ltail_st Y)) ->
  SK L flush rest0 lo r F fc me Q Z_SLOW_LTAIL Y.
Proof.
  intros Q Y Rss Rla Rao KR KH0. unfold SK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_zs ZS. open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR, Z_SLOW_LTAIL. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 8 zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r me (ltail_st Y) mB).
  { split; [split|].
    - do 4 eexists. exact ZS.
    - unfold ltail_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold SKret in KR. unfold Z_SLOW_EPI in KR.
    replace (wz (cs_avail_out (ds_strm Y))) with (wz 0) by (f_equal; lia).
    eapply (KR KB). exact SI'.
  - unfold Z_SLOW_HEAD in KH0. eapply (KH0 KB). exact SI'.
Qed.

Lemma slow_aexit : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 ->
  (cs_avail_out (ds_strm Z0) = 0 -> SKret L flush rest0 lo r F fc me Q 0 Z0) ->
  (cs_avail_out (ds_strm Z0) <> 0 -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD Z0) ->
  SK L flush rest0 lo r F fc me Q 0x19d60 Z0.
Proof.
  intros Q Z0 Rao KR KH0. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  open_zs ZS. open_A GA. unfold slowR.
  zs. zs. zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold Z_SLOW_HEAD in KH0. eapply (KH0 KB). exact SI.
  - zs. unfold SKret in KR. unfold Z_SLOW_EPI in KR.
    replace (wz (cs_avail_out (ds_strm Z0))) with (wz 0) by (f_equal; lia).
    eapply (KR KB). exact SI.
Qed.

(* 1.4 (zl14-cmp): FLUSH_BLOCK(s, 1)'s finish test is `avail_out == 0 && (pending != 0 || wrap != 0)` for
   finish_started (2), else finish_done (3) (0x19f34..0x19f5c). Under wrap <> 0 this is 1.3.1's
   `avail_out == 0 ? 2 : 3`, so the statement keeps that code and takes wrap <> 0 as a premise. *)
Lemma slow_fin : forall (Q : machine_state -> Prop) (Z0 : deflate_state),
  0 <= cs_avail_out (ds_strm Z0) < 2^31 -> ds_wrap Z0 <> 0 -> - 2^31 <= ds_wrap Z0 < 2^31 ->
  SKret L flush rest0 lo r F fc me Q (if cs_avail_out (ds_strm Z0) =? 0 then 2 else 3) Z0 ->
  SKx L flush rest0 lo r F fc me Q 0x19f94 Z0.
Proof.
  intros Q Z0 Rao W0 Rw KR. unfold SKx. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [ZS ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY1].
  open_zs ZS. open_A GA.
  unfold SKret in KR. unfold Z_SLOW_EPI in KR.
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

Lemma slow_decide : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= ds_prev_length X <= 258 -> 0 <= ds_match_length X <= 258 -> 0 <= ds_match_available X <= 1 ->
  (dist_cond X = true ->
   forall (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r me X m' ->
     evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19a3c) fc None m' (seg_rom psegs))) ->
  (dist_cond X = false -> ds_match_available X <> 0 -> SK L flush rest0 lo r F fc me Q 0x19bcc X) ->
  (dist_cond X = false -> ds_match_available X = 0 -> SK L flush rest0 lo r F fc me Q 0x19c9c X) ->
  KD L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X Rpl Rml Rma KDI KLI KAV. unfold KD. intros until m'. intros SI. unfold slowR, Z_SLOW_DECIDE.
  assert (C70C : dist_cond X = false ->
    forall (a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31 : word),
    evt psegs Q (MS (slowR L r a1 a5 a6 a7 (wz flush) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31) F (wz 0x19bc4) fc None m' (seg_rom psegs))).
  { intros DC. intros. pose proof SI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    unfold slowR. zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
    - eapply (KAV DC KM). exact SI.
    - eapply (KLI DC KM). exact SI. }
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  - eapply C70C. unfold dist_cond. replace (3 <=? ds_prev_length X) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + eapply C70C. unfold dist_cond. replace (ds_match_length X <=? ds_prev_length X) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
    + eapply KDI; [|exact SI]. unfold dist_cond. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
End MISC.
