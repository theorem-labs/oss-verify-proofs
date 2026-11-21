(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Zg_slow_frame
  Zg_fast_model Zg_fast_kit Zg_fast_dist1 Zg_fast_dist2 Zg_fast_ins.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FDIST.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma fast_dist : forall (Q : machine_state -> Prop) (X : deflate_state),
  trip_inv X -> 3 <= ds_match_length X -> dist_ok X -> 1 <= ds_lookahead X <= 65536 ->
  ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (snd (st_dist X) = false -> FK L flush rest0 lo r F fc me Q Z_FAST_HEAD (fst (st_dist X))) ->
  (snd (st_dist X) = true -> FKA L flush rest0 lo r F fc me Q (fst (st_dist X))) ->
  FKD L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X SV ML3 (MLLA & DD & SS2) RLA WS HS LBS KH0 KA0.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *. rewrite LBS in *.
  destruct (tally_dist_eq X) as [EF ES]. rewrite EF, ES in KH0, KA0. clear EF ES. cbv zeta in KH0, KA0.
  apply (fast_tdist1 L flush inp rest0 lo r F fc me CTX Q X SV ML3 RLA WS LBS).
  unfold KT1F. intros until m'. intros SI1 EDD.
  assert (RD : 0 <= tdist_D X < 32768).
  { unfold tdist_D in *. pose proof (Z.mod_pos_bound (ds_strstart X - ds_match_start X + -1) (2^16) ltac:(lia)). lia. }
  remember (tdist2 (tdist1 X) (d_code (tdist_D X))) as T eqn:ET.
  assert (TSS : ds_strstart T = ds_strstart X) by (rewrite ET; reflexivity).
  assert (TML : ds_match_length T = ds_match_length X) by (rewrite ET; reflexivity).
  assert (THS : ds_hash_shift T = ds_hash_shift X) by (rewrite ET; reflexivity).
  assert (TI : ILIF T).
  { rewrite ET. unfold ILIF, tdist2, tdist1. cbv zeta. dsred.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros j Hj; apply Rwb; lia | intros j Hj; apply Rhb; lia]. }
  assert (ESN : ds_sym_next (tdist1 X) = ds_sym_next X + 3) by reflexivity.
  assert (ESE : ds_sym_end (tdist1 X) = ds_sym_end X) by reflexivity.
  eapply (fast_tdist2 L flush inp rest0 lo r F fc me CTX Q (tdist1 X) (tdist_D X) w10); [exact SI1| exact EDD| exact RD| | | | | | | | | ].
  1:{ unfold tdist1. cbv zeta. dsred. lia. } 1:{ unfold tdist1. cbv zeta. dsred. lia. } 1:{ unfold tdist1. cbv zeta. dsred. lia. }
  1:{ unfold tdist1. cbv zeta. dsred. lia. } 1:{ rewrite ESN. lia. } 1:{ rewrite ESE. lia. }
  1:{ intros i Hi. unfold tdist1. cbv zeta. dsred. apply Rdfc. exact Hi. }
  -
    rewrite <- ET. intros IC. rewrite IC in KH0, KA0. rewrite ESN, ESE.
    apply (fast_insbr L flush inp rest0 lo r F fc me CTX Q T); [exact TI| rewrite TML; lia| rewrite TSS, TML; lia| lia| lia| |].
    + intros NE. apply KH0. apply Z.eqb_neq. exact NE.
    + intros EQ. apply KA0. apply Z.eqb_eq. exact EQ.
  -
    rewrite <- ET. intros IC. rewrite IC in KH0, KA0. rewrite ESN, ESE. rewrite noins_eq in KH0, KA0.
    apply (fast_noins L flush inp rest0 lo r F fc me CTX Q T); [exact TI| rewrite TML; lia| rewrite TSS, TML; lia| lia| lia| |].
    + intros NE. apply KH0. apply Z.eqb_neq. exact NE.
    + intros EQ. apply KA0. apply Z.eqb_eq. exact EQ.
Qed.
End FDIST.
