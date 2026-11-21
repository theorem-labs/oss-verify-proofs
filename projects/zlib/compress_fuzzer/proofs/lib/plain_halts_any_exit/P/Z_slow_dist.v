(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod Z_slow_dist1 Z_slow_dist2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma slow_dist : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  strip_inv X -> dist_cond X = true -> sdist_ok 32768 X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (snd (st_sdist X) = false -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (fst (st_sdist X))) ->
  (snd (st_sdist X) = true -> KA L flush rest0 lo r F fc me Q (fst (st_sdist X))) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x197f4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros SI SV DC (PLLA & SL3 & DD & _ & _) RLA WS HS LBS KH0 KA0.
  unfold dist_cond in DC. apply andb_prop in DC. destruct DC as [DC1 _]. apply Z.leb_le in DC1.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *. rewrite LBS in *.
  destruct (sdist_eq X DC1 PLLA ltac:(lia) SL3 ltac:(lia)) as [EF ES]. rewrite EF, ES in KH0, KA0. clear EF ES.
  eapply (slow_tdist1 L flush inp rest0 lo r F fc me CTX Q X); [exact SI| exact SV| exact DC1| exact RLA| exact WS| exact LBS|].
  unfold KT1. intros until m'. intros SI1 EDD.
  eapply (slow_tdist2 L flush inp rest0 lo r F fc me CTX Q (sdist1 X) (sdist_D X) w12); [exact SI1| exact EDD| | | | | | | | | | ].
  1:{ unfold sdist_D in *. pose proof (Z.mod_pos_bound (ds_strstart X - ds_prev_match X + -2) (2^16) ltac:(lia)). lia. }
  1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. }
  1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. }
  1:{ intros i Hi. unfold sdist1. dsred. apply Rdfc. exact Hi. }
  remember (dist2_st (sdist2 (sdist1 X) (d_code (sdist_D X)))) as T eqn:ET.
  assert (TSS : ds_strstart T = ds_strstart X) by (rewrite ET; unfold dist2_st, sdist2, sdist1; dsred; reflexivity).
  assert (TPL : ds_prev_length T = ds_prev_length X - 2) by (rewrite ET; unfold dist2_st, sdist2, sdist1; dsred; reflexivity).
  assert (TI : ILI T).
  { rewrite ET. unfold ILI, dist2_st, sdist2, sdist1. dsred.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros j Hj; apply Rwb; lia | intros j Hj; apply Rhb; lia]. }
  replace (ds_strstart (sdist1 X) + ds_lookahead (sdist1 X) - 3) with (ds_strstart X + ds_lookahead X - 3) by (unfold sdist1; dsred; reflexivity).
  eapply (slow_ins L flush inp rest0 lo r F fc me CTX (Z.to_nat (ds_prev_length X - 2)) Q T (ds_strstart X + ds_lookahead X - 3)); [exact TI| rewrite TPL; lia| lia| lia| rewrite TSS; lia| lia| lia|].
  intros until m'0. intros SIF.
  eapply (slow_dexit L flush inp rest0 lo r F fc me CTX Q _ (ds_sym_next (sdist1 X)) (ds_sym_end (sdist1 X))); [exact SIF| unfold sdist1; dsred; lia| unfold sdist1; dsred; lia| |].
  - intros NE. apply KH0. apply Z.eqb_neq. unfold sdist1 in NE. dsred in NE. exact NE.
  - intros EQ. apply KA0. apply Z.eqb_eq. unfold sdist1 in EQ. dsred in EQ. exact EQ.
Qed.
End DIST.
