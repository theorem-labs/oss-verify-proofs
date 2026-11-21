(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure InfPure_w7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sinv_tables_live : forall cx st lf cf, sinv cx st lf cf -> codes_liveP (t_mode st) -> tables_live cx st cf.
Proof.
  intros cx st lf cf (R & W & P & Mo) HL.
  assert (X : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get Mo. exact (X HL).
Qed.

Lemma sinv_tabs_cases : forall cx st lf cf, sinv cx st lf cf -> codes_liveP (t_mode st) ->
  (exists o, t_lc st = CDyn 0 /\ t_dc st = CDyn o /\ 1 <= t_lb st <= 15 /\ 1 <= t_db st <= 15 /\ 0 <= o /\ o <= t_nx st /\ t_nx st <= 1444
             /\ tab_ok LENS (rdc cf (CDyn 0)) (t_lb st) o = true /\ tab_ok DISTS (rdc cf (CDyn o)) (t_db st) (t_nx st - o) = true)
  \/ (t_lc st = CLenfix /\ t_dc st = CDistfix /\ t_lb st = 9 /\ t_db st = 5
      /\ tab_ok LENS (rdc cf CLenfix) 9 512 = true /\ tab_ok DISTS (rdc cf CDistfix) 5 32 = true).
Proof.
  intros cx st lf cf SI HL. pose proof (sinv_tables_live _ _ _ _ SI HL) as TL. unfold tables_live in TL.
  destruct (t_lc st) as [o1| |]; destruct (t_dc st) as [o2| |]; try contradiction.
  - left. destruct TL as (E1 & LB & DB & O0 & ONX & NX & TL1 & TL2). subst o1. exists o2. unfold N_CODES in NX. split; [reflexivity|]. split; [reflexivity|]. split; [exact LB|]. split; [exact DB|]. split; [exact O0|]. split; [exact ONX|]. split; [exact NX|]. split; [exact TL1| exact TL2].
  - right. destruct TL as (LB & DB). split; [reflexivity|]. split; [reflexivity|]. split; [exact LB|]. split; [exact DB|]. split; [exact lenfix_ok | exact distfix_ok].
Qed.

Lemma codes_live_DIST : codes_liveP DIST. Proof. unfold codes_liveP. modes_cbv. lia. Qed.
Lemma codes_live_LEN : codes_liveP LEN. Proof. unfold codes_liveP. modes_cbv. lia. Qed.

Lemma sinv_bits_facts : forall cx st lf cf, sinv cx st lf cf ->
  0 <= t_cin st /\ t_cin st <= c_n cx /\ 0 <= t_bits st <= 40 /\ t_bits st <= 8 * t_cin st /\ 0 <= t_hold st < 2 ^ t_bits st.
Proof.
  intros cx st lf cf (R & _). unfold IDefs.RNG in R.
  destruct R as (R1 & R2 & _ & _ & _ & R6 & R7 & R8 & R9 & R10 & _). lia.
Qed.
