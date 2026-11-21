(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintCall.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintInit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintCore.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zlength_zfirstn_le {A} n (l : list A) : 0 <= n -> 0 <= zlength (zfirstn n l) <= n.
Proof.
  intros Hn. unfold zfirstn, zlength. rewrite length_firstn.
  pose proof (Nat.le_min_l (Z.to_nat n) (length l)). lia.
Qed.

Lemma bytes_okP_zfirstn n l : bytes_okP l -> bytes_okP (zfirstn n l).
Proof.
  unfold bytes_okP, zfirstn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; constructor; auto.
Qed.

Lemma bytes_okP_zskipn' n l : bytes_okP l -> bytes_okP (zskipn n l).
Proof.
  unfold bytes_okP, zskipn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; [constructor|constructor|constructor; auto|apply IH].
Qed.

Lemma zlength_rev_append' {A} (l r : list A) : zlength (List.rev_append l r) = zlength l + zlength r.
Proof. unfold zlength. rewrite rev_append_rev, length_app, length_rev. lia. Qed.

Lemma deflate_m_facts ds zc flush :
  dreach ds -> dcall_wf zc -> 0 <= flush < 16 ->
  let r := snd (deflate_m ds zc flush) in
  zstrm_okP (zr_strm r)
  /\ 0 <= zlength (zr_output r) <= zc_avail_out zc
  /\ 0 <= zr_consumed r <= zlength (zc_input zc)
  /\ zs_total_out (zr_strm r) = wrap64 (zs_total_out (zc_strm zc) + zlength (zr_output r))
  /\ Forall (fun b => 0 <= b < 256) (zr_output r).
Proof.
  intros Hr Hzc Hfl. cbv zeta.
  pose proof (dreach_DD ds Hr) as HDD.
  set (c0 := cstrm_of_call zc). set (s0 := set_strm ds c0).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  assert (H0 : DC c0 s0) by (split; [apply DD_set_strm; exact HDD | subst s0 c0; apply SV_entry; exact Hzc]).
  pose proof H0 as [[D0 X0] V0].
  assert (HS0 : ST c0 s0 s0) by (split; [exact H0 | reflexivity]).
  pose proof (core_result _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok)
                c0 s0 HC0 eq_refl D0 flush HS0 Hfl) as [[_ V] _].
  unfold deflate_m. fold c0 s0.
  destruct (deflate_core s0 flush) as [s' rc]. cbn [fst snd] in V |- *.
  unfold zret_of_cs. cbn [zr_strm zr_output zr_consumed zstrm_of_cs zs_total_in zs_total_out zs_adler zs_data_type].
  pose proof (sv_out _ _ V) as Ho. pose proof (sv_aout _ _ V) as Hao. pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil.
  pose proof (sv_ain _ _ V) as Hai. pose proof (sv_tout _ _ V) as Hto.
  assert (Ec0 : zlen (cs_out_rev c0) = 0 /\ cs_avail_out c0 = zc_avail_out zc /\ arr_len (cs_input c0) = zlength (zc_input zc) /\ cs_total_out c0 = zs_total_out (zc_strm zc)).
  { subst c0. unfold cstrm_of_call, zlen. cbn [cs_out_rev cs_avail_out cs_input cs_total_out length Z.of_nat]. rewrite arr_len_of_list. repeat split; reflexivity. }
  destruct Ec0 as (E1 & E2 & E3 & E4).
  assert (EL : zlength (cs_output (ds_strm s')) = zlen (cs_out_rev (ds_strm s'))).
  { unfold cs_output, zlen. rewrite zlength_rev_append'. unfold zlength. cbn. lia. }
  unfold zstrm_okP, zstrm_of_cs. cbn [zs_total_in zs_total_out zs_adler zs_data_type].
  split.
  { split; [exact (sv_tin _ _ V)|]. split; [rewrite Hto; apply wrap64_range|]. split; [exact (sv_adler _ _ V) | exact (sv_dt _ _ V)]. }
  split; [rewrite EL; unfold zlen in *; lia|].
  split; [lia|].
  split; [rewrite Hto, EL, E4, E1; f_equal; lia|].
  unfold cs_output. rewrite rev_append_rev, app_nil_r. apply Forall_rev. exact (sv_outb _ _ V).
Qed.

Section End_.
  Context {MM : MallocModel}.
End End_.

Record C2I (dl : Z) (src : list Z) (x1 x2 : c2st) : Prop := {
  ci_s : DCALL (c2_s x1) (c2_s x2);
  ci_z : c2_z x2 = c2_z x1;
  ci_left : c2_left x2 = c2_left x1;
  ci_sl : c2_sourceLen x2 = c2_sourceLen x1;
  ci_pos : c2_in_pos x2 = c2_in_pos x1;
  ci_ain : c2_avail_in x2 = c2_avail_in x1;
  ci_aout : c2_avail_out x2 = c2_avail_out x1;
  ci_out : c2_out_rev x2 = c2_out_rev x1;
  ci_err : c2_err x2 = c2_err x1;
  ci_zok : zstrm_okP (c2_z x1);
  ci_aout0 : 0 <= c2_avail_out x1 <= C2_MAX;
  ci_left0 : 0 <= c2_left x1;
  ci_sum_out : zlength (c2_out_rev x1) + c2_avail_out x1 + c2_left x1 = dl;
  ci_pos0 : 0 <= c2_in_pos x1;
  ci_ain0 : 0 <= c2_avail_in x1 <= C2_MAX;
  ci_sl0 : 0 <= c2_sourceLen x1;
  ci_sum_in : c2_in_pos x1 + c2_avail_in x1 + c2_sourceLen x1 = zlength src;
  ci_tot : zs_total_out (c2_z x1) = wrap64 (zlength (c2_out_rev x1));
  ci_outb : Forall (fun b => 0 <= b < 256) (c2_out_rev x1) }.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require  DeflateCongr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
