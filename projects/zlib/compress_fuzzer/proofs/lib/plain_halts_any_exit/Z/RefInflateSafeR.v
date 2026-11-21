(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSimPre.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSim2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItShape.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItRep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma applyw_unique : forall ws a i v,
  (forall j w w', In (j, w) ws -> In (j, w') ws -> w = w') ->
  In (i, v) ws -> 0 <= i < arr_len a -> arr_get (applyw ws a) i = v.
Proof.
  intros ws a i v U Hin Hr.
  destruct (applyw_in ws a i (in_map_fst ws i v Hin) Hr) as [v' [Hin' E]]. rewrite E. exact (U i v' v Hin' Hin).
Qed.

Theorem inflate_table_TBLg : forall ty lens lens_ofs codes tbl table bits work,
  0 <= codes <= 288 -> codes <= arr_len work ->
  (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens i <= 15) ->
  ty_ok ty (lens_list lens lens_ofs codes) bits ->
  1 <= bits <= 15 -> 0 <= table -> table + it_room ty <= arr_len tbl ->
  let '(ret, tbl', toff, bits', work') := inflate_table ty lens lens_ofs codes tbl table bits work in
  (arr_len tbl' = arr_len tbl /\ arr_len work' = arr_len work) /\
  (ret = 0 ->
   1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty
   /\ TBLg ty (fun x => arr_get tbl' (table + x)) bits' (toff - table)
   /\ (forall i, ~ (table <= i < toff) -> arr_get tbl' i = arr_get tbl i)).
Proof.
  intros ty lens lens_ofs codes tbl table bits work Hcodes Hwork Hlens Hty Hbits Htable Hroom.
  set (ll := lens_list lens lens_ofs codes) in *. set (wl := wl_of ll).
  assert (Hty' : ty = CODES -> codes <= 19).
  { intros ->. cbn [ty_ok] in Hty. destruct Hty as [H _]. subst ll. unfold NC, lens_list in H. unfold zlength in H. rewrite length_map, length_seq in H. lia. }
  rewrite (inflate_table_abs ty lens lens_ofs codes ll wl table bits Hcodes Hlens eq_refl eq_refl Hty' Hbits tbl work Hwork).
  pose proof (ItSimPre.Hll lens lens_ofs codes ll wl Hcodes Hlens eq_refl eq_refl) as Hll.
  pose proof (it_abs_props wl ll table bits Hll eq_refl Hbits ty Hty) as P.
  pose proof (it_abs_rep wl ll table bits Hll eq_refl Hbits ty Hty) as R.
  destruct (it_abs wl ll ty table bits) as [[[[ret ws] toff] bits'] ww].
  split; [split; apply arr_len_applyw|].
  intros Hret. specialize (P Hret). specialize (R Hret).
  destruct P as (P1 & P2 & P3 & P4 & P5). destruct R as (U & RR & RS).
  pose proof (Z.pow_pos_nonneg 2 bits' ltac:(lia) ltac:(lia)) as PB.
  assert (GETW : forall x v, In (table + x, v) ws -> arr_get (applyw ws tbl) (table + x) = v).
  { intros x v Hin. apply (applyw_unique ws tbl _ v U Hin). pose proof (P3 _ _ Hin). lia. }
  assert (COV : forall x, 0 <= x < toff - table -> exists v, In (table + x, v) ws /\ arr_get (applyw ws tbl) (table + x) = v).
  { intros x Hx. apply applyw_in; [apply P4; lia | lia]. }
  split; [exact P1|]. split; [exact P2|]. split.
  - split; [exact P1|]. split; [lia|]. split; [|split].
    + intros x Hx. destruct (COV x Hx) as [v [Hin ->]]. left.
      replace x with (table + x - table) at 1 by lia. apply P5. exact Hin.
    + intros x x' Hx Hx' Hb Hm. destruct (COV x ltac:(lia)) as [v [Hin E]]. rewrite E in *.
      apply GETW. apply (RR x x' v Hin Hx Hx' Hm).
    + intros x Hx Hop y y' Hy Hy' Hb Hm. destruct (COV x ltac:(lia)) as [L [HinL EL]]. rewrite EL in *.
      destruct (RS x L y y' 0 HinL Hx Hop Hy Hy') as [Hrange _].
      destruct (COV (code_val L + y) ltac:(lia)) as [v [Hin Ev]]. rewrite Ev in *.
      rewrite Z.add_assoc in Hin.
      destruct (RS x L y y' v HinL Hx Hop Hy Hy') as [_ Hrep].
      apply GETW. rewrite Z.add_assoc. apply Hrep; [exact Hin | exact Hm].
  - intros i Hi. apply applyw_other. intros v Hin. pose proof (P3 _ _ Hin). lia.
Qed.
