(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j AMTac ARtStmts ANodijx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

Lemma pg_up_land : forall x, 0 <= x -> x + 4095 < 2^64 -> Z.land (x + 4095) 18446744073709547520 = pg_up x.
Proof.
  intros x H0 H1. change 18446744073709547520 with (2^64 - 2^12). rewrite land_align_down by lia.
  unfold pg_up. change (2^12) with 4096. rewrite Zmod_eq_full by lia. lia.
Qed.
Lemma pg_dn_land : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = pg_dn x.
Proof.
  intros x H. change 18446744073709547520 with (2^64 - 2^12). rewrite land_align_down by lia.
  unfold pg_dn. change (2^12) with 4096. rewrite Zmod_eq_full by lia. lia.
Qed.
Lemma pg_up_bounds : forall x, x <= pg_up x <= x + 4095 /\ pg_up x mod 4096 = 0.
Proof. intros x. unfold pg_up. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). split; [lia|]. apply Z_mod_mult. Qed.
Lemma pg_dn_bounds : forall x, x - 4095 <= pg_dn x <= x /\ pg_dn x mod 4096 = 0.
Proof. intros x. unfold pg_dn. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). split; [lia|]. apply Z_mod_mult. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pg_interior_nonempty : forall q s, 8191 <= s -> pg_up q < pg_dn (q + s).
Proof.
  intros q s Hs. unfold pg_up, pg_dn.
  pose proof (Z.div_mod (q + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (q + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (q + s) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (q + s) 4096 ltac:(lia)) as M2.
  assert ((q + 4095) / 4096 < (q + s) / 4096); [| lia]. lia.
Qed.
Lemma a8_interior_nonempty : forall a size, 8191 <= size / 8 -> a8_pbeg a < a8_pend a size.
Proof. intros a size H. unfold a8_pbeg, a8_pend. apply pg_interior_nonempty. exact H. Qed.
