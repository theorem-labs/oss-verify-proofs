(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Mem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Vct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_one : sx32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Lemma zx16_vct : forall c, zx16 (Z_to_bv 64 (vct c)) = Z_to_bv 64 (vct c).
Proof.
  intros c. pose proof (vct_range c) as R. unfold zx16. rewrite unsigned_lit by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.
