(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma sext16_smallA : forall n, - 32768 <= n < 32768 ->
Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (n mod 18446744073709551616) 48))) 48 = n.
Proof.
intros n Hn. rewrite Z_to_bv_signed. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (18446744073709551616 / 2) with 9223372036854775808. change (2^48) with 281474976710656.
Z.div_mod_to_equations. lia.
Qed.
Lemma rw_update_valA : forall n rw, -1 <= n <= rw -> rw <= 4095 ->
bv_swrap 32 (Z.lor (Z.shiftr (bv_signed (Z_to_bv 64 n)) 63 mod 18446744073709551616)
(bv_swrap 32 (0 - n mod 18446744073709551616) mod 18446744073709551616) + rw)
= (if n <? 0 then rw - 1 else rw - n).
Proof.
intros n rw Hn Hrw. destruct (Z.ltb_spec n 0) as [L|G].
- assert (n = -1) by lia. subst n.
change (Z.lor (Z.shiftr (bv_signed (Z_to_bv 64 (-1))) 63 mod 18446744073709551616)
(bv_swrap 32 (0 - -1 mod 18446744073709551616) mod 18446744073709551616)) with 18446744073709551615.
apply swrap32_eqm; [lia|]. Z.div_mod_to_equations. lia.
- rewrite signed_lit by lia. rewrite (Z.shiftr_div_pow2 n 63) by lia. rewrite (Z.div_small n (2^63)) by lia.
rewrite Z.mod_0_l by lia. rewrite Z.lor_0_l. rewrite (Z.mod_small n) by lia.
rewrite (swrap32_small (0 - n)) by lia.
apply swrap32_eqm; [lia|]. Z.div_mod_to_equations. lia.
Qed.
Lemma rw0_valA : forall tl, 5 <= tl <= 12 ->
Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (tl mod 32)) mod 18446744073709551616) 18446744073709551615 = 2^tl - 1.
Proof.
intros tl H.
assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma rw0_valA' : forall tl, 5 <= tl <= 12 ->
Z.lxor (Z.land (bv_swrap 32 (Z.shiftl 18446744073709551615 (tl mod 32))) 18446744073709551615) 18446744073709551615 = 2^tl - 1.
Proof.
intros tl H.
assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma land_ones32A : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.
Lemma shl48_landA : forall x, 0 <= x < 65536 -> Z.land (Z.shiftl x 48) 18446744073709551615 = x * 281474976710656.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
change (2^48) with 281474976710656. change (2^64) with 18446744073709551616. apply Z.mod_small. lia.
Qed.
