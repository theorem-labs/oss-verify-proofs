(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rl.
Import ListNotations.
Local Open Scope Z_scope.

Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac show_hyp H := let T := type of H in idtac H ":" T.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma znth_In' : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
intros l i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
apply nth_In. lia.
Qed.
Lemma zbytes_nth : forall txt i, 0 <= i < zlength txt ->
nth_error (zbytes txt) (Z.to_nat i) = Some (Z_to_bv 8 (znth txt i)).
Proof.
intros txt i Hi. unfold zbytes, zlength, znth in *. rewrite nth_error_map.
destruct (Z.ltb_spec0 i 0); [lia|].
destruct (nth_error txt (Z.to_nat i)) as [c|] eqn:E.
- cbn. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
- apply nth_error_None in E. lia.
Qed.
