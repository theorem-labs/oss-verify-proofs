(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA Layout RT_iface Lept_kit Lept_iface LeptC_kit Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sx32_s32 : forall z, - 2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. destruct (Z_lt_ge_dec z 0) as [N|P]; [| apply sx32_small; lia].
  unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  replace (z mod 2^64) with (z + 2^64) by (apply Z.mod_unique with (q := -1); lia).
  rewrite swrap32_high by lia. lia.
Qed.
Ltac sx32s_fix := repeat match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_s32 z) by lia end.

(* [comment removed for export] *)
Lemma optrS_frame : forall spa off, 0 <= spa < 2^64 -> 0 <= off -> spa + off + 4 <= USTACK_TOP -> spa mod 16 = 0 -> off mod 4 = 0 ->
  optrS (Z_to_bv 64 spa) (spa + off) 4.
Proof.
  intros spa off HS HO HT HA HM. unfold optrS. rewrite unsigned_lit by (change (2^64) with 18446744073709551616 in HS; lia).
  split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.
