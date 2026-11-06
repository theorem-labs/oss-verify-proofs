(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Export BnTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma land7 : forall x, (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros x H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma land7_wrap : forall e, (e mod 8 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 e)) 7 = 0%Z.
Proof.
  intros e H. apply land7. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia.
Qed.

Definition ub_ptr_ok (n p : Z) : Prop := (0 < n -> 0 < p /\ p mod 8 = 0)%Z.

Definition ub_top (n ap bp : Z) : Prop := (0 < n -> ap + 8 * n <= 140737488355328 /\ bp + 8 * n <= 140737488355328)%Z.

Ltac chk_lit := zstep; if_false.
Ltac chk tac := zstep; let C := fresh "C" in if_cases C; [ exfalso; zify_cond C; tac C | clear C ].
Ltac chkP C P := clear - C P; lia.

