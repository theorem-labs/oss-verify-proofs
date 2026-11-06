(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts DecCut AsanKit AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import DecCutB B0F_decV B0F_bzdV.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition FROsB (c : foctx) (lo : Z) (m : word -> option byte) : Prop :=
  FROsA DI_B0 c m /\ aconsts B0C m /\ stk b0segs m lo (bv_unsigned (o_SP c)).
End ACeilS1.

Lemma zmod16_lin : forall x, (x mod 16 = 0)%Z -> exists q, (x = 16 * q)%Z.
Proof. intros x H. exists (x / 16)%Z. pose proof (Z.div_mod x 16 ltac:(lia)). lia. Qed.
Lemma zmod8_lin : forall x, (x mod 8 = 0)%Z -> exists q, (x = 8 * q)%Z.
Proof. intros x H. exists (x / 8)%Z. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Lemma zmod4_lin : forall x, (x mod 4 = 0)%Z -> exists q, (x = 4 * q)%Z.
Proof. intros x H. exists (x / 4)%Z. pose proof (Z.div_mod x 4 ltac:(lia)). lia. Qed.
Lemma zmod2_lin : forall x, (x mod 2 = 0)%Z -> exists q, (x = 2 * q)%Z.
Proof. intros x H. exists (x / 2)%Z. pose proof (Z.div_mod x 2 ltac:(lia)). lia. Qed.
(* [comment removed for export] *)
Lemma div256_range : forall w, (0 <= w < 4294967296)%Z -> (0 <= w / 256 < 16777216)%Z.
Proof. intros w Hw. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.
(* [comment removed for export] *)
Lemma u64_mod32_small : forall v, (0 <= v < 4294967296)%Z -> (bv_unsigned (Z_to_bv 64 v) mod 4294967296 = v)%Z.
Proof. intros v Hv. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
