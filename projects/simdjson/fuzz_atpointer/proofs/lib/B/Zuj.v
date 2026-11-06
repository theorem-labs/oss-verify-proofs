(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf Zqc Zqd Zqh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma b2z_ltb_eq0 : forall a b, Z.b2z (a <? b) = 0 -> b <= a.
Proof. intros a b H. destruct (Z.ltb_spec a b); [discriminate H| assumption]. Qed.
Lemma b2z_ltb_ne0 : forall a b, Z.b2z (a <? b) <> 0 -> a < b.
Proof. intros a b H. destruct (Z.ltb_spec a b); [assumption| exfalso; apply H; reflexivity]. Qed.
Lemma b2z_eqb_eq0 : forall a b, Z.b2z (a =? b) = 0 -> a <> b.
Proof. intros a b H. destruct (Z.eqb_spec a b); [discriminate H| assumption]. Qed.
Lemma b2z_eqb_ne0 : forall a b, Z.b2z (a =? b) <> 0 -> a = b.
Proof. intros a b H. destruct (Z.eqb_spec a b); [assumption| exfalso; apply H; reflexivity]. Qed.
Ltac b2z_lin :=
  repeat match goal with
  | H : Z.b2z (_ <? _) = 0 |- _ => apply b2z_ltb_eq0 in H
  | H : Z.b2z (_ <? _) <> 0 |- _ => apply b2z_ltb_ne0 in H
  | H : Z.b2z (_ =? _) = 0 |- _ => apply b2z_eqb_eq0 in H
  | H : Z.b2z (_ =? _) <> 0 |- _ => apply b2z_eqb_ne0 in H
  end.
