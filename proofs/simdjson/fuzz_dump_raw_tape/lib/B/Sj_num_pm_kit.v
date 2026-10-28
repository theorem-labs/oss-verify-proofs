(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_bkit.
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
