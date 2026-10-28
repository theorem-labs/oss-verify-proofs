(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.musl Require Import Bs0Memchr_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import SegStrlen_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SegRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma src0_strlen_spec : SR.strlen_spec Ubsan.M.loaded_segments 0x13698 0x136b0 0xabee4.
Proof.
  intros fx mem s buf K rom regs ret Hbuf Hwin Hnw HK0 Hz Hnz Hro Hret H1 H10.
  assert (HOK : slenH mem s buf K) by (constructor; assumption).
  destruct (ref_strlen mem s buf K rom regs ret HOK Hret H1 H10) as (regs' & Hms & Hag & Ha0).
  exists regs'. split; [|split; [|exact Ha0]].
  - replace (Z_to_bv 64 0xabee4) with (0xabee4%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - intros r N10 N11 N12 N13 N14 N15 N16. apply (sl_agree_getr _ _ r Hag).
    unfold sl_clob. cbn [In]. intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst r; contradiction.
Qed.
