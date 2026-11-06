(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface
     N6_rip N6_memset N6_memcpy N6_memmove N6_strlen N6_imemcpy N6_imemmove.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~0h0asan_memset_stmt0h0asan_memcpy_stmt0h0memcpy_icpt_stmt0h1asan_memmove_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma asan_memset_ok : ltac2:(zQ "10!jd@1$0?5HCEIL").
Proof.
  unfold asan_memset_stmt. intros.
  eapply amemset_body; eassumption.
Qed.

Lemma asan_memcpy_ok : ltac2:(zQ "10!l0@1$0?5HCEIL").
Proof.
  unfold asan_memcpy_stmt, amemcpy_stmt_at. intros.
  eapply amemcpy_body; try eassumption. apply ACONST_memcpyp. assumption.
Qed.

Lemma memcpy_icpt_ok : ltac2:(zQ "10!m3@1$0?5HCEIL").
Proof.
  unfold memcpy_icpt_stmt, amemcpy_stmt_at. intros.
  eapply imemcpy_body; try eassumption. apply ACONST_memcpyp. assumption.
Qed.

Lemma asan_memmove_ok : ltac2:(zQ "10!n6@1$0?5HCEIL").
Proof.
  unfold asan_memmove_stmt, amemmove_stmt_at. intros.
  eapply amemmove_body; eassumption.
Qed.

(* [comment removed for export] *)

End HCW.

(* [comment removed for export] *)
