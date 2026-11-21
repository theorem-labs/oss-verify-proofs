(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from P/Drv_base.v: rz_step_evt and rz_die restated over BudgetWit.Rzb.rzb, with their released proofs. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb Lib_SCPSB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Lemma rzb_step_evt : forall ms mo T,
  MOK mo -> evt psegs (fun ms' => rzb psegs (mkCfg ms' mo) T) ms -> rzb psegs (mkCfg ms mo) T.
Proof. intros ms mo T HM He. eapply rzb_evt; [exact HM| exact He|]. intros ms' H. exact H. Qed.

Lemma rzb_die : forall c msg fs,
  rzb psegs c (t_emit (W 2 msg) (t_emit (W 1 []) (t_exit (wz 2) fs))) -> rzb psegs c (t_die msg fs).
Proof.
  intros c msg fs H. unfold t_die. eapply rzb_conseq; [exact H|]. apply t_eq_emit. cbn [W map]. apply t_emit_nil_eq. apply t_exit_nil.
Qed.
