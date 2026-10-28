(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_defs Pj_stmts Pj_ser_defs Pj_ser_loop_defs Pj_ser_top Pj_ser_obj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem ser_closed : rmalloc_stmt -> rfree_stmt -> str_stmt -> key_stmt -> forall d, ser_stmt d.
Proof.
  intros HM HF PSTR PKEY d.
  induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf).
  apply (ser_of_rec HM HF PSTR PKEY). intros k d' Hd'.
  apply (cont_of_ser HM HF). apply IH. lia.
Qed.

Corollary cont_closed : rmalloc_stmt -> rfree_stmt -> str_stmt -> key_stmt -> forall k d, cont_stmt k d.
Proof. intros HM HF PSTR PKEY k d. apply (cont_of_ser HM HF), (ser_closed HM HF PSTR PKEY). Qed.

End WithCeiling0.
