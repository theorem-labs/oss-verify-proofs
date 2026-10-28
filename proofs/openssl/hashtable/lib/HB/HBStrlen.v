(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StepTac RefMemcpyLib SumsLib RtStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ha_istrlen_entry : word := 0x1d05c4.

Lemma ha_istrlen_code :
  code_at AsanUbsan.M.loaded_segments ha_istrlen_entry 0 istrlen_words.
Proof. unfold istrlen_words. code_at_vm. Qed.

Theorem ha_istrlen : forall mem (s : word) buf K rom regs (ret : word),
  strH AsanUbsan.M.loaded_segments mem s buf K ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs ha_istrlen_entry mem rom) (mkst regs' ret mem rom)
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ regs_agree (fun r => In r istrlen_clob) regs regs'.
Proof.
  intros mem s buf K rom regs ret HOK Hret H1 H10.
  rewrite <- (at_0 ha_istrlen_entry).
  exact (istrlen_run _ _ mem s buf K rom (istrlen_code_of_code_at _ _ ha_istrlen_code) HOK regs ret Hret H1 H10).
Qed.
