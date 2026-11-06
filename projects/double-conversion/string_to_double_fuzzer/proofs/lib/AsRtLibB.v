(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare MemSplit BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import ZX BM. Open Scope Z_scope.

Lemma cellN_rt_B : forall mem a n v,
  rt_ok_B mem -> tbl_val RT_B a n = Some v -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN SEGS_B mem a n v.
Proof. intros mem a n v Hrt Hv Ha Hb. apply (cellN_of_rdtbl SEGS_B RT_B); [exact Hrt | exact Hv | exact Ha | exact Hb]. Qed.

Lemma cellN_ro_B : forall mem a n v,
  ro_ok SEGS_B RO_B mem -> in_ro RO_B a n = true -> rom_val SEGS_B a n = Some v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> cellN SEGS_B mem a n v.
Proof. intros. eapply cellN_ro; eauto. Qed.
