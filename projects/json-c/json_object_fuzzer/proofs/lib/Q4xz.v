(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq6.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition LIT_NULL_A : Z := 0x23100.
Definition LIT_NAN_A : Z := 0x23120.
Definition LIT_TRUE_A : Z := 0x231e0.
Definition LIT_FALSE_A : Z := 0x23200.
Definition nullstrA : list byte := Eval vm_compute in match image_bytes asegs 0x23100 4 with Some bs => bs | None => [] end.
Definition nanstrA : list byte := Eval vm_compute in match image_bytes asegs 0x23120 3 with Some bs => bs | None => [] end.
Definition truestrA : list byte := Eval vm_compute in match image_bytes asegs 0x231e0 4 with Some bs => bs | None => [] end.
Definition falsestrA : list byte := Eval vm_compute in match image_bytes asegs 0x23200 5 with Some bs => bs | None => [] end.

Lemma rodata_bytes_at : forall m a bs, mem_inv asegs m -> ro_bytes_b asegs a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> bytes_at asegs m a bs.
Proof.
intros m a bs MI IMG Ha Hb. assert (RO : ro_cells asegs m a [CB (length bs) bs]) by (apply ro_cells_image; [exact MI | exact IMG | exact Ha | exact Hb]).
destruct RO as [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma null_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m LIT_NULL_A (nullstrA ++ [b0]).
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | unfold LIT_NULL_A; lia | cbn; unfold LIT_NULL_A; lia]. Qed.
Lemma nan_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m LIT_NAN_A (nanstrA ++ [b0]).
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | unfold LIT_NAN_A; lia | cbn; unfold LIT_NAN_A; lia]. Qed.
Lemma true_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m LIT_TRUE_A (truestrA ++ [b0]).
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | unfold LIT_TRUE_A; lia | cbn; unfold LIT_TRUE_A; lia]. Qed.
Lemma false_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m LIT_FALSE_A (falsestrA ++ [b0]).
Proof. intros m MI. apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | unfold LIT_FALSE_A; lia | cbn; unfold LIT_FALSE_A; lia]. Qed.

Lemma null_srcA : forall k, 0 < k <= 5 -> src_globA LIT_NULL_A k.
Proof.
intros k Hk. assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
repeat (destruct C as [-> | C]; [apply src_globA_of_chk; vm_compute; reflexivity|]). subst k. apply src_globA_of_chk; vm_compute; reflexivity.
Qed.
Lemma nan_srcA : forall k, 0 < k <= 4 -> src_globA LIT_NAN_A k.
Proof.
intros k Hk. assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
repeat (destruct C as [-> | C]; [apply src_globA_of_chk; vm_compute; reflexivity|]). subst k. apply src_globA_of_chk; vm_compute; reflexivity.
Qed.
Lemma true_srcA : forall k, 0 < k <= 5 -> src_globA LIT_TRUE_A k.
Proof.
intros k Hk. assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
repeat (destruct C as [-> | C]; [apply src_globA_of_chk; vm_compute; reflexivity|]). subst k. apply src_globA_of_chk; vm_compute; reflexivity.
Qed.
Lemma false_srcA : forall k, 0 < k <= 6 -> src_globA LIT_FALSE_A k.
Proof.
intros k Hk. assert (C : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
repeat (destruct C as [-> | C]; [apply src_globA_of_chk; vm_compute; reflexivity|]). subst k. apply src_globA_of_chk; vm_compute; reflexivity.
Qed.

Definition nandblA : list byte := Eval vm_compute in match image_bytes asegs 0x103f8 8 with Some bs => bs | None => [] end.
Lemma nandbl_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x103f8 [CB 8 nandblA].
Proof. intros m MI. change 8%nat with (length nandblA). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.
End RC__1.
