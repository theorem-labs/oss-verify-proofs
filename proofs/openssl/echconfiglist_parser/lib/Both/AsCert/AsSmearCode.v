(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma asan_smear_x : 0 <= x_smear ASAN_H /\ x_smear ASAN_H + 112 < 2 ^ 64.
Proof. cbn [x_smear ASAN_H]. lia. Qed.

Lemma asan_smear_fwa :
  fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H)) = Some (0x00155593%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 4)) = Some (0x55555637%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 8)) = Some (0x333336b7%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 12)) = Some (0x0f0f1737%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 16)) = Some (0x010107b7%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 20)) = Some (0x00b56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 24)) = Some (0x5556059b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 28)) = Some (0x3336861b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 32)) = Some (0xf0f7069b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 36)) = Some (0x1017871b%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 40)) = Some (0x00255793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 44)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 48)) = Some (0x02059793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 52)) = Some (0x00f585b3%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 56)) = Some (0x02061793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 60)) = Some (0x00f60633%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 64)) = Some (0x02069793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 68)) = Some (0x00f686b3%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 72)) = Some (0x02071793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 76)) = Some (0x00f70733%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 80)) = Some (0x00455793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 84)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 88)) = Some (0x00855793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 92)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 96)) = Some (0x01055793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 100)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 104)) = Some (0x02055793%bv : bv 32)
    /\ fetch_word ASEGS (Z_to_bv 64 (x_smear ASAN_H + 108)) = Some (0x00f56533%bv : bv 32).
Proof. repeat split; vm_refl. Qed.
