(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23PFBase V23PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x636a4; SSP.ls_handler_cell := 0x127c68; SSP.ls_devnull := 0x6366c;
     SSP.ls_canary_got := 0x126c00; SSP.ls_canary := 0x158440;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x123000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x159000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x109df; 0x11fa6; 0x11fe5; 0x152d7; 0x15a86; 0x161f1; 0x16977; 0x169a5;
                  0x176fb; 0x17eae; 0x18b8f; 0x19310; 0x1acc2; 0x1c08e; 0x1c850; 0x1d05d; 0x1d560];
     SSP.ls_fmts2 := [0x1e3b4];
     SSP.ls_sev_got := 0x126a70; SSP.ls_sev := 0x127c60 |}.

Lemma LU21_ok1 : ls_ok1 LU16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU21_ok2 : ls_ok2 LU16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16).
Proof. exact (lept_stderr_s1_contract LU16 LU21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU16).
Proof. exact (lept_stderr_s2_contract LU16 LU21_ok2). Qed.
End WithFP.
