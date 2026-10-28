(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10PFBase. Import V10Kit.V10PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x157d0; SSP.ls_handler_cell := 0x34e08; SSP.ls_devnull := 0x15798;
     SSP.ls_canary_got := 0x33dc0; SSP.ls_canary := 0x656e8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x33000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x66000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1035d; 0x1047f; 0x104be; 0x10a28; 0x10ab2; 0x10b50; 0x10c1c; 0x10c4a;
                  0x10d4a; 0x10dff; 0x10eac; 0x10f6a; 0x11136; 0x112f2; 0x113a1; 0x11436; 0x114ec];
     SSP.ls_fmts2 := [0x115cf];
     SSP.ls_sev_got := 0x33d90; SSP.ls_sev := 0x34e00 |}.

Lemma LU21_ok1 : ls_ok1 LU16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU21_ok2 : ls_ok2 LU16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16).
Proof. exact (lept_stderr_s1_contract LU16 LU21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU16).
Proof. exact (lept_stderr_s2_contract LU16 LU21_ok2). Qed.
End WithFP.
