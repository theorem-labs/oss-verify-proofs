(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9Kit.
Import V9Kit.V9PFBase. Import V9Kit.V9PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x5d1f8; SSP.ls_handler_cell := 0xfa308; SSP.ls_devnull := 0x5d1c0;
     SSP.ls_canary_got := 0xf92a8; SSP.ls_canary := 0x12aac8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0xf5000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x12c000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1080e; 0x11ab8; 0x11af7; 0x145b2; 0x14c53; 0x1520d; 0x15830; 0x1585e;
                  0x1637a; 0x169a2; 0x174a3; 0x17a9d; 0x18f9a; 0x19f0d; 0x1a578; 0x1ac3e; 0x1b06c];
     SSP.ls_fmts2 := [0x1bc62];
     SSP.ls_sev_got := 0xf9120; SSP.ls_sev := 0xfa300 |}.

Lemma LU21_ok1 : ls_ok1 LU16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU21_ok2 : ls_ok2 LU16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16).
Proof. exact (lept_stderr_s1_contract LU16 LU21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU16).
Proof. exact (lept_stderr_s2_contract LU16 LU21_ok2). Qed.
End WithFP.
