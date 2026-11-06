(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8Kit.
Import V8Kit.V8PFBase. Import V8Kit.V8PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU8 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13e58; SSP.ls_handler_cell := 0x21818; SSP.ls_devnull := 0x13e20;
     SSP.ls_canary_got := 0x207d0; SSP.ls_canary := 0x51dd8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x20000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x53000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x10330; 0x10398; 0x103c8; 0x10414; 0x104c3; 0x1063a; 0x106c5; 0x106f3; 0x1077d;
                  0x107ab; 0x10842; 0x108da; 0x1092d; 0x109a4; 0x10ac0; 0x10ba1; 0x10c14; 0x10c58;
                  0x10cce];
     SSP.ls_fmts2 := [0x10cbd];
     SSP.ls_sev_got := 0x207a0; SSP.ls_sev := 0x21810 |}.

Lemma LU8_ok1 : ls_ok1 LU8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU8_ok2 : ls_ok2 LU8 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU8).
Proof. exact (lept_stderr_s1_contract LU8 LU8_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU8).
Proof. exact (lept_stderr_s2_contract LU8 LU8_ok2). Qed.
End WithFP.
