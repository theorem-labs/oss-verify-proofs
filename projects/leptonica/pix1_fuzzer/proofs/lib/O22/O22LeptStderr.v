(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Kit.
Import O22Kit.O22PFBase. Import O22Kit.O22PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L22 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x1371c; SSP.ls_handler_cell := 0x1f848; SSP.ls_devnull := 0x136e4;
     SSP.ls_canary_got := 0x1e800; SSP.ls_canary := 0x4fe08;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1e000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x51000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102f1; 0x1034f; 0x1037f; 0x104fd; 0x10561; 0x1058f; 0x10601; 0x1062f; 0x10692;
                  0x10717; 0x1074c; 0x1079e; 0x10845; 0x1090e; 0x1094f; 0x10987];
     SSP.ls_fmts2 := [0x109d4];
     SSP.ls_sev_got := 0x1e7d0; SSP.ls_sev := 0x1f840 |}.

Lemma L22_ok1 : ls_ok1 L22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L22_ok2 : ls_ok2 L22 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L22).
Proof. exact (lept_stderr_s1_contract L22 L22_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L22).
Proof. exact (lept_stderr_s2_contract L22 L22_ok2). Qed.
End WithFP.
