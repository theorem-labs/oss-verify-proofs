(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require Import V22Kit.
Import V22Kit.V22PFBase. Import V22Kit.V22PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU22 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x137dc; SSP.ls_handler_cell := 0x1fec0; SSP.ls_devnull := 0x137a4;
     SSP.ls_canary_got := 0x1ee78; SSP.ls_canary := 0x50478;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1e000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x51000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102fd; 0x1035b; 0x1038b; 0x1051c; 0x10580; 0x105ae; 0x10620; 0x1064e; 0x106be;
                  0x10743; 0x10778; 0x107d9; 0x1088f; 0x10958; 0x10999; 0x109dd];
     SSP.ls_fmts2 := [0x10a2a];
     SSP.ls_sev_got := 0x1ee48; SSP.ls_sev := 0x1feb8 |}.

Lemma LU22_ok1 : ls_ok1 LU22 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU22_ok2 : ls_ok2 LU22 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU22).
Proof. exact (lept_stderr_s1_contract LU22 LU22_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU22).
Proof. exact (lept_stderr_s2_contract LU22 LU22_ok2). Qed.
End WithFP.
