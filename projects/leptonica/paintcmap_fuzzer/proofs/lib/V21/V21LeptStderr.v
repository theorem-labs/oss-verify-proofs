(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21Kit.
Import V21Kit.V21PFBase. Import V21Kit.V21PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU21 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13e70; SSP.ls_handler_cell := 0x21ed0; SSP.ls_devnull := 0x13e38;
     SSP.ls_canary_got := 0x20e88; SSP.ls_canary := 0x52488;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x20000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x53000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102fd; 0x10388; 0x103be; 0x103fd; 0x105ec; 0x10674; 0x106a2; 0x10730; 0x1075e;
                  0x1080c; 0x108a8; 0x1090e; 0x109ae; 0x10a8c; 0x10b9c; 0x10bfa; 0x10c3e; 0x10c9b];
     SSP.ls_fmts2 := [0x10ce5];
     SSP.ls_sev_got := 0x20e58; SSP.ls_sev := 0x21ec8 |}.

Lemma LU21_ok1 : ls_ok1 LU21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU21_ok2 : ls_ok2 LU21 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU21).
Proof. exact (lept_stderr_s1_contract LU21 LU21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU21).
Proof. exact (lept_stderr_s2_contract LU21 LU21_ok2). Qed.
End WithFP.
