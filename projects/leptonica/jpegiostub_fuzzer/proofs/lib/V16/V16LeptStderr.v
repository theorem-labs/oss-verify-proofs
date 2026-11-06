(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.V16 Require Import V16Kit.
Import V16Kit.V16PFBase. Import V16Kit.V16PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x137d8; SSP.ls_handler_cell := 0x1fe40; SSP.ls_devnull := 0x137a0;
     SSP.ls_canary_got := 0x1edf8; SSP.ls_canary := 0x503f8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1e000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x51000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102fd; 0x1035b; 0x1038b; 0x104ff; 0x10563; 0x10591; 0x10603; 0x10631; 0x106a1;
                  0x10726; 0x1075b; 0x107bc; 0x10887; 0x10950; 0x10991; 0x109d5];
     SSP.ls_fmts2 := [0x10a30];
     SSP.ls_sev_got := 0x1edc8; SSP.ls_sev := 0x1fe38 |}.

Lemma LU16_ok1 : ls_ok1 LU16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU16_ok2 : ls_ok2 LU16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16).
Proof. exact (lept_stderr_s1_contract LU16 LU16_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU16).
Proof. exact (lept_stderr_s2_contract LU16 LU16_ok2). Qed.
End WithFP.
