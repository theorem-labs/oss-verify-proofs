(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17Kit.
Import V17Kit.V17PFBase. Import V17Kit.V17PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU17 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13b08; SSP.ls_handler_cell := 0x20a48; SSP.ls_devnull := 0x13ad0;
     SSP.ls_canary_got := 0x1fa00; SSP.ls_canary := 0x51008;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1f000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x52000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1030e; 0x1038c; 0x103bc; 0x10492; 0x105b2; 0x10616; 0x10655; 0x106c7; 0x106f5;
                  0x10765; 0x107ea; 0x1085d; 0x108be; 0x10980; 0x10a49; 0x10a8a; 0x10adf; 0x10b3d];
     SSP.ls_fmts2 := [0x10b81];
     SSP.ls_sev_got := 0x1f9d0; SSP.ls_sev := 0x20a40 |}.

Lemma LU17_ok1 : ls_ok1 LU17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU17_ok2 : ls_ok2 LU17 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU17).
Proof. exact (lept_stderr_s1_contract LU17 LU17_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU17).
Proof. exact (lept_stderr_s2_contract LU17 LU17_ok2). Qed.
End WithFP.
