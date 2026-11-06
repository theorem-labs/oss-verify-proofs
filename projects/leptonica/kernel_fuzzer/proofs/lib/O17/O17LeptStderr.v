(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17Kit.
Import O17Kit.O17PFBase. Import O17Kit.O17PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L17 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13a04; SSP.ls_handler_cell := 0x201c8; SSP.ls_devnull := 0x139cc;
     SSP.ls_canary_got := 0x1f180; SSP.ls_canary := 0x50788;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1f000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x51000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x10302; 0x10380; 0x103b0; 0x10486; 0x10593; 0x105f7; 0x10636; 0x106a8; 0x106d6;
                  0x10739; 0x107be; 0x10831; 0x10883; 0x10936; 0x109ff; 0x10a40; 0x10a89; 0x10ae7];
     SSP.ls_fmts2 := [0x10b2b];
     SSP.ls_sev_got := 0x1f150; SSP.ls_sev := 0x201c0 |}.

Lemma L17_ok1 : ls_ok1 L17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L17_ok2 : ls_ok2 L17 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L17).
Proof. exact (lept_stderr_s1_contract L17 L17_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L17).
Proof. exact (lept_stderr_s2_contract L17 L17_ok2). Qed.
End WithFP.
