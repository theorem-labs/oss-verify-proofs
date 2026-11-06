(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10Kit.
Import O10Kit.O10PFBase. Import O10Kit.O10PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x156a0; SSP.ls_handler_cell := 0x2ca90; SSP.ls_devnull := 0x15668;
     SSP.ls_canary_got := 0x2ba48; SSP.ls_canary := 0x5d368;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x2b000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x5e000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1035d; 0x1047f; 0x104be; 0x10a28; 0x10ab2; 0x10b50; 0x10c1c; 0x10c4a;
                  0x10d4a; 0x10dff; 0x10eac; 0x10f6a; 0x11136; 0x112f2; 0x113a1; 0x11436; 0x114ec];
     SSP.ls_fmts2 := [0x115cf];
     SSP.ls_sev_got := 0x2ba18; SSP.ls_sev := 0x2ca88 |}.

Lemma L21_ok1 : ls_ok1 L16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L21_ok2 : ls_ok2 L16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof. exact (lept_stderr_s1_contract L16 L21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof. exact (lept_stderr_s2_contract L16 L21_ok2). Qed.
End WithFP.
