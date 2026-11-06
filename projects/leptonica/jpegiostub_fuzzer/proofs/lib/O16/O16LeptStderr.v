(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require Import O16Kit.
Import O16Kit.O16PFBase. Import O16Kit.O16PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x1371c; SSP.ls_handler_cell := 0x1f7f8; SSP.ls_devnull := 0x136e4;
     SSP.ls_canary_got := 0x1e7b0; SSP.ls_canary := 0x4fdb8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1e000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x51000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102f1; 0x1034f; 0x1037f; 0x104e0; 0x10544; 0x10572; 0x105e4; 0x10612; 0x10675;
                  0x106fa; 0x1072f; 0x10781; 0x1083d; 0x10906; 0x10947; 0x1097f];
     SSP.ls_fmts2 := [0x109da];
     SSP.ls_sev_got := 0x1e780; SSP.ls_sev := 0x1f7f0 |}.

Lemma L16_ok1 : ls_ok1 L16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L16_ok2 : ls_ok2 L16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof. exact (lept_stderr_s1_contract L16 L16_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof. exact (lept_stderr_s2_contract L16 L16_ok2). Qed.
End WithFP.
