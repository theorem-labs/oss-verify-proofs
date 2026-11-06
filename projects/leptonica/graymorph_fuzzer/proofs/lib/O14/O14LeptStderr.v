(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit.
Import O14Kit.O14PFBase. Import O14Kit.O14PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x153a0; SSP.ls_handler_cell := 0x2bab8; SSP.ls_devnull := 0x15368;
     SSP.ls_canary_got := 0x2aa70; SSP.ls_canary := 0x5c078;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x2a000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x5d000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1034c; 0x1041e; 0x1045d; 0x1090c; 0x1098a; 0x10a01; 0x10aeb; 0x10b19;
                  0x10c10; 0x10cac; 0x10d2c; 0x10de2; 0x10f6f; 0x11121; 0x111ab; 0x11252; 0x112e7];
     SSP.ls_fmts2 := [0x113a3];
     SSP.ls_sev_got := 0x2aa40; SSP.ls_sev := 0x2bab0 |}.

Lemma L21_ok1 : ls_ok1 L16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L21_ok2 : ls_ok2 L16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof. exact (lept_stderr_s1_contract L16 L21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof. exact (lept_stderr_s2_contract L16 L21_ok2). Qed.
End WithFP.
