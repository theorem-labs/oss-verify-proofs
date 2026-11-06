(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8Kit.
Import O8Kit.O8PFBase. Import O8Kit.O8PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L8 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13d84; SSP.ls_handler_cell := 0x21018; SSP.ls_devnull := 0x13d4c;
     SSP.ls_canary_got := 0x1ffd0; SSP.ls_canary := 0x515d8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x1f000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x52000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x10324; 0x1038c; 0x103bc; 0x10408; 0x104b7; 0x1061b; 0x106a6; 0x106d4; 0x1075e;
                  0x1078c; 0x10816; 0x108ae; 0x10901; 0x10969; 0x10a76; 0x10b57; 0x10bca; 0x10c02;
                  0x10c78];
     SSP.ls_fmts2 := [0x10c67];
     SSP.ls_sev_got := 0x1ffa0; SSP.ls_sev := 0x21010 |}.

Lemma L8_ok1 : ls_ok1 L8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L8_ok2 : ls_ok2 L8 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L8).
Proof. exact (lept_stderr_s1_contract L8 L8_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L8).
Proof. exact (lept_stderr_s2_contract L8 L8_ok2). Qed.
End WithFP.
