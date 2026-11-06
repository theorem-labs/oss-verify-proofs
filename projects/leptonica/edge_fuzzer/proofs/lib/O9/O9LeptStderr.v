(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9Kit.
Import O9Kit.O9PFBase. Import O9Kit.O9PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x5ce08; SSP.ls_handler_cell := 0xef758; SSP.ls_devnull := 0x5cdd0;
     SSP.ls_canary_got := 0xee6f8; SSP.ls_canary := 0x11ff18;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0xeb000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x121000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x1080e; 0x11ab8; 0x11af7; 0x14596; 0x14c37; 0x151f1; 0x15814; 0x15842;
                  0x1635e; 0x16986; 0x17472; 0x17a6b; 0x18f5b; 0x19ebd; 0x1a528; 0x1abd9; 0x1afcc];
     SSP.ls_fmts2 := [0x1bbc2];
     SSP.ls_sev_got := 0xee570; SSP.ls_sev := 0xef750 |}.

Lemma L21_ok1 : ls_ok1 L16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L21_ok2 : ls_ok2 L16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof. exact (lept_stderr_s1_contract L16 L21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof. exact (lept_stderr_s2_contract L16 L21_ok2). Qed.
End WithFP.
