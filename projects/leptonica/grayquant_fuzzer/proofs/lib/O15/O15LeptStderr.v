(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Kit.
Import O15Kit.O15PFBase. Import O15Kit.O15PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x153dc; SSP.ls_handler_cell := 0x2d7f8; SSP.ls_devnull := 0x153a4;
     SSP.ls_canary_got := 0x2c7b0; SSP.ls_canary := 0x5ddb8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x2c000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x5f000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x10389; 0x10454; 0x10493; 0x108c1; 0x1094b; 0x109e6; 0x10a94; 0x10ac2;
                  0x10bfa; 0x10cf9; 0x10d7a; 0x10e47; 0x10fe4; 0x11199; 0x1124f; 0x11310; 0x11372];
     SSP.ls_fmts2 := [0x11483];
     SSP.ls_sev_got := 0x2c780; SSP.ls_sev := 0x2d7f0 |}.

Lemma L21_ok1 : ls_ok1 L16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L21_ok2 : ls_ok2 L16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof. exact (lept_stderr_s1_contract L16 L21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof. exact (lept_stderr_s2_contract L16 L21_ok2). Qed.
End WithFP.
