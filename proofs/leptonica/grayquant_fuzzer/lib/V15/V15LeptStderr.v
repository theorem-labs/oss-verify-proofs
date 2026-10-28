(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit.
Import V15Kit.V15PFBase. Import V15Kit.V15PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition LU16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x15520; SSP.ls_handler_cell := 0x35270; SSP.ls_devnull := 0x154e8;
     SSP.ls_canary_got := 0x34228; SSP.ls_canary := 0x65828;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x34000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x67000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x10389; 0x10454; 0x10493; 0x108c1; 0x1094b; 0x109e6; 0x10a94; 0x10ac2;
                  0x10bfa; 0x10cf9; 0x10d7a; 0x10e47; 0x10fe4; 0x11199; 0x1124f; 0x11310; 0x11372];
     SSP.ls_fmts2 := [0x11483];
     SSP.ls_sev_got := 0x341f8; SSP.ls_sev := 0x35268 |}.

Lemma LU21_ok1 : ls_ok1 LU16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma LU21_ok2 : ls_ok2 LU16 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LU16).
Proof. exact (lept_stderr_s1_contract LU16 LU21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LU16).
Proof. exact (lept_stderr_s2_contract LU16 LU21_ok2). Qed.
End WithFP.
