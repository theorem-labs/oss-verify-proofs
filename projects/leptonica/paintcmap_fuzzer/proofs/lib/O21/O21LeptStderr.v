(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21Kit.
Import O21Kit.O21PFBase. Import O21Kit.O21PFSpec.
Import ListNotations.
Open Scope Z_scope.

Definition L21 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x13de8; SSP.ls_handler_cell := 0x21598; SSP.ls_devnull := 0x13db0;
     SSP.ls_canary_got := 0x20550; SSP.ls_canary := 0x51b58;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x20000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x53000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x102fd; 0x10388; 0x103be; 0x103fd; 0x105ec; 0x10674; 0x106a2; 0x10730; 0x1075e;
                  0x1080c; 0x108a8; 0x1090e; 0x109ae; 0x10a8c; 0x10b9c; 0x10bfa; 0x10c3e; 0x10c9b];
     SSP.ls_fmts2 := [0x10ce5];
     SSP.ls_sev_got := 0x20520; SSP.ls_sev := 0x21590 |}.

Lemma L21_ok1 : ls_ok1 L21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma L21_ok2 : ls_ok2 L21 = true. Proof. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L21).
Proof. exact (lept_stderr_s1_contract L21 L21_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L21).
Proof. exact (lept_stderr_s2_contract L21 L21_ok2). Qed.
End WithFP.
