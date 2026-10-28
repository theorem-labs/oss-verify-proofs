(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL .
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF PFBase PFSpec.
Import ListNotations.
Open Scope Z_scope.

Section Env.
Context {RLOC : Reloc}.
Definition LG : SSP.ls_addrs :=
  {| SSP.ls_entry := (0x13694 + dF_13694); SSP.ls_handler_cell := (0x1f428 + dA_1f3f8); SSP.ls_devnull := (0x1365c + dF_1365c);
     SSP.ls_canary_got := (0x1e3e0 + dA_1e3b8); SSP.ls_canary := (0x2f848 + dA_2f848);
     SSP.ls_img_lo := rl_img_lo; SSP.ls_img_hi := rl_rw_lo;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := rl_img_hi + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [(0x102fd + dVLS_102fd); (0x1035b + dVLS_1035b); (0x1038b + dVLS_1038b); (0x104ff + dVLS_104ff); (0x10563 + dVLS_10563); (0x10591 + dVLS_10591); (0x10603 + dVLS_10603); (0x10631 + dVLS_10631); (0x106a1 + dVLS_106a1);
                  (0x10726 + dVLS_10726); (0x1075b + dVLS_1075b); (0x107bc + dVLS_107bc); (0x10887 + dVLS_10887); (0x10950 + dVLS_10950); (0x10991 + dVLS_10991); (0x109d5 + dVLS_109d5)];
     SSP.ls_fmts2 := [(0x10a13 + dS_10a13)];
     SSP.ls_sev_got := (0x1e3b0 + dA_1e3a0); SSP.ls_sev := (0x1f420 + dA_1f3f8) |}.
End Env.

Class RelocLeptEnvVL (RL : Reloc) := {
  rl_lenv_ok1 : ls_ok1 (@LG RL) = true;
  rl_lenv_ok2 : ls_ok2 (@LG RL) = true }.

Section WithFP.
  Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC}
          {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LG).
Proof. exact (lept_stderr_s1_contract LG rl_lenv_ok1). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LG).
Proof. exact (lept_stderr_s2_contract LG rl_lenv_ok2). Qed.
End WithFP.
