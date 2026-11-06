(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/CfNmaxwPreset.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset (a Theorem Labs lane): the instance witness of YGcfMallocComposeE.nmaxw_cf_ok
   at preset's CfParams (CfParams_preset, lib/A/CfParamsPreset.v, passed by name).
   nmaxw_cf_ok NOBW ROOMW is the three premises of the widened secondary Allocate (lib/AU/AGioMB.v:63-65; cgif/cgif_file_fuzzer lib/AGio.v (file sha256 0a46493e54da; donor not released) :71-73, as history:
   HNW, HNOB, HROOM) at NMAXW := cf_malloc_max.  At preset: cf_malloc_max = 2 ^ 28 + 2 ^ 27 = 402,653,184,
   NOBW = 2 ^ 29 (= preset's cf_nob, ImgBaseAGS.NOB), ROOMW = 2 ^ 30 (the model's VM_HEAD, YG0n.v:543); the values of
   AGif5.sec_w_preset_room (lib/AU/AGif5.v:1218; cgif/cgif_file_fuzzer lib/AGif5.v (file sha256 6abb6763e12f; donor not released) :1200, as history).  Arithmetic only: no image constant, no function is
   proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
Local Open Scope Z_scope.

Lemma nmaxw_preset_ok : @YGcfMallocComposeE.nmaxw_cf_ok CfParams_preset (2 ^ 29) (2 ^ 30).
Proof. unfold YGcfMallocComposeE.nmaxw_cf_ok. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.
