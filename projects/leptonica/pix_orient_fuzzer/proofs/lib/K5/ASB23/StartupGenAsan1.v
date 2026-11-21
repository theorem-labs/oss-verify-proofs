(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the ASan+UBSan image's start-up join and hole tables WITH
   CONFIG_RSEQ (r = 1: 29 auxv pairs), computed from [asan_a_init 1] by one run of
   [StartupCoGen.gc_cc] ([startup_coll 1]). *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupCoGen.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.ASB23 Require Import StartupJSAsan StartupGenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_tabs_1 : gc_out := Eval vm_compute in gc_one (startup_coll 1) startup_seedJ.
