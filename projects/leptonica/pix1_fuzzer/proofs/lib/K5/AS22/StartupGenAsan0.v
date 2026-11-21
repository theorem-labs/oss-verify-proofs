(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the ASan image's start-up join and hole tables WITHOUT
   CONFIG_RSEQ (r = 0: 27 auxv pairs), computed by [StartupCoGen.gc_go2] from [asan_a_init 0]. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupCoGen.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS22 Require Import StartupJSAsan StartupGenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_tabs_0 : gc_out := Eval vm_compute in gc_go2 (startup_chk 0) js_0 startup_rounds startup_seedJ.
