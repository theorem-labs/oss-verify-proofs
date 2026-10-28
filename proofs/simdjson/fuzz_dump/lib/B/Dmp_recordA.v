(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc D_libiface El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_topA Dmp_clientA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Open Scope Z_scope.

Section Rec.

Variable PJ : forall PMc, pj_root_cpsA RTA PMc.

Theorem dmp_cl_fuzz : rt_contracts2 RTA -> fuzz_one_cps RTA el_libA.
Proof. intros _. exact (rta_fuzz_one_dmp PJ). Qed.
End Rec.
