(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_state RT_rep RT_stackmalloc RT_stackmalloc3 RT_smgc D_libiface El_defsA
     Drt_hdefsA Drt_topA Drt_clientA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Open Scope Z_scope.

Lemma rta_sm3 : drt_sm3_contract RTA.
Proof. exact (rta_stack_malloc_3 smgc3_proof). Qed.

Theorem drt_cl_fuzz : rt_contracts2 RTA -> fuzz_one_cps RTA el_libA.
Proof. intros _. exact (rta_fuzz_one_drt rta_sm3). Qed.
