(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_gaps_iface Lept_iface Ed_iface Ed_numa_create Ed_numa_addfast Ed_numa_add Ed_ext.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section EXTC.
Variable RT : rt_sig.
Hypothesis RC : rt_contracts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.

Theorem numaFindExtrema_closed : numaFindExtrema_cps RT.
Proof using RC GP EG.
  pose proof (rc_facts RT RC) as AF.
  exact (numaFindExtrema_ok RT AF GP EG (numaCreate_ok RT AF GP EG) (numaAddNumber_fast_ok RT AF GP) (numaAddNumber_ok RT AF GP EG RC)).
Qed.
End EXTC.
