(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec HeapIface HeapIfaceA L5Defs L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0
     L5BOpnew L5BRoundUpS L5BAReserve L5BBReserve L5BResize.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5SLICEA.
Section SCFG_1.
Context {SCFG_P : L5Defs.ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : L5A.as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Theorem opnew_ok : L5CSA.opnew_spec L ar HI. Proof. exact (L5ANEW.opnew_ok L ar C HI LY HIok). Qed.
Theorem roundup_ok : L5CSA.roundup_spec L ar HI. Proof. exact (L5ARUS.roundup_ok L ar C HI LY HIok). Qed.
Theorem areserve_ok : L5CSA.areserve_spec L ar HI. Proof. exact (L5AARS.areserve_ok L ar C HI LY HIok roundup_ok opnew_ok). Qed.
Theorem reserve_ok : L5CSA.reserve_spec L ar HI. Proof. exact (L5ARSV.reserve_ok L ar C HI LY HIok areserve_ok). Qed.
Theorem resize_ok : L5CSA.resize_spec L ar HI. Proof. exact (L5ARZ.resize_ok L ar C HI LY HIok reserve_ok). Qed.
End SCFG_1.
End L5SLICEA.
