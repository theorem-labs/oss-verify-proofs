(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Definition in_foot_f (F0L : list SR.region) (b : expr) (k : Z) (w : Z) : bool := SegBoil.in_foot_b b k w F0L.
Definition in_kn_f (kn0 : list kentry) (K : kentry) : bool := SegBoil.in_kn_b K kn0.
Definition live_f (SPV : nat) (spoff : Z) (b : expr) (k : Z) : bool := SegBoil.live_b spoff b k SPV.
Definition cells_of_f (live : Z -> expr -> Z -> bool) (in_foot : expr -> Z -> Z -> bool) (in_kn0 : kentry -> bool) (sF : sym_state) (spoff : Z)
: list kentry := SegBoil.cells_of_b sF spoff live in_foot in_kn0.
Definition spoff_of_f (SPV : nat) (sF : sym_state) : Z := SegBoil.spoff_of_b sF SPV.
Definition mkps_f (F0L : list SR.region) (cells_of : sym_state -> Z -> list kentry) (spoff_of : sym_state -> Z) (st : sym_state) : SR.post_spec :=
SegBoil.mkps_b st F0L cells_of spoff_of.
Definition v0_f (k : Z) : expr := SegBoil.v0_b k.
Definition ps_f (pc : Z) (regs_out : list expr) (F0L : list SR.region) (cells : list kentry) : SR.post_spec := SegBoil.ps_b pc regs_out F0L cells.
