(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
Import ListNotations.
Open Scope Z_scope.

Notation A0_TSD_INITED := 733536%Z.
Notation A0_ASAN_INITED := 738776%Z.
Notation A0_TSD := 6323480%Z.
Notation PAGE_CELL := 1323936%Z.
Notation GOT_PAGE := 696496%Z.

Record athread := mkAT {
  at_ctx : Z;
  at_thr : Z;
  at_top : Z;
  at_bottom : Z
}.

Section E.
Context {HC : HasCeiling}.
Variable L : athread.

Definition thread_env (m : mem) : Prop :=
  rw_cells asegs m A0_TSD_INITED [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]
  /\ rw_cells asegs m A0_ASAN_INITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 6187288 [C8 (wz A0_TSD)]
  /\ rw_cells asegs m A0_TSD [C8 (wz (at_ctx L))]
  /\ rw_cells asegs m (at_ctx L + 152) [C8 (wz (at_thr L))]
  /\ rw_cells asegs m (at_thr L + 8) [C8 (wz (at_top L)); C8 (wz (at_bottom L))]
  /\ rw_cells asegs m (at_thr L + 40) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m (at_thr L + 3168) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m GOT_PAGE [C8 (wz PAGE_CELL)]
  /\ rw_cells asegs m PAGE_CELL [C8 (wz 4096)].

Definition thread_layout_ok : Prop :=
  (((0 < at_ctx L /\ at_ctx L + 4096 <= 0x10000) \/ (0x609000 <= at_ctx L /\ at_ctx L + 4096 <= 0x7fff7000) \/ 0x10007fff8000 <= at_ctx L) /\ 0x10007fff8000 <= alloc_ceiling) /\ at_ctx L + 4096 <= alloc_ceiling /\
  (((0 < at_thr L /\ at_thr L + 4096 <= 0x10000) \/ (0x609000 <= at_thr L /\ at_thr L + 4096 <= 0x7fff7000) \/ 0x10007fff8000 <= at_thr L) /\ 0x10007fff8000 <= alloc_ceiling) /\ at_thr L + 4096 <= alloc_ceiling /\
  (at_ctx L + 4096 <= at_thr L \/ at_thr L + 4096 <= at_ctx L) /\
  at_ctx L mod 4096 = 0 /\ at_thr L mod 4096 = 0 /\
  alloc_ceiling - 160 <= at_bottom L < alloc_ceiling + 4096 /\ at_bottom L + 2^23 = at_top L /\ at_top L <= 2^47 /\ at_top L mod 4096 = 0.

End E.

Ltac te_split TE :=
  let H1 := fresh "TE_tsd" in let H2 := fresh "TE_inited" in let H3 := fresh "TE_tp" in let H4 := fresh "TE_ctx" in
  let H5 := fresh "TE_thr" in let H6 := fresh "TE_bounds" in let H7 := fresh "TE_sw" in let H8 := fresh "TE_unw" in
  let H9 := fresh "TE_gotpg" in let H10 := fresh "TE_pg" in
  destruct TE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
