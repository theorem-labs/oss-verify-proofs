(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
Import ListNotations. Import SP.
Open Scope Z_scope.

Definition REF_ATB : atable :=
  {| t_memcpy := 0x23640; t_memset := 0x23a44; t_strnlen := 0x23d3c; t_memchr := 0x23544; t_F := 0x13e80;
     t_F_ret := 0x13d7c; t_tp := 0x367b0; t_F_frame := 0x205c0; t_F_nmax := 0x4000000; t_cas_or := 0x1c430;
     t_cas_or_k := 0x1c450; t_cas_and := 0x1cc10; t_cas_and_k := 0x1cc30; t_cas_lock := 0x1bb18;
     t_cas_lock_k := 0x1bb28; t_calls := 0x13d9c; t_main_ret := 0x13b54; t_main_join := 0x13bd4;
     t_enframe := 0x1d374; t_freepro := 0x1bdd4; t_freepro_k := 0x1beb0; t_stdio_write := 0x1df28;
     d_prng := 0x26360; d_errno := 0x3670c; d_mcount := 0x366d8; d_ro_hi := 0x2427c; d_malloc_ctx := 0x56ab0;
     d_stdout := 0x26548; d_canary_got := 0x252f8; d_canary := 0x567f0; t_printf := 0x13e38;
     t_printf_ret := 0x13d8c; t_exitc := 0x1baf8; d_stdout_buf := 0x57280; d_stderr := 0x26368; d_sctbl := 0x110c0;
     d_rw_lo := 0x26000;
     e_cells := [(0x56a18, 4%nat, 0x0) (* [comment removed for export] *);
                 (0x25328, 8%nat, 0x25290) (* [comment removed for export] *);
                 (0x25330, 8%nat, 0x25288) (* [comment removed for export] *);
                 (0x25288, 8%nat, 0x13950) (* [comment removed for export] *);
                 (0x26688, 1%nat, 0x0) (* [comment removed for export] *);
                 (0x252d0, 8%nat, 0x1b9dc) (* [comment removed for export] *);
                 (0x252d8, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x56a3b, 1%nat, 0x0) (* [comment removed for export] *);
                 (0x56e60, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26540, 8%nat, 0x26458) (* [comment removed for export] *);
                 (0x26630, 8%nat, 0x26548) (* [comment removed for export] *);
                 (0x26450, 8%nat, 0x26368) (* [comment removed for export] *);
                 (0x56808, 8%nat, 0x56810) (* [comment removed for export] *);
                 (0x567fc, 4%nat, 0x0) (* [comment removed for export] *);
                 (0x26338, 8%nat, 0x26338) (* [comment removed for export] *);
                 (0x264e4, 4%nat, 0xffffffff) (* [comment removed for export] *);
                 (0x26480, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26490, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26460, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26468, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x263f4, 4%nat, 0xffffffff) (* [comment removed for export] *);
                 (0x56800, 4%nat, 0x1) (* [comment removed for export] *);
                 (0x56810, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x56818, 8%nat, 0x1baa4) (* [comment removed for export] *);
                 (0x56918, 8%nat, 0x13e08) (* [comment removed for export] *);
                 (0x36694, 1%nat, 0x0) (* [comment removed for export] *)]%Z |}.
