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

Definition UB_ATB : atable :=
  {| t_memcpy := 0x23ae8; t_memset := 0x23eec; t_strnlen := 0x241e4; t_memchr := 0x239ec; t_F := 0x13f60;
     t_F_ret := 0x13e5c; t_tp := 0x36c60; t_F_frame := 0x20610; t_F_nmax := 0x4000000; t_cas_or := 0x1c8d8;
     t_cas_or_k := 0x1c8f8; t_cas_and := 0x1d0b8; t_cas_and_k := 0x1d0d8; t_cas_lock := 0x1bfc0;
     t_cas_lock_k := 0x1bfd0; t_calls := 0x13e7c; t_main_ret := 0x13c34; t_main_join := 0x13cb4;
     t_enframe := 0x1d81c; t_freepro := 0x1c27c; t_freepro_k := 0x1c358; t_stdio_write := 0x1e3d0;
     d_prng := 0x26808; d_errno := 0x36bbc; d_mcount := 0x36b88; d_ro_hi := 0x24724; d_malloc_ctx := 0x56f60;
     d_stdout := 0x269f0; d_canary_got := 0x257a0; d_canary := 0x56ca0; t_printf := 0x13f18;
     t_printf_ret := 0x13e6c; t_exitc := 0x1bfa0; d_stdout_buf := 0x57730; d_stderr := 0x26810; d_sctbl := 0x110b8;
     d_rw_lo := 0x26000;
     e_cells := [(0x56ec8, 4%nat, 0x0) (* [comment removed for export] *);
                 (0x257d0, 8%nat, 0x25738) (* [comment removed for export] *);
                 (0x257d8, 8%nat, 0x25730) (* [comment removed for export] *);
                 (0x25730, 8%nat, 0x13a30) (* [comment removed for export] *);
                 (0x26b38, 1%nat, 0x0) (* [comment removed for export] *);
                 (0x25778, 8%nat, 0x1be84) (* [comment removed for export] *);
                 (0x25780, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x56eeb, 1%nat, 0x0) (* [comment removed for export] *);
                 (0x57310, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x269e8, 8%nat, 0x26900) (* [comment removed for export] *);
                 (0x26ad8, 8%nat, 0x269f0) (* [comment removed for export] *);
                 (0x268f8, 8%nat, 0x26810) (* [comment removed for export] *);
                 (0x56cb8, 8%nat, 0x56cc0) (* [comment removed for export] *);
                 (0x56cac, 4%nat, 0x0) (* [comment removed for export] *);
                 (0x267e0, 8%nat, 0x267e0) (* [comment removed for export] *);
                 (0x2698c, 4%nat, 0xffffffff) (* [comment removed for export] *);
                 (0x26928, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26938, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26908, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x26910, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x2689c, 4%nat, 0xffffffff) (* [comment removed for export] *);
                 (0x56cb0, 4%nat, 0x1) (* [comment removed for export] *);
                 (0x56cc0, 8%nat, 0x0) (* [comment removed for export] *);
                 (0x56cc8, 8%nat, 0x1bf4c) (* [comment removed for export] *);
                 (0x56dc8, 8%nat, 0x13ee8) (* [comment removed for export] *);
                 (0x36b44, 1%nat, 0x0) (* [comment removed for export] *)]%Z |}.
