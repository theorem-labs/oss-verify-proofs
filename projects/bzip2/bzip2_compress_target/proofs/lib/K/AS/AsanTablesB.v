(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x62b000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x316cc; rw_lo := 0xcc000; rw_len := 0x55f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x647dc; x_imemcpy := 0x64760; x_memset := 0xc6568; x_memcpy := 0xc6164; x_memiszero := 0x64d0c;
     x_istrncpy := 0x64c08; x_sealed := 0x11871; x_popfree := 0x37ab8;
     x_sniff := 0x65e24; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xbbd48; x_envscan_k := 0xbbd54; x_pnscan := 0xbbe0c; x_pnscan_k := 0xbbe18;
     stops_more := [0x3572c; 0x36d50; 0x54ae8; 0x5aea0; 0x5aeb4; 0x5aec8; 0x60858; 0x60928; 0x6de54; 0x6ed60; 0x6eef0; 0x78c48];
     x_hsort := 0x52788 |}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_b_init : acs := init_acs_of ASAN_B.
