(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x61e000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x317e4; rw_lo := 0xbf000; rw_len := 0x55f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x64d90; x_imemcpy := 0x64d14; x_memset := 0xb9188; x_memcpy := 0xb8d84; x_memiszero := 0x652c0;
     x_istrncpy := 0x651bc; x_sealed := 0x11871; x_popfree := 0x37bd0;
     x_sniff := 0x663d8; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xae968; x_envscan_k := 0xae974; x_pnscan := 0xaea2c; x_pnscan_k := 0xaea38;
     stops_more := [0x35844; 0x36e68; 0x5509c; 0x5b454; 0x5b468; 0x5b47c; 0x60e0c; 0x60edc; 0x6e408; 0x6f314; 0x6f4a4; 0x791fc];
     x_hsort := 0x528a0 |}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_a_init : acs := init_acs_of ASAN_A.
