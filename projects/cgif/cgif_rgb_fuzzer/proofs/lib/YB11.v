(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0a.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TRB : atable :=
{| img_lo := 0x10000; img_hi := 0x600000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30828; rw_lo := 0xa4000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64748; x_imemcpy := 0x646cc; x_memset := 0x9c980; x_memcpy := 0x9c57c; x_memiszero := 0x64c78;
x_istrncpy := 0x64b74; x_sealed := 0x1184d; x_popfree := 0x36e20;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x91e68; x_envscan_k := 0x91e74; x_pnscan := 0x91f2c; x_pnscan_k := 0x91f38;
stops_more := [0x34a94; 0x360b8; 0x54a54; 0x5ae0c; 0x5ae20; 0x5ae34; 0x607c4; 0x60894; 0x6ddc0; 0x6eccc; 0x6ee5c; 0x78bb4]
|}.
Definition TRB_TEXT_LO : Z := 0x30828.
Definition TRB_TEXT_N : nat := 111037.
