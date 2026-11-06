(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v, with its module paths changed; the image table is fuzz_grant.asan's, from its program headers, symbols and .text size. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fa000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x307dc; rw_lo := 0x9e000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63b88; x_imemcpy := 0x63b0c; x_memset := 0x95e30; x_memcpy := 0x95a2c; x_memiszero := 0x640b8;
x_istrncpy := 0x63fb4; x_sealed := 0x117fe; x_popfree := 0x36bc8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8b830; x_envscan_k := 0x8b83c; x_pnscan := 0x8b8f4; x_pnscan_k := 0x8b900;
stops_more := [0x3483c; 0x35e60; 0x53e94; 0x5a24c; 0x5a260; 0x5a274; 0x5fc04; 0x5fcd4; 0x6d200; 0x6e10c; 0x6e29c; 0x77ff4]
|}.
Definition TFIB_TEXT_LO : Z := 0x307dc.
Definition TFIB_TEXT_N : nat := 109154.
