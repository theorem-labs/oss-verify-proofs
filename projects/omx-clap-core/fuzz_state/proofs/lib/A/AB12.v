(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: GENERATED, not relocated: the TFIB atable emitted by a Theorem Labs lane's startcmd-parts/ab12/atable.py --side A from fuzz_state.asan sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0 (symbols from its unstripped twin, PT_LOAD bytes equal); TFIB_TEXT_N is .text's word count. *)
(* Read from: fuzz_state.asan (omx-clap-core/fuzz_state asan) sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0; unstripped twin sha256 7c4afaee248b8017a370860e6a03a41f552f7666067c565774544e0b8115b23b *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fd000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30cb0; rw_lo := 0xa1000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x643f4; x_imemcpy := 0x64378; x_memset := 0x98e24; x_memcpy := 0x98a20; x_memiszero := 0x64924;
x_istrncpy := 0x64820; x_sealed := 0x1184c; x_popfree := 0x372a8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c06c; x_envscan_k := 0x8c078; x_pnscan := 0x8c130; x_pnscan_k := 0x8c13c;
stops_more := [0x34f1c; 0x36540; 0x54700; 0x5aab8; 0x5aacc; 0x5aae0; 0x60470; 0x60540; 0x6da6c; 0x6e978; 0x6eb08; 0x78860]
|}.
Definition TFIB_TEXT_LO : Z := 0x30cb0.
Definition TFIB_TEXT_N : nat := 111914.
