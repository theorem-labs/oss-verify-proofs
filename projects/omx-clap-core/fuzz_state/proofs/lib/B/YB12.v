(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB12.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fd000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30d20; rw_lo := 0xa1000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64464; x_imemcpy := 0x643e8; x_memset := 0x99340; x_memcpy := 0x98f3c; x_memiszero := 0x64994;
x_istrncpy := 0x64890; x_sealed := 0x1184c; x_popfree := 0x37318;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c588; x_envscan_k := 0x8c594; x_pnscan := 0x8c64c; x_pnscan_k := 0x8c658;
stops_more := [0x34f8c; 0x365b0; 0x54770; 0x5ab28; 0x5ab3c; 0x5ab50; 0x604e0; 0x605b0; 0x6dadc; 0x6e9e8; 0x6eb78; 0x788d0]
|}.
Definition TFIB_TEXT_LO : Z := 0x30d20.
Definition TFIB_TEXT_N : nat := 112213.
