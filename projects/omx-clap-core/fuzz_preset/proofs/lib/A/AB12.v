(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by the internal file gen_geom.py from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v: every image number is computed from that ELF (program headers, symbols, asan_globals), module paths changed. *)
(* Generator: tools/startup/gen_geom.py sha256 62d913384d64f806abd4c64988fe0dd3acec6cc5f7b3a7be6c55ff04693a6d93; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; donor A/AB12.v blob 58931e15a4d1cec7b4c9eb5906508d95e830d2fd. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x600000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x31374; rw_lo := 0xa3000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64ab8; x_imemcpy := 0x64a3c; x_memset := 0x9b6b8; x_memcpy := 0x9b2b4; x_memiszero := 0x64fe8;
x_istrncpy := 0x64ee4; x_sealed := 0x1184c; x_popfree := 0x3796c;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8e900; x_envscan_k := 0x8e90c; x_pnscan := 0x8e9c4; x_pnscan_k := 0x8e9d0;
stops_more := [0x355e0; 0x36c04; 0x54dc4; 0x5b17c; 0x5b190; 0x5b1a4; 0x60b34; 0x60c04; 0x6e130; 0x6f03c; 0x6f1cc; 0x78f24]
|}.
Definition TFIB_TEXT_LO : Z := 0x31374.
Definition TFIB_TEXT_N : nat := 114078.
