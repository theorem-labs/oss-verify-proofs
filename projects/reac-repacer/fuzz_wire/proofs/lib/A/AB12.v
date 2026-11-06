(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire's asan image by atable.py (sha256 42e18a7eef50, not in the published tree) from fuzz_wire.asan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at c8557374ad2e gives the text only. *)
(* Read from: fuzz_wire.asan (reac-repacer/fuzz_wire asan) sha256 2f8f8697cd4f99bd15999cce4963a6fcc39b308444bd58e2bf526ec7c1ad5fa1; unstripped twin sha256 d2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128 *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f5000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2ff7c; rw_lo := 0x9a000; rw_len := 0x55b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63330; x_imemcpy := 0x632b4; x_memset := 0x91f18; x_memcpy := 0x91b14; x_memiszero := 0x63860;
x_istrncpy := 0x6375c; x_sealed := 0x11806; x_popfree := 0x36368;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x87918; x_envscan_k := 0x87924; x_pnscan := 0x879dc; x_pnscan_k := 0x879e8;
stops_more := [0x33fdc; 0x35600; 0x5363c; 0x599f4; 0x59a08; 0x59a1c; 0x5f3ac; 0x5f47c; 0x6c9a8; 0x6d8b4; 0x6da44; 0x7779c; 0x6dbb4]
|}.
Definition TFIB_TEXT_LO : Z := 0x2ff7c.
Definition TFIB_TEXT_N : nat := 105652.
