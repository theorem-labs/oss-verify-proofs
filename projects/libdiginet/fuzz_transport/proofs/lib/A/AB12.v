(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_transport's asan image by atable.py (start-up set of record, sha256 e88affcf0526) from fuzz_transport.asan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's 13 self-loops; cgif_file_fuzzer's A/AB12.v at origin/ossv/recipes 25e3d17bdb50 gives the text only. *)
(* Read from: fuzz_transport.asan (libdiginet/fuzz_transport asan) sha256 e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350; unstripped twin sha256 86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792 *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x616000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x310d0; rw_lo := 0xa5000; rw_len := 0x571000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x6473c; x_imemcpy := 0x646c0; x_memset := 0x9d614; x_memcpy := 0x9d210; x_memiszero := 0x64c6c;
x_istrncpy := 0x64b68; x_sealed := 0x1183c; x_popfree := 0x374bc;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x93014; x_envscan_k := 0x93020; x_pnscan := 0x930d8; x_pnscan_k := 0x930e4;
stops_more := [0x35130; 0x36754; 0x54a48; 0x5ae00; 0x5ae14; 0x5ae28; 0x607b8; 0x60888; 0x6ddb4; 0x6ecc0; 0x6ee50; 0x78ba8; 0x6efc0]
|}.
Definition TFIB_TEXT_LO : Z := 0x310d0.
Definition TFIB_TEXT_N : nat := 116254.
