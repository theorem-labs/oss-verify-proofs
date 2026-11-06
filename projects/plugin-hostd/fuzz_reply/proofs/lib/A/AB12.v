(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (27 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: TFIB_TEXT_N is a word count, not an address: the donor's range [0x302dc, 0x302dc + 4*111012) ends at lseek+0x8; fuzz_reply.asan's lseek+0x8 is 0x9c3a4, so the count from 0x30994 is 110212 (the mechanical relocation had moved 111012 as if it were a .rodata address). *)
(* Modified by Theorem Labs, 2026-10: taken into a Theorem Labs lane's generated set: every TFIB field checked against fuzz_reply.asan (a_entry = e_entry 0x30994; img_lo/img_hi = the PT_LOAD hull 0x10000..0x5fb000; x_imemset/x_imemcpy/x_memset/x_memcpy/x_memiszero/x_istrncpy = __sanitizer_internal_memset 0x65204 / __sanitizer_internal_memcpy 0x65188 / memset 0x96900 / memcpy 0x964cc / mem_is_zero 0x65734 / internal_strncpy 0x65630 by nm); stops_more exercised by the collector's run, whose 50 states reach main *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted by tools/startup/atable.py (frozen-1ce98fbad397, bundle atable-1ce9-ks5e82.tsv). TFIB_TEXT_N now covers this image's OWN whole .text - ceil(.text size / 4) from the SECTION HEADER (stream lead item 1i), not the donor's relocated end, which was 37 words short on image A and 157 on image B; stops_more is the image's WHOLE self-loop set, appending SealedRepairReservation+0xc0, which cgif's released list omits too. *)
(* Read from: fuzz_reply.asan (plugin-hostd/fuzz_reply asan) sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a; unstripped twin sha256 d751b179ea493ead8cda011f65c1503ba46920e9d4eefe8638cf412fb1a55709 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fb000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30994; rw_lo := 0x9f000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x65204; x_imemcpy := 0x65188; x_memset := 0x96900; x_memcpy := 0x964cc; x_memiszero := 0x65734;
x_istrncpy := 0x65630; x_sealed := 0x11833; x_popfree := 0x36f8c;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c2d0; x_envscan_k := 0x8c2dc; x_pnscan := 0x8c394; x_pnscan_k := 0x8c3a0;
stops_more := [0x34c00; 0x36224; 0x55478; 0x5b830; 0x5b844; 0x5b858; 0x61280; 0x61350; 0x6ee3c; 0x6fd48; 0x6fed8; 0x79c30; 0x70048]
|}.
Definition TFIB_TEXT_LO : Z := 0x30994.
Definition TFIB_TEXT_N : nat := 110249.
