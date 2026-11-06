(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB12.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (29 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: taken into a Theorem Labs lane's generated set from RelocB's relocation: a_entry = e_entry 0x309ec, img_lo/img_hi = the PT_LOAD hull 0x10000..0x5fc000, rw window 0x9f000 +0x55d000; the collector's run on these values reached main in all 50 states *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted by tools/startup/atable.py; TFIB_TEXT_N 110423 -> 110422. The donor's pair is not this image's whole .text (cgif B states 111037 words from 0x3030c, end 0x9ca00, where its .text holds 111193, end 0x9cc70), so the end is cgif B's 0x9ca00 relocated into this image by its surrounding code (64 words, pc-relative immediates masked, unique match) = 0x9c744, and N = (0x9c744 - 0x309ec) / 4 = 110422. *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted by tools/startup/atable.py (frozen-1ce98fbad397, bundle atable-1ce9-ks5e82.tsv). TFIB_TEXT_N now covers this image's OWN whole .text - ceil(.text size / 4) from the SECTION HEADER (stream lead item 1i), not the donor's relocated end, which was 37 words short on image A and 157 on image B; stops_more is the image's WHOLE self-loop set, appending SealedRepairReservation+0xc0, which cgif's released list omits too. *)
(* Read from: fuzz_reply.asan-ubsan (plugin-hostd/fuzz_reply asan-ubsan) sha256 10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c; unstripped twin sha256 3389287e1d6107841f4e2bb22c691542a11433094c1a07d94fd5828afc3671f7 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fc000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x309ec; rw_lo := 0x9f000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x6525c; x_imemcpy := 0x651e0; x_memset := 0x96e80; x_memcpy := 0x96a4c; x_memiszero := 0x6578c;
x_istrncpy := 0x65688; x_sealed := 0x11833; x_popfree := 0x36fe4;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c850; x_envscan_k := 0x8c85c; x_pnscan := 0x8c914; x_pnscan_k := 0x8c920;
stops_more := [0x34c58; 0x3627c; 0x554d0; 0x5b888; 0x5b89c; 0x5b8b0; 0x612d8; 0x613a8; 0x6ee94; 0x6fda0; 0x6ff30; 0x79c88; 0x700a0]
|}.
Definition TFIB_TEXT_LO : Z := 0x309ec.
Definition TFIB_TEXT_N : nat := 110579.
