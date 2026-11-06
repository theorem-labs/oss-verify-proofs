(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to libreac/fuzz_decode's split library and every image numeral recomputed from fuzz_decode.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). Every field is fuzz_decode.asan's own: img_lo / img_hi / n_res / rw_lo / rw_len / ph_* from its PT_LOADs, a_entry = e_entry 0x30008, shadow_off 0x7fff8000, the code fields and the 12 stops = symbol + cgif's offset in the unstripped twin, x_sealed = the image's unique "<sealed>" string 0x11816; emitted by the frozen atable emitter (provenance/evidence/startup-A/inputs/atable.py, sha256 7b569be5151f), whose control reproduces cgif's released A/AB12.v on cgif's image (37 of 37 fields). TFIB_TEXT_N is the true .text word count (0x677a0 / 4 = 105960); no file reads it. *)
(* Read from: fuzz_decode.asan (libreac/fuzz_decode asan) sha256 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036; unstripped twin sha256 4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2 *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f6000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30008; rw_lo := 0x9a000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x6353c; x_imemcpy := 0x634c0; x_memset := 0x92474; x_memcpy := 0x92070; x_memiszero := 0x63a6c;
x_istrncpy := 0x63968; x_sealed := 0x11816; x_popfree := 0x364d4;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x87e74; x_envscan_k := 0x87e80; x_pnscan := 0x87f38; x_pnscan_k := 0x87f44;
stops_more := [0x34148; 0x3576c; 0x534e4; 0x59aec; 0x59b00; 0x59b14; 0x5f5b8; 0x5f688; 0x6cbb4; 0x6dac0; 0x6dc50; 0x779a8]
|}.
Definition TFIB_TEXT_LO : Z := 0x30008.
Definition TFIB_TEXT_N : nat := 105960.
