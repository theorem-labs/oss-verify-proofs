(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_segconf image A by atable.py e88affcf0526 (the start-up tool set of record at commit d9aa42da992) from fuzz_segconf.asan and its unstripped twin; TFIB_TEXT_N covers this image's own whole .text (0x31ed4, 112997 words); stops_more is the image's 13 self-loops; module paths changed. *)
(* Read from: fuzz_segconf.asan (reac-pw/fuzz_segconf asan) sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8; unstripped twin sha256 4362701197e4cecdb46108f7694774021f7b8d5e7bd85cfe200fa90ad7a63c32 *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x601000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x31ed4; rw_lo := 0xa4000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x6820c; x_imemcpy := 0x68190; x_memset := 0x9a828; x_memcpy := 0x9a3f4; x_memiszero := 0x6873c;
x_istrncpy := 0x68638; x_sealed := 0x11848; x_popfree := 0x383a0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x901f8; x_envscan_k := 0x90204; x_pnscan := 0x902bc; x_pnscan_k := 0x902c8;
stops_more := [0x36014; 0x37638; 0x581b4; 0x5e7bc; 0x5e7d0; 0x5e7e4; 0x64288; 0x64358; 0x71884; 0x72790; 0x72920; 0x7c678; 0x72a90]
|}.
Definition TFIB_TEXT_LO : Z := 0x31ed4.
Definition TFIB_TEXT_N : nat := 112997.
