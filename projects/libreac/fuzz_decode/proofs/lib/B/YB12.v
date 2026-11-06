(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_decode by the frozen atable emitter (atable.py b9aa677211b7) from the pau-pipeline ORIGINAL bin/fuzz_decode/fuzz_decode.asan-ubsan (sha256 5d05689fd5b196976890b91e68c113953d385775b9d811ef98c712b2cac7d4a9) and its unstripped twin (sha256 6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4); every field a symbol+offset of this image. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f6000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30054; rw_lo := 0x9a000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63588; x_imemcpy := 0x6350c; x_memset := 0x92a1c; x_memcpy := 0x92618; x_memiszero := 0x63ab8;
x_istrncpy := 0x639b4; x_sealed := 0x1181e; x_popfree := 0x36520;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8841c; x_envscan_k := 0x88428; x_pnscan := 0x884e0; x_pnscan_k := 0x884ec;
stops_more := [0x34194; 0x357b8; 0x53530; 0x59b38; 0x59b4c; 0x59b60; 0x5f604; 0x5f6d4; 0x6cc00; 0x6db0c; 0x6dc9c; 0x779f4]
|}.
Definition TFIB_TEXT_LO : Z := 0x30054.
Definition TFIB_TEXT_N : nat := 106303.
