(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire's asan-ubsan image by atable.py (sha256 42e18a7eef50, not in the published tree) from fuzz_wire.asan-ubsan and its unstripped twin: image fields from the program headers, code fields as symbol + offset, TFIB_TEXT_N from the .text section size, stops_more the image's self-loops; proofs/cgif/cgif_file_fuzzer/lib/YB12.v at commit 25e3d17bdb50 gives the text only. *)
(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan) sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6; unstripped twin sha256 51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3 *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f6000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2ff5c; rw_lo := 0x9a000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x630d0; x_imemcpy := 0x63054; x_memset := 0x91fac; x_memcpy := 0x91ba8; x_memiszero := 0x63600;
x_istrncpy := 0x634fc; x_sealed := 0x11806; x_popfree := 0x36348;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x879ac; x_envscan_k := 0x879b8; x_pnscan := 0x87a70; x_pnscan_k := 0x87a7c;
stops_more := [0x33fbc; 0x355e0; 0x533dc; 0x59794; 0x597a8; 0x597bc; 0x5f14c; 0x5f21c; 0x6c748; 0x6d654; 0x6d7e4; 0x7753c; 0x6d954]
|}.
Definition TFIB_TEXT_LO : Z := 0x2ff5c.
Definition TFIB_TEXT_N : nat := 105697.
