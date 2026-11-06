(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for fuzz_ctrl's asan-ubsan image (sha256 12136677c5cf..., symbols from its unstripped twin ee07e2c38d94...) in the form of proofs/cgif/cgif_file_fuzzer/lib/YB12.v (origin/ossv/recipes c8557374ad2e), by the atable emitter of a Theorem Labs lane (atable.py sha256 7b569be5151fa55d...). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fe000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3112c; rw_lo := 0xa2000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x644f0; x_imemcpy := 0x64474; x_memset := 0x98e34; x_memcpy := 0x98a30; x_memiszero := 0x64a20;
x_istrncpy := 0x6491c; x_sealed := 0x11835; x_popfree := 0x37518;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8e834; x_envscan_k := 0x8e840; x_pnscan := 0x8e8f8; x_pnscan_k := 0x8e904;
stops_more := [0x3518c; 0x367b0; 0x547fc; 0x5abb4; 0x5abc8; 0x5abdc; 0x6056c; 0x6063c; 0x6db68; 0x6ea74; 0x6ec04; 0x7895c]
|}.
Definition TFIB_TEXT_LO : Z := 0x3112c.
Definition TFIB_TEXT_N : nat := 111631.
