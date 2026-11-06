(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for fuzz_ctrl's asan image (sha256 aac16e1fe728..., symbols from its unstripped twin 78efaeda1de5...) in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v (origin/ossv/recipes c8557374ad2e), by the atable emitter of a Theorem Labs lane (atable.py sha256 7b569be5151fa55d...). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fe000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30ff0; rw_lo := 0xa1000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x643b4; x_imemcpy := 0x64338; x_memset := 0x98010; x_memcpy := 0x97c0c; x_memiszero := 0x648e4;
x_istrncpy := 0x647e0; x_sealed := 0x11835; x_popfree := 0x373dc;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8da10; x_envscan_k := 0x8da1c; x_pnscan := 0x8dad4; x_pnscan_k := 0x8dae0;
stops_more := [0x35050; 0x36674; 0x546c0; 0x5aa78; 0x5aa8c; 0x5aaa0; 0x60430; 0x60500; 0x6da2c; 0x6e938; 0x6eac8; 0x78820]
|}.
Definition TFIB_TEXT_LO : Z := 0x30ff0.
Definition TFIB_TEXT_N : nat := 110805.
