(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_qdisc image A by atable.py 1ce98fbad397 (port-reply start-up set startup-set-2026-10-29) from fuzz_qdisc.asan and its unstripped twin, TFIB_TEXT_N over this image's own .text (h-small-a3). *)
(* Read from: fuzz_qdisc.asan (reac-pw/fuzz_qdisc asan) sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e; unstripped twin sha256 d77ead7cec5c42ebc28aff0443565f333cbb4dd08f5f1101d3deb805d5e34aac *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f3000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2f9e4; rw_lo := 0x97000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x61b64; x_imemcpy := 0x61ae8; x_memset := 0x8effc; x_memcpy := 0x8ebf8; x_memiszero := 0x62094;
x_istrncpy := 0x61f90; x_sealed := 0x117f6; x_popfree := 0x35dd0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x84a00; x_envscan_k := 0x84a0c; x_pnscan := 0x84ac4; x_pnscan_k := 0x84ad0;
stops_more := [0x33a44; 0x35068; 0x51e70; 0x58228; 0x5823c; 0x58250; 0x5dbe0; 0x5dcb0; 0x6b1dc; 0x6c0e8; 0x6c278; 0x75fd0; 0x6c3e8]
|}.
Definition TFIB_TEXT_LO : Z := 0x2f9e4.
Definition TFIB_TEXT_N : nat := 102995.
