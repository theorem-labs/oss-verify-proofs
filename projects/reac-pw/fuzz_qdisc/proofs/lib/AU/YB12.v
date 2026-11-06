(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_qdisc image B by atable.py 1ce98fbad397 (port-reply start-up set startup-set-2026-10-29) from fuzz_qdisc.asan-ubsan and its unstripped twin, TFIB_TEXT_N over this image's own .text (h-small-q1). *)
(* Read from: fuzz_qdisc.asan-ubsan (reac-pw/fuzz_qdisc asan-ubsan) sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062; unstripped twin sha256 a8f38ed20eaa71da2be09efbc294ab6854786e94e1564acbf2a11cdbdf8585f1 *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f3000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2f9ec; rw_lo := 0x97000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x61b6c; x_imemcpy := 0x61af0; x_memset := 0x8f034; x_memcpy := 0x8ec30; x_memiszero := 0x6209c;
x_istrncpy := 0x61f98; x_sealed := 0x117f6; x_popfree := 0x35dd8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x84a38; x_envscan_k := 0x84a44; x_pnscan := 0x84afc; x_pnscan_k := 0x84b08;
stops_more := [0x33a4c; 0x35070; 0x51e78; 0x58230; 0x58244; 0x58258; 0x5dbe8; 0x5dcb8; 0x6b1e4; 0x6c0f0; 0x6c280; 0x75fd8; 0x6c3f0]
|}.
Definition TFIB_TEXT_LO : Z := 0x2f9ec.
Definition TFIB_TEXT_N : nat := 103007.
