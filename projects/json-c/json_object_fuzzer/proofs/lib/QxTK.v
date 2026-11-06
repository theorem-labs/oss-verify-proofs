(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz.
Import ListNotations. Import AX2. Import APC. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition ATOK : atable :=
{| img_lo := 0x10000; img_hi := 0x5ed000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x32988; rw_lo := 0xad000; rw_len := 0x540000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x68a64; x_imemcpy := 0x689e8; x_memset := 0xa70d4; x_memcpy := 0xa6cd0; x_memiszero := 0x68f94;
x_istrncpy := 0x68e90; x_sealed := 0x118de; x_popfree := 0x39060;
x_sniff := 1; sniff_tab := 1; sniff_cell := 1;
x_envscan := 0x99c84; x_envscan_k := 0x99c90; x_pnscan := 0x99d48; x_pnscan_k := 0x99d54;
stops_more := [0x36cd4; 0x382f8; 0x58a0c; 0x5f014; 0x5f028; 0x5f03c; 0x64ae0; 0x64bb0; 0x720d4; 0x72fe0; 0x73170; 0x7cd8c] |}.

Definition ATOK_TEXT_LO : Z := 0x32988.
Definition ATOK_TEXT_N : nat := 125286.
Definition atok_init : acs := init_acs_of ATOK.
