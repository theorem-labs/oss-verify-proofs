(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz.
Import ListNotations. Import AX2. Import APC. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition BJO6 : atable :=
{| img_lo := 0x10000; img_hi := 0x647000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3e050; rw_lo := 0xe4000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x75348; x_imemcpy := 0x752cc; x_memset := 0xdde14; x_memcpy := 0xdda10; x_memiszero := 0x75878;
x_istrncpy := 0x75774; x_sealed := 0x11afc; x_popfree := 0x447e0;
x_sniff := 1; sniff_tab := 1; sniff_cell := 1;
x_envscan := 0xce390; x_envscan_k := 0xce39c; x_pnscan := 0xce454; x_pnscan_k := 0xce460;
stops_more := [0x42454; 0x43a78; 0x650a0; 0x6b8f8; 0x6b90c; 0x6b920; 0x713c4; 0x71494; 0x7e9c0; 0x7f8cc; 0x7fa5c; 0x897b4] |}.

Definition BJO6_TEXT_LO : Z := 0x3e050.
Definition BJO6_TEXT_N : nat := 169542.
Definition bjo_init : acs := init_acs_of BJO6.
