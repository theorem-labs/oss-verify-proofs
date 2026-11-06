(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ASAN0 : atable :=
{| img_lo := 0x10000; img_hi := 0x693000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x50c70; rw_lo := 0x12e000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x8add8; x_imemcpy := 0x8ad5c; x_memset := 0x126be8; x_memcpy := 0x1267e4; x_memiszero := 0x8b324;
x_istrncpy := 0x8b204; x_sealed := 0x11b13; x_popfree := 0x57320;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x114cb0; x_envscan_k := 0x114cbc; x_pnscan := 0x114d74; x_pnscan_k := 0x114d80;
stops_more := [0x54f94; 0x565b8; 0x7a954; 0x8149c; 0x814b0; 0x814c4; 0x86e54; 0x86f24; 0x9446c; 0x95378; 0x95508; 0x9f260] |}.
Definition ASAN0_TEXT_LO : Z := 0x50c70.
Definition ASAN0_TEXT_N : nat := 225718%nat.
Definition asan0_init : acs := init_acs_of ASAN0.
Definition ASEGS0 := AsanUbsan.M.loaded_segments.
Definition APH0 : PhdrInfo := AsanUbsan.M.phdrs.
Definition AIM_ASAN0 : aim_params := mkAIM 0x7a508 0x1343a8 0x1343b0 0x1343b8 0x13d728 0x13d730 0x13d720.
Definition X_MAXVA_ASAN0 : Z := 0x8c43c.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
