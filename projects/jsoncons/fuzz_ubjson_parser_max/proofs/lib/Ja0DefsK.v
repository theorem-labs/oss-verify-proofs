(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ASAN0 : atable :=
{| img_lo := 0x10000; img_hi := 0x691000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x509a0; rw_lo := 0x12c000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x8ab08; x_imemcpy := 0x8aa8c; x_memset := 0x124db0; x_memcpy := 0x1249ac; x_memiszero := 0x8b054;
x_istrncpy := 0x8af34; x_sealed := 0x11b12; x_popfree := 0x57050;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x112e78; x_envscan_k := 0x112e84; x_pnscan := 0x112f3c; x_pnscan_k := 0x112f48;
stops_more := [0x54cc4; 0x562e8; 0x7a684; 0x811cc; 0x811e0; 0x811f4; 0x86b84; 0x86c54; 0x9419c; 0x950a8; 0x95238; 0x9ef90] |}.
Definition ASAN0_TEXT_LO : Z := 0x509a0.
Definition ASAN0_TEXT_N : nat := 223964%nat.
Definition asan0_init : acs := init_acs_of ASAN0.
Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.
Definition AIM_ASAN0 : aim_params := mkAIM 0x7a238 0x132640 0x132648 0x132650 0x13b9e8 0x13b9f0 0x13b9e0.
Definition X_MAXVA_ASAN0 : Z := 0x8c16c.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
