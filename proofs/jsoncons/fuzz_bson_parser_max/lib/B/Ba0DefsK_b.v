(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x696000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x513a0; rw_lo := 0x131000; rw_len := 0x564480; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x8b460; x_imemcpy := 0x8b3e4; x_memset := 0x129d04; x_memcpy := 0x129900; x_memiszero := 0x8b9ac;
     x_istrncpy := 0x8b88c; x_sealed := 0x11b38; x_popfree := 0x57a50;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x117dcc; x_envscan_k := 0x117dd8; x_pnscan := 0x117e90; x_pnscan_k := 0x117e9c;
     stops_more := [0x556c4; 0x56ce8; 0x7afdc; 0x81b24; 0x81b38; 0x81b4c; 0x874dc; 0x875ac; 0x94af4; 0x95a00; 0x95b90; 0x9f8e8] |}.
Definition ASAN0_TEXT_LO : Z := 0x513a0.
Definition ASAN0_TEXT_N : nat := 228401%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := AsanUbsan.M.loaded_segments.
Definition APH0 : PhdrInfo := AsanUbsan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x7ab90 0x1374c8 0x1374d0 0x1374d8 0x140928 0x140930 0x140920.
Definition X_MAXVA_ASAN0 : Z := 0x8cac4.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
