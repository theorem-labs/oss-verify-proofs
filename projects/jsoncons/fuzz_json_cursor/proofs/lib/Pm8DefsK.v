(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x6b3000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x58218; rw_lo := 0x14c000; rw_len := 0x567000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x92640; x_imemcpy := 0x925c4; x_memset := 0x145308; x_memcpy := 0x144f04; x_memiszero := 0x92b8c;
     x_istrncpy := 0x92a6c; x_sealed := 0x11cbd; x_popfree := 0x5e8c8;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x1333cc; x_envscan_k := 0x1333d8; x_pnscan := 0x133490; x_pnscan_k := 0x13349c;
     stops_more := [0x5c53c; 0x5db60; 0x821bc; 0x88d04; 0x88d18; 0x88d2c; 0x8e6bc; 0x8e78c; 0x9bcd4; 0x9cbe0; 0x9cd70; 0xa6ac8] |}.
Definition ASAN0_TEXT_LO : Z := 0x58218.
Definition ASAN0_TEXT_N : nat := 249364%nat.
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x81d70 0x153140 0x153148 0x153150 0x15d6a8 0x15d6b0 0x15d6a0.
Definition X_MAXVA_ASAN0 : Z := 0x93ca4.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
