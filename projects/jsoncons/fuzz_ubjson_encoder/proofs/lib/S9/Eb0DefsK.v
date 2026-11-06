(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x69c000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x523b0; rw_lo := 0x137000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x8c60c; x_imemcpy := 0x8c590; x_memset := 0x130034; x_memcpy := 0x12fc30; x_memiszero := 0x8cb58;
     x_istrncpy := 0x8ca38; x_sealed := 0x11b79; x_popfree := 0x58a60;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x11e0f8; x_envscan_k := 0x11e104; x_pnscan := 0x11e1bc; x_pnscan_k := 0x11e1c8;
     stops_more := [0x566d4; 0x57cf8; 0x7c188; 0x82cd0; 0x82ce4; 0x82cf8; 0x88688; 0x88758; 0x95ca0; 0x96bac; 0x96d3c; 0xa0a94] |}.
Definition ASAN0_TEXT_LO : Z := 0x523b0.
Definition ASAN0_TEXT_N : nat := 233721%nat.
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := AsanUbsan.M.loaded_segments.
Definition APH0 : PhdrInfo := AsanUbsan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x7bd3c 0x13d8d0 0x13d8d8 0x13d8e0 0x146de8 0x146df0 0x146de0.
Definition X_MAXVA_ASAN0 : Z := 0x8dc70.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
