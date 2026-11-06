(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x694000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x50fd8; rw_lo := 0x12e000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x8b098; x_imemcpy := 0x8b01c; x_memset := 0x127758; x_memcpy := 0x127354; x_memiszero := 0x8b5e4;
     x_istrncpy := 0x8b4c4; x_sealed := 0x11b2f; x_popfree := 0x57688;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x115820; x_envscan_k := 0x11582c; x_pnscan := 0x1158e4; x_pnscan_k := 0x1158f0;
     stops_more := [0x552fc; 0x56920; 0x7ac14; 0x8175c; 0x81770; 0x81784; 0x87114; 0x871e4; 0x9472c; 0x95638; 0x957c8; 0x9f520] |}.
Definition ASAN0_TEXT_LO : Z := 0x50fd8.
Definition ASAN0_TEXT_N : nat := 226232%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x7a7c8 0x134fe0 0x134fe8 0x134ff0 0x13e4a8 0x13e4b0 0x13e4a0.
Definition X_MAXVA_ASAN0 : Z := 0x8c6fc.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
