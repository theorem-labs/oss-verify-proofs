(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x698000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x51b88; rw_lo := 0x132000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x8bde4; x_imemcpy := 0x8bd68; x_memset := 0x12b88c; x_memcpy := 0x12b488; x_memiszero := 0x8c330;
     x_istrncpy := 0x8c210; x_sealed := 0x11b42; x_popfree := 0x58238;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x119950; x_envscan_k := 0x11995c; x_pnscan := 0x119a14; x_pnscan_k := 0x119a20;
     stops_more := [0x55eac; 0x574d0; 0x7b960; 0x824a8; 0x824bc; 0x824d0; 0x87e60; 0x87f30; 0x95478; 0x96384; 0x96514; 0xa026c] |}.
Definition ASAN0_TEXT_LO : Z := 0x51b88.
Definition ASAN0_TEXT_N : nat := 229657%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x7b514 0x1391c0 0x1391c8 0x1391d0 0x1426e8 0x1426f0 0x1426e0.
Definition X_MAXVA_ASAN0 : Z := 0x8d448.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
