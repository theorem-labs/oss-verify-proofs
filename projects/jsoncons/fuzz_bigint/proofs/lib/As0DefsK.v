(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x633000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3c12c; rw_lo := 0xd2000; rw_len := 0x561000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x71360; x_imemcpy := 0x712e4; x_memset := 0xcbb2c; x_memcpy := 0xcb728; x_memiszero := 0x71890;
     x_istrncpy := 0x7178c; x_sealed := 0x11a30; x_popfree := 0x427dc;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xbca80; x_envscan_k := 0xbca8c; x_pnscan := 0xbcb44; x_pnscan_k := 0xbcb50;
     stops_more := [0x40450; 0x41a74; 0x6141c; 0x67a24; 0x67a38; 0x67a4c; 0x6d3dc; 0x6d4ac; 0x7a9d8; 0x7b8e4; 0x7ba74; 0x857cc] |}.
Definition ASAN0_TEXT_LO : Z := 0x3c12c.
Definition ASAN0_TEXT_N : nat := 152568%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x60fd0 0xd58c0 0xd58c8 0xd58d0 0xde828 0xde830 0xde820.
Definition X_MAXVA_ASAN0 : Z := 0x729a8.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
