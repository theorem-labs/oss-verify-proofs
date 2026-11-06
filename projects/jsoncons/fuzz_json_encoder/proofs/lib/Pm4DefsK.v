(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x6c0000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x595e4; rw_lo := 0x15a000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x93a0c; x_imemcpy := 0x93990; x_memset := 0x152ea4; x_memcpy := 0x152aa0; x_memiszero := 0x93f58;
     x_istrncpy := 0x93e38; x_sealed := 0x11d17; x_popfree := 0x5fc94;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x140f68; x_envscan_k := 0x140f74; x_pnscan := 0x14102c; x_pnscan_k := 0x141038;
     stops_more := [0x5d908; 0x5ef2c; 0x83588; 0x8a0d0; 0x8a0e4; 0x8a0f8; 0x8fa88; 0x8fb58; 0x9d0a0; 0x9dfac; 0x9e13c; 0xa7e94] |}.
Definition ASAN0_TEXT_LO : Z := 0x595e4.
Definition ASAN0_TEXT_N : nat := 262152%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := Asan.M.loaded_segments.
Definition APH0 : PhdrInfo := Asan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x8313c 0x160c20 0x160c28 0x160c30 0x16abe8 0x16abf0 0x16abe0.
Definition X_MAXVA_ASAN0 : Z := 0x95070.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
