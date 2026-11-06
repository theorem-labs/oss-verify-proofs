(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x6c4000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x59eb4; rw_lo := 0x15e000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x942dc; x_imemcpy := 0x94260; x_memset := 0x1568bc; x_memcpy := 0x1564b8; x_memiszero := 0x94828;
     x_istrncpy := 0x94708; x_sealed := 0x11baa; x_popfree := 0x60564;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x1448e0; x_envscan_k := 0x1448ec; x_pnscan := 0x1449a4; x_pnscan_k := 0x1449b0;
     stops_more := [0x5e1d8; 0x5f7fc; 0x83e58; 0x8a9a0; 0x8a9b4; 0x8a9c8; 0x90358; 0x90428; 0x9d970; 0x9e87c; 0x9ea0c; 0xa8764] |}.
Definition ASAN0_TEXT_LO : Z := 0x59eb4.
Definition ASAN0_TEXT_N : nat := 265306%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := AsanUbsan.M.loaded_segments.
Definition APH0 : PhdrInfo := AsanUbsan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x83a0c 0x164520 0x164528 0x164530 0x16e4a8 0x16e4b0 0x16e4a0.
Definition X_MAXVA_ASAN0 : Z := 0x95940.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
