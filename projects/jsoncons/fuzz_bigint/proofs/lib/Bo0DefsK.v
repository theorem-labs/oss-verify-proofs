(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanNodesExtraDefsK.
Import ListNotations.
Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ASAN0 : atable :=
  {| img_lo := 0x10000; img_hi := 0x634000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3c3ac; rw_lo := 0xd2000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x715e0; x_imemcpy := 0x71564; x_memset := 0xcc740; x_memcpy := 0xcc33c; x_memiszero := 0x71b10;
     x_istrncpy := 0x71a0c; x_sealed := 0x11a38; x_popfree := 0x42a5c;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xbd694; x_envscan_k := 0xbd6a0; x_pnscan := 0xbd758; x_pnscan_k := 0xbd764;
     stops_more := [0x406d0; 0x41cf4; 0x6169c; 0x67ca4; 0x67cb8; 0x67ccc; 0x6d65c; 0x6d72c; 0x7ac58; 0x7bb64; 0x7bcf4; 0x85a4c] |}.
Definition ASAN0_TEXT_LO : Z := 0x3c3ac.
Definition ASAN0_TEXT_N : nat := 153181%nat.   (* [comment removed for export] *)
Definition asan0_init : acs := init_acs_of ASAN0.

Definition ASEGS0 := AsanUbsan.M.loaded_segments.
Definition APH0 : PhdrInfo := AsanUbsan.M.phdrs.

Definition AIM_ASAN0 : aim_params := mkAIM 0x61250 0xd64d0 0xd64d8 0xd64e0 0xdf428 0xdf430 0xdf420.
Definition X_MAXVA_ASAN0 : Z := 0x72c28.
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 95 then xn_addrisinmem ASEGS0 NX0 AIM_ASAN0 args cs
  else if Nat.eqb id 97 then xn_smearva X_MAXVA_ASAN0 args cs
  else if Nat.eqb id 98 then xn_absbytes ASEGS0 NX0 args cs
  else None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
