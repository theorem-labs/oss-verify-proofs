(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HSEGS : list Segment := Asan.M.loaded_segments.
Definition HPH := Asan.M.phdrs.

(* [comment removed for export] *)
Definition ASAN_H : atable :=
  {| img_lo := 0x10000; img_hi := 0xbd0000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x19ac80; rw_lo := 0x538000; rw_len := 0x698000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x1d60f4; x_imemcpy := 0x1d6078; x_memset := 0x530800; x_memcpy := 0x5303cc; x_memiszero := 0x1d6624;
     x_istrncpy := 0x1d6520; x_sealed := 0x13fe3; x_popfree := 0x1a1448; x_smear := 0x1d7820;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x524558; x_envscan_k := 0x524564; x_pnscan := 0x52461c; x_pnscan_k := 0x524628;
     stops_more := [0x19f0bc; 0x1a06e0; 0x1c5c5c; 0x1cc4c0; 0x1cc4d4; 0x1cc4e8; 0x1d2170; 0x1d2240; 0x1e0d40; 0x1e1c78; 0x1e1e08; 0x1ebbb4] |}.

Definition HLIMIT : Z := target_alloc_limit.
Definition hinit : acs := init_acs_of ASAN_H.

(* [comment removed for export] *)
Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
