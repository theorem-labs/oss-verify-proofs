(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HSEGS : list Segment := Asan.M.loaded_segments.
Definition HPH := Asan.M.phdrs.

(* [comment removed for export] *)
Definition ASAN_H : atable :=
  {| img_lo := 0x10000; img_hi := 0x67f000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4dbac; rw_lo := 0x115000; rw_len := 0x56a000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x850a4; x_imemcpy := 0x85028; x_memset := 0x10db7c; x_memcpy := 0x10d778; x_memiszero := 0x855d4;
     x_istrncpy := 0x854d0; x_sealed := 0x11c43; x_popfree := 0x5425c; x_smear := 0x867d0;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xfe8c8; x_envscan_k := 0xfe8d4; x_pnscan := 0xfe98c; x_pnscan_k := 0xfe998;
     stops_more := [0x51ed0; 0x534f4; 0x74a3c; 0x7b584; 0x7b598; 0x7b5ac; 0x81120; 0x811f0; 0x8fcb4; 0x90bc0; 0x90d50; 0x90ec0; 0x9aab4] |}.

Definition HLIMIT : Z := target_alloc_limit.
Definition hinit : acs := init_acs_of ASAN_H.

(* [comment removed for export] *)
Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
