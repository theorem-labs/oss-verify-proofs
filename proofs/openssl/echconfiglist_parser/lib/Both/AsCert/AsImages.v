(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HSEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition HPH := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition ASAN_H : atable :=
  {| img_lo := 0x10000; img_hi := 0xc04000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x195ba8; rw_lo := 0x571000; rw_len := 0x693000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x1d101c; x_imemcpy := 0x1d0fa0; x_memset := 0x569e10; x_memcpy := 0x5699dc; x_memiszero := 0x1d154c;
     x_istrncpy := 0x1d1448; x_sealed := 0x140d1; x_popfree := 0x19c370; x_smear := 0x1d2748;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x55db68; x_envscan_k := 0x55db74; x_pnscan := 0x55dc2c; x_pnscan_k := 0x55dc38;
     stops_more := [0x199fe4; 0x19b608; 0x1c0b84; 0x1c73e8; 0x1c73fc; 0x1c7410; 0x1cd098; 0x1cd168; 0x1dbc68; 0x1dcba0; 0x1dcd30; 0x1e6adc] |}.

Definition HLIMIT : Z := target_alloc_limit.
Definition hinit : acs := init_acs_of ASAN_H.

(* [comment removed for export] *)
Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
