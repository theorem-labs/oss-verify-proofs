(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BothPlanCore BothPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition HSEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition HPH := AsanUbsan.M.phdrs.

Definition ASAN_H : atable :=
  {| img_lo := 0x10000; img_hi := 0x6e8000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x91258; rw_lo := 0x17e000; rw_len := 0x56a000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xcbd50; x_imemcpy := 0xcbcd4; x_memset := 0x176ea4; x_memcpy := 0x176aa0; x_memiszero := 0xcc29c;
     x_istrncpy := 0xcc17c; x_sealed := 0x11b9c; x_popfree := 0x97908; x_smear := 0xcd3b4;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x1649cc; x_envscan_k := 0x1649d8; x_pnscan := 0x164a90; x_pnscan_k := 0x164a9c;
     stops_more := [0x9557c; 0x96ba0; 0xbb8cc; 0xc2414; 0xc2428; 0xc243c; 0xc7dcc; 0xc7e9c; 0xd53e4; 0xd62f0; 0xd6480; 0xd65f0; 0xe01d8] |}.

Definition HLIMIT : Z := target_alloc_limit.
Definition hinit : acs := init_acs_of ASAN_H.

Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
