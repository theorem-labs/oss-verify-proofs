(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition HSEGS : list Segment := Asan.M.loaded_segments.
Definition HPH := Asan.M.phdrs.

Definition ASAN_H : atable :=
  {| img_lo := 0x10000; img_hi := 0x6e6000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x91350; rw_lo := 0x17c000; rw_len := 0x56a000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x0cc108; x_imemcpy := 0x0cc08c; x_memset := 0x175500; x_memcpy := 0x1750fc; x_memiszero := 0x0cc654;
     x_istrncpy := 0x0cc534; x_sealed := 0x11c99; x_popfree := 0x97a00; x_smear := 0xcd76c;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x163028; x_envscan_k := 0x163034; x_pnscan := 0x1630ec; x_pnscan_k := 0x1630f8;
     stops_more := [0x95674; 0x96c98; 0x0bbc84; 0x0c27cc; 0x0c27e0; 0x0c27f4; 0x0c8184; 0x0c8254; 0x0d579c; 0x0d66a8; 0x0d6838; 0x0d69a8; 0x0e0590] |}.

Definition HLIMIT : Z := target_alloc_limit.
Definition hinit : acs := init_acs_of ASAN_H.

Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
