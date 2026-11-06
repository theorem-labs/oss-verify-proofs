(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition BSEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition BPH := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition BOTH_H : atable :=
  {| img_lo := 0x10000; img_hi := 0x684000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ee78; rw_lo := 0x119000; rw_len := 0x56b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x86370; x_imemcpy := 0x862f4; x_memset := 0x111eb8; x_memcpy := 0x111ab4; x_memiszero := 0x868a0;
     x_istrncpy := 0x8679c; x_sealed := 0x11be5; x_popfree := 0x55528; x_smear := 0x87a9c;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x102c04; x_envscan_k := 0x102c10; x_pnscan := 0x102cc8; x_pnscan_k := 0x102cd4;
     stops_more := [0x5319c; 0x547c0; 0x75d08; 0x7c850; 0x7c864; 0x7c878; 0x823ec; 0x824bc; 0x90f80; 0x91e8c; 0x9201c; 0x9218c; 0x9bd80] |}.

Definition BLIMIT : Z := target_alloc_limit.
Definition bhinit : acs := init_acs_of BOTH_H.

(* [comment removed for export] *)
Definition res_code (r : cres) : Z := match r with COk _ => -1 | CErr c _ _ => c end.
Definition res_pc (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => pc cs end.
Definition res_nxt (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (nxt cs) end.
Definition res_nkn (r : cres) : Z := match r with COk _ => -1 | CErr _ _ cs => Z.of_nat (length (kn cs)) end.
Definition res_where (r : cres) : option plan := match r with COk _ => None | CErr _ p _ => Some p end.
Definition res_cs (r : cres) : option acs := match r with COk _ => None | CErr _ _ cs => Some cs end.
