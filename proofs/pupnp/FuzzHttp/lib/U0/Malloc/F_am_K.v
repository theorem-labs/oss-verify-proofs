(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
Import ListNotations.
Open Scope Z_scope.

Lemma zeros_length n : length (zeros n) = n. Proof. unfold zeros. apply repeat_length. Qed.

Lemma le8_zero : le8 (wz 0) = zeros 8. Proof. reflexivity. Qed.
Lemma le4_zero : le4 (wz 0) = zeros 4. Proof. reflexivity. Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.

Definition carve_st (st : mstate) (p : aptr) : mstate :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.