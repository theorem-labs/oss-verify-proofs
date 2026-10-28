(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5 MallocRep_u5 F_malloc_free_u5 MallocTree_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import MallocKit_B_u5 MallocModel_B_u5 MallocKit_B3_u5 F_ntf_B_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_am_A_u5 F_am_K_u5.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Definition pgal (z : Z) : Prop := z mod 4096 = 0.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma carve_st_some st p tl ar :
  c_meta_area_tail (ctx st) = Some tl -> (s_areas st) !! tl = Some ar -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
  unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

Lemma carve_st_none st p :
  c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
  carve_st st p =
    let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
    let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
    let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
    set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
  intros HT Hp. unfold carve_st.
  cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
  cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
