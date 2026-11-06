(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import TacS8 ImageS8 ZBridgeS8 SysStepS8 SFModelS8 ArrS8.

From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import F_syscallsS8 MallocRepS8 F_malloc_freeS8 MallocTreeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import MallocKit_BS8 MallocModel_BS8 MallocKit_B3S8 F_ntf_BS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Agent Require Import F_am_AS8 F_am_KS8.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition pgal (z : Z) : Prop := z mod 4096 = 0.

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

