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
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zeros_length n : length (zeros n) = n. Proof. unfold zeros. apply repeat_length. Qed.

Lemma bytes_at_zeros_sub m A n off k :
  bytes_at asegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at asegs m (A + off) (zeros k).
Proof.
  intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_of_zeros m A n off cs :
  bytes_at asegs m A (zeros n) -> wr_at asegs m A (Z.of_nat n) ->
  cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
  rw_cells asegs m (A + off) cs.
Proof.
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (bytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.

Lemma le8_zero : le8 (wz 0) = zeros 8. Proof. reflexivity. Qed.
Lemma le4_zero : le4 (wz 0) = zeros 4. Proof. reflexivity. Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

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
End CEIL_WRAP_1.

(* [comment removed for export] *)
