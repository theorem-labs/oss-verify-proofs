(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApErrKit ApErrKit2 ApErrKit3.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation ofree := CtRepP.ApErrKit.ofree.
Notation ecd := CtRepP.ApErrKit.ecd.
Notation err_clear_data_false_tree := CtRepP.ApErrKit.err_clear_data_false_tree.
Notation ecl_mid := CtRepP.ApErrKit.ecl_mid.
Notation ecl_fin := CtRepP.ApErrKit.ecl_fin.
Notation apbind_ofree := CtRepP.ApErrKit.apbind_ofree.
Notation free_file_slot_tree := CtRepP.ApErrKit.free_file_slot_tree.
Notation free_func_slot_tree := CtRepP.ApErrKit.free_func_slot_tree.
Notation err_clear_false_tree := CtRepP.ApErrKit.err_clear_false_tree.
Notation enew_top := CtRepP.ApErrKit.enew_top.
Notation enew_bot := CtRepP.ApErrKit.enew_bot.
Notation enew_st1 := CtRepP.ApErrKit.enew_st1.
Notation err_new_tree := CtRepP.ApErrKit.err_new_tree.
Notation eserr_fin := CtRepP.ApErrKit.eserr_fin.
Notation err_set_error_tree := CtRepP.ApErrKit.err_set_error_tree.
Notation ecd_proj := CtRepP.ApErrKit.ecd_proj.
Notation NoDup_app_remove_l := CtRepP.ApErrKit.NoDup_app_remove_l.
Notation ids_ok_perm := CtRepP.ApErrKit.ids_ok_perm.
Notation ids_ok_sub := CtRepP.ApErrKit.ids_ok_sub.
Notation ids_ok_same := CtRepP.ApErrKit.ids_ok_same.
Notation ids_ok_top := CtRepP.ApErrKit.ids_ok_top.
Notation ids_ok0_perm := CtRepP.ApErrKit.ids_ok0_perm.
Notation ids_ok0_sub := CtRepP.ApErrKit.ids_ok0_sub.
Notation ids_ok0_same := CtRepP.ApErrKit.ids_ok0_same.
Notation marks_sub_ecd := CtRepP.ApErrKit.marks_sub_ecd.
Notation marks_sub_ecl_fin := CtRepP.ApErrKit.marks_sub_ecl_fin.
Notation marks_sub_eserr_fin := CtRepP.ApErrKit.marks_sub_eserr_fin.
Notation marks_sub_enew_st1 := CtRepP.ApErrKit.marks_sub_enew_st1.
Notation marks_ok_set_marks := CtRepP.ApErrKit.marks_ok_set_marks.
Notation st_blocks_ecd := CtRepP.ApErrKit.st_blocks_ecd.
Notation badr_cons := CtRepP.ApErrKit.badr_cons.
Notation badr_remove_other := CtRepP.ApErrKit.badr_remove_other.
Notation badr_in := CtRepP.ApErrKit.badr_in.
Notation optb_ok_nth := CtRepP.ApErrKit.optb_ok_nth.
Notation fm_in := CtRepP.ApErrKit.fm_in.
Notation es_ids_file := CtRepP.ApErrKit.es_ids_file.
Notation es_ids_func := CtRepP.ApErrKit.es_ids_func.
Notation es_ids_data := CtRepP.ApErrKit.es_ids_data.
Notation ids_ok_not_env := CtRepP.ApErrKit.ids_ok_not_env.
Notation env_ids_unfold := CtRepP.ApErrKit.env_ids_unfold.
Notation esg := CtRepP.ApErrKit.esg.
Notation mkG := CtRepP.ApErrKit.mkG.
Notation g_fl := CtRepP.ApErrKit.g_fl.
Notation g_ma := CtRepP.ApErrKit.g_ma.
Notation g_bu := CtRepP.ApErrKit.g_bu.
Notation g_da := CtRepP.ApErrKit.g_da.
Notation g_ds := CtRepP.ApErrKit.g_ds.
Notation g_df := CtRepP.ApErrKit.g_df.
Notation g_fi := CtRepP.ApErrKit.g_fi.
Notation g_li := CtRepP.ApErrKit.g_li.
Notation g_fu := CtRepP.ApErrKit.g_fu.
Notation g_top := CtRepP.ApErrKit.g_top.
Notation g_bot := CtRepP.ApErrKit.g_bot.
Notation set_g_fl := CtRepP.ApErrKit.set_g_fl.
Notation set_g_ma := CtRepP.ApErrKit.set_g_ma.
Notation set_g_bu := CtRepP.ApErrKit.set_g_bu.
Notation set_g_da := CtRepP.ApErrKit.set_g_da.
Notation set_g_ds := CtRepP.ApErrKit.set_g_ds.
Notation set_g_df := CtRepP.ApErrKit.set_g_df.
Notation set_g_fi := CtRepP.ApErrKit.set_g_fi.
Notation set_g_li := CtRepP.ApErrKit.set_g_li.
Notation set_g_fu := CtRepP.ApErrKit.set_g_fu.
Notation set_g_top := CtRepP.ApErrKit.set_g_top.
Notation set_g_bot := CtRepP.ApErrKit.set_g_bot.
Notation g_len := CtRepP.ApErrKit.g_len.
Notation g_of := CtRepP.ApErrKit.g_of.
Notation g_len_of := CtRepP.ApErrKit.g_len_of.
Notation nth_error_wl := CtRepP.ApErrKit.nth_error_wl.
Notation nth_error_len := CtRepP.ApErrKit.nth_error_len.
Notation cnf_rblocks := CtRepP.ApErrKit.cnf_rblocks.
Notation rest_blocks := CtRepP.ApErrKit.rest_blocks.
Notation rest_ids := CtRepP.ApErrKit.rest_ids.
Notation NoDup_app_disjoint := CtRepP.ApErrKit.NoDup_app_disjoint.
Notation cnf_ids_in_es_ids := CtRepP.ApErrKit.cnf_ids_in_es_ids.
Notation ffd_not_rest := CtRepP.ApErrKit.ffd_not_rest.
Notation data_not_rest := CtRepP.ApErrKit.data_not_rest.
Notation file_not_rest := CtRepP.ApErrKit.file_not_rest.
Notation func_not_rest := CtRepP.ApErrKit.func_not_rest.
Notation seg_iv := CtRepP.ApErrKit.seg_iv.
Notation seg_outside := CtRepP.ApErrKit.seg_outside.
Notation lremove := CtRepP.ApErrKit.lremove.
Notation g_of_set_top := CtRepP.ApErrKit.g_of_set_top.
Notation g_of_set_bottom := CtRepP.ApErrKit.g_of_set_bottom.
Notation g_of_set_marks := CtRepP.ApErrKit.g_of_set_marks.
Notation g_of_set_buf := CtRepP.ApErrKit.g_of_set_buf.
Notation g_of_set_line := CtRepP.ApErrKit.g_of_set_line.
Notation g_of_set_dflags := CtRepP.ApErrKit.g_of_set_dflags.
Notation g_of_set_file := CtRepP.ApErrKit.g_of_set_file.
Notation g_of_set_func := CtRepP.ApErrKit.g_of_set_func.
Notation g_of_set_data := CtRepP.ApErrKit.g_of_set_data.
Notation upd_nth_error_same := CtRepP.ApErrKit.upd_nth_error_same.
Notation upd_zeros := CtRepP.ApErrKit.upd_zeros.
Notation g_len_set := CtRepP.ApErrKit.g_len_set.
Notation g_of_adr_ext := CtRepP.ApErrKit.g_of_adr_ext.
Notation optb_ok_remove := CtRepP.ApErrKit.optb_ok_remove.
Notation optb_ok_cons := CtRepP.ApErrKit.optb_ok_cons.
Notation optb_ok_lset_none := CtRepP.ApErrKit.optb_ok_lset_none.
Notation optb_ok_lset_some := CtRepP.ApErrKit.optb_ok_lset_some.
Notation in_lset := CtRepP.ApErrKit.in_lset.
Notation NoDup_lb_remove := CtRepP.ApErrKit.NoDup_lb_remove.
Notation es_shape_setters := CtRepP.ApErrKit.es_shape_setters.
Notation nth_wl_optr := CtRepP.ApErrKit.nth_wl_optr.
Notation nth_wl := CtRepP.ApErrKit.nth_wl.
Notation lremove_keep := CtRepP.ApErrKit.lremove_keep.
Notation lremove_incl := CtRepP.ApErrKit.lremove_incl.
Notation lremove_app := CtRepP.ApErrKit.lremove_app.
Notation lremove_nodup := CtRepP.ApErrKit.lremove_nodup.
Notation badr_lremove := CtRepP.ApErrKit.badr_lremove.
Notation ids_es_ne := CtRepP.ApErrKit.ids_es_ne.
Notation ids_file_func_ne := CtRepP.ApErrKit.ids_file_func_ne.
Notation lb_client_ne := CtRepP.ApErrKit.lb_client_ne.
Notation rest_blocks_lremove := CtRepP.ApErrKit.rest_blocks_lremove.
Notation optb_ok_lremove := CtRepP.ApErrKit.optb_ok_lremove.
Notation fm_in' := CtRepP.ApErrKit.fm_in'.
Notation es_ids_in := CtRepP.ApErrKit.es_ids_in.
Notation ids_pre_disjoint := CtRepP.ApErrKit.ids_pre_disjoint.
Notation st_blocks_ecl_fin := CtRepP.ApErrKit.st_blocks_ecl_fin.
Notation dflags_ok_ecd := CtRepP.ApErrKit.dflags_ok_ecd.
Notation dflags_ok_same := CtRepP.ApErrKit.dflags_ok_same.
Notation get_data_lset_none := CtRepP.ApErrKit.get_data_lset_none.
Notation get_data_ecd := CtRepP.ApErrKit.get_data_ecd.
Notation badr_size_unique := CtRepP.ApErrKit.badr_size_unique.
Notation ids_file_data_ne := CtRepP.ApErrKit.ids_file_data_ne.
Notation ids_func_data_ne := CtRepP.ApErrKit.ids_func_data_ne.
Notation ids_data_es_ne := CtRepP.ApErrKit.ids_data_es_ne.
Notation land1_mod := CtRepP.ApErrKit.land1_mod.
Notation dflag_bit := CtRepP.ApErrKit.dflag_bit.
Notation land_malloced_mask := CtRepP.ApErrKit.land_malloced_mask.
Notation land_malloced_range := CtRepP.ApErrKit.land_malloced_range.
Notation land_shift_small_0 := CtRepP.ApErrKit.land_shift_small_0.
Notation err_pack_val := CtRepP.ApErrKit.err_pack_val.
Notation err_pack_range := CtRepP.ApErrKit.err_pack_range.
Notation err_pack_bits := CtRepP.ApErrKit.err_pack_bits.
Notation zext32_shifts := CtRepP.ApErrKit.zext32_shifts.
Notation kept := CtRepP.ApErrKit.kept.
Notation kept_refl := CtRepP.ApErrKit.kept_refl.
Notation kept_trans := CtRepP.ApErrKit.kept_trans.
Notation K_lremove := CtRepP.ApErrKit.K_lremove.
Notation K_not_es := CtRepP.ApErrKit.K_not_es.
Notation K_not_env := CtRepP.ApErrKit.K_not_env.
Notation es_ids_sub_perm := CtRepP.ApErrKit.es_ids_sub_perm.
Notation ids_ok_add := CtRepP.ApErrKit2.ids_ok_add.
Notation ids_in := CtRepP.ApErrKit2.ids_in.
Notation ids_in_remove := CtRepP.ApErrKit2.ids_in_remove.
Notation ids_in_cons := CtRepP.ApErrKit2.ids_in_cons.
Notation ids_in_add := CtRepP.ApErrKit2.ids_in_add.
Notation fresh_not_ids := CtRepP.ApErrKit2.fresh_not_ids.
Notation upd_ext := CtRepP.ApErrKit2.upd_ext.
Notation upd_upd_same := CtRepP.ApErrKit2.upd_upd_same.
Notation fm_nodup_slots := CtRepP.ApErrKit3.fm_nodup_slots.
Notation ids_ok_nodup_arrays := CtRepP.ApErrKit3.ids_ok_nodup_arrays.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EsRaw.
Definition es_raw (m : mem) (A : Z) (g : esg) : Prop :=
  u32arr ctasegs m (A + ESO_FLAGS) (g_fl g)
  /\ u32arr ctasegs m (A + ESO_MARKS) (g_ma g)
  /\ u64arr ctasegs m (A + ESO_BUFFER) (g_bu g)
  /\ u64arr ctasegs m (A + ESO_DATA) (g_da g)
  /\ u64arr ctasegs m (A + ESO_DSIZE) (g_ds g)
  /\ u32arr ctasegs m (A + ESO_DFLAGS) (g_df g)
  /\ u64arr ctasegs m (A + ESO_FILE) (g_fi g)
  /\ u32arr ctasegs m (A + ESO_LINE) (g_li g)
  /\ u64arr ctasegs m (A + ESO_FUNC) (g_fu g)
  /\ rw_cells ctasegs m (A + ESO_TOP) [C4 (wz (g_top g)); C4 (wz (g_bot g))].


Lemma es_at_raw : forall m A st adr, es_at m A st adr <-> es_raw m A (g_of st adr).
Proof. intros. unfold es_at, es_raw, g_of. cbn -[u32arr u64arr rw_cells wl Z.add map optr osize repeat ERR_NUM Z.of_nat]. tauto. Qed.



Local Ltac eso := unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM in *.

(* [comment removed for export] *)



Lemma es_raw_bound : forall m A g, es_raw m A g -> 0 <= A /\ A + 904 <= 2^64.
Proof.
  intros m A g H. destruct H as (Hfl & _ & _ & _ & _ & _ & _ & _ & _ & HT). pose proof (rw_cells_bound _ _ _ _ HT) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (u32arr_bound _ _ _ _ Hfl) as B0. eso. lia.
Qed.

Lemma es_rd_fl : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 4 = Some (le4 (nth i (g_fl g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fl g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i)); [exact Hfl | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_ma : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_MARKS + 4 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 4 = Some (le4 (nth i (g_ma g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_ma g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i)); [exact Hma | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_bu : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_BUFFER + 8 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 8 = Some (le8 (nth i (g_bu g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_bu g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i)); [exact Hbu | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_da : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DATA + 8 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 8 = Some (le8 (nth i (g_da g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_da g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_DATA) (g_da g) (Z.of_nat i)); [exact Hda | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_ds : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DSIZE + 8 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 8 = Some (le8 (nth i (g_ds g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_ds g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i)); [exact Hds | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_df : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DFLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 4 = Some (le4 (nth i (g_df g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_df g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i)); [exact Hdf | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_fi : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FILE + 8 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 8 = Some (le8 (nth i (g_fi g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fi g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i)); [exact Hfi | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_li : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_LINE + 4 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 4 = Some (le4 (nth i (g_li g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_li g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u32arr_read _ m (A + ESO_LINE) (g_li g) (Z.of_nat i)); [exact Hli | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_fu : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_FUNC + 8 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 8 = Some (le8 (nth i (g_fu g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. eso.
  destruct (nth_error_len (g_fu g) i ltac:(lia)) as (w & Hw & <-).
  eapply (u64arr_read _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i)); [exact Hfu | rewrite Nat2Z.id; exact Hw | lia | reflexivity].
Qed.

Lemma es_rd_top : forall m A g a, es_raw m A g -> a = wa (A + 896) -> ov_read_bytes ctasegs m a 4 = Some (le4 (wz (g_top g))).
Proof.
  intros m A g a H ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). eso.
  apply (rw_cells_read_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 0%nat (C4 (wz (g_top g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.
Lemma es_rd_bot : forall m A g a, es_raw m A g -> a = wa (A + 900) -> ov_read_bytes ctasegs m a 4 = Some (le4 (wz (g_bot g))).
Proof.
  intros m A g a H ->. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). eso.
  apply (rw_cells_read_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 4%nat (C4 (wz (g_bot g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia].
Qed.

Lemma es_wr_fl : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_FLAGS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FLAGS + 4 * Z.of_nat i)) (le4 v)) A (set_g_fl (upd (g_fl g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i)); [exact Hfl | lia | reflexivity]. }
  unfold es_raw, set_g_fl. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_FLAGS) (g_fl g) (Z.of_nat i) v Hfl ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_ma : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_MARKS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_MARKS + 4 * Z.of_nat i)) (le4 v)) A (set_g_ma (upd (g_ma g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i)); [exact Hma | lia | reflexivity]. }
  unfold es_raw, set_g_ma. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_MARKS) (g_ma g) (Z.of_nat i) v Hma ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_bu : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_BUFFER + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_BUFFER + 8 * Z.of_nat i)) (le8 v)) A (set_g_bu (upd (g_bu g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i)); [exact Hbu | lia | reflexivity]. }
  unfold es_raw, set_g_bu. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_BUFFER) (g_bu g) (Z.of_nat i) v Hbu ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_da : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_DATA + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DATA + 8 * Z.of_nat i)) (le8 v)) A (set_g_da (upd (g_da g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_DATA) (g_da g) (Z.of_nat i)); [exact Hda | lia | reflexivity]. }
  unfold es_raw, set_g_da. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_DATA) (g_da g) (Z.of_nat i) v Hda ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_ds : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_DSIZE + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DSIZE + 8 * Z.of_nat i)) (le8 v)) A (set_g_ds (upd (g_ds g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i)); [exact Hds | lia | reflexivity]. }
  unfold es_raw, set_g_ds. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_DSIZE) (g_ds g) (Z.of_nat i) v Hds ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_df : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_DFLAGS + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_DFLAGS + 4 * Z.of_nat i)) (le4 v)) A (set_g_df (upd (g_df g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i)); [exact Hdf | lia | reflexivity]. }
  unfold es_raw, set_g_df. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_DFLAGS) (g_df g) (Z.of_nat i) v Hdf ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_fi : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_FILE + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FILE + 8 * Z.of_nat i)) (le8 v)) A (set_g_fi (upd (g_fi g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i)); [exact Hfi | lia | reflexivity]. }
  unfold es_raw, set_g_fi. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_FILE) (g_fi g) (Z.of_nat i) v Hfi ltac:(lia)). }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_li : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_LINE + 4 * Z.of_nat i)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_LINE + 4 * Z.of_nat i)) (le4 v)) A (set_g_li (upd (g_li g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u32arr_store_ok _ m (A + ESO_LINE) (g_li g) (Z.of_nat i)); [exact Hli | lia | reflexivity]. }
  unfold es_raw, set_g_li. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u32arr_write _ m (A + ESO_LINE) (g_li g) (Z.of_nat i) v Hli ltac:(lia)). }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le4; lia | rewrite length_le4; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_fu : forall m A g (i : nat) (v : word), es_raw m A g -> g_len g -> (i < ERR_NUM)%nat ->
  store_ok ctasegs m (wa (A + ESO_FUNC + 8 * Z.of_nat i)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + ESO_FUNC + 8 * Z.of_nat i)) (le8 v)) A (set_g_fu (upd (g_fu g) i v) g).
Proof.
  intros m A g i v H HL Hi. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply (u64arr_store_ok _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i)); [exact Hfu | lia | reflexivity]. }
  unfold es_raw, set_g_fu. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { rewrite <- (Nat2Z.id i) at 2. exact (u64arr_write _ m (A + ESO_FUNC) (g_fu g) (Z.of_nat i) v Hfu ltac:(lia)). }
  apply rw_cells_frame; [exact HT | lia | rewrite length_le8; lia | rewrite length_le8; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_wr_top : forall m A g (t : Z), es_raw m A g -> g_len g ->
  store_ok ctasegs m (wa (A + 896)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + 896)) (le4 (wz t))) A (set_g_top t g).
Proof.
  intros m A g t H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { apply (rw_cells_store_ok_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 0%nat (C4 (wz (g_top g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  unfold es_raw, set_g_top. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 0%nat _ (C4 (wz t)) HT eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 0) with (A + 896) in W by lia. exact W.
Qed.

Lemma es_wr_bot : forall m A g (t : Z), es_raw m A g -> g_len g ->
  store_ok ctasegs m (wa (A + 900)) 4 = true
  /\ es_raw (write_to_mem m (wa (A + 900)) (le4 (wz t))) A (set_g_bot t g).
Proof.
  intros m A g t H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { apply (rw_cells_store_ok_at _ m (A + 896) [C4 (wz (g_top g)); C4 (wz (g_bot g))] 4%nat (C4 (wz (g_bot g))) 4); [exact HT | reflexivity | reflexivity | unfold wa; f_equal; lia]. }
  unfold es_raw, set_g_bot. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot]. eso.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le4; lia | rewrite length_le4; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 4%nat _ (C4 (wz t)) HT eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 4) with (A + 900) in W by lia. exact W.
Qed.

Lemma es_raw_transport : forall W m m' A g, es_raw m A g -> g_len g -> munch W m m' -> wmono ctasegs m m' ->
  disjoint_from W A 904 -> es_raw m' A g.
Proof.
  intros W m m' A g H HL MU WM HD. unfold es_raw in *. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  assert (D : forall a n, A <= a -> a + n <= A + 904 -> disjoint_from W a n).
  { intros a n Ha Hn. clear - HD Ha Hn. induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct HD as [HD1 HD2]. split; [lia | apply IH; exact HD2]. }
  split. { eapply u32arr_transport; [exact Hfl | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hma | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hbu | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hda | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hds | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hdf | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hfi | exact MU | exact WM | apply D; lia]. }
  split. { eapply u32arr_transport; [exact Hli | exact MU | exact WM | apply D; lia]. }
  split. { eapply u64arr_transport; [exact Hfu | exact MU | exact WM | apply D; lia]. }
  eapply rw_cells_transport; [exact HT | exact MU | exact WM | apply D; cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma es_raw_agree : forall P m m' A g, es_raw m A g -> g_len g -> agree_on P m m' -> (forall a, A <= a < A + 904 -> P a) -> es_raw m' A g.
Proof.
  intros P m m' A g H HL AG HP. unfold es_raw in *. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL. destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). eso.
  split. { eapply u32arr_agree; [exact AG | exact Hfl | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hma | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hbu | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hda | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hds | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hdf | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hfi | intros a Ha; apply HP; lia]. }
  split. { eapply u32arr_agree; [exact AG | exact Hli | intros a Ha; apply HP; lia]. }
  split. { eapply u64arr_agree; [exact AG | exact Hfu | intros a Ha; apply HP; lia]. }
  eapply rw_cells_agree; [exact AG | exact HT | intros a Ha; apply HP; cbn [cells_size csize Nat.add] in Ha; lia].
Qed.

End EsRaw.

Section EsRaw2.
Local Ltac eso := unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM in *.
Lemma es_rd_df1 : forall m A g (i : nat) a, es_raw m A g -> g_len g -> (i < ERR_NUM)%nat -> a = wa (A + ESO_DFLAGS + 4 * Z.of_nat i) ->
  ov_read_bytes ctasegs m a 1 = Some (le1 (nth i (g_df g) (wz 0))).
Proof.
  intros m A g i a H HL Hi ->. destruct H as (_ & _ & _ & _ & _ & [Hb _] & _). unfold g_len, ERR_NUM in *.
  destruct (nth_error_len (g_df g) i ltac:(lia)) as (w & Hw & <-).
  destruct (u32s_split _ _ _ Hw) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * Z.of_nat i) with (Z.of_nat (4 * i)) by lia.
  rewrite (bytes_at_ov_read ctasegs m (A + ESO_DFLAGS) (u32s (g_df g)) (4 * i) 1 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  unfold le4, le1. cbn [Z_to_le_bytes firstn app]. reflexivity.
Qed.

Lemma rw_cells_CB_of : forall m A cs, rw_cells ctasegs m A cs -> rw_cells ctasegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact W|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.

Lemma es_wr_tb0 : forall m A g, es_raw m A g -> g_len g ->
  store_ok ctasegs m (wa (A + 896)) 8 = true
  /\ es_raw (write_to_mem m (wa (A + 896)) (le8 (wz 0))) A (set_g_bot 0 (set_g_top 0 g)).
Proof.
  intros m A g H HL. pose proof (es_raw_bound m A g H) as HB. destruct H as (Hfl & Hma & Hbu & Hda & Hds & Hdf & Hfi & Hli & Hfu & HT). unfold g_len in HL.
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM in *.
  pose proof (rw_cells_CB_of _ _ _ HT) as HT8. cbn [cells_size csize cells_bytes cbytes Nat.add] in HT8. rewrite app_nil_r in HT8.
  split. { exact (rw_cells_store_ok_at _ m (A + 896) _ 0%nat _ 8 (wa (A + 896)) HT8 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)). }
  unfold es_raw, set_g_top, set_g_bot. cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot].
  unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP.
  split. { apply u32arr_frame; [exact Hfl | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hma | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hbu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hda | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hds | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hdf | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfi | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u32arr_frame; [exact Hli | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  split. { apply u64arr_frame; [exact Hfu | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  pose proof (rw_cells_write _ m (A + 896) _ 0%nat _ (C8 (wz 0)) HT8 eq_refl eq_refl I) as W. cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in W.
  replace (A + 896 + Z.of_nat 0) with (A + 896) in W by lia.
  eapply rw_cells_recast; [exact W|cbn; tauto|vm_compute; reflexivity|reflexivity].
Qed.
End EsRaw2.
