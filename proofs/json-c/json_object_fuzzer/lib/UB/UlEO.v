(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x527b4%Z.
Definition w_6 := 0x00013617%Z.
Definition w_7 := 0x20463483%Z.
Definition w_26 := 0x00045817%Z.
Definition w_27 := 0x76480913%Z.
Definition w_31 := 0xfffc4817%Z.
Definition w_32 := 0xd1080813%Z.
Definition w_93 := 0x00045697%Z.
Definition w_94 := 0x65868693%Z.
Definition w_245 := 0xc9cfe0ef%Z.
Definition hi_6 := (Z_to_bv 20 19).
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_31 := (Z_to_bv 20 1048516).
Definition hi_93 := (Z_to_bv 20 69).
Definition lo_7 := (Z_to_bv 12 516).
Definition lo_27 := (Z_to_bv 12 1892).
Definition lo_32 := (Z_to_bv 12 3344).
Definition lo_94 := (Z_to_bv 12 1624).
Definition joff_245 := (Z_to_bv 21 2090140).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Lemma CODE : CodeAt.code_at rsegs 0x527b4 (Qy8Z.Mq9.ntf_code 0x00013617%Z 0x20463483%Z 0x00045817%Z 0x76480913%Z 0xfffc4817%Z 0xd1080813%Z 0x00045697%Z 0x65868693%Z 0xc9cfe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x527b4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x527b4 /\ 0x527b4 + 984 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mq9.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End RC__1.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl rsegs mX) as WMq end.

Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
eapply rw_cells_congr; [ | | | exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Qy8Z.Mq9.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Qy8Z.Mq9.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Qy8Z.Mq9.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QDXD.Mq2.rntf_ret_post) (@UIMz.rntf_ret_post) (Q6nq.gwt_def (@Qy8Z.Mq9.rntf_ret_post) (@UIMz.rntf_ret_post) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qy8Z.Mq9.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Qy8Z.Mq9.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq2.rfree_fp) (@UIMz.rfree_fp) (Q6nq.gwt_def (@Qy8Z.Mq9.rfree_fp) (@UIMz.rfree_fp) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Qy8Z.Mq9.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))))))).
#[using="Type"] Lemma rntf_ret : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq9.rntf_ret) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]] '([(-96); 338780]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@Qy8Z.Mq9.rntf_frame) (@rntf_frame) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_ret) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_ret)]. Qed.

#[using="Type"] Lemma rntf_aor : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq9.rntf_aor) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([(-96); 338740]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@Qy8Z.Mq9.rntf_frame) (@rntf_frame) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_aor) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_aor)]. Qed.

#[using="Type"] Lemma rntf_frame_remerge : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq9.rntf_frame_remerge) [] '(@nil Z) '(Q6nq.gwt_def (@Qy8Z.Mq9.rntf_frame) (@rntf_frame) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_frame_remerge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_frame_remerge)]. Qed.

#[using="Type"] Lemma rntf_fm : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq9.rntf_fm) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]] '([(-96); 338584]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RCTX (Q6nq.gwt_def (@Qy8Z.Mq9.rntf_frame) (@rntf_frame) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_fm) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq9.rntf_fm)]. Qed.

End RC__2.
