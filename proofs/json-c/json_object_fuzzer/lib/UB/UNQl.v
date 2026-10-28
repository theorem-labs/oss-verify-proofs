(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00.
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
Definition base := 0x524d8%Z.
Definition w_21 := 0xfffc4717%Z.
Definition w_23 := 0x01470713%Z.
Definition w_64 := 0x00046717%Z.
Definition w_71 := 0x8bb74883%Z.
Definition w_85 := 0x00046597%Z.
Definition w_86 := 0x94c58593%Z.
Definition w_89 := 0x7150d0ef%Z.
Definition w_95 := 0x00046517%Z.
Definition w_96 := 0x92450513%Z.
Definition w_97 := 0x17c0e0ef%Z.
Definition w_99 := 0xcfcfe0ef%Z.
Definition w_104 := 0x59d010ef%Z.
Definition hi_21 := (Z_to_bv 20 1048516).
Definition hi_64 := (Z_to_bv 20 70).
Definition hi_85 := (Z_to_bv 20 70).
Definition hi_95 := (Z_to_bv 20 70).
Definition lo_23 := (Z_to_bv 12 20).
Definition lo_71 := (Z_to_bv 12 2235).
Definition lo_86 := (Z_to_bv 12 2380).
Definition lo_96 := (Z_to_bv 12 2340).
Definition joff_89 := (Z_to_bv 21 57108).
Definition joff_97 := (Z_to_bv 21 57724).
Definition joff_99 := (Z_to_bv 21 2090236).
Definition joff_104 := (Z_to_bv 21 7580).
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Definition rlock_entry := UKNz.rlock_entry.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x524d8 (Qy8Z.Mq5.free_code 0xfffc4717%Z 0x01470713%Z 0x00046717%Z 0x8bb74883%Z 0x00046597%Z 0x94c58593%Z 0x7150d0ef%Z 0x00046517%Z 0x92450513%Z 0x17c0e0ef%Z 0xcfcfe0ef%Z 0x59d010ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x524d8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x524d8 /\ 0x524d8 + 460 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qy8Z.Mq5.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition runlock_spec := ltac:(pose proof (@runlock_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QCa8.Mq4.runlock_post) (@UpkF.runlock_post) (Q6nq.gwt_def (@Qy8Z.Mq5.runlock_post) (@UpkF.runlock_post) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Qy8Z.Mq5.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QDXD.Mq2.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Qy8Z.Mq5.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Qy8Z.Mq5.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qy8Z.Mq5.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Qy8Z.Mq5.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Qy8Z.Mq5.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))))).
#[using="Type"] Lemma rfree_fin0 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq5.rfree_fin0) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([337484]%Z : list Z) '(Q6nq.gwt_zc RATP (Q6nq.gwt_def (@Qy8Z.Mq5.rffin_post) (@rffin_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_fin0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_fin0)]. Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x5267c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="Type"] Lemma rfree_tomunmap : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq5.rfree_tomunmap) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([337484]%Z : list Z) '(Q6nq.gwt_zc RATP (Q6nq.gwt_def (@Qy8Z.Mq5.rfmun_post) (@rfmun_post) (Q6nq.gwt_def (@Qy8Z.Mq5.rffin_post) (@rffin_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_tomunmap) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_tomunmap)]. Qed.

#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 490332 <= a < 490336 -> ~ rrepfoot st a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rerrno_avoids_repfoot) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rerrno_avoids_repfoot)]. Qed.

#[using="Type"] Lemma rmrep_transport_frame_errno : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq5.rmrep_transport_frame_errno) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([490332; 490336]%Z : list Z) '(Q6nq.gwt_unf (@RERRNO) (Q6nq.gwt_def (@Qy8Z.Mq5.rfmun_post) (@rfmun_post) (Q6nq.gwt_def (@Qy8Z.Mq5.rffin_post) (@rffin_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rmrep_transport_frame_errno) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rmrep_transport_frame_errno)]. Qed.

#[using="Type"] Lemma rfree_fin1 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq5.rfree_fin1) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([337532; 490332; 490336]%Z : list Z) '(Q6nq.gwt_unf (@RERRNO) (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@Qy8Z.Mq5.rfmun_post) (@rfmun_post) (Q6nq.gwt_def (@Qy8Z.Mq5.rffin_post) (@rffin_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_fin1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq5.rfree_fin1)]. Qed.

End RC__1.
