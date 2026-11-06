(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiOj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8FW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDxd_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x510dc%Z.
Definition w_11 := 0xcd1fd0ef%Z.
Definition w_26 := 0x00045597%Z.
Definition w_27 := 0xa458493%Z.
Definition w_37 := 0x314010ef%Z.
Definition w_40 := 0x00045517%Z.
Definition w_41 := 0xf8754503%Z.
Definition w_43 := 0x00045517%Z.
Definition w_44 := 0x06050513%Z.
Definition w_45 := 0x6380d0ef%Z.
Definition w_57 := 0xfffc5617%Z.
Definition w_59 := 0x33860993%Z.
Definition w_85 := 0xfffc5617%Z.
Definition w_90 := 0x2e860593%Z.
Definition w_125 := 0x00045517%Z.
Definition w_126 := 0xe3354503%Z.
Definition w_128 := 0x00045517%Z.
Definition w_129 := 0xf0c50513%Z.
Definition w_130 := 0x4e40d0ef%Z.
Definition w_147 := 0x00045517%Z.
Definition w_148 := 0xec050513%Z.
Definition w_149 := 0x7200d0ef%Z.
Definition w_152 := 0x350010ef%Z.
Definition w_203 := 0x6480d0ef%Z.
Definition w_216 := 0x00045517%Z.
Definition w_217 := 0xdac50513%Z.
Definition w_218 := 0x60c0d0ef%Z.
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_40 := (Z_to_bv 20 69).
Definition hi_43 := (Z_to_bv 20 69).
Definition hi_57 := (Z_to_bv 20 1048517).
Definition hi_85 := (Z_to_bv 20 1048517).
Definition hi_125 := (Z_to_bv 20 69).
Definition hi_128 := (Z_to_bv 20 69).
Definition hi_147 := (Z_to_bv 20 69).
Definition hi_216 := (Z_to_bv 20 69).
Definition lo_27 := (Z_to_bv 12 164).
Definition lo_41 := (Z_to_bv 12 3975).
Definition lo_44 := (Z_to_bv 12 96).
Definition lo_59 := (Z_to_bv 12 824).
Definition lo_90 := (Z_to_bv 12 744).
Definition lo_126 := (Z_to_bv 12 3635).
Definition lo_129 := (Z_to_bv 12 3852).
Definition lo_148 := (Z_to_bv 12 3776).
Definition lo_217 := (Z_to_bv 12 3500).
Definition joff_11 := (Z_to_bv 21 2088144).
Definition joff_37 := (Z_to_bv 21 4884).
Definition joff_45 := (Z_to_bv 21 54840).
Definition joff_130 := (Z_to_bv 21 54500).
Definition joff_149 := (Z_to_bv 21 55072).
Definition joff_152 := (Z_to_bv 21 4944).
Definition joff_203 := (Z_to_bv 21 54856).
Definition joff_218 := (Z_to_bv 21 54796).
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rerrno_loc_entry := QKNz.rerrno_loc_entry.
Definition rvm_wait_entry := QKNz.rvm_wait_entry.
Definition rlock_entry := QKNz.rlock_entry.
Definition runlock_entry := QKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x510dc (Qy8Z.Mq7.malloc_code 0xcd1fd0ef%Z 0x00045597%Z 0xa458493%Z 0x314010ef%Z 0x00045517%Z 0xf8754503%Z 0x00045517%Z 0x06050513%Z 0x6380d0ef%Z 0xfffc5617%Z 0x33860993%Z 0xfffc5617%Z 0x2e860593%Z 0x00045517%Z 0xe3354503%Z 0x00045517%Z 0xf0c50513%Z 0x4e40d0ef%Z 0x00045517%Z 0xec050513%Z 0x7200d0ef%Z 0x350010ef%Z 0x6480d0ef%Z 0x00045517%Z 0xdac50513%Z 0x60c0d0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x510dc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x510dc /\ 0x510dc + 880 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qy8Z.Mq7.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition runlock_spec := ltac:(pose proof (@runlock_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition renframe_walk := ltac:(pose proof (@renframe_walk) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mq7.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qy8Z.Mq7.runlock_post) (@QpkF.runlock_post) (Q6nq.gwt_def (@QCa8.Mq4.runlock_post) (@QpkF.runlock_post) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Qy8Z.Mq7.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@Qy8Z.Mq7.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Qy8Z.Mq7.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Qy8Z.Mq7.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Qy8Z.Mq7.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@Qy8Z.Mq7.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq3.renframe_tail_mem) (@QiOj.renframe_tail_mem) (Q6nq.gwt_def (@QCa8.Mq3.renframe_off_mem) (@QiOj.renframe_off_mem) (Q6nq.gwt_def (@Qy8Z.Mq7.ren3_post) (@QiOj.ren3_post) (Q6nq.gwt_def (@QCa8.Mq3.ren3_post) (@QiOj.ren3_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@Qy8Z.Mq7.rarea_rep) (@QQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))))))))))).
#[using="Type"] Lemma renf_glue_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq7.renf_glue_walk) [[@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([332800]%Z : list Z) '(Q6nq.gwt_zc renframe_entry (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_zc RCTX gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.renf_glue_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.renf_glue_walk)]. Qed.

#[using="Type"] Lemma bytes_at_enframe_user : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq7.bytes_at_enframe_user) [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.bytes_at_enframe_user) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.bytes_at_enframe_user)]. Qed.

Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (o m0 m1 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
(r : mstate * optr) (ms' : machine_state) : Prop :=
exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
r = (st', Some p)
/\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
/\ enf_leaf o st1 g b idx n st' p
/\ (forall bs, bytes_at rsegs m1 (conc st' p) bs -> Z.of_nat (length bs) <= n -> bytes_at rsegs m' (conc st' p) bs).

#[using="Type"] Lemma renf_implT : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq7.renf_implT) [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '([332800]%Z : list Z) '(Q6nq.gwt_zc RMLOCK (Q6nq.gwt_def (@Qy8Z.Mq7.renf_post) (@renf_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.renf_implT) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq7.renf_implT)]. Qed.

End RC__1.
