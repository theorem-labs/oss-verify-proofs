(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UznK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UAr0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUSO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUSO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un81. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5k8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5k8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Jg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7Jg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UVfK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVfK.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x531d4%Z.
Definition w_14 := 0x00012517%Z.
Definition w_15 := 0x7c453a03%Z.
Definition w_18 := 0x00045597%Z.
Definition w_19 := 0xd5c58b13%Z.
Definition w_114 := 0xfffc3597%Z.
Definition w_116 := 0x18458593%Z.
Definition w_121 := 0xfffc3517%Z.
Definition w_122 := 0x18850c93%Z.
Definition w_130 := 0x00045597%Z.
Definition w_131 := 0xae45b583%Z.
Definition w_136 := 0xfffc3697%Z.
Definition w_137 := 0x1ac68693%Z.
Definition w_148 := 0xfffc3697%Z.
Definition w_149 := 0x19768693%Z.
Definition w_218 := 0xfffc3697%Z.
Definition w_220 := 0xfe468693%Z.
Definition w_311 := 0xfffc3717%Z.
Definition w_313 := 0xe9070713%Z.
Definition w_427 := 0x18d000ef%Z.
Definition w_552 := 0xdb0fd0ef%Z.
Definition hi_14 := (Z_to_bv 20 18).
Definition hi_18 := (Z_to_bv 20 69).
Definition hi_114 := (Z_to_bv 20 1048515).
Definition hi_121 := (Z_to_bv 20 1048515).
Definition hi_130 := (Z_to_bv 20 69).
Definition hi_136 := (Z_to_bv 20 1048515).
Definition hi_148 := (Z_to_bv 20 1048515).
Definition hi_218 := (Z_to_bv 20 1048515).
Definition hi_311 := (Z_to_bv 20 1048515).
Definition lo_15 := (Z_to_bv 12 1988).
Definition lo_19 := (Z_to_bv 12 3420).
Definition lo_116 := (Z_to_bv 12 388).
Definition lo_122 := (Z_to_bv 12 392).
Definition lo_131 := (Z_to_bv 12 2788).
Definition lo_137 := (Z_to_bv 12 428).
Definition lo_149 := (Z_to_bv 12 407).
Definition lo_220 := (Z_to_bv 12 4068).
Definition lo_313 := (Z_to_bv 12 3728).
Definition joff_427 := (Z_to_bv 21 2444).
Definition joff_552 := (Z_to_bv 21 2086320).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x531d4 (QROt.Mq3.alloc_slot_code 0x00012517%Z 0x7c453a03%Z 0x00045597%Z 0xd5c58b13%Z 0xfffc3597%Z 0x18458593%Z 0xfffc3517%Z 0x18850c93%Z 0x00045597%Z 0xae45b583%Z 0xfffc3697%Z 0x1ac68693%Z 0xfffc3697%Z 0x19768693%Z 0xfffc3697%Z 0xfe468693%Z 0xfffc3717%Z 0xe9070713%Z 0x18d000ef%Z 0xdb0fd0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x531d4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x531d4 /\ 0x531d4 + 2212 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq8.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq8.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QZxv.Mqo.rt1_regs) (@UVfK.rt1_regs) (Q6nq.gwt_def (@Q5m9.Mq8.rt1_regs) (@UVfK.rt1_regs) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q5m9.Mq8.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q5m9.Mq8.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q5m9.Mq8.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q5m9.Mq8.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q5m9.Mq8.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))).
#[using="Type"] Lemma lw_slli52_srli58_sc : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq8.lw_slli52_srli58_sc) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.lw_slli52_srli58_sc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.lw_slli52_srli58_sc)]. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

#[using="RC__ mr MR MSL AV0"] Lemma ravz_pre_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq8.ravz_pre_walk) [[@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]] '([340720; 340732]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ravz_pre_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ravz_pre_walk)]. Qed.

#[using="b MR MSL AV0 Hmem Hgh AI FR32 MW MASK BNC SC0"] Lemma ravz_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
bv_unsigned gw = G -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53374) fc None m' (seg_rom rsegs)
/\ munch [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep st5 m')
(MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x532fc) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ravz_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ravz_walk)]. Qed.
End AVZ.

Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

#[using="SZ"] Lemma rspan_loop_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq8.rspan_loop_walk) [] '([4096; 341744; 341764]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.rspan_loop_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.rspan_loop_walk)]. Qed.
End SPANLOOP.
#[using="Type"] Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ai_byte_land224) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ai_byte_land224)]. Qed.

Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

#[using="RC__ b mr MR MSL Hmem Hgh AI0 MASKR"] Lemma ract_skip_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq8.ract_skip_walk) [[@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([340680; 340720]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_skip_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_skip_walk)]. Qed.

#[using="b MR MSL SC Hmem Hgh AI0"] Lemma ract_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x532f0) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x532c8) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_next_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_next_walk)]. Qed.

#[using="ai0 MR MSL Hgh AI0"] Lemma rspan_tail_walk :
forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x532fc) fc None m' (seg_rom rsegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x53714) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.rspan_tail_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.rspan_tail_walk)]. Qed.

#[using="MR MSL Hmem Hgh AI0"] Lemma ract_span_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
(forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
g_meta gh = Some g -> m_avail mr = 0 ->
mem_inv rsegs m ->
let sc' := m_sizeclass mr in
let cnt := ai0 + 2 in
let size := size_class sc' * UNIT in
let span := UNIT + size * cnt in
let cnt1 := span_loop 300 cnt span size in
let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
evt rsegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x532fc) fc None m' (seg_rom rsegs)
/\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x532c8) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rt1_regs__3; @gw_eq_rt1_regs__2; @gw_eq_rt1_regs]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_span_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq8.ract_span_walk)]. Qed.
End ACT.

End RC__1.
