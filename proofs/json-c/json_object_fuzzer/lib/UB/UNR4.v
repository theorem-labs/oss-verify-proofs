(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x52b8c%Z.
Definition w_7 := 0x00013517%Z.
Definition w_8 := 0xe2853903%Z.
Definition w_10 := 0x00045597%Z.
Definition w_12 := 0x3c458993%Z.
Definition w_14 := 0x00045597%Z.
Definition w_15 := 0x2cc58413%Z.
Definition w_30 := 0x0350c0ef%Z.
Definition w_98 := 0x4f8010ef%Z.
Definition w_120 := 0x4a0010ef%Z.
Definition w_173 := 0x4b8010ef%Z.
Definition w_175 := 0xd19fd0ef%Z.
Definition w_181 := 0x9c4fe0ef%Z.
Definition hi_7 := (Z_to_bv 20 19).
Definition hi_10 := (Z_to_bv 20 69).
Definition hi_14 := (Z_to_bv 20 69).
Definition lo_8 := (Z_to_bv 12 3624).
Definition lo_12 := (Z_to_bv 12 964).
Definition lo_15 := (Z_to_bv 12 716).
Definition joff_30 := (Z_to_bv 21 51252).
Definition joff_98 := (Z_to_bv 21 5368).
Definition joff_120 := (Z_to_bv 21 5280).
Definition joff_173 := (Z_to_bv 21 5304).
Definition joff_175 := (Z_to_bv 21 2088216).
Definition joff_181 := (Z_to_bv 21 2089412).
Definition e_197bc := 0x51024%Z.
Definition e_24f80 := 0x5f438%Z.
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
Lemma CODE : CodeAt.code_at rsegs 0x52b8c (QQRC.Mq5.alloc_meta_code 0x00013517%Z 0xe2853903%Z 0x00045597%Z 0x3c458993%Z 0x00045597%Z 0x2cc58413%Z 0x0350c0ef%Z 0x4f8010ef%Z 0x4a0010ef%Z 0x4b8010ef%Z 0xd19fd0ef%Z 0x9c4fe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52b8c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52b8c /\ 0x52b8c + 728 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QQRC.Mq5.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mq5.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
Lemma gw_eq_ram_fp : @ram_fp = ltac:(GwInst.gw_term (@QQRC.Mq5.ram_fp UKNz.RATP) (@ram_fp)). Proof. unfold ram_fp, QQRC.Mq5.ram_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_ram_fp : gw_eqs.

#[using="Type"] Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. rewrite ?gw_eq_ram_fp; ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_fp__3; @gw_eq_ralloc_fp__2; @gw_eq_ralloc_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_alloc_fp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_alloc_fp)]. Qed.
#[using="Type"] Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. rewrite ?gw_eq_ram_fp; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_stack) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_stack)]. Qed.
#[using="Type"] Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. rewrite ?gw_eq_ram_fp; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_ctx)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QQRC.Mq5.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QQRC.Mq5.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)))).
#[using="Type"] Lemma ram_fp_region : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_fp_region) [[@gw_eq_ram_fp]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ram_fp; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_region)]. Qed.
#[using="Type"] Lemma ram_fp_not_errno : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_fp_not_errno) [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]; [@gw_eq_ram_fp]] '([490496]%Z : list Z) '(Q6nq.gwt_unf (@RATP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))).
Proof. rewrite ?gw_eq_ram_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_not_errno) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_not_errno)]. Qed.
#[using="Type"] Lemma ram_fp_meta : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_fp_meta) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_ram_fp]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ram_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_meta)]. Qed.

#[using="Type"] Lemma ram_fp_area : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_fp_area) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_ram_fp]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) gwt_X)).
Proof. rewrite ?gw_eq_ram_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_area) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_area)]. Qed.
#[using="Type"] Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. rewrite ?gw_eq_ram_fp; first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_same) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_fp_same)]. Qed.

Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 rc_canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma ram_tail : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_tail) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]] '([339456]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@QQRC.Mq5.ram_frame) (@ram_frame) (Q6nq.gwt_def (@QQRC.Mq5.ram_ret_post) (@ram_ret_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_tail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_tail)]. Qed.

#[using="Type"] Lemma ram_b0 : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq5.ram_b0) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]] '([339444]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_def (@QQRC.Mq5.ram_frame) (@ram_frame) (Q6nq.gwt_def (@QQRC.Mq5.ram_ret_post) (@ram_ret_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_b0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq5.ram_b0)]. Qed.

End RC__1.
Lemma gw_eq_ram_fp__2 : @ram_fp = ltac:(GwInst.gw_term (@QQRC.Mq5.ram_fp UKNz.RATP) (@ram_fp)). Proof. unfold ram_fp, QQRC.Mq5.ram_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ram_fp__2 : gw_eqs.
