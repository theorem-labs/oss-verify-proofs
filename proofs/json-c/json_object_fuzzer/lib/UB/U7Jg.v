(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.
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
Definition rdbi_range := ltac:(pose proof (@rdbi_range) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rdebruijn_read := ltac:(pose proof (@rdebruijn_read) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition mul_srliw27_sxv := ltac:(pose proof (@mul_srliw27_sxv) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rcoarse_post__3; @gw_eq_rcoarse_post__2; @gw_eq_rcoarse_post]; [@gw_eq_rfc_post__3; @gw_eq_rfc_post__2; @gw_eq_rfc_post]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QROt.Mq3.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QROt.Mq3.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QROt.Mq3.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QROt.Mq3.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QROt.Mq3.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QROt.Mq3.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QROt.Mq3.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QROt.Mq3.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QROt.Mq3.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QROt.Mq3.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QROt.Mq3.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))).
#[using="Type"] Lemma ras_ret : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.Mq3.ras_ret) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([(-144); 342580]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@QROt.Mq3.rta_frame) (@rta_frame) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QROt.Mq3.ras_ret) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.Mq3.ras_ret)]. Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.Mq3.rfin_walk) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([(-144); 340852]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@QROt.Mq3.rta_frame) (@rta_frame) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@QROt.Mq3.rfin_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.Mq3.rfin_walk)]. Qed.
End FIN.

End RC__1.
