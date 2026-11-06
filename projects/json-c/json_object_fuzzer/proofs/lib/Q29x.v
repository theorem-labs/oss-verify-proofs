(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8eV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC00. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8FW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDxd_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5k8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5k8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Jg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Jg.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5144c%Z.
Definition w_14 := 0x00013517%Z.
Definition w_15 := 0xa0453a03%Z.
Definition w_18 := 0x00045597%Z.
Definition w_19 := 0xd5458b13%Z.
Definition w_114 := 0xfffc5597%Z.
Definition w_116 := 0xee458593%Z.
Definition w_121 := 0xfffc5517%Z.
Definition w_122 := 0xee850c93%Z.
Definition w_130 := 0x00045597%Z.
Definition w_131 := 0xadc5b583%Z.
Definition w_136 := 0xfffc5697%Z.
Definition w_137 := 0xf0c68693%Z.
Definition w_148 := 0xfffc5697%Z.
Definition w_149 := 0xef768693%Z.
Definition w_218 := 0xfffc5697%Z.
Definition w_220 := 0xd4468693%Z.
Definition w_311 := 0xfffc5717%Z.
Definition w_313 := 0xbf070713%Z.
Definition w_427 := 0x18d000ef%Z.
Definition w_552 := 0xdb0fd0ef%Z.
Definition hi_14 := (Z_to_bv 20 19).
Definition hi_18 := (Z_to_bv 20 69).
Definition hi_114 := (Z_to_bv 20 1048517).
Definition hi_121 := (Z_to_bv 20 1048517).
Definition hi_130 := (Z_to_bv 20 69).
Definition hi_136 := (Z_to_bv 20 1048517).
Definition hi_148 := (Z_to_bv 20 1048517).
Definition hi_218 := (Z_to_bv 20 1048517).
Definition hi_311 := (Z_to_bv 20 1048517).
Definition lo_15 := (Z_to_bv 12 2564).
Definition lo_19 := (Z_to_bv 12 3412).
Definition lo_116 := (Z_to_bv 12 3812).
Definition lo_122 := (Z_to_bv 12 3816).
Definition lo_131 := (Z_to_bv 12 2780).
Definition lo_137 := (Z_to_bv 12 3852).
Definition lo_149 := (Z_to_bv 12 3831).
Definition lo_220 := (Z_to_bv 12 3396).
Definition lo_313 := (Z_to_bv 12 3056).
Definition joff_427 := (Z_to_bv 21 2444).
Definition joff_552 := (Z_to_bv 21 2086320).
Definition e_197bc := 0x4f29c%Z.
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rvm_wait_entry := QKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x5144c (QROt.Mq3.alloc_slot_code 0x00013517%Z 0xa0453a03%Z 0x00045597%Z 0xd5458b13%Z 0xfffc5597%Z 0xee458593%Z 0xfffc5517%Z 0xee850c93%Z 0x00045597%Z 0xadc5b583%Z 0xfffc5697%Z 0xf0c68693%Z 0xfffc5697%Z 0xef768693%Z 0xfffc5697%Z 0xd4468693%Z 0xfffc5717%Z 0xbf070713%Z 0x18d000ef%Z 0xdb0fd0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5144c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5144c /\ 0x5144c + 2212 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Lemma ROM_RSMALL_CNT : ltac2:(GwEq.gw_fact_ty 'segs '(@QZxv.Mqm.gw_all) @ROM_RSMALL_CNT). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_RMED_CNT : ltac2:(GwEq.gw_fact_ty 'segs '(@QZxv.Mqm.gw_all) @ROM_RMED_CNT). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rsmall_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Lemma gw_eq_rsmall_cnt_bytes : @rsmall_cnt_bytes = ltac:(GwInst.gw_term (@QZxv.Mqm.rsmall_cnt_bytes) (@rsmall_cnt_bytes)). Proof. unfold rsmall_cnt_bytes, QZxv.Mqm.rsmall_cnt_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rsmall_cnt_bytes : gw_eqs.
Definition rmed_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RMED_CNT 4 with Some bs => bs | None => [] end).
Lemma gw_eq_rmed_cnt_bytes : @rmed_cnt_bytes = ltac:(GwInst.gw_term (@QZxv.Mqm.rmed_cnt_bytes) (@rmed_cnt_bytes)). Proof. unfold rmed_cnt_bytes, QZxv.Mqm.rmed_cnt_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmed_cnt_bytes : gw_eqs.

#[using="Type"] Lemma rsmall_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. rewrite ?gw_eq_rsmall_cnt_bytes; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rsmall_cnt_ro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rsmall_cnt_ro)]. Qed.
#[using="Type"] Lemma rmed_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. rewrite ?gw_eq_rmed_cnt_bytes; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rmed_cnt_ro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rmed_cnt_ro)]. Qed.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
#[using="Type"] Lemma rsmall_cnt_read : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rsmall_cnt_read) [[@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '(@nil Z) '(Q6nq.gwt_zc RSMALL_CNT (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rsmall_cnt_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rsmall_cnt_read)]. Qed.

#[using="Type"] Lemma rmed_cnt_read : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rmed_cnt_read) [[@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '(@nil Z) '(Q6nq.gwt_zc RMED_CNT (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rmed_cnt_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rmed_cnt_read)]. Qed.

Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.
Lemma gw_eq_rcnt_regs : @rcnt_regs = ltac:(GwInst.gw_term (@QZxv.Mqm.rcnt_regs) (@rcnt_regs)). Proof. unfold rcnt_regs, QZxv.Mqm.rcnt_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rcnt_regs : gw_eqs.

#[using="SZ"] Lemma rhalve_big_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rhalve_big_walk) [[@gw_eq_rcnt_regs]; [@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '([333532; 333552]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rcnt_regs; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_big_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_big_walk)]. Qed.
End HALVE.
Lemma gw_eq_rcnt_regs__2 : @rcnt_regs = ltac:(GwInst.gw_term (@QZxv.Mqm.rcnt_regs) (@rcnt_regs)). Proof. unfold rcnt_regs, QZxv.Mqm.rcnt_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rcnt_regs__2 : gw_eqs.
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.land2_half_parity) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.land2_half_parity)]. Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

#[using="UR"] Lemma rhalve_even_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rhalve_even_loop) [[@gw_eq_rcnt_regs__2]; [@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '([333492; 333532]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rcnt_regs__2; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_even_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_even_loop)]. Qed.

#[using="UR"] Lemma rhalve_even_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rhalve_even_walk) [[@gw_eq_rcnt_regs__2]; [@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '([333484; 333532]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rcnt_regs__2; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_even_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rhalve_even_walk)]. Qed.
End HALVE2.

Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcnt0_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcnt0_range)]. Qed.

#[using="RC__ MR SC UR"] Lemma rcount_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rcount_walk) [[@gw_eq_rcnt_regs__2]; [@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '([333392; 333552]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RSIZE_CLASSES (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))).
Proof. rewrite ?gw_eq_rcnt_regs__2; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcount_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcount_walk)]. Qed.
End COUNT.

Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="SZ C0"] Lemma rcnt2_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqm.rcnt2_walk) [[@gw_eq_rcnt_regs__2]; [@gw_eq_rsmall_cnt_bytes__3; @gw_eq_rsmall_cnt_bytes__2; @gw_eq_rsmall_cnt_bytes]; [@gw_eq_rmed_cnt_bytes__3; @gw_eq_rmed_cnt_bytes__2; @gw_eq_rmed_cnt_bytes]] '([2048; 333552; 333592; 333660]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rcnt_regs__2; first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcnt2_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqm.rcnt2_walk)]. Qed.
End CNT2.

End RC__1.
Lemma gw_eq_rsmall_cnt_bytes__2 : @rsmall_cnt_bytes = ltac:(GwInst.gw_term (@QZxv.Mqm.rsmall_cnt_bytes) (@rsmall_cnt_bytes)). Proof. unfold rsmall_cnt_bytes, QZxv.Mqm.rsmall_cnt_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rsmall_cnt_bytes__2 : gw_eqs.
Lemma gw_eq_rmed_cnt_bytes__2 : @rmed_cnt_bytes = ltac:(GwInst.gw_term (@QZxv.Mqm.rmed_cnt_bytes) (@rmed_cnt_bytes)). Proof. unfold rmed_cnt_bytes, QZxv.Mqm.rmed_cnt_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmed_cnt_bytes__2 : gw_eqs.
Lemma gw_eq_rcnt_regs__3 : @rcnt_regs = ltac:(GwInst.gw_term (@QZxv.Mqm.rcnt_regs) (@rcnt_regs)). Proof. unfold rcnt_regs, QZxv.Mqm.rcnt_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rcnt_regs__3 : gw_eqs.
