(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzQg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiOj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QznK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAr0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUSO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUSO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5k8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5k8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Jg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Jg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVfK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVfK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTPE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTPE.
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
Definition rdbi_range := ltac:(pose proof (@rdbi_range) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rdebruijn_read := ltac:(pose proof (@rdebruijn_read) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition mul_srliw27_sxv := ltac:(pose proof (@mul_srliw27_sxv) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rcoarse_post__3; @gw_eq_rcoarse_post__2; @gw_eq_rcoarse_post]; [@gw_eq_rfc_post__3; @gw_eq_rfc_post__2; @gw_eq_rfc_post]]); exact gw_h_).
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QzQg.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QzQg.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).
Lemma gw_eq_rta_fp : @rta_fp = ltac:(GwInst.gw_term (@QzQg.rta_fp QKNz.RATP) (@rta_fp)). Proof. unfold rta_fp, QzQg.rta_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rta_fp : gw_eqs.

#[using="Type"] Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. rewrite ?gw_eq_rta_fp; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_stack) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_stack)]. Qed.
#[using="Type"] Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. rewrite ?gw_eq_rta_fp; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_ctx)]. Qed.
#[using="Type"] Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. rewrite ?gw_eq_rta_fp; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_meta)]. Qed.
#[using="Type"] Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. rewrite ?gw_eq_rta_fp; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_grp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_fp_grp)]. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).

Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv rsegs m' -> stk rsegs m' lo spv ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)).

#[using="CLO LO HK1"] Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
rmrep stX mZ -> mem_inv rsegs mZ -> rw_cells rsegs mZ (spv + -144) (FRM junk) -> stk rsegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_fin stX g3 msk K) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x515ec) fc None mZ (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rta_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [ (pose proof HK1 as gw_h_; clear HK1; rewrite ?gw_eq_rta_fp in gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into HK1) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rfin_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rfin_block)]. Qed.

#[using="TAF SC CLO LO HK1"] Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
(pc = 0x51568 \/ pc = 0x51574) ->
ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
rmrep stZ mZ -> mem_inv rsegs mZ -> rw_cells rsegs mZ (spv + -144) (FRM junk) -> stk rsegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_avz K bail stZ g3) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rta_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [ (pose proof HK1 as gw_h_; clear HK1; rewrite ?gw_eq_rta_fp in gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into HK1) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.ravz_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.ravz_block)]. Qed.

#[using="TAF SC CLO LO HK1"] Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
msk = m_freed (get_meta_rec stY g2) ->
(forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
m_next (get_meta_rec stY g2) <> None ->
rmrep stY mY -> mem_inv rsegs mY -> rw_cells rsegs mY (spv + -144) (FRM junk) -> stk rsegs mY lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mY ->
rimplT o (ta_act sc K bail stY g2 msk) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0x51540) fc None mY (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rta_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [ (pose proof HK1 as gw_h_; clear HK1; rewrite ?gw_eq_rta_fp in gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into HK1) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.ract_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.ract_block)]. Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.
Lemma gw_eq_rnclosed : @rnclosed = ltac:(GwInst.gw_term (@QzQg.rnclosed) (@rnclosed)). Proof. unfold rnclosed, QzQg.rnclosed; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rnclosed : gw_eqs.

#[using="TAF SC CLO LO HK1"] Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
rmrep stX mX -> mem_inv rsegs mX -> rw_cells rsegs mX (spv + -144) (FRM junk) -> stk rsegs mX lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mX ->
rimplT o (ta_m sc K bail stX g1) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x51514) fc None mX (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rta_fp, ?gw_eq_rnclosed; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [ (pose proof HK1 as gw_h_; clear HK1; rewrite ?gw_eq_rta_fp in gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into HK1) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rm_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rm_block)]. Qed.

#[using="TAF SC CLO LO HK1"] Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
a0 = Z_to_bv 64 sc ->
rmrep st m -> mem_inv rsegs m -> stk rsegs m lo spv ->
(forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m' -> mem_inv rsegs m' -> rw_cells rsegs m' (spv + -144) (FRM junk) -> stk rsegs m' lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0x5162c) fc None m' (seg_rom rsegs))) ->
rimplT o (try_avail sc st K bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rta_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [ (pose proof HK1 as gw_h_; clear HK1; rewrite ?gw_eq_rta_fp in gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into HK1) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_phase) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QzQg.rta_phase)]. Qed.
End PHASE.
Lemma gw_eq_rnclosed__2 : @rnclosed = ltac:(GwInst.gw_term (@QzQg.rnclosed) (@rnclosed)). Proof. unfold rnclosed, QzQg.rnclosed; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rnclosed__2 : gw_eqs.

End RC__1.
Lemma gw_eq_rta_fp__2 : @rta_fp = ltac:(GwInst.gw_term (@QzQg.rta_fp QKNz.RATP) (@rta_fp)). Proof. unfold rta_fp, QzQg.rta_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rta_fp__2 : gw_eqs.
Lemma gw_eq_rnclosed__3 : @rnclosed = ltac:(GwInst.gw_term (@QzQg.rnclosed) (@rnclosed)). Proof. unfold rnclosed, QzQg.rnclosed; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rnclosed__3 : gw_eqs.
