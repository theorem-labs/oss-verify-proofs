(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKZH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh29.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh29.
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
Definition base := 0x53d40%Z.
Definition w_15 := 0xde5fc0ef%Z.
Definition w_59 := 0x00044797%Z.
Definition w_62 := 0x1547b783%Z.
Definition w_67 := 0xfffc2797%Z.
Definition w_70 := 0x6f478793%Z.
Definition w_145 := 0xfffc2317%Z.
Definition w_147 := 0x59c30313%Z.
Definition w_185 := 0x31c000ef%Z.
Definition w_238 := 0x3400b0ef%Z.
Definition hi_59 := (Z_to_bv 20 68).
Definition hi_67 := (Z_to_bv 20 1048514).
Definition hi_145 := (Z_to_bv 20 1048514).
Definition lo_62 := (Z_to_bv 12 340).
Definition lo_70 := (Z_to_bv 12 1780).
Definition lo_147 := (Z_to_bv 12 1436).
Definition joff_15 := (Z_to_bv 21 2084324).
Definition joff_185 := (Z_to_bv 21 796).
Definition joff_238 := (Z_to_bv 21 45888).
Definition e_memcpy := 0x5f438%Z.
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
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QSsB.Mq9.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QKZH.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition lor_shl5 := ltac:(pose proof (@lor_shl5) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QKZH.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rr_ss_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
let r := E - P - n in
let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].
Lemma gw_eq_rr_ss_mem : @rr_ss_mem = ltac:(GwInst.gw_term (@QKZH.rr_ss_mem) (@rr_ss_mem)). Proof. unfold rr_ss_mem, QKZH.rr_ss_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rr_ss_mem : gw_eqs.

Definition rr_inplace_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (P E n k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ m' = rr_ss_mem m P E n k
/\ mem_inv rsegs m'.
Lemma gw_eq_rr_inplace_post : @rr_inplace_post = ltac:(GwInst.gw_term (@QKZH.rr_inplace_post rsegs) (@rr_inplace_post)). Proof. unfold rr_inplace_post, QKZH.rr_inplace_post; rewrite ?gw_eq_rr_ss_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rr_inplace_post : gw_eqs.

#[using="Type"] Lemma land31_idem k : Z.land (Z.land k 31) 31 = Z.land k 31.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QKZH.land31_idem) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.land31_idem)]. Qed.
End RC__1.
Lemma gw_eq_rr_ss_mem__2 : @rr_ss_mem = ltac:(GwInst.gw_term (@QKZH.rr_ss_mem) (@rr_ss_mem)). Proof. unfold rr_ss_mem, QKZH.rr_ss_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rr_ss_mem__2 : gw_eqs.
Lemma gw_eq_rr_inplace_post__2 : @rr_inplace_post = ltac:(GwInst.gw_term (@QKZH.rr_inplace_post rsegs) (@rr_inplace_post)). Proof. unfold rr_inplace_post, QKZH.rr_inplace_post; rewrite ?gw_eq_rr_ss_mem__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rr_inplace_post__2 : gw_eqs.

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QKZH.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QKZH.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)))).
#[using="Type"] Lemma rr_inplace_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@QKZH.rr_inplace_walk) [[@gw_eq_rr_inplace_post__2]; [@gw_eq_rr_ss_mem__3; @gw_eq_rr_ss_mem__2; @gw_eq_rr_ss_mem]] '([256; 344332]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rr_inplace_post__2; first [GwApply2.gw_by_name2 GwI.segs (@QKZH.rr_inplace_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.rr_inplace_walk)]. Qed.
End RC__2.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rr_inplace_mrep : ltac2:(Q6nq.ty2 'U4EM.GwI.segs '(@QKZH.rr_inplace_mrep) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rr_ss_mem__2]; [@gw_eq_rr_inplace_post__3; @gw_eq_rr_inplace_post__2; @gw_eq_rr_inplace_post]] '([256]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_rr_ss_mem__2; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 U4EM.GwI.segs (@QKZH.rr_inplace_mrep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 U4EM.GwI.segs (@QKZH.rr_inplace_mrep)]. Qed.

#[using="Type"] Lemma rpres_rr_ss : ltac2:(Q6nq.ty2 'U4EM.GwI.segs '(@QKZH.rpres_rr_ss) [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_rr_ss_mem__2]; [@gw_eq_rr_inplace_post__3; @gw_eq_rr_inplace_post__2; @gw_eq_rr_inplace_post]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rr_ss_mem__2; ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 U4EM.GwI.segs (@QKZH.rpres_rr_ss) | autorewrite with gw_eqs; GwApply2.gw_by_name2 U4EM.GwI.segs (@QKZH.rpres_rr_ss)]. Qed.

End RC__3.
