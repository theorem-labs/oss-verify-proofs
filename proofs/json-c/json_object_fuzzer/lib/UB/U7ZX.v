(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UznK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdkX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdkX.
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
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QQRC.Mqa.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q8l1.Mqb.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rdbi_range := ltac:(pose proof (@rdbi_range) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rdebruijn_read := ltac:(pose proof (@rdebruijn_read) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition mul_srliw27 := ltac:(pose proof (@mul_srliw27) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rclz_pow_eq := ltac:(pose proof (@rclz_pow_eq) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition lxor_4k_124 := ltac:(pose proof (@lxor_4k_124) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition lor_even_1 := ltac:(pose proof (@lor_even_1) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mqb.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rr_s2c_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqb.rr_s2c_walk) [] '([343864; 344264]%Z : list Z) '(Q6nq.gwt_zc RSIZE_CLASSES (Q6nq.gwt_zc MMAP_THRESHOLD Q6nq.gwt_nil))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqb.rr_s2c_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqb.rr_s2c_walk)]. Qed.

Definition cond_inplace (n avail sc : Z) : bool := (n <=? avail) && (n <? MMAP_THRESHOLD) && (sc <=? size_to_class n + 1).
Lemma gw_eq_cond_inplace : @cond_inplace = ltac:(GwInst.gw_term (@Q8l1.Mqb.cond_inplace) (@cond_inplace)). Proof. unfold cond_inplace, Q8l1.Mqb.cond_inplace; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_cond_inplace : gw_eqs.
Definition cond_mremap (n sc : Z) : bool := (48 <=? sc) && (MMAP_THRESHOLD <=? n).
Lemma gw_eq_cond_mremap : @cond_mremap = ltac:(GwInst.gw_term (@Q8l1.Mqb.cond_mremap) (@cond_mremap)). Proof. unfold cond_mremap, Q8l1.Mqb.cond_mremap; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_cond_mremap : gw_eqs.

#[using="Type"] Lemma rr_branch : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqb.rr_branch) [[@gw_eq_cond_inplace]; [@gw_eq_cond_mremap]] '([343848; 344020; 344024; 344264; 344268; 344328; 344332]%Z : list Z) '(Q6nq.gwt_zc RSIZE_CLASSES (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_cond_inplace, ?gw_eq_cond_mremap; first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqb.rr_branch) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqb.rr_branch)]. Qed.

End RC__1.
Lemma gw_eq_cond_inplace__2 : @cond_inplace = ltac:(GwInst.gw_term (@Q8l1.Mqb.cond_inplace) (@cond_inplace)). Proof. unfold cond_inplace, Q8l1.Mqb.cond_inplace; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_cond_inplace__2 : gw_eqs.
Lemma gw_eq_cond_mremap__2 : @cond_mremap = ltac:(GwInst.gw_term (@Q8l1.Mqb.cond_mremap) (@cond_mremap)). Proof. unfold cond_mremap, Q8l1.Mqb.cond_mremap; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_cond_mremap__2 : gw_eqs.
