(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZ24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZ24.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Open Scope Z_scope.
Local Unset Keyed Unification.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x54208%Z.
Definition w_11 := 0x92dfc0ef%Z.
Definition w_17 := 0x915fc0ef%Z.
Definition w_58 := 0xd3dfc0ef%Z.
Definition w_62 := 0x00044697%Z.
Definition w_63 := 0xbc06b683%Z.
Definition w_73 := 0xd01fc0ef%Z.
Definition w_85 := 0x00011297%Z.
Definition w_86 := 0x6742b483%Z.
Definition w_96 := 0xfd8fc0ef%Z.
Definition w_116 := 0xc55fc0ef%Z.
Definition w_130 := 0xc15fc0ef%Z.
Definition w_142 := 0xbedfc0ef%Z.
Definition hi_62 := (Z_to_bv 20 68).
Definition hi_85 := (Z_to_bv 20 17).
Definition lo_63 := (Z_to_bv 12 3008).
Definition lo_86 := (Z_to_bv 12 1652).
Definition joff_11 := (Z_to_bv 21 2083116).
Definition joff_17 := (Z_to_bv 21 2083092).
Definition joff_58 := (Z_to_bv 21 2084156).
Definition joff_73 := (Z_to_bv 21 2084096).
Definition joff_96 := (Z_to_bv 21 2082776).
Definition joff_116 := (Z_to_bv 21 2083924).
Definition joff_130 := (Z_to_bv 21 2083860).
Definition joff_142 := (Z_to_bv 21 2083820).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rsysret_entry := UKNz.rsysret_entry.
Lemma CODE : CodeAt.code_at rsegs 0x54208 (Q8QT.Mq3.mm_code 0x92dfc0ef%Z 0x915fc0ef%Z 0xd3dfc0ef%Z 0x00044697%Z 0xbc06b683%Z 0xd01fc0ef%Z 0x00011297%Z 0x6742b483%Z 0xfd8fc0ef%Z 0xc55fc0ef%Z 0xc15fc0ef%Z 0xbedfc0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x54208 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x54208 /\ 0x54208 + 596 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition w_sysret_7 := 0xb19ff0ef%Z.
Lemma CODE_rsysret_entry : CodeAt.code_at rsegs rsysret_entry (Q8QT.Mq3.sysret_code 0xb19ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q8QT.Mq3.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition sysret_spec := ltac:(pose proof (@sysret_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_sysret_entry__3; @gw_eq_sysret_entry__2; @gw_eq_sysret_entry]; [@gw_eq_sysret_post__3; @gw_eq_sysret_post__2; @gw_eq_sysret_post]]); exact gw_h_).
End GwI.

Local Abbreviation mem := (word -> option byte).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rmremap_entry : Z := 0x54340.
Lemma gw_eq_rmremap_entry : @rmremap_entry = ltac:(GwInst.gw_term (@Q8QT.Mq3.rmremap_entry 0x54208) (@rmremap_entry)). Proof. unfold rmremap_entry, Q8QT.Mq3.rmremap_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmremap_entry : gw_eqs.

Definition mremap_mem (x : mremap_ans) (old oldlen newlen : Z) (m2 : mem) : mem :=
match x with
| MrErr _ => m2
| MrInPlace => if newlen <? oldlen then apply_unmaps m2 [(wa (old + newlen), Z_to_bv 64 (oldlen - newlen))]
else apply_zeros m2 [(wa (old + oldlen), Z_to_bv 64 (newlen - oldlen))]
| MrMoved a => apply_copy m2 (apply_zeros (apply_unmaps m2 [(wa old, Z_to_bv 64 oldlen)]) [(wa (a + oldlen), Z_to_bv 64 (newlen - oldlen))])
(mkCopy (wa old) (wa a) (Z_to_bv 64 oldlen))
end.
Lemma gw_eq_mremap_mem : @mremap_mem = ltac:(GwInst.gw_term (@Q8QT.Mq3.mremap_mem) (@mremap_mem)). Proof. unfold mremap_mem, Q8QT.Mq3.mremap_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_mremap_mem : gw_eqs.

Definition mremap_ret (x : mremap_ans) (old : Z) : Z :=
match x with MrErr _ => -1 | MrInPlace => old | MrMoved a => a end.
Lemma gw_eq_mremap_ret : @mremap_ret = ltac:(GwInst.gw_term (@Q8QT.Mq3.mremap_ret) (@mremap_ret)). Proof. unfold mremap_ret, Q8QT.Mq3.mremap_ret; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_mremap_ret : gw_eqs.

Definition mremap_safe (x : mremap_ans) (old oldlen newlen : Z) : Prop :=
match x with
| MrErr _ => True
| MrInPlace => newlen < oldlen \/ (old + newlen <= alloc_ceiling /\ (old + newlen <= 0x10000 \/ 0x99000 <= old + oldlen))
| MrMoved a => (a + newlen <= 0x10000 \/ 0x99000 <= a) /\ (old + oldlen <= a \/ a + newlen <= old)
end.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(old oldlen newlen : Z) (errv : word) (lo : Z) (m : mem) (x : mremap_ans) : machine_state -> Prop :=
fun ms' =>
match x with
| MrErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
/\ e = 12
| _ => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mremap_ret x old)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mremap_mem x old oldlen newlen m2) (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m2
/\ wmono rsegs m m2 /\ mem_inv rsegs m2
/\ stk rsegs (mremap_mem x old oldlen newlen m2) lo (bv_unsigned sp)
/\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
/\ match x with MrMoved a => oldlen < newlen /\ a mod 4096 = 0 /\ 0 < a /\ a + newlen <= alloc_ceiling | _ => True end
end.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq3.sysret_post) (@UZ24.sysret_post) (Q6nq.gwt_def (@Q91D.Mq7.sysret_post) (@UZ24.sysret_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma rmremap_spec : ltac2:(Q6nq.ty2 'U1sW.GwI.segs '(@Q8QT.Mq3.rmremap_spec) [[@gw_eq_rmremap_entry]; [@gw_eq_mremap_mem__3; @gw_eq_mremap_mem__2; @gw_eq_mremap_mem]; [@gw_eq_mremap_ret__3; @gw_eq_mremap_ret__2; @gw_eq_mremap_ret]] '([(-112); 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc rmremap_entry (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RGOT_SSP (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@Q8QT.Mq3.rmremap_post) (@rmremap_post) (Q6nq.gwt_def (@Q8QT.Mq3.mremap_safe) (@mremap_safe) (Q6nq.gwt_pat (@RGOT_SSP) (@RGOT_SSP) (Q6nq.gwt_hdr GwI.RGOT_SSP (@RGOT_SSP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))))))).
Proof. rewrite ?gw_eq_rmremap_entry; first [GwApply2.gw_by_name2 U1sW.GwI.segs (@Q8QT.Mq3.rmremap_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 U1sW.GwI.segs (@Q8QT.Mq3.rmremap_spec)]. Qed.

#[using="Type"] Lemma rmremap_huge_spec : ltac2:(Q6nq.ty2 'U1sW.GwI.segs '(@Q8QT.Mq3.rmremap_huge_spec) [[@gw_eq_rmremap_entry]; [@gw_eq_mremap_mem__3; @gw_eq_mremap_mem__2; @gw_eq_mremap_mem]; [@gw_eq_mremap_ret__3; @gw_eq_mremap_ret__2; @gw_eq_mremap_ret]] '([(-112)]%Z : list Z) '(Q6nq.gwt_zc rmremap_entry (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RGOT_SSP (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@Q8QT.Mq3.rmremap_post) (@rmremap_post) (Q6nq.gwt_def (@Q8QT.Mq3.mremap_safe) (@mremap_safe) (Q6nq.gwt_pat (@RGOT_SSP) (@RGOT_SSP) (Q6nq.gwt_hdr GwI.RGOT_SSP (@RGOT_SSP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))))).
Proof. rewrite ?gw_eq_rmremap_entry; first [GwApply2.gw_by_name2 U1sW.GwI.segs (@Q8QT.Mq3.rmremap_huge_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 U1sW.GwI.segs (@Q8QT.Mq3.rmremap_huge_spec)]. Qed.

End RC__1.
Lemma gw_eq_rmremap_entry__2 : @rmremap_entry = ltac:(GwInst.gw_term (@Q8QT.Mq3.rmremap_entry 0x54208) (@rmremap_entry)). Proof. unfold rmremap_entry, Q8QT.Mq3.rmremap_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmremap_entry__2 : gw_eqs.
Lemma gw_eq_mremap_mem__2 : @mremap_mem = ltac:(GwInst.gw_term (@Q8QT.Mq3.mremap_mem) (@mremap_mem)). Proof. unfold mremap_mem, Q8QT.Mq3.mremap_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_mremap_mem__2 : gw_eqs.
Lemma gw_eq_mremap_ret__2 : @mremap_ret = ltac:(GwInst.gw_term (@Q8QT.Mq3.mremap_ret) (@mremap_ret)). Proof. unfold mremap_ret, Q8QT.Mq3.mremap_ret; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_mremap_ret__2 : gw_eqs.
