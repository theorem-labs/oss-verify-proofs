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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZ24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZ24. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

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
Lemma CODE : CodeAt.code_at rsegs 0x54208 (Q8QT.Mq2.mm_code 0x92dfc0ef%Z 0x915fc0ef%Z 0xd3dfc0ef%Z 0x00044697%Z 0xbc06b683%Z 0xd01fc0ef%Z 0x00011297%Z 0x6742b483%Z 0xfd8fc0ef%Z 0xc55fc0ef%Z 0xc15fc0ef%Z 0xbedfc0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x54208 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x54208 /\ 0x54208 + 596 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition w_sysret_7 := 0xb19ff0ef%Z.
Lemma CODE_rsysret_entry : CodeAt.code_at rsegs rsysret_entry (Q8QT.Mq2.sysret_code 0xb19ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q8QT.Mq2.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition sysret_spec := ltac:(pose proof (@sysret_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_sysret_entry__3; @gw_eq_sysret_entry__2; @gw_eq_sysret_entry]; [@gw_eq_sysret_post__3; @gw_eq_sysret_post__2; @gw_eq_sysret_post]]); exact gw_h_).
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
/\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ match a with RgErr e => e = 12%Z | _ => True end.
Lemma gw_eq_rmunmap_post : @rmunmap_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmunmap_post rsegs) (@rmunmap_post)). Proof. unfold rmunmap_post, Q8QT.Mq2.rmunmap_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmunmap_post : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq2.sysret_post) (@UZ24.sysret_post) (Q6nq.gwt_def (@Q91D.Mq7.sysret_post) (@UZ24.sysret_post) Q6nq.gwt_nil)).
#[using="Type"] Lemma rmunmap_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq2.rmunmap_spec) [[@gw_eq_rmunmap_post]] '([164]%Z : list Z) '(Q6nq.gwt_zc rmunmap_entry gwt_X)).
Proof. rewrite ?gw_eq_rmunmap_post; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmunmap_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmunmap_spec)]. Qed.

#[using="Type"] Lemma rmprotect_args : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq2.rmprotect_args) [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]] '([4095; 4096; 18446744073709547520]%Z : list Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmprotect_args) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmprotect_args)]. Qed.

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ rw_cells rsegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
/\ match a with
| RgErr e => e = 12%Z
| RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
| RgDone false => True
end.
Lemma gw_eq_rmprotect_post : @rmprotect_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmprotect_post rsegs UKNz.RATP) (@rmprotect_post)). Proof. unfold rmprotect_post, Q8QT.Mq2.rmprotect_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmprotect_post : gw_eqs.

#[using="Type"] Lemma rmprotect_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq2.rmprotect_spec) [[@gw_eq_rmprotect_post]; [@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]] '([164; 4096; 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc rmprotect_entry (Q6nq.gwt_zc RPAGE_SIZE (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))).
Proof. rewrite ?gw_eq_rmprotect_post; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmprotect_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmprotect_spec)]. Qed.

#[using="Type"] Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.land_ones64) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.land_ones64)]. Qed.

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
: machine_state -> Prop :=
fun ms' =>
match a with
| MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
/\ e = 12%Z
| MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
/\ wmono rsegs m m2 /\ mem_inv rsegs m2
/\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
/\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
/\ mmap_addr_ok len avoid x = true
end.

#[using="Type"] Lemma rmmap_anon_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq2.rmmap_anon_spec) [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]] '([(-80); 164]%Z : list Z) '(Q6nq.gwt_zc rmmap_entry (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_anon_post) (@rmmap_anon_post) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmmap_anon_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmmap_anon_spec)]. Qed.

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
R a r u /\
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (u = false -> wmono rsegs m m')
/\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
Lemma gw_eq_rmmap_fixed_post : @rmmap_fixed_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmmap_fixed_post rsegs) (@rmmap_fixed_post)). Proof. unfold rmmap_fixed_post, Q8QT.Mq2.rmmap_fixed_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmmap_fixed_post : gw_eqs.

#[using="Type"] Lemma rmmap_fixed_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq2.rmmap_fixed_spec) [[@gw_eq_rmmap_fixed_post]; [@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]] '([(-80); 164]%Z : list Z) '(Q6nq.gwt_zc rmmap_entry (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_anon_post) (@rmmap_anon_post) gwt_X))).
Proof. rewrite ?gw_eq_rmmap_fixed_post; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmmap_fixed_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq2.rmmap_fixed_spec)]. Qed.

End RC__1.
Lemma gw_eq_rmunmap_post__2 : @rmunmap_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmunmap_post rsegs) (@rmunmap_post)). Proof. unfold rmunmap_post, Q8QT.Mq2.rmunmap_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmunmap_post__2 : gw_eqs.
Lemma gw_eq_rmprotect_post__2 : @rmprotect_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmprotect_post rsegs UKNz.RATP) (@rmprotect_post)). Proof. unfold rmprotect_post, Q8QT.Mq2.rmprotect_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmprotect_post__2 : gw_eqs.
Lemma gw_eq_rmmap_fixed_post__2 : @rmmap_fixed_post = ltac:(GwInst.gw_term (@Q8QT.Mq2.rmmap_fixed_post rsegs) (@rmmap_fixed_post)). Proof. unfold rmmap_fixed_post, Q8QT.Mq2.rmmap_fixed_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmmap_fixed_post__2 : gw_eqs.
