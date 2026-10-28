(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5102c%Z.
Definition w_7 := 0xb19ff0ef%Z.
Definition joff_7 := (Z_to_bv 21 2095896).
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Lemma CODE : CodeAt.code_at rsegs 0x5102c (Q91D.Mq7.sysret_code 0xb19ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5102c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5102c /\ 0x5102c + 56 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q91D.Mq7.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Definition sysret_entry := 0x5102c%Z.
Lemma gw_eq_sysret_entry : @sysret_entry = ltac:(GwInst.gw_term (@Q91D.Mq7.sysret_entry 0x5102c) (@sysret_entry)). Proof. unfold sysret_entry, Q91D.Mq7.sysret_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sysret_entry : gw_eqs.

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
Lemma gw_eq_sysret_post : @sysret_post = ltac:(GwInst.gw_term (@Q91D.Mq7.sysret_post rsegs) (@sysret_post)). Proof. unfold sysret_post, Q91D.Mq7.sysret_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sysret_post : gw_eqs.

Lemma sysret_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q91D.Mq7.sysret_spec) [[@gw_eq_sysret_post]; [@gw_eq_sysret_entry__3; @gw_eq_sysret_entry__2; @gw_eq_sysret_entry]] '([164; 331820]%Z : list Z) '(Q6nq.gwt_unf (@sysret_entry) Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_sysret_post; first [GwApply2.gw_by_name2 GwI.segs (@Q91D.Mq7.sysret_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q91D.Mq7.sysret_spec)]. Qed.

