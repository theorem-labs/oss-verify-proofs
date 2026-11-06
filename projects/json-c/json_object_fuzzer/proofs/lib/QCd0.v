(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8eV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x50750%Z.
Definition w_21 := 0xfffc6717%Z.
Definition w_23 := 0xd7470713%Z.
Definition w_64 := 0x00046717%Z.
Definition w_71 := 0x8b374883%Z.
Definition w_85 := 0x00046597%Z.
Definition w_86 := 0x94458593%Z.
Definition w_89 := 0x7150d0ef%Z.
Definition w_95 := 0x00046517%Z.
Definition w_96 := 0x91c50513%Z.
Definition w_97 := 0x17c0e0ef%Z.
Definition w_99 := 0xcfcfe0ef%Z.
Definition w_104 := 0x59d010ef%Z.
Definition hi_21 := (Z_to_bv 20 1048518).
Definition hi_64 := (Z_to_bv 20 70).
Definition hi_85 := (Z_to_bv 20 70).
Definition hi_95 := (Z_to_bv 20 70).
Definition lo_23 := (Z_to_bv 12 3444).
Definition lo_71 := (Z_to_bv 12 2227).
Definition lo_86 := (Z_to_bv 12 2372).
Definition lo_96 := (Z_to_bv 12 2332).
Definition joff_89 := (Z_to_bv 21 57108).
Definition joff_97 := (Z_to_bv 21 57724).
Definition joff_99 := (Z_to_bv 21 2090236).
Definition joff_104 := (Z_to_bv 21 7580).
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rerrno_loc_entry := QKNz.rerrno_loc_entry.
Definition rvm_wait_entry := QKNz.rvm_wait_entry.
Definition rlock_entry := QKNz.rlock_entry.
Definition runlock_entry := QKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x50750 (Qy8Z.Mq4.free_code 0xfffc6717%Z 0xd7470713%Z 0x00046717%Z 0x8b374883%Z 0x00046597%Z 0x94458593%Z 0x7150d0ef%Z 0x00046517%Z 0x91c50513%Z 0x17c0e0ef%Z 0xcfcfe0ef%Z 0x59d010ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x50750 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x50750 /\ 0x50750 + 460 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qy8Z.Mq4.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qy8Z.Mq4.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Qy8Z.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@Qy8Z.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Qy8Z.Mq4.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Qy8Z.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@Qy8Z.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq2.rfree_fp) (@QIMz.rfree_fp) (Q6nq.gwt_def (@Qy8Z.Mq4.rfree_fp) (@QIMz.rfree_fp) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@Qy8Z.Mq4.rarea_rep) (@QQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))))).
#[using="Type"] Lemma rfree_fp_meta0 : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq4.rfree_fp_meta0) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_fp_meta0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_fp_meta0)]. Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except C m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

#[using="Type"] Lemma rfree_triv : ltac2:(Q6nq.ty2 'GwI.segs '(@Qy8Z.Mq4.rfree_triv) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([329812; 616528]%Z : list Z) '(Q6nq.gwt_def (@Qy8Z.Mq4.rftriv_post) (@rftriv_post) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_triv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_triv)]. Qed.

#[using="Type"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv rsegs m -> meta_slot st g ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
(m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
evt rsegs (fun ms' => exists x2 x3 x4 x5 x6 x7,
ms' = MS (mkR (Z_to_bv 64 0x508c4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x50a2c) fc None m (seg_rom rsegs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 0x96850) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x50854) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]]); first [GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_tocall) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qy8Z.Mq4.rfree_tocall)]. Qed.

End RC__1.
