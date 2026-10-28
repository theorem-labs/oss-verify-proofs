(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJOB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x52e64%Z.
Definition w_11 := 0xcd1fd0ef%Z.
Definition w_26 := 0x00045597%Z.
Definition w_27 := 0xac58493%Z.
Definition w_37 := 0x314010ef%Z.
Definition w_40 := 0x00045517%Z.
Definition w_41 := 0xf8f54503%Z.
Definition w_43 := 0x00045517%Z.
Definition w_44 := 0x06850513%Z.
Definition w_45 := 0x6380d0ef%Z.
Definition w_57 := 0xfffc3617%Z.
Definition w_59 := 0x5d860993%Z.
Definition w_85 := 0xfffc3617%Z.
Definition w_90 := 0x58860593%Z.
Definition w_125 := 0x00045517%Z.
Definition w_126 := 0xe3b54503%Z.
Definition w_128 := 0x00045517%Z.
Definition w_129 := 0xf1450513%Z.
Definition w_130 := 0x4e40d0ef%Z.
Definition w_147 := 0x00045517%Z.
Definition w_148 := 0xec850513%Z.
Definition w_149 := 0x7200d0ef%Z.
Definition w_152 := 0x350010ef%Z.
Definition w_203 := 0x6480d0ef%Z.
Definition w_216 := 0x00045517%Z.
Definition w_217 := 0xdb450513%Z.
Definition w_218 := 0x60c0d0ef%Z.
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_40 := (Z_to_bv 20 69).
Definition hi_43 := (Z_to_bv 20 69).
Definition hi_57 := (Z_to_bv 20 1048515).
Definition hi_85 := (Z_to_bv 20 1048515).
Definition hi_125 := (Z_to_bv 20 69).
Definition hi_128 := (Z_to_bv 20 69).
Definition hi_147 := (Z_to_bv 20 69).
Definition hi_216 := (Z_to_bv 20 69).
Definition lo_27 := (Z_to_bv 12 172).
Definition lo_41 := (Z_to_bv 12 3983).
Definition lo_44 := (Z_to_bv 12 104).
Definition lo_59 := (Z_to_bv 12 1496).
Definition lo_90 := (Z_to_bv 12 1416).
Definition lo_126 := (Z_to_bv 12 3643).
Definition lo_129 := (Z_to_bv 12 3860).
Definition lo_148 := (Z_to_bv 12 3784).
Definition lo_217 := (Z_to_bv 12 3508).
Definition joff_11 := (Z_to_bv 21 2088144).
Definition joff_37 := (Z_to_bv 21 4884).
Definition joff_45 := (Z_to_bv 21 54840).
Definition joff_130 := (Z_to_bv 21 54500).
Definition joff_149 := (Z_to_bv 21 55072).
Definition joff_152 := (Z_to_bv 21 4944).
Definition joff_203 := (Z_to_bv 21 54856).
Definition joff_218 := (Z_to_bv 21 54796).
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
Definition rlock_entry := UKNz.rlock_entry.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x52e64 (Qy8Z.Mq7.malloc_code 0xcd1fd0ef%Z 0x00045597%Z 0xac58493%Z 0x314010ef%Z 0x00045517%Z 0xf8f54503%Z 0x00045517%Z 0x06850513%Z 0x6380d0ef%Z 0xfffc3617%Z 0x5d860993%Z 0xfffc3617%Z 0x58860593%Z 0x00045517%Z 0xe3b54503%Z 0x00045517%Z 0xf1450513%Z 0x4e40d0ef%Z 0x00045517%Z 0xec850513%Z 0x7200d0ef%Z 0x350010ef%Z 0x6480d0ef%Z 0x00045517%Z 0xdb450513%Z 0x60c0d0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52e64 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52e64 /\ 0x52e64 + 880 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QQRC.Mq8.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53188) fc None m1 (seg_rom rsegs)).

Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> QUZl.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> errv = Z_to_bv 64 12 -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QQRC.Mq8.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QQRC.Mq8.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QQRC.Mq8.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QQRC.Mq8.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QQRC.Mq8.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QQRC.Mq8.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QQRC.Mq8.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QQRC.Mq8.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QQRC.Mq8.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QQRC.Mq8.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QQRC.Mq8.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QQRC.Mq8.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QQRC.Mq8.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QQRC.Mq8.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@QQRC.Mq8.ralloc_fp) (@Uv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))))).
#[using="Type"] Lemma rmalloc_fp_cases : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq8.rmalloc_fp_cases) [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) '(Q6nq.gwt_def (@QQRC.Mq8.rfail_hyp) (@rfail_hyp) (Q6nq.gwt_def (@QQRC.Mq8.renf_hyp) (@renf_hyp) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_cases) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_cases)]. Qed.

#[using="Type"] Lemma rframe_after_call : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq8.rframe_after_call) [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_def (@QQRC.Mq8.rfail_hyp) (@rfail_hyp) (Q6nq.gwt_def (@QQRC.Mq8.renf_hyp) (@renf_hyp) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rframe_after_call) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rframe_after_call)]. Qed.

#[using="Type"] Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_sp_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_sp_mono)]. Qed.

#[using="Type"] Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_st_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_st_mono)]. Qed.

#[using="Type"] Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
0x62000 <= a < 0x99000 -> RCTX <= a < RCTX + 928 \/ 0x77b5c <= a < 0x77b60.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rmalloc_fp_image)]. Qed.

#[using="Type"] Lemma rauxv_ok_malloc_fp : ltac2:(Q6nq.ty2 'GwI.segs '(@QQRC.Mq8.rauxv_ok_malloc_fp) [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_def (@QQRC.Mq8.rfail_hyp) (@rfail_hyp) (Q6nq.gwt_def (@QQRC.Mq8.renf_hyp) (@renf_hyp) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rauxv_ok_malloc_fp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QQRC.Mq8.rauxv_ok_malloc_fp)]. Qed.

End RC__1.
