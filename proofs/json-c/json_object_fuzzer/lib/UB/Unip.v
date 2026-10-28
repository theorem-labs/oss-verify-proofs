(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rfree_entry := UKNz.rfree_entry.
Definition rmalloc_entry := UKNz.rmalloc_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QkTt.Mq6.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QkTt.Mq6.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QkTt.Mq6.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QkTt.Mq6.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QkTt.Mq6.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QkTt.Mq6.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QkTt.Mq6.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QkTt.Mq6.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_stmt) (@UXT6.rmalloc_stmt) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QkTt.Mq6.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@QDXD.Mq3.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@QkTt.Mq6.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq3.rfree_stmt) (@UXT6.rfree_stmt) (Q6nq.gwt_def (@QkTt.Mq6.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@QDXD.Mq3.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@QkTt.Mq6.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QDXD.Mq3.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QkTt.Mq6.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QkTt.Mq6.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QkTt.Mq6.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QkTt.Mq6.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QDXD.Mq3.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QkTt.Mq6.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QDXD.Mq3.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QDXD.Mq3.RMALLOC_SYM) (@UXT6.RMALLOC_SYM) (Q6nq.gwt_def (@QDXD.Mq3.RMALLOC_STACK) (@UXT6.RMALLOC_STACK) (Q6nq.gwt_def (@QkTt.Mq6.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@QDXD.Mq3.RFREE_SYM) (@UXT6.RFREE_SYM) (Q6nq.gwt_def (@QDXD.Mq3.RFREE_STACK) (@UXT6.RFREE_STACK) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma impl_bind_inv : ltac2:(Q6nq.ty2 'GwI.segs '(@QkTt.Mq6.impl_bind_inv) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.impl_bind_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.impl_bind_inv)]. Qed.

#[using="Type"] Lemma impl_ebind_inv : ltac2:(Q6nq.ty2 'GwI.segs '(@QkTt.Mq6.impl_ebind_inv) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.impl_ebind_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.impl_ebind_inv)]. Qed.

#[using="Type"] Lemma implM_bind_inv : ltac2:(Q6nq.ty2 'GwI.segs '(@QkTt.Mq6.implM_bind_inv) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_bind_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_bind_inv)]. Qed.

#[using="Type"] Lemma implM_ret_inv : forall {St A} (a : A) (s : St) Q ms,
implM rsegs (mret a) s Q ms -> evt rsegs (Q a s) ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_ret_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_ret_inv)]. Qed.

#[using="Type"] Lemma implM_upd_inv : forall {St} (f : St -> St) s Q ms,
implM rsegs (mupd f) s Q ms -> evt rsegs (Q tt (f s)) ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_upd_inv) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.implM_upd_inv)]. Qed.

Definition rmalloc_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM rsegs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).

Definition rfree_impl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM rsegs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma rmalloc_stmt_of_impl : rmalloc_impl_stmt -> rmalloc_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N.
eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
{ unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

#[using="Type"] Lemma rfree_stmt_of_impl : rfree_impl_stmt -> rfree_stmt.
Proof.
intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv.
intros HP Hin AV HB ST LO SLO ERR MI TP A0.
eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
{ unfold RFREE_SYM. step. apply evt_done. reflexivity. }
intros ms' ->. eapply H; eauto.
Qed.

Definition cm_conv (st' : mstate) (n : Z) (p : option cptr) : option bptr :=
match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end.
Lemma gw_eq_cm_conv : @cm_conv = ltac:(GwInst.gw_term (@QkTt.Mq6.cm_conv) (@cm_conv)). Proof. unfold cm_conv, QkTt.Mq6.cm_conv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_cm_conv : gw_eqs.

#[using="Type"] Lemma rmalloc_membed : ltac2:(Q6nq.ty2 'GwI.segs '(@QkTt.Mq6.rmalloc_membed) [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmalloc_post__3; @gw_eq_rmalloc_post__2; @gw_eq_rmalloc_post]; [@gw_eq_cm_conv]] '(@nil Z) '(Q6nq.gwt_zc rmalloc_entry (Q6nq.gwt_zc RMALLOC_STACK (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@QkTt.Mq6.rfree_impl_stmt) (@rfree_impl_stmt) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@rmalloc_impl_stmt) (Q6nq.gwt_pat (@rmalloc_entry) (@rmalloc_entry) (Q6nq.gwt_hdr GwI.rmalloc_entry (@rmalloc_entry) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof. rewrite ?gw_eq_cm_conv; ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_RMALLOC_STACK__3; @gw_eq_RMALLOC_STACK__2; @gw_eq_RMALLOC_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmalloc_post__3; @gw_eq_rmalloc_post__2; @gw_eq_rmalloc_post]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.rmalloc_membed) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.rmalloc_membed)]. Qed.

#[using="Type"] Lemma rfree_membed : ltac2:(Q6nq.ty2 'GwI.segs '(@QkTt.Mq6.rfree_membed) [[@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rfree_post__3; @gw_eq_rfree_post__2; @gw_eq_rfree_post]; [@gw_eq_cm_conv__3; @gw_eq_cm_conv__2; @gw_eq_cm_conv]] '(@nil Z) '(Q6nq.gwt_zc rfree_entry (Q6nq.gwt_zc RFREE_STACK (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@QkTt.Mq6.rfree_impl_stmt) (@rfree_impl_stmt) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@rmalloc_impl_stmt) (Q6nq.gwt_pat (@rfree_entry) (@rfree_entry) (Q6nq.gwt_hdr GwI.rfree_entry (@rfree_entry) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFREE_STACK__3; @gw_eq_RFREE_STACK__2; @gw_eq_RFREE_STACK]; [@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rfree_post__3; @gw_eq_rfree_post__2; @gw_eq_rfree_post]]); first [GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.rfree_membed) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QkTt.Mq6.rfree_membed)]. Qed.

End RC__1.
Lemma gw_eq_cm_conv__2 : @cm_conv = ltac:(GwInst.gw_term (@QkTt.Mq6.cm_conv) (@cm_conv)). Proof. unfold cm_conv, QkTt.Mq6.cm_conv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_cm_conv__2 : gw_eqs.
