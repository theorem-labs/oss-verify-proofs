(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

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
Definition ralloc_meta_entry := UKNz.ralloc_meta_entry.
Definition ralloc_slot_entry := UKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QQRC.Mq4.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved rc_secret).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rimplT_steq {R} o (t1 t2 : QUZl.M R) s Q ms :
steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.rimplT_steq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.rimplT_steq)]. Qed.

#[using="Type"] Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> QUZl.M R') -> QUZl.M R' -> QUZl.M R')
(k : X -> Y -> QUZl.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
rimplT o (P _ kS bS) s QS ms ->
(forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
(forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
rimplT o (P R k bail) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.rimplT_nat2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.rimplT_nat2)]. Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
(exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
/\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv2 st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

#[using="Type"] Lemma ras_post2_post : ras_post2 = ras_post as_inv2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ras_post__3; @gw_eq_ras_post__2; @gw_eq_ras_post]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ras_post2_post) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ras_post2_post)]. Qed.

Definition ralloc_slot_stmt2 (fuel : nat) : Prop :=
forall (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).

#[using="Type"] Lemma ralloc_slot_stmt2_all : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_slot_stmt__3; @gw_eq_ralloc_slot_stmt__2; @gw_eq_ralloc_slot_stmt]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_slot_stmt2_all) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_slot_stmt2_all)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QQRC.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QQRC.Mq4.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QQRC.Mq4.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@QQRC.Mq4.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QQRC.Mq4.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Qy8Z.Mq1.RAS_STACK) (@UWfR.RAS_STACK) (Q6nq.gwt_def (@QCa8.Mq5.RAM_STACK) (@Uv2Y.RAM_STACK) Q6nq.gwt_nil)))))))))))).
#[using="Type"] Lemma ralloc_slot_stmtL : ltac2:(Q6nq.ty2 'Un81.GwI.segs '(@QQRC.Mq4.ralloc_slot_stmtL) [[@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) '(Q6nq.gwt_zc ralloc_slot_entry (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@QQRC.Mq4.ralloc_slot_stmt2) (@ralloc_slot_stmt2) (Q6nq.gwt_def (@QQRC.Mq4.ras_post2) (@ras_post2) (Q6nq.gwt_def (@QQRC.Mq4.ras_pre2) (@ras_pre2) (Q6nq.gwt_pat (@ralloc_slot_entry) (@ralloc_slot_entry) (Q6nq.gwt_hdr GwI.ralloc_slot_entry (@ralloc_slot_entry) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_slot_stmtL) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_slot_stmtL)]. Qed.

#[using="Type"] Lemma ralloc_meta_stmtL : ltac2:(Q6nq.ty2 'Un81.GwI.segs '(@QQRC.Mq4.ralloc_meta_stmtL) [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]; [@gw_eq_ralloc_meta_stmt__3; @gw_eq_ralloc_meta_stmt__2; @gw_eq_ralloc_meta_stmt]; [@gw_eq_ram_post__3; @gw_eq_ram_post__2; @gw_eq_ram_post]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([490496]%Z : list Z) '(Q6nq.gwt_unf (@RATP) (Q6nq.gwt_zc ralloc_meta_entry (Q6nq.gwt_zc RAM_STACK (Q6nq.gwt_def (@QQRC.Mq4.ralloc_slot_stmt2) (@ralloc_slot_stmt2) (Q6nq.gwt_def (@QQRC.Mq4.ras_post2) (@ras_post2) (Q6nq.gwt_def (@QQRC.Mq4.ras_pre2) (@ras_pre2) (Q6nq.gwt_pat (@ralloc_meta_entry) (@ralloc_meta_entry) (Q6nq.gwt_hdr GwI.ralloc_meta_entry (@ralloc_meta_entry) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]; [@gw_eq_ralloc_meta_stmt__3; @gw_eq_ralloc_meta_stmt__2; @gw_eq_ralloc_meta_stmt]; [@gw_eq_ram_post__3; @gw_eq_ram_post__2; @gw_eq_ram_post]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_meta_stmtL) | autorewrite with gw_eqs; GwApply2.gw_by_name2 Un81.GwI.segs (@QQRC.Mq4.ralloc_meta_stmtL)]. Qed.

End RC__1.
