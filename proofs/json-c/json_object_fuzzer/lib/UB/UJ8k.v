(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFs1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFs1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un81. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Jg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7Jg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UVfK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVfK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U29x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U29x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UISU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UISU. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8bj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8bj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x531d4%Z.
Definition w_14 := 0x00012517%Z.
Definition w_15 := 0x7c453a03%Z.
Definition w_18 := 0x00045597%Z.
Definition w_19 := 0xd5c58b13%Z.
Definition w_114 := 0xfffc3597%Z.
Definition w_116 := 0x18458593%Z.
Definition w_121 := 0xfffc3517%Z.
Definition w_122 := 0x18850c93%Z.
Definition w_130 := 0x00045597%Z.
Definition w_131 := 0xae45b583%Z.
Definition w_136 := 0xfffc3697%Z.
Definition w_137 := 0x1ac68693%Z.
Definition w_148 := 0xfffc3697%Z.
Definition w_149 := 0x19768693%Z.
Definition w_218 := 0xfffc3697%Z.
Definition w_220 := 0xfe468693%Z.
Definition w_311 := 0xfffc3717%Z.
Definition w_313 := 0xe9070713%Z.
Definition w_427 := 0x18d000ef%Z.
Definition w_552 := 0xdb0fd0ef%Z.
Definition hi_14 := (Z_to_bv 20 18).
Definition hi_18 := (Z_to_bv 20 69).
Definition hi_114 := (Z_to_bv 20 1048515).
Definition hi_121 := (Z_to_bv 20 1048515).
Definition hi_130 := (Z_to_bv 20 69).
Definition hi_136 := (Z_to_bv 20 1048515).
Definition hi_148 := (Z_to_bv 20 1048515).
Definition hi_218 := (Z_to_bv 20 1048515).
Definition hi_311 := (Z_to_bv 20 1048515).
Definition lo_15 := (Z_to_bv 12 1988).
Definition lo_19 := (Z_to_bv 12 3420).
Definition lo_116 := (Z_to_bv 12 388).
Definition lo_122 := (Z_to_bv 12 392).
Definition lo_131 := (Z_to_bv 12 2788).
Definition lo_137 := (Z_to_bv 12 428).
Definition lo_149 := (Z_to_bv 12 407).
Definition lo_220 := (Z_to_bv 12 4068).
Definition lo_313 := (Z_to_bv 12 3728).
Definition joff_427 := (Z_to_bv 21 2444).
Definition joff_552 := (Z_to_bv 21 2086320).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x531d4 (QROt.Mq3.alloc_slot_code 0x00012517%Z 0x7c453a03%Z 0x00045597%Z 0xd5c58b13%Z 0xfffc3597%Z 0x18458593%Z 0xfffc3517%Z 0x18850c93%Z 0x00045597%Z 0xae45b583%Z 0xfffc3697%Z 0x1ac68693%Z 0xfffc3697%Z 0x19768693%Z 0xfffc3697%Z 0xfe468693%Z 0xfffc3717%Z 0xe9070713%Z 0x18d000ef%Z 0xdb0fd0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x531d4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x531d4 /\ 0x531d4 + 2212 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_RSMALL_CNT : ltac2:(GwEq.gw_fact_ty 'segs '(@QSsB.Mq7.gw_all) @ROM_RSMALL_CNT). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_RMED_CNT : ltac2:(GwEq.gw_fact_ty 'segs '(@QSsB.Mq7.gw_all) @ROM_RMED_CNT). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv rsegs m3 /\ stk rsegs m3 lo (bv_unsigned sp + -144) /\
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x533cc) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
(wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
a1 (wz cnt1) (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 pc) fc None m3 (seg_rom rsegs).
Lemma gw_eq_rcnt_state : @rcnt_state = ltac:(GwInst.gw_term (@QSsB.Mq7.rcnt_state rsegs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rcnt_state)). Proof. unfold rcnt_state, QSsB.Mq7.rcnt_state; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rcnt_state : gw_eqs.

Definition rHMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0x534a0 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0x534e4 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rHAG_stmt__3; @gw_eq_rHAG_stmt__2; @gw_eq_rHAG_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq7.rhag_ok) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq7.rhag_ok)]. Qed.
End LEVEL.
Lemma gw_eq_rcnt_state__2 : @rcnt_state = ltac:(GwInst.gw_term (@QSsB.Mq7.rcnt_state rsegs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rcnt_state)). Proof. unfold rcnt_state, QSsB.Mq7.rcnt_state; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rcnt_state__2 : gw_eqs.

End RC__1.
Lemma gw_eq_rcnt_state__3 : @rcnt_state = ltac:(GwInst.gw_term (@QSsB.Mq7.rcnt_state rsegs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rcnt_state)). Proof. unfold rcnt_state, QSsB.Mq7.rcnt_state; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rcnt_state__3 : gw_eqs.
