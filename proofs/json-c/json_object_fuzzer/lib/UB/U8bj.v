(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVfK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UVV4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVV4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMDA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMDA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX99.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX99. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UISU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UISU.
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
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.Mq6.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.Mq6.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
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

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Lemma gw_eq_rag_regs : @rag_regs = ltac:(GwInst.gw_term (@Qe1A.Mq6.rag_regs UKNz.RATP) (@rag_regs)). Proof. unfold rag_regs, Qe1A.Mq6.rag_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rag_regs : gw_eqs.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Definition rHAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (ag_body f sc req k bail st2 mm) s' Q
(MS (rag_regs (Z_to_bv 64 0x533cc) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
F (Z_to_bv 64 0x533d8) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : rHAG_stmt.

#[using="RC__ TP"] Lemma rerrno_lit2 : errno_addr tp = 0x77b5c.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rerrno_lit2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rerrno_lit2)]. Qed.

#[using="RC__ m MR"] Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rconc_meta_stable) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rconc_meta_stable)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QzQg.rta_fp) (@UVV4.rta_fp) (Q6nq.gwt_def (@Qe1A.Mq6.rta_fp) (@UVV4.rta_fp) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Qe1A.Mq6.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qe1A.Mq6.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@Qe1A.Mq6.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Qe1A.Mq6.rimplT) (@Uv2Y.rimplT) Q6nq.gwt_nil)))))))))).
#[using="m ER MR"] Lemma rta_fp_malloc_fp : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq6.rta_fp_malloc_fp) [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]; [@gw_eq_rag_regs__3; @gw_eq_rag_regs__2; @gw_eq_rag_regs]] '(@nil Z) '(Q6nq.gwt_def (@Qe1A.Mq6.rHAG_stmt) (@rHAG_stmt) (Q6nq.gwt_def (@Qe1A.Mq6.rFRM) (@rFRM) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_malloc_fp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_malloc_fp)]. Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_image a : 0x10000 <= a < 0x99000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_image)]. Qed.

#[using="RC__ m sc MR CLO LO"] Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]]); first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]]); rename gw_h_ into LO) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_high) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_high)]. Qed.

#[using="UA"] Lemma runk_agree_keep : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq6.runk_agree_keep) [[@gw_eq_rag_regs__3; @gw_eq_rag_regs__2; @gw_eq_rag_regs]] '(@nil Z) '(Q6nq.gwt_def (@Qe1A.Mq6.rHAG_stmt) (@rHAG_stmt) (Q6nq.gwt_def (@Qe1A.Mq6.rFRM) (@rFRM) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.runk_agree_keep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.runk_agree_keep)]. Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_inband : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq6.rta_fp_not_inband) [[@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]; [@gw_eq_rag_regs__3; @gw_eq_rag_regs__2; @gw_eq_rag_regs]] '(@nil Z) '(Q6nq.gwt_def (@Qe1A.Mq6.rHAG_stmt) (@rHAG_stmt) (Q6nq.gwt_def (@Qe1A.Mq6.rFRM) (@rFRM) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_inband) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rta_fp_not_inband)]. Qed.

#[using="st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG"] Lemma rag_phase : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq6.rag_phase) [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]; [@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]; [@gw_eq_rag_regs]] '([(-144); 340916]%Z : list Z) '(Q6nq.gwt_def (@Qe1A.Mq6.rHAG_stmt) (@rHAG_stmt) (Q6nq.gwt_def (@Qe1A.Mq6.rFRM) (@rFRM) gwt_X))).
Proof. rewrite ?gw_eq_rag_regs; ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_rta_fp__3; @gw_eq_rta_fp__2; @gw_eq_rta_fp]]); first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]]); rename gw_h_ into LO) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rag_phase) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq6.rag_phase)]. Qed.
End LEVEL.
Lemma gw_eq_rag_regs__2 : @rag_regs = ltac:(GwInst.gw_term (@Qe1A.Mq6.rag_regs UKNz.RATP) (@rag_regs)). Proof. unfold rag_regs, Qe1A.Mq6.rag_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rag_regs__2 : gw_eqs.

End RC__1.
Lemma gw_eq_rag_regs__3 : @rag_regs = ltac:(GwInst.gw_term (@Qe1A.Mq6.rag_regs UKNz.RATP) (@rag_regs)). Proof. unfold rag_regs, Qe1A.Mq6.rag_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rag_regs__3 : gw_eqs.
