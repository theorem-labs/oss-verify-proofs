(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq Lib.GwApply Qfw3 Q9A7 QlEo Q5Rg UEQM Q2qa Qy5Y QDUx Q4J3 QytA Qnxq QJE4 QWTl QPjm QZAi QUZl Q7S0 Ql2m QGeV QLsg QkQT QlkP QyjG QM7w QNAo QXTs UQXM Uv2Y UpkF UIMz Un7h U8eV U8FW UxSL UDxd UWfR Un81 U7Jg UVfK UMDA UISU U8bj UJ8k UFNY Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0 QXTs.
Import UQXM Uv2Y UpkF UIMz Un7h U8eV U8FW UxSL UDxd UWfR Un81 U7Jg UVfK UMDA UISU U8bj UJ8k UFNY.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
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
Hypothesis IHf : ralloc_slot_stmt2 f.

Hypothesis NFAIL : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Hypothesis NSUCC : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.

#[using="LB AR ER SC MR CLO LO TP IHf NFAIL NSUCC"] Lemma rhnest_ok : rHNEST_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
clear A0 FIT RQ.
intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R SMc.
destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
pose proof (rerrno_lit5 tp TP) as EA.
pose proof (size_class_range sc SC) as SZR.
destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
pose proof (RAS_STACK_nest sc (ncls sc cnt1) SCJ ltac:(lia)) as RSN. pose proof (RAS_STACK_ge (ncls sc cnt1)) as ASGj.
unfold ag_nest. cbv zeta. fold (nreq sc cnt1). fold (ncls sc cnt1).
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
unfold rcnt_state.

riprefixT.
eapply evt_cut.
{ replace (wz (size_class sc * UNIT * cnt1)) with (wz (size_class sc * 16 * cnt1)) by (unfold UNIT; reflexivity).
eapply (rnest_call_walk (size_class sc) cnt1 SZR C1R ltac:(unfold UNIT in SMc; lia)). exact MI3. }
cbv beta. intros ms' (a2x & a3x & a4x & ->).
replace (size_to_class (size_class sc * 16 * cnt1 + 12)) with (ncls sc cnt1) by (unfold ncls; rewrite ENR; reflexivity).
replace (wz (size_class sc * 16 * cnt1 + 12)) with (wz (nreq sc cnt1)) by (rewrite ENR; reflexivity).
apply evt_done.
assert (AUX4 : rauxv_ok m3 (bv_unsigned sp - 144)).
{ eapply rauxv_ok_weaken; [exact AUX3| split; [unfold alloc_ceiling; lia| lia]]. }
set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp - 144) by (subst sp'; rewrite unsigned_lit by lia; lia).
eapply (ralloc_slot_stmtL f IHf R _ bail o s' Q (Z_to_bv 64 0x535b4) sp' gp tp) with (st0 := st0) (lo := lo) (sc := ncls sc cnt1) (req := nreq sc cnt1);
rewrite ?SP'.
-  split; [exists LB; split; [exact AR| exact IS2]|]. split; [exact ER2|]. split; [exact AC2|]. split; [lia|]. split; [lia|]. exact NFIT.
- exact MR3.
- exact TK3.
- exact UA3.
- exact BL2.
- exact AUX4.
- replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact ST3.
- exact CLO.
- lia.
- exact ERR3.
- exact MI3.
- exact TP.
- reflexivity.
- unfold wz. reflexivity.
-
intros st3 idx s'' ms'' PO LEAF.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & ut3 & ut4 & ut5 & ut6 & m'' & errv'' & -> & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & RES).
rewrite ?SP' in *.

assert (FR'' : rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
{ eapply (rframe_keep_ER st0 st m MR ER st3 m'' lo (bv_unsigned sp - 144) m3 m''); [exact MR''| exact PE''| | lia| unfold alloc_ceiling; lia].
replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact FR3. }
assert (PSM2 : ps_m s'' = ps_m s) by (etransitivity; [exact PSM''| exact PSM]).
assert (PSF2 : ps_fa s'' = ps_fa s) by (etransitivity; [exact PSF''| exact PSF]).
assert (PSO2 : ps_so s'' = ps_so s) by (etransitivity; [exact PSO''| exact PSO]).
assert (NCX : rnest_ctx f o s ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m st0 st lo sc st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o) by (repeat (split; [assumption|]); assumption).
cbv beta.
assert (IR : -1 <= idx < 32).
{ destruct RES as [[-> _]|(I0 & g3 & b3 & r3 & HA3 & SO3 & _)]; [lia|]. pose proof (so_idx _ _ _ _ _ _ SO3). pose proof (so_li _ _ _ _ _ _ SO3). lia. }
replace (ret_pc (Z_to_bv 64 0x535b4)) with (Z_to_bv 64 0x535b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
riprefixT. eapply evt_cut.
{ eapply (rnest_ret_walk (Z_to_bv 64 0x535b4) sp' gp tp) with (idx := idx); [exact IR| exact MI'']. }
cbv beta. intros ms' ->. apply evt_done.
replace sp' with (Z_to_bv 64 (bv_unsigned sp + -144)) by reflexivity.
destruct RES as [[-> E12]|(I0 & g3 & b3 & r3 & HA3 & SO3 & SPAN3 & RDV3)].
+ change (-1 <? 0) with true. change (-1 =? -1) with true. cbv iota.
apply (NFAIL st1 st2 mm cnt1 st3 m3 m'' s' s'' errv'' junk oo o); [exact NCX| exact E12].
+ replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (idx =? -1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite HA3. cbv iota beta.
apply (NSUCC st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o g3 b3 r3); [exact NCX| exact I0| exact HA3| exact SO3| exact SPAN3| exact RDV3].
Qed.
End LEVEL.

End RC__1.
End Mq0.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDkC.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXTs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXTs.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVfK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMd6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMd6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX99.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX99. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UISU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UISU. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8bj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8bj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFNY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFNY.
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
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition ralloc_slot_entry := UKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rfailm1_walk := ltac:(pose proof (@rfailm1_walk) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rfailW__3; @gw_eq_rfailW__2; @gw_eq_rfailW]]); exact gw_h_).
Definition ras_ret0 := @ras_ret0.
Definition rconc_meta_stable' := ltac:(pose proof (@rconc_meta_stable') as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rnest_regs__3; @gw_eq_rnest_regs__2; @gw_eq_rnest_regs]]); exact gw_h_).
Definition rmalloc_fp_widen := ltac:(pose proof (@rmalloc_fp_widen) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rnest_regs__3; @gw_eq_rnest_regs__2; @gw_eq_rnest_regs]]); exact gw_h_).
Definition rerrno_lit5 := ltac:(pose proof (@rerrno_lit5) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rnest_regs__3; @gw_eq_rnest_regs__2; @gw_eq_rnest_regs]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QDkC.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
(0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
\/ iv = (spv - 144, spv).

#[using="Type"] Lemma rlowW_meta spv st m' q : rmrep st m' -> meta_slot st q -> rlowW spv (conc st q, conc st q + 40).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_meta)]. Qed.

Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
(exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).
Lemma gw_eq_rmetaW : @rmetaW = ltac:(GwInst.gw_term (@QDkC.rmetaW UKNz.RATP) (@rmetaW)). Proof. unfold rmetaW, QDkC.rmetaW; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmetaW : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QDkC.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q5m9.Mq7.rfailW) (@UMd6.rfailW) (Q6nq.gwt_def (@QDkC.rfailW) (@UMd6.rfailW) Q6nq.gwt_nil)))).
#[using="Type"] Lemma rfailW_shape : ltac2:(Q6nq.ty2 'GwI.segs '(@QDkC.rfailW_shape) [[@gw_eq_rfailW__3; @gw_eq_rfailW__2; @gw_eq_rfailW]; [@gw_eq_rmetaW]] '(@nil Z) '(Q6nq.gwt_def (@QDkC.rlowW) (@rlowW) gwt_X)).
Proof. rewrite ?gw_eq_rmetaW; ltac2:(GwEq.gw_rw [[@gw_eq_rfailW__3; @gw_eq_rfailW__2; @gw_eq_rfailW]]); first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rfailW_shape) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rfailW_shape)]. Qed.

#[using="Type"] Lemma rfailW_low : ltac2:(Q6nq.ty2 'GwI.segs '(@QDkC.rfailW_low) [[@gw_eq_rfailW__3; @gw_eq_rfailW__2; @gw_eq_rfailW]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rmetaW__3; @gw_eq_rmetaW__2; @gw_eq_rmetaW]] '(@nil Z) '(Q6nq.gwt_def (@QDkC.rlowW) (@rlowW) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfailW__3; @gw_eq_rfailW__2; @gw_eq_rfailW]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rfailW_low) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rfailW_low)]. Qed.

#[using="Type"] Lemma rlowW_disjoint : ltac2:(Q6nq.ty2 'GwI.segs '(@QDkC.rlowW_disjoint) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmetaW__3; @gw_eq_rmetaW__2; @gw_eq_rmetaW]] '([(-144)]%Z : list Z) '(Q6nq.gwt_def (@QDkC.rlowW) (@rlowW) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_disjoint) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_disjoint)]. Qed.

#[using="Type"] Lemma rlowW_disjoint_img : ltac2:(Q6nq.ty2 'GwI.segs '(@QDkC.rlowW_disjoint_img) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmetaW__3; @gw_eq_rmetaW__2; @gw_eq_rmetaW]] '([(-144); 928; 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_zc RCTX (Q6nq.gwt_def (@QDkC.rlowW) (@rlowW) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_disjoint_img) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rlowW_disjoint_img)]. Qed.

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

#[using="LB req errv AR IS ER SC RQ MR AUX CLO LO ERR TP HK"] Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rNFAIL_stmt__3; @gw_eq_rNFAIL_stmt__2; @gw_eq_rNFAIL_stmt]]); first [ (pose proof LO as gw_h_; clear LO; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAS_STACK__3; @gw_eq_RAS_STACK__2; @gw_eq_RAS_STACK]]); rename gw_h_ into LO) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QDkC.rnfail_ok) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDkC.rnfail_ok)]. Qed.
End LEVEL.

End RC__1.
Lemma gw_eq_rmetaW__2 : @rmetaW = ltac:(GwInst.gw_term (@QDkC.rmetaW UKNz.RATP) (@rmetaW)). Proof. unfold rmetaW, QDkC.rmetaW; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmetaW__2 : gw_eqs.
