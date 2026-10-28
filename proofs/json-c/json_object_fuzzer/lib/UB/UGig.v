(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4vs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1ti. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUSO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUSO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x527b4%Z.
Definition w_6 := 0x00013617%Z.
Definition w_7 := 0x20463483%Z.
Definition w_26 := 0x00045817%Z.
Definition w_27 := 0x76480913%Z.
Definition w_31 := 0xfffc4817%Z.
Definition w_32 := 0xd1080813%Z.
Definition w_93 := 0x00045697%Z.
Definition w_94 := 0x65868693%Z.
Definition w_245 := 0xc9cfe0ef%Z.
Definition hi_6 := (Z_to_bv 20 19).
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_31 := (Z_to_bv 20 1048516).
Definition hi_93 := (Z_to_bv 20 69).
Definition lo_7 := (Z_to_bv 12 516).
Definition lo_27 := (Z_to_bv 12 1892).
Definition lo_32 := (Z_to_bv 12 3344).
Definition lo_94 := (Z_to_bv 12 1624).
Definition joff_245 := (Z_to_bv 21 2090140).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Lemma CODE : CodeAt.code_at rsegs 0x527b4 (Qy8Z.Mq9.ntf_code 0x00013617%Z 0x20463483%Z 0x00045817%Z 0x76480913%Z 0xfffc4817%Z 0xd1080813%Z 0x00045697%Z 0x65868693%Z 0xc9cfe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x527b4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x527b4 /\ 0x527b4 + 984 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition meta_word_sc2 := @meta_word_sc2.
Definition meta_word_pg := @meta_word_pg.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mqa.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8l1.Mqa.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs).
Lemma gw_eq_RAT : @RAT = ltac:(GwInst.gw_term (@Q8l1.Mqa.RAT rsegs) (@RAT)). Proof. unfold RAT, Q8l1.Mqa.RAT; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RAT : gw_eqs.

Definition rentry_cases (ms' : machine_state) : Prop :=

(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x52b34 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x52918 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x529dc (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x52970 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x528ec (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
Lemma gw_eq_rentry_cases : @rentry_cases = ltac:(GwInst.gw_term (@Q8l1.Mqa.rentry_cases rsegs 0x527b4 UKNz.RATP) (@rentry_cases)). Proof. unfold rentry_cases, Q8l1.Mqa.rentry_cases; rewrite ?gw_eq_RAT; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rentry_cases : gw_eqs.
End POST.
Lemma gw_eq_RAT__2 : @RAT = ltac:(GwInst.gw_term (@Q8l1.Mqa.RAT rsegs) (@RAT)). Proof. unfold RAT, Q8l1.Mqa.RAT; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_RAT__2 : gw_eqs.
Lemma gw_eq_rentry_cases__2 : @rentry_cases = ltac:(GwInst.gw_term (@Q8l1.Mqa.rentry_cases rsegs 0x527b4 UKNz.RATP) (@rentry_cases)). Proof. unfold rentry_cases, Q8l1.Mqa.rentry_cases; rewrite ?gw_eq_RAT__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rentry_cases__2 : gw_eqs.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96)
/\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.

#[using="Type"] Lemma meta_word_sc52 mr : mw_ok mr ->
Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.meta_word_sc52) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.meta_word_sc52)]. Qed.

#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.meta_word_mod32) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.meta_word_mod32)]. Qed.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv rsegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.

Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -96) /\ rw_cells rsegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.

#[using="i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rmaskw_zero) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rmaskw_zero)]. Qed.
#[using="Type"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rmaskw_range) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rmaskw_range)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8l1.Mqa.rmrep) (@UQXM.rmrep) Q6nq.gwt_nil)).
#[using="EH"] Lemma rntf_notall : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqa.rntf_notall) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RAT__3; @gw_eq_RAT__2; @gw_eq_RAT]; [@gw_eq_rentry_cases__3; @gw_eq_rentry_cases__2; @gw_eq_rentry_cases]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([338192]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@Q8l1.Mqa.rmid_ctx) (@rmid_ctx) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_post) (@rentry_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_notall) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_notall)]. Qed.

#[using="EH"] Lemma rntf_fge : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqa.rntf_fge) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RAT__3; @gw_eq_RAT__2; @gw_eq_RAT]; [@gw_eq_rentry_cases__3; @gw_eq_rentry_cases__2; @gw_eq_rentry_cases]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([338120]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RCTX (Q6nq.gwt_def (@Q8l1.Mqa.rmid_ctx) (@rmid_ctx) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_post) (@rentry_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_fge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_fge)]. Qed.

#[using="EH"] Lemma rntf_okchk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqa.rntf_okchk) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RAT__3; @gw_eq_RAT__2; @gw_eq_RAT]; [@gw_eq_rentry_cases__3; @gw_eq_rentry_cases__2; @gw_eq_rentry_cases]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_sxv__3; @gw_eq_sxv__2; @gw_eq_sxv]] '([337944]%Z : list Z) '(Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_def (@Q8l1.Mqa.rmid_ctx) (@rmid_ctx) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_post) (@rentry_post) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_okchk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_okchk)]. Qed.

#[using="EH MI0 LO LOLE"] Lemma rntf_entry : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mqa.rntf_entry) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_RAT__3; @gw_eq_RAT__2; @gw_eq_RAT]; [@gw_eq_rentry_cases__3; @gw_eq_rentry_cases__2; @gw_eq_rentry_cases]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]] '([337844]%Z : list Z) '(Q6nq.gwt_unf (@rnontrivial_free_entry) (Q6nq.gwt_def (@Q8l1.Mqa.rmid_ctx) (@rmid_ctx) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_post) (@rentry_post) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_entry) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mqa.rntf_entry)]. Qed.
End ENTRY.

End RC__1.
Lemma gw_eq_RAT__3 : @RAT = ltac:(GwInst.gw_term (@Q8l1.Mqa.RAT rsegs) (@RAT)). Proof. unfold RAT, Q8l1.Mqa.RAT; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RAT__3 : gw_eqs.
Lemma gw_eq_rentry_cases__3 : @rentry_cases = ltac:(GwInst.gw_term (@Q8l1.Mqa.rentry_cases rsegs 0x527b4 UKNz.RATP) (@rentry_cases)). Proof. unfold rentry_cases, Q8l1.Mqa.rentry_cases; rewrite ?gw_eq_RAT__3; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rentry_cases__3 : gw_eqs.
