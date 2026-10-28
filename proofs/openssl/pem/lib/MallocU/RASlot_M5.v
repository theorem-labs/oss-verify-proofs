(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M5D.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W12 RASlot_M0 RASlot_M2 RASlot_M3 RASlot_M5D.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Hypothesis IHf : ralloc_slot_stmt2 f.

Hypothesis NFAIL : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Hypothesis NSUCC : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.

Lemma rhnest_ok : rHNEST_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  clear A0 FIT RQ.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R SMc.
  destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in CLO'; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  pose proof (RAS_STACK_nest sc (ncls sc cnt1) SCJ ltac:(lia)) as RSN. pose proof (RAS_STACK_ge (ncls sc cnt1)) as ASGj.
  unfold ag_nest. cbv zeta. fold (nreq sc cnt1). fold (ncls sc cnt1).
  pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _).
  unfold rcnt_state.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT * cnt1)) with (wz (size_class sc * 16 * cnt1)) by (unfold UNIT; reflexivity).
    eapply (rnest_call_walk (size_class sc) cnt1 SZR C1R ltac:(unfold UNIT in SMc; lia)). exact MI3. }
  cbv beta. intros ms' (a2x & a3x & a4x & ->).
  replace (size_to_class (size_class sc * 16 * cnt1 + 12)) with (ncls sc cnt1) by (unfold ncls; rewrite ENR; reflexivity).
  replace (wz (size_class sc * 16 * cnt1 + 12)) with (wz (nreq sc cnt1)) by (rewrite ENR; reflexivity).
  apply evt_done.
  assert (AUX4 : rauxv_ok m3 (bv_unsigned sp - 144)).
  { eapply rauxv_ok_weaken; [exact AUX3| split; [unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia| lia]]. }
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 144) by (subst sp'; rewrite unsigned_lit by lia; lia).
  eapply (ralloc_slot_stmtL f IHf R _ bail o s' Q (Z_to_bv 64 0x2b1c3c) sp' gp tp) with (st0 := st0) (lo := lo) (sc := ncls sc cnt1) (req := nreq sc cnt1);
    rewrite ?SP'.
  - (* [comment removed for export] *) split; [exists LB; split; [exact AR| exact IS2]|]. split; [exact ER2|]. split; [exact AC2|]. split; [lia|]. split; [lia|]. exact NFIT.
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
  - (* [comment removed for export] *)
    intros st3 idx s'' ms'' PO LEAF.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & ut3 & ut4 & ut5 & ut6 & m'' & errv'' & -> & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & RES).
    rewrite ?SP' in *.
    (* [comment removed for export] *)
    assert (FR'' : rw_cells usegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply (rframe_keep_ER st0 st m MR ER st3 m'' lo (bv_unsigned sp - 144) m3 m''); [exact MR''| exact PE''| | lia| unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia].
      replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact FR3. }
    assert (PSM2 : ps_m s'' = ps_m s) by (etransitivity; [exact PSM''| exact PSM]).
    assert (PSF2 : ps_fa s'' = ps_fa s) by (etransitivity; [exact PSF''| exact PSF]).
    assert (PSO2 : ps_so s'' = ps_so s) by (etransitivity; [exact PSO''| exact PSO]).
    assert (NCX : rnest_ctx f o s ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m st0 st lo sc st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o) by (repeat (split; [assumption|]); assumption).
    cbv beta.
    assert (IR : -1 <= idx < 32).
    { destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & _)]; [lia|]. pose proof (so_idx _ _ _ _ _ _ SO3). pose proof (so_li _ _ _ _ _ _ SO3). lia. }
    replace (ret_pc (Z_to_bv 64 0x2b1c3c)) with (Z_to_bv 64 0x2b1c3c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT. eapply evt_cut.
    { eapply (rnest_ret_walk (Z_to_bv 64 0x2b1c3c) sp' gp tp) with (idx := idx); [exact IR| exact MI'']. }
    cbv beta. intros ms' ->. apply evt_done.
    replace sp' with (Z_to_bv 64 (bv_unsigned sp + -144)) by reflexivity.
    destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & SPAN3 & RDV3)].
    + change (-1 <? 0) with true. change (-1 =? -1) with true. cbv iota.
      apply (NFAIL st1 st2 mm cnt1 st3 m3 m'' s' s'' errv'' junk oo o). exact NCX.
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (idx =? -1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite HA3. cbv iota beta.
      apply (NSUCC st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o g3 b3 r3); [exact NCX| exact I0| exact HA3| exact SO3| exact SPAN3| exact RDV3].
Qed.
End LEVEL.
End WithCeiling0.
