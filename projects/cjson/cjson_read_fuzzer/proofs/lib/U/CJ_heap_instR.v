(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_entry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W9.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W13.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W14.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_M5D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RASlot_I.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RASlot_M5F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RASlot_M0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RASlot_M5S.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W13 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M5P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W13 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M5D.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rgrp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG nelH_; (nelim nelH_ 5%nat; intros b gh Hb Hf Ho). exists b, gh. rewrite EG. auto. Qed.

Lemma rmrep_st_model stT sc cnt ai ml mt p (SC : 0 <= sc < 48) (CNT : 1 <= cnt <= 32)
      (REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml) (P0 : 0 <= snd p) m :
  rmrep (stFin stT sc cnt ai ml mt p) m -> rmrep (st_model stT sc cnt ai mt p) m.
Proof using .
  intros MR. eapply (rmrep_extW _ _ _ MR); try reflexivity.
  intros q. apply (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
Qed.

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
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnsucc_ok : rNSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof using AR AUX CLO ER ERR FIT HK IS LO MR RQ SC TP.
  intros st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC I0 HA3 SO3 SPAN3 RDV3.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' (* [comment removed for export] *)
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  (nelim (nest_class sc SC cnt1 C1R SMc) 6%nat; intros ENR JR FITN SCJ NRR NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), idx; split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 idx AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  (nelimp (rmeta_slot_bounds st3 m'' mm MR'' MS3) 4%nat; intros Gpos GC GI _).
  (* [comment removed for export] *)
  pose proof (so_mem _ _ _ _ _ _ SO3) as Hmem3. pose proof (so_reg _ _ _ _ _ _ SO3) as Hr3. pose proof (so_kind _ _ _ _ _ _ SO3) as Hk3.
  pose proof (so_mslot _ _ _ _ _ _ SO3) as MSLg. pose proof (so_fit _ _ _ _ _ _ SO3) as FIT3. pose proof (so_idx _ _ _ _ _ _ SO3) as IDX3.
  pose proof (so_b0 _ _ _ _ _ _ SO3) as B30. pose proof (so_span _ _ _ _ _ _ SO3) as SP3. pose proof (so_li _ _ _ _ _ _ SO3) as LI3.
  pose proof (mf_active _ _ MF3) as FA3. change (fact_active (strip st3)) with (fact_active st3) in FA3.
  (nelim (FA3 (ncls sc cnt1) g3 HA3) 3%nat; intros _ GSC3 _).
  pose proof (lf_host_stride _ (isf_lf _ _ F3) g3 b3 Hmem3 ltac:(change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3); rewrite GSC3; lia)) as STR3.
  change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in STR3. rewrite GSC3 in STR3.
  (nelimp (lf_mw _ (isf_lf _ _ F3) g3) 3%nat; intros MW3 _ _). change (get_meta_rec (strip st3) g3) with (get_meta_rec st3 g3) in MW3.
  set (strideg := get_stride (get_meta_rec st3 g3)) in *.
  set (szc := size_class sc) in *.
  assert (FITg : 16 * szc * cnt1 + 16 <= strideg) by lia.
  assert (SZC1 : 16 * szc <= 16 * szc * cnt1) by nia.
  assert (SO_N : slot_ok st3 g3 b3 r3 idx (UNIT * size_class (ncls sc cnt1) - IB)) by (eapply slot_ok_N; [exact SO3| unfold IB; lia| unfold UNIT, IB; lia]).
  set (X := snd b3 + (16 + strideg * idx)) in *.
  set (p := (fst b3, X) : aptr).
  (nelimp (rregion_facts st3 m'' (fst b3) r3 MR'' Hr3) 5%nat; intros R4 RAL RC RI1 RI2). unfold alloc_ceiling in RC.
  assert (CB3 : conc st3 b3 = r_base r3 + snd b3) by (apply conc_region'; exact Hr3).
  assert (CP : conc st3 p = r_base r3 + X) by (apply conc_region'; exact Hr3).
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (XEND : X + strideg <= round_up_pg (r_len r3)).
  { unfold X. eapply Z.le_trans; [| exact SP3]. fold strideg.
    assert (strideg * idx + strideg <= strideg * (m_last_idx (get_meta_rec st3 g3) + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  assert (JR' : 0 <= ncls sc cnt1 < 48) by lia.
  assert (FRESH3 : forall o' v t, X <= o' < X + strideg - 4 -> (r_cells (get_shadow st3 (fst b3))) !! o' = Some (v, t) -> (t < s_tick st3)%N).
  { intros o' v t Ho Hc. eapply (ai_fresh _ _ _ _ _ AI'' I0 (fst b3) X (strideg - 4)); [| | exact Hc]; [| lia].
    exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  (* [comment removed for export] *)
  rewrite (nest_model_eq st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SO_N STR3).
  replace (slot_of st3 g3 idx) with p by (unfold slot_of, slot_start'; rewrite Hmem3; reflexivity).
  (nelim (nt_tail_hyps st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3) 10%nat; intros TMS TREC TREG TP0 TP16 TPEND TGN TNOG TOLD TTK)
.
  fold strideg X p in TMS, TREC, TREG, TP0, TP16, TPEND, TGN, TNOG, TOLD, TTK.
  set (stT := nt_stT st3 g3 b3 idx sc cnt1 mm) in *.
  assert (ACT3 : active st3 sc = None).
  { rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). exact ACT0. }
  assert (ACTT : active stT sc = None) by (unfold stT; rewrite ntT_active; exact ACT3).
  rewrite (ag_tail_kq_eq sc k bail stT mm p cnt1 (cnt1 - 1)); [| rewrite TREC; reflexivity| rewrite TREC; reflexivity| exact ACTT].
  (nelim (ntT_proj st3 g3 b3 idx sc cnt1 mm) 8%nat; intros TPR TPG TPA TPT TPN TPRS TPC TPS). fold stT in TPR, TPG, TPA, TPT, TPN, TPRS, TPC, TPS.
  assert (URT : 0 <= usage stT sc < 2^60).
  { unfold stT. rewrite ntT_usage. pose proof (mf_usage _ _ MF3 sc) as U. exact U. }
  assert (TCONC : forall q, conc stT q = conc st3 q) by (intros q; unfold stT; apply ntT_conc).
  (* [comment removed for export] *)
  riprefixT. unfold rnest_regs. rewrite <- GE.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rnenf_walk st3 m'' o g3 b3 r3 idx (ncls sc cnt1) MR'' UA'' JR' HA3 MSLg MW3 GSC3 STR3 SO_N TK''); [exact CTR''| exact MI'']. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 21%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m5 -> MU5 WM5 MI5 MR5 TK5).
  fold strideg.
  (* [comment removed for export] *)
  assert (MWmm : mw_ok (get_meta_rec st3 mm)) by (rewrite G3; unfold mw_ok, meta0; cbn; lia).
  eapply evt_cut.
  { change (wz cnt1) with (Z_to_bv 64 cnt1).
    eapply (renfD_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' JR' SO_N TK''); [exact MS3| exact MWmm| exact C1R| exact MR5| exact TK5| exact MI5]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros m6 -> MU6 WM6 MI6 MR6 TK6).
  fold strideg in MU5, MU6, MR6, TK6 |- *.
  change (wr8 (fst b3, snd b3 + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192) (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g3 b3 idx)))
    with (nt_stW st3 g3 b3 idx mm) in MR6, TK6.
  (* [comment removed for export] *)
  set (P := conc st3 b3 + 16 + strideg * idx) in *.
  assert (EP : P = r_base r3 + X) by (unfold P, X; rewrite CB3; lia).
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT)) with (Z_to_bv 64 (16 * szc)) by (unfold wz, szc, UNIT; f_equal; lia).
    replace (Z_to_bv 64 (P + 12)) with (Z_to_bv 64 (P + 12 + 16 * szc * 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (cnt1 + 1)) with (Z_to_bv 64 (cnt1 + 1 - 0)) by (f_equal; lia).
    eapply (rzero_loop_walk st3 m'' g3 b3 r3 idx (ncls sc cnt1) MR'' STR3 SO_N (Z.to_nat (cnt1 + 1)) 0 szc cnt1 (nt_stW st3 g3 b3 idx mm) m6 m6);
      [lia| lia| unfold szc; lia| lia| unfold strideg in FITg; lia
      | apply (proj1 (ntW_proj st3 g3 b3 idx mm))| apply (proj1 (proj2 (ntW_proj st3 g3 b3 idx mm)))
      | exact MR6| exact TK6| exact MI6| apply munch_refl| apply wmono_refl]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 10%nat; intros m7 -> MU7 WM7 MI7 MR7 TK7 RG7 GR7 PW7).
  change (zero_hdrs (pp st3 g3 b3 idx) (16 * szc) 0 (Z.to_nat (cnt1 + 1)) (nt_stW st3 g3 b3 idx mm)) with stT in MR7, TK7, RG7, GR7.
  fold P in MU7, PW7.
  (* [comment removed for export] *)
  eapply evt_cut.
  { replace (Z_to_bv 64 P) with (Z_to_bv 64 (conc stT p)) by (rewrite TCONC, CP, EP; reflexivity).
    replace (Z_to_bv 64 (conc st3 mm)) with (Z_to_bv 64 (conc stT mm)) by (rewrite TCONC; reflexivity).
    eapply (rtail_walk stT sc cnt1 (cnt1 - 1) 0 mm p r3 SC C1R ltac:(lia) ltac:(lia) TMS TREC TREG Hk3 TP0 TP16 TPEND TGN TNOG TOLD URT ACTT TK7);
      [exact MR7| exact MI7]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros s0x a1x a2y a3x a4z m8 -> MU8 WM8 MI8 MR8 TK8).
  (* [comment removed for export] *)
  set (W58 := ([(P - 3, P); (conc st3 mm, conc st3 mm + 40); (P - 3, P - 2); (P + 12, P + 12 + 16 * szc * cnt1 + 1)]%Z ++ rtailW stT sc mm p)).
  assert (LOWW : Forall (fun iv : Z * Z => snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x56000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928))) W58).
  { apply Forall_forall. intros [lo' hi'] HI. cbn [fst snd]. unfold W58, rtailW in HI. rewrite !TCONC, CP in HI. cbn [app In] in HI.
    pose proof (round_up_pg_ge (r_len r3)).
    destruct HI as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; inversion E; subst; unfold RCTX; lia. }
  assert (MU58 : munch W58 m'' m8).
  { intros x Hx. unfold W58 in Hx. rewrite outside_app' in Hx. destruct Hx as [H4x H8].
    rewrite (MU8 x H8). cbn [outside] in H4x. (nelim H4x 5%nat; intros H5 H6a H6b H7 _).
    rewrite (MU7 x) by (cbn; auto). rewrite (MU6 x) by (cbn; auto). rewrite (MU5 x) by (cbn; auto). reflexivity. }
  assert (WM58 : wmono usegs m'' m8).
  { eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6|]. eapply wmono_trans; [exact WM7| exact WM8]. }
  assert (DJhigh : forall A n, alloc_ceiling <= A -> disjoint_from W58 A n).
  { intros A n HA. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [H _]. lia. }
  assert (DJimg : forall A n, 0x10000 <= A -> A + n <= 0x56000 -> (A + n <= RCTX \/ RCTX + 928 <= A) -> disjoint_from W58 A n).
  { intros A n H1 H2 H3. eapply Forall_disjoint_from; [exact LOWW|]. cbn. intros lo' hi' [_ H]. unfold RCTX in *. lia. }
  assert (FR8 : rw_cells usegs m8 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact FR''. }
  assert (ST8 : stk usegs m8 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU58| exact WM58| apply DJhigh; lia]. replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR8 : rw_cells usegs m8 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU58| exact WM58|]. rewrite EA. apply DJimg; [lia| cbn; lia| unfold RCTX; cbn; lia]. }
  set (stF := st_model stT sc cnt1 (cnt1 - 1) mm p).
  assert (MRF : rmrep stF m8) by (exact (rmrep_st_model stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 m8 MR8)).
  eapply evt_cut. { unfold rFRM in FR8. eapply (ras_ret0 sp gp tp); [exact MRF| exact MI8| exact FR8| exact ST8| exact CLO| lia]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1w a2w -> ST9). apply evt_done.
  apply HK.
  (* [comment removed for export] *)
  fold strideg in MU7, PW7. fold P in MU7, PW7.
  (nelim (smg_proj stT sc cnt1 (cnt1 - 1) mm p) 10%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10).
  fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
  rewrite TPR in PF1. rewrite TPA in PF4. rewrite TPT in PF5. rewrite TPN in PF6. rewrite TPRS in PF7.
  assert (CTXT : ctx stT = ctx st3) by (unfold stT; apply ntT_ctx).
  rewrite CTXT in PF8, PF9, PF10.
  assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK8]; reflexivity).
  assert (MSF : meta_slot stF mm) by (apply (proj1 (smg_meta_slot stT sc cnt1 (cnt1 - 1) mm p mm)); exact TMS).
  assert (CF : forall q, conc stF q = conc st3 q) by (intros q; unfold stF; rewrite (smg_conc stT sc cnt1 (cnt1 - 1) mm p q); apply TCONC).
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR'' as (WF3 & _). (nelimp WF3 4%nat; intros RS3 WR3 DJ3 _).
  assert (STRF : get_stride (get_meta_rec stF mm) = 16 * szc) by (exact (ntF_stride st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N G3 MS3 FRESH3)).
  (* [comment removed for export] *)
  assert (HOLD2 : forall q rq, (s_regions st2) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. (nelim (mrel_regions _ _ MREL'' q rq Hq) 5%nat; intros r' Hr' K' B' L'). exists r'. rewrite PF1. auto. }
  assert (HOLD3 : forall q rq, (s_regions st3) !! q = Some rq -> exists r', (s_regions stF) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
  { intros q rq Hq. exists rq. rewrite PF1. repeat split; auto. lia. }
  assert (INSPAN : forall a, r_base r3 + X - 4 <= a < r_base r3 + X + strideg - 4 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3). apply SPAN3. unfold X in Ha. lia. }
  assert (INMETA : forall a, conc st3 mm <= a < conc st3 mm + 40 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
  { intros a Ha. left. do 3 right. destruct (rmeta_chunk_facts stF m8 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
    exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite CF in L0, H0'. lia. }
  assert (INCTX : forall a, RCTX <= a < RCTX + 928 -> rmalloc_fp st0 stF lo (bv_unsigned sp) a) by (intros a Ha; left; right; right; left; exact Ha).
  (* [comment removed for export] *)
  assert (HDR0N : cell_read (get_shadow st3 (fst b3)) (X + strideg - 4) = Known 0).
  { pose proof (mf_hdr0 _ _ MF3 g3 b3 (idx + 1) Hmem3 ltac:(lia)) as H.
    unfold sstart_of in H. rewrite Hmem3 in H. cbn [default from_option id snd] in H. fold strideg in H. unfold IB, UNIT in H.
    replace (X + strideg - 4) with (snd b3 + 16 + strideg * (idx + 1) - 4) by (unfold X; lia). exact H. }
  assert (M6A : m6 (wa (r_base r3 + (X + strideg - 4))) = Some (b8 0)).
  { apply (rregion_byte_raw (nt_stW st3 g3 b3 idx mm) m6 (fst b3) r3 (X + strideg - 4) 0 MR6).
    - rewrite (proj1 (ntW_proj st3 g3 b3 idx mm)). exact Hr3.
    - exact Hk3.
    - lia.
    - rewrite (ntW_cell_read_other st3 g3 b3 idx (ncls sc cnt1) sc mm SC JR' (X + strideg - 4)) by (unfold X; lia). exact HDR0N. }
  assert (PE67 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m6 m7).
  { intros a Ha NC. split; [| intros W; apply WM7; exact W].
    destruct (arith_prog_dec a (P + 12) (16 * szc) cnt1 ltac:(lia)) as [(j & Hj & Ea)|NA].
    - destruct (Z_lt_le_dec a (P + strideg - 4)) as [LT|GE'].
      + exfalso. apply NC. apply INSPAN. lia.
      + assert (J16 : 16 * szc * j <= 16 * szc * cnt1) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (Ea' : a = r_base r3 + (X + strideg - 4)) by lia.
        rewrite Ea', M6A.
        apply (rregion_byte_raw stT m7 (fst b3) r3 (X + strideg - 4) 0 MR7); [rewrite TPR; exact Hr3| exact Hk3| lia|].
        assert (EJ : 16 * szc * j = 16 * szc * cnt1) by lia.
        replace (X + strideg - 4) with (X + 12 + cnt1 * (16 * szc)) by lia.
        unfold stT. apply (ntT_cell_read_zero st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R TK''). lia.
    - apply PW7. rewrite wa_unsigned by lia. intros j Hj. specialize (NA j Hj). lia. }
  assert (PE08 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m8).
  { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04|]. intros a Ha. exact (rmalloc_fp_mono st0 st2 stF lo (bv_unsigned sp) a HOLD2 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE''|]. intros a Ha. exact (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia) HOLD3 Ha). }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU5| exact WM5|]. intros a Ha NC. cbn. split; [|exact I]. intros Xa; apply NC. apply INSPAN. lia. }
    eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros Xa; apply NC; [apply INMETA; lia| apply INSPAN; lia]. }
    eapply rpres_except_trans. { exact PE67. }
    eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. unfold rtailW. rewrite !TCONC, CP. cbn.
    split; [|split; [|split; [|split; [|exact I]]]]; intros Xa; apply NC; [apply INCTX; unfold RCTX in *; lia| apply INMETA; lia| apply INSPAN; lia| apply INCTX; unfold RCTX in *; lia]. }
  (* [comment removed for export] *)
  assert (UAF : unk_agree stF o m8).
  { intros rid rr off h Hrr Kr Ho Hc NG. rewrite PF1 in Hrr.
    (nelim (WR3 _ _ Hrr) 5%nat; intros R0 _ _ RCr _). unfold alloc_ceiling in RCr.
    (nelim (rregion_facts st3 m'' rid rr MR'' Hrr) 5%nat; intros _ _ _ RI1r RI2r). specialize (RI1r ltac:(lia)). specialize (RI2r ltac:(lia)).
    (nelim (rmeta_chunk_facts st3 m'' mm MR'' MS3) 7%nat; intros _ _ _ _ _ GRG _). pose proof (GRG rid rr Hrr Kr) as GRr.
    assert (NG3 : ~ grp_hdr_cov st3 rid off).
    { intros CV. apply NG. unfold stF. apply (smg_grp_hdr_cov_old stT sc cnt1 (cnt1 - 1) mm p TP0 rid off TGN).
      eapply rgrp_hdr_cov_same; [exact TPG| exact CV]. }
    destruct (N.eq_dec rid (fst b3)) as [->|NE].
    - rewrite Hr3 in Hrr. inversion Hrr; subst rr.
      destruct (ntF_unknown st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N TK'' off h ltac:(lia) Hc) as [CV|(Hc3 & NH & NZ)].
      { exfalso. apply NG. exact CV. }
      rewrite <- (UA'' (fst b3) r3 off h Hr3 Kr Ho Hc3 NG3).
      assert (NHC : ~ (X <= off < X + 12)).
      { intros Hx. apply NG. unfold stF. change (fst b3) with (fst p). apply (smg_grp_hdr_cov stT sc cnt1 (cnt1 - 1) mm p SC). unfold p. cbn [snd]. lia. }
      transitivity (m7 (wa (r_base r3 + off))). { apply MU8. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). unfold rtailW. rewrite !TCONC, CP. cbn. unfold RCTX. clear - Ho RI1r RI2r GRr NHC SC; lia. }
      transitivity (m6 (wa (r_base r3 + off))). { apply PW7. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). intros j Hj E. apply NZ. exists j. split; [exact Hj|]. clear - E EP Hj; lia. }
      transitivity (m5 (wa (r_base r3 + off))). { apply MU6. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). cbn. clear - GRr Ho EP NH B30 SK; lia. }
      apply MU5. rewrite wa_unsigned by (clear - R0 Ho RCr; lia). cbn. clear - EP NH B30 SK; lia.
    - assert (Hc3 : cell_read (get_shadow st3 rid) off = Unknown h).
      { rewrite <- (ntF_shadow_other st3 g3 b3 idx sc cnt1 mm rid NE). exact Hc. }
      rewrite <- (UA'' rid rr off h Hrr Kr Ho Hc3 NG3).
      pose proof (lr_lo_group rr Kr) as LR1. pose proof (lr_lo_group r3 Hk3) as LR2.
      assert (NE' : fst b3 <> rid) by (intros E; apply NE; symmetry; exact E).
      pose proof (round_up_pg_ge (r_len r3)) as RU3.
      destruct (DJ3 _ _ _ _ Hr3 Hrr NE') as [D|D].
      all: transitivity (m7 (wa (r_base rr + off))); [apply MU8; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); unfold rtailW; rewrite !TCONC, CP; cbn [outside]; unfold RCTX; clear - Ho RI1r RI2r SC GRr D LR1 LR2 B30 SK XEND FITg SZC1 SZR; lia|].
      all: transitivity (m6 (wa (r_base rr + off))); [apply MU7; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia|].
      all: transitivity (m5 (wa (r_base rr + off))); [apply MU6; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho GRr D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia|].
      all: apply MU5; rewrite wa_unsigned by (clear - R0 Ho RCr; lia); cbn [outside]; clear - Ho D LR1 LR2 B30 SK XEND EP FITg SZC1 SZR; lia. }
  assert (RSP3 : ret_span st3 (ncls sc cnt1) idx (fst b3) X (strideg - 4)).
  { exists g3, b3. split; [exact HA3|]. split; [exact Hmem3|]. split; [reflexivity|]. split; [unfold X; lia| reflexivity]. }
  unfold ras_post2.
  nexists 14%nat. exists m8, errv''. split; [reflexivity|].
  split; [exact MI8|]. split; [exact ST9|]. split; [exact ERR8|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m8); [exact MRF| exact AUX| exact PE08| exact CLO| lia]|].
  split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE08|].
  split. { split.
    - intros q rq Hq. rewrite <- REG1 in Hq. (nelim (amr_regions _ _ _ REL q rq Hq) 6%nat; intros r' H' K' B' L' _).
      (nelim (HOLD2 q r' H') 5%nat; intros r'' H'' K'' B'' L''). exists r''. split; [exact H''|]. split; [rewrite K''; exact K'|]. split; [rewrite B''; exact B'|]. lia.
    - rewrite PF6. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF7, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF8. destruct (c_brk (ctx st3)) as [| |brid boff]; auto. rewrite CF. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. unfold stF. rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p c'). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold stT. rewrite ntT_active. rewrite (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF5, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros _ rid' S len RSP o' v t Ho Hc.
      (nelim (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) 3%nat; intros -> -> ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho.
      unfold p in Hc, Ho. cbn [fst snd] in Hc, Ho. rewrite PF5.
      unfold stF, stT, p in Hc. rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') in Hc by (fold szc; lia).
      eapply FRESH3; [| exact Hc]. lia.
    - intros E0 _ rid' S len RSP o' Ho.
      (nelim (smg_ret_span stT sc cnt1 (cnt1 - 1) 0 mm p SC C1R TREC TP0 rid' S len RSP) 3%nat; intros -> -> ->).
      rewrite (smg_stride sc cnt1 (cnt1 - 1) 0 mm p SC C1R) in Ho. rewrite andb_false_r in Ho. unfold p in Ho. cbn [snd] in Ho.
      (nelim (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 o' ltac:(lia)) 3%nat; intros V1 V2 V3).
      unfold p. cbn [fst]. unfold stF, stT, p. split; [| split].
      + rewrite (ntF_span_cells st3 g3 b3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R o') by (fold szc; lia). exact V1.
      + rewrite (ntF_span_hav st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' SO_N o') by lia. exact V2.
      + rewrite (ntF_havp st3 g3 b3 idx sc cnt1 mm). exact V3. }
  split. { rewrite PF9. exact CTR''. }
  right. split; [lia|]. exists mm, p, r3.
  split; [unfold stF; rewrite (smg_active stT sc cnt1 (cnt1 - 1) mm p sc), Z.eqb_refl; reflexivity|].
  split; [unfold stF, stT, p, X; apply (nt_slot_ok st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N STR3 ltac:(fold szc; lia) G3 MS3 TK'' FRESH3 req); lia|].
  rewrite STRF. unfold p. cbn [fst snd]. split.
  + intros a Ha. apply INSPAN. lia.
  + intros E0. replace (X + (16 + 16 * szc * 0) + -3) with (X + 13) by lia.
    (nelim (ai_virgin _ _ _ _ _ AI'' E0 I0 (fst b3) X (strideg - 4) RSP3 (X + 13) ltac:(lia)) 3%nat; intros V1 V2 V3).
    unfold stF, stT. apply (ntF_rdv13 st3 g3 b3 r3 idx (ncls sc cnt1) sc cnt1 mm SC JR' C1R SO_N o V1 V2 V3).
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M5S.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W15.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_malloc_join.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_malloc_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_malloc_bigw.
Module RF_malloc_big.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.F_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_bigw.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Lemma rmrep_ext : forall st st' m,
  rmrep st m ->
  s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_reserved st' = s_reserved st ->
  rmrep st' m.
Proof using .
  intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact EA| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof using G0.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof using n rid.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof using c st3. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof using c n rid.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma rbf_regions : s_regions stF = s_regions st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_areas : s_areas stF = s_areas st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof using g n rid. reflexivity. Qed.
Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using GN n.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof using c n. reflexivity. Qed.
Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof using c g n rid st3. reflexivity. Qed.
Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma rbf_ctx : ctx stF = ctx stM.
Proof using HC g n rid. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof using HC stM. rewrite rbf_ctx. reflexivity. Qed.

Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof using G0 GN HC n.
  intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
  - exact rbf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
  - rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof using NR.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof using n.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
  a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x56000 <= a).
Proof using .
  intros MR RF. pose proof MR as (WF & _). (nelimp WF 3%nat; intros _ WR _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
  - lia. - lia. - lia. - lia.
  - (nelim (rarea_conc st ak ar WF Hak) 10%nat; intros ra Hra Ca Sa0 Sa1 _ NK RB0 RBAL RBC).
    (nelim (WR _ _ Hra) 5%nat; intros _ _ _ _ RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - (nelim (rgroup_conc st b gh WF Hb) 9%nat; intros rb Hrb Cb Kb Sb0 Sb1 _ RB0 RBC).
    (nelim (WR _ _ Hrb) 5%nat; intros _ _ _ _ RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - (nelim (WR _ _ Hq) 5%nat; intros _ _ _ RC RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
  - lia. - lia.
Qed.

(* [comment removed for export] *)
Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
  rmrep st m -> munch [(spv - 80, spv); (0x3492c, 0x3492c + 4)] m m' -> wmono usegs m m' -> alloc_ceiling <= spv - 80 ->
  rmrep st m'.
Proof.
  intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed.

Lemma rpres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

(* [comment removed for export] *)
Lemma rfp_below_ceiling K st3 stx m lo spv a :
  rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try heap_lia_pruned.
  - rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
  - unfold RCTX, alloc_ceiling in *. lia.
  - pose proof MR as (WF & _). (nelimp WF 3%nat; intros _ WR _). (nelim (WR q rq Hq) 5%nat; intros _ _ _ RC _). lia.
Qed.

Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof using . intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Lemma rregion_facts_hi : forall st m rid r,
  rmrep st m -> (s_regions st) !! rid = Some r ->
  r_base r + round_up_pg (r_len r) <= 0x24000 \/ 0x56000 <= r_base r.
Proof.
  intros st m rid r (WF & _) Hr. (nelimp WF 3%nat; intros _ WR _).
  (nelim (WR rid r Hr) 5%nat; intros RB0 RBAL RL0 RBC RFr).
  (nelim (rreserved_disjoint _ _ RFr) 4%nat; intros _ _ _ D). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).


Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof using .
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

Lemma rbig_spec : rbig_stmt.
Proof using AM AMP.
  pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  riprefixT. unfold alloc_ceiling in CLO. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
  unfold RMLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rewrite F_mm_syscalls.alloc_ceiling_val; lia
    | rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (215504 + -164, 215504 + -164 + 4)] m1 m2 -> wmono usegs m1 m2 ->
            rw_cells usegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| unfold alloc_ceiling; lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. (nelimp (rregion_facts st1 m1 rid r MR1 Hr) 4%nat; intros R1 _ R2 _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. unfold alloc_ceiling in R2. cbn. lia.
      + intros rid r Hr. (nelimp (rregion_facts st1 m1 rid r MR1 Hr) 4%nat; intros R1 _ R2 _). unfold alloc_ceiling in R2. lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 He).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply rimplT_ret.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (nelim (FRAME m2 MU2 WM2) 5%nat; intros FR2 MR2 AUX2 PE2 UA2).
    replace (ret_pc (Z_to_bv 64 0x16e8c)) with (Z_to_bv 64 0x16e8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
    exists m2, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). nexists 14%nat. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 AOK).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    (nelim (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) 5%nat; intros X0 XA XC XRF ISE). rewrite ISE.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (nelim (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) 5%nat; intros FR2 MR2 AUX2 PE2 UA2).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. unfold alloc_ceiling in XC. unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep st2 mz).
    { rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). (nelimp WF1 3%nat; intros RS1 WR1 _).
    assert (XI : xa + L <= 0x10000 \/ 0x56000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv usegs mz).
    { unfold mz. apply (mem_inv_zeros usegs m2 xa L); try heap_lia_pruned; [exact MI2 | intros w Hw; apply ref_ro_addr_false; heap_lia_pruned | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; heap_lia_pruned]. }
    assert (FRz : rw_cells usegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. (nelim (WR1 q r Hq1) 5%nat; intros B0 _ _ BC _). unfold alloc_ceiling in BC.
        pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }
    (* [comment removed for export] *)
    riprefixT.
    replace (ret_pc (Z_to_bv 64 0x16e8c)) with (Z_to_bv 64 0x16e8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. (nelim FC 6%nat; intros FC1 FC2 FC3 FC4 FC5 FC6).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (rbig_seq_walk sp gp (Z_to_bv 64 215504)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| unfold alloc_ceiling; lia| exact MIz]. }
    intros ms1 nelH_; (nelim nelH_ 10%nat; intros wa0 wa1 m3 -> MU3 WM3 MI3 ST3 FR3 MR3).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono usegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m2 xa L); try heap_lia_pruned; exact Hw).
    assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells usegs mz (215504 + -164) [C4 errv]).
    { eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (ERR3 : rw_cells usegs m3 (215504 + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. (nelim PT1 8%nat; intros _ _ _ _ _ _ P7 _). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply AM.
    { apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| unfold alloc_ceiling; lia]. }
    { rewrite SP'. exact ST3. }
    { unfold alloc_ceiling; lia. }
    { rewrite SP'. unfold RAM_STACK. lia. }
    { unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    (nelim PO3 28%nat; intros u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m4 errv4 -> MI4 ST4 ERR4 AUX4 PE4 MR4 TK4 PSM PSF PSO REL).
    rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
    replace (ret_pc (Z_to_bv 64 0x16f80)) with (Z_to_bv 64 0x16f80) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| unfold alloc_ceiling; lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { (nelim (amr_regions _ _ _ REL rid _ RR2) 6%nat; intros r' Hr' K' B' L' G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    pose proof MR4 as (WF4 & _ & (ML4 & _) & _). (nelimp WF4 4%nat; intros RS4 WR4 DJ4 _).
    assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
              rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
      eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply rimplT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; unfold alloc_ceiling in GC; lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        (nelim PT3 10%nat; intros _ _ _ _ _ _ _ _ _ P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        (nelim PT3 10%nat; intros _ _ _ _ _ _ _ _ P9 _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold alloc_ceiling; lia) sp gp (Z_to_bv 64 215504));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      intros ms5 nelH_; (nelim nelH_ 11%nat; intros a0' a1' m7 -> MU7 WM7 MI7 ST7 FR7 MR7 TK7).
      apply evt_done. cbn [rcoreQ].
      set (stF := big_final st3 g rid n).
      rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. nexists 17%nat.
      split; [reflexivity|].
      assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). (nelimp WFz 3%nat; intros _ WRz _).
          (nelim (WRz q r Hq2) 5%nat; intros B0 _ _ BC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). unfold alloc_ceiling in BC.
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - (nelim (amr_regions _ _ _ REL q r2 E) 6%nat; intros r' Hr' K' _ _ G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. (nelim (WR4 q r Hq) 5%nat; intros B0 _ _ BC RFq). unfold alloc_ceiling in BC.
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - rewrite unsigned_lit in X by lia. (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). lia.
          - unfold RCTX in X. (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). lia.
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
          split. { intros off nelH_; (nelim nelH_ 5%nat; intros b gh Hb Hf Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. (nelim (WR4 q r Hq) 5%nat; intros B0 _ _ BC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). unfold alloc_ceiling in BC.
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells usegs m7 (215504 + -164) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_trans.
        { eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold RCTX in *. lia. }
        apply rpres_except_refl. }
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| unfold alloc_ceiling; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          (nelim (amr_regions _ _ _ REL q rq Hq2) 6%nat; intros r' Hr' K' B' L' _).
          exists r'. split; [|repeat split; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. repeat split; lia. }
      split. { intros _. unfold F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      repeat split; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      riprefixT.
      eapply evt_cut.
      { apply rbig_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply rimplT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
          | lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; unfold alloc_ceiling in *; lia
          | rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      (nelim PM 22%nat; intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m6 -> MU6 WM6 MI6 ST6 ERR6 He6).
      rewrite (munmap_answer_ok_range ans2 He6). apply rimplT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
      replace (ret_pc (Z_to_bv 64 0x17058)) with (Z_to_bv 64 0x17058) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. unfold alloc_ceiling in *. lia. }
      eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
      set (stF := drop_region rid st3).
      assert (MRF : rmrep stF m6).
      { eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < alloc_ceiling /\ (a + 1 <= 215504 + -164 \/ 215504 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [unfold RMLOCK, alloc_ceiling in *; lia| unfold RLIBC, alloc_ceiling in *; lia| unfold RGOT_SSP, alloc_ceiling in *; lia| unfold RSSP_GUARD, alloc_ceiling in *; lia|].
          (nelim (WR4 q rq Hq) 5%nat; intros _ _ _ RC RFq). (nelimp (rreserved_disjoint _ _ RFq) 4%nat; intros _ _ _ D). pose proof (lr_lo_ge rq).
          split; [lia|]. split; [lia|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        unfold alloc_ceiling in A1.
        apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
        do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm_syscalls.rg_errno ans2 errv4). nexists 14%nat. split; [reflexivity|].
      split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| unfold alloc_ceiling; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          (nelim (amr_regions _ _ _ REL q rq Hq2) 6%nat; intros r' Hr' K' B' L' _).
          exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
        (nelim PT3 8%nat; intros _ _ _ _ _ _ P7 _). rewrite Hb in P7. exact P7. }
      repeat split; assumption.
Qed.
End BIG.


End CeilWrap.
End RF_malloc_big.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W11.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require ASlot_W16.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A3.
Module RASlot_M4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W16 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W17 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W15.F_malloc_bigw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W14.F_malloc_big.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W11 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W14 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W16 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W17 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W18 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W19 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M5D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F RASlot_M5S RF_malloc_big.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rhmm_ok : rHMM_stmt k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof using A1 AR AUX CLO ER FIT HK LO MR RQ SC TP.
  clear A0 F0 IS AC TK UA BL ST MI ERR.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R BIGc.
  (nelim CT 23%nat; intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
  pose proof (rerrno_lit5 tp TP) as EA.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2) as URall. change (fact_usage (strip st2)) with (fact_usage st2) in URall.
  (nelimp (mf_ctx _ _ MF2) 6%nat; intros FC1 FC2 FC3 FC4 FC5 FC6).
  change (ctx (strip st2)) with (ctx st2) in FC1, FC2, FC3, FC4. change (bounces (strip st2)) with (bounces st2) in FC5. change (unmap_seq (strip st2)) with (unmap_seq st2) in FC6.
  pose proof (size_class_range sc SC) as SZR.
  unfold rcnt_state.
  replace (size_class sc * UNIT * cnt1) with (UNIT * size_class sc * cnt1) by lia.
  replace (size_class sc * UNIT) with (UNIT * size_class sc) by lia.
  set (size := UNIT * size_class sc) in *.
  assert (SZ : 16 <= size < 2^18) by (subst size; unfold UNIT; lia).
  rewrite A1. rewrite (ag_mmap_eq sc req k bail st2 mm cnt1).
  set (stS := step_seq (account_bounce sc st2)).
  set (nos := is_bouncing sc st2).
  set (u1 := mm_usage1 stS sc (usage st2 sc)).
  set (cR := mm_cnt_red sc size cnt1 u1 nos).
  assert (CRR : 1 <= cR <= 32) by (subst cR; apply mm_cnt_red_range; exact C1R).
  destruct (mm_final size req u1 cR nos) as [c nd] eqn:EF.
  (nelim (mm_final_props size req u1 cR nos c nd CRR ltac:(lia) ltac:(lia) ltac:(subst size; unfold UNIT; lia) EF) 4%nat; intros CR NDM NDR NDC).
  assert (NDB : 16 <= nd < 2^40).
  { pose proof (round_up_pg_props (req + 20) ltac:(lia)). pose proof (round_up_pg_props (size * c + 16) ltac:(apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia| lia])).
    assert (size * c <= 2^18 * 32) by (apply Z.mul_le_mono_nonneg; lia). destruct NDC as [[Ec En]|[LE En]]; rewrite En; lia. }
  cbv beta iota.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_cut. { eapply (rmm_seq_walk sc SC); [exact MR3| exact FC4| exact FC5| exact FC6| exact MI3]. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros u0 u1' wa3 wa6 wa7 m4 -> -> MU4 WM4 MI4 MR4).
  fold nos stS in MR4 |- *.
  (* [comment removed for export] *)
  (nelim (stS_shape sc st2) 3%nat; intros fS ES HS). fold stS in ES.
  assert (US : forall i, usage stS i = usage st2 i) by (intros i; unfold usage; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (proj2 (HS _))); reflexivity).
  eapply evt_cut.
  { replace (wz (size + 16)) with (wz (size + 16)) by reflexivity.
    eapply (rmmc_walk sc size req nos SC SZ RQ) with (st := stS) (m := m4); [exact MR4| exact C1R| apply URall| intros i; rewrite US; apply URall]. }
  cbv beta. unfold rmmc_post. intros ms' nelH_; (nelim nelH_ 10%nat; intros v0 va0 va1 va2 va3 va4 va5 va6 va7 ->).
  fold u1. fold cR. rewrite ?EF. cbn [fst snd].
  (* [comment removed for export] *)
  assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
  { eapply rw_cells_transport; [exact FR3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ST4 : stk usegs m4 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [exact ST3| exact MU4| exact WM4|]. unfold rseqW, RCTX. cbn. lia. }
  assert (ERR4 : rw_cells usegs m4 (errno_addr tp) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. rewrite EA. unfold rseqW, RCTX. cbn. lia. }
  assert (PE04 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4).
  { eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_of_munch; [exact MU4| exact WM4|].
    intros a Ha NC. unfold rseqW. cbn. split; [|exact I]. intros X. apply NC. left. right. right. left. unfold RCTX in *. lia. }
  assert (AUX4 : rauxv_ok m4 (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. unfold rseqW, RAUXV_CELL, RCTX, RLIBC. constructor; [cbn; lia| constructor]. }
  (nelimp (rmeta_slot_bounds st2 m3 mm MR3 MSL) 4%nat; intros Gpos GC GI _).
  (* [comment removed for export] *)
  eapply evt_cut. { eapply rmm_call_walk. }
  cbv beta. intros ms' ->.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -144) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | lia | rewrite SP'; lia | exact CLO
    | rewrite SP', EA; lia | rewrite TP; unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  (* [comment removed for export] *)
  assert (REGS : s_regions stS = s_regions st2) by (rewrite ES; reflexivity).
  assert (SHS : s_shadow stS = s_shadow st2) by (rewrite ES; reflexivity).
  assert (GRS : s_groups stS = s_groups st2) by (rewrite ES; reflexivity).
  assert (ARS : s_areas stS = s_areas st2) by (rewrite ES; reflexivity).
  assert (TKS' : s_tick stS = s_tick st2) by (rewrite ES; reflexivity).
  assert (NRS : s_next_rid stS = s_next_rid st2) by (rewrite ES; reflexivity).
  assert (RSS : s_reserved stS = s_reserved st2) by (rewrite ES; reflexivity).
  assert (RECS : forall q, get_meta_rec stS q = get_meta_rec st2 q) by (intros q; rewrite ES; reflexivity).
  assert (ACTS : forall c', active stS c' = active st2 c') by (intros c'; unfold active; rewrite ES; unfold ctx, upd_ctx; cbn; rewrite (proj1 (HS _)); reflexivity).
  assert (BRKS : c_brk (ctx stS) = c_brk (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (HS _))))).
  assert (CTRS : c_mmap_counter (ctx stS) = c_mmap_counter (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (HS _)))))).
  assert (FMHS : c_free_meta_head (ctx stS) = c_free_meta_head (ctx st2)) by (rewrite ES; unfold ctx, upd_ctx; cbn; apply (proj1 (proj2 (proj2 (proj2 (proj2 (HS _))))))).
  assert (CONCS : forall q, conc stS q = conc st2 q) by (intros q; unfold conc, get_region; rewrite REGS; reflexivity).
  assert (MSLS : meta_slot stS mm) by (eapply meta_slot_same_areas; [exact ARS| exact MSL]).
  assert (TKS : ticks_ok stS) by (eapply ticks_ok_same; [exact SHS| exact TKS'| exact TK3]).
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  pose proof MR as (WF & _). (nelimp WF 4%nat; intros RS0 WR0 DJ0 _).
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 He).
    cbn [mmap_val]. unfold mm_after. fold stS. destruct (mmap_answer_ok_err (live_ranges stS) nd e He) as [-> ->]. cbn [negb].
    rewrite as_free_meta_eq. cbn [as_kq].
    rewrite SP' in MU6, ST6. rewrite EA in MU6.
    replace (ret_pc (Z_to_bv 64 0x17814)) with (Z_to_bv 64 0x17814) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rwrapper_munch_keeps stS m4 m6 (bv_unsigned sp - 144) lo MR4); [| exact WM6| unfold alloc_ceiling; lia].
      eapply munch_weaken; [| exact MU6]. intros y; cbn; lia. }
    (* [comment removed for export] *)
    pose proof (lf_freelist _ (isf_lf _ _ F2)) as FFL. change (fact_freelist (strip st2)) with (fact_freelist st2) in FFL.
    assert (FL : forall h, c_free_meta_head (ctx stS) = Some h ->
              meta_slot stS h /\ h <> mm /\ exists p, m_prev (get_meta_rec stS h) = Some p /\ meta_slot stS p /\ p <> mm).
    { intros h Hh. rewrite FMHS in Hh. (nelim (FFL h Hh) 8%nat; intros MSh MEMh NXh p HP MSp MEMp NXp).
      change (meta_slot (strip st2) h) in MSh. change (get_meta_rec (strip st2) h) with (get_meta_rec st2 h) in MEMh, NXh, HP.
      change (meta_slot (strip st2) p) in MSp. change (get_meta_rec (strip st2) p) with (get_meta_rec st2 p) in MEMp, NXp.
      split; [eapply meta_slot_same_areas; [exact ARS| exact MSh]|].
      split; [intros ->; rewrite G0 in NXh; apply NXh; reflexivity|].
      exists p. rewrite RECS. split; [exact HP|]. split; [eapply meta_slot_same_areas; [exact ARS| exact MSp]|].
      intros ->. rewrite G0 in NXp. apply NXp. reflexivity. }
    riprefixT.
    eapply evt_cut. { eapply rmm_ret_fail_walk. }
    cbv beta. intros ms' ->.
    eapply evt_cut. { rewrite <- (CONCS mm). subst sp'. unfold rFRM in FR6. eapply (rfailm2_walk stS mm MSLS FL); [exact MR6| exact MI6| exact FR6| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 9%nat; intros s6x m7 junk' -> FR7 MU7 WM7 MI7 MR7).
    assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW stS mm (bv_unsigned sp))).
    { eapply (rfailW_low stS mm m6 _ MR6 MSLS). intros h Hh. (nelim (FL h Hh) 6%nat; intros MSh _ p HP MSp _).
      split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
    assert (ST7 : stk usegs m7 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [exact ST6| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]]. }
    assert (ERR7 : rw_cells usegs m7 (errno_addr tp) [C4 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e))]).
    { eapply rw_cells_transport; [exact ERR6| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
    eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1y a2y -> ST8). apply evt_done.
    (* [comment removed for export] *)
    set (stF := as_fm_st stS mm) in *.
    (nelim (fm_proj stS mm) 13%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10 PF11 PF12 _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
    assert (FS : Forall (rmetaW (bv_unsigned sp) stS) (rfailW stS mm (bv_unsigned sp))).
    { apply (rfailW_shape stS mm _ MSLS). intros h Hh; (nelim (FL h Hh) 6%nat; intros MSh _ p HP MSp _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
    assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
    { eapply rpres_except_trans.
      - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr. exists r. rewrite PF1, REGS. repeat split; auto; lia.
      - eapply rpres_except_trans.
        + eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|split; [|exact I]]; intros X; apply NC; left; [left; lia| right; left; rewrite unsigned_lit by lia; lia].
        + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
          intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          * cbn in E1, E2. subst lo' hi'. left. do 3 right.
            assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
            destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
            exists rid0, r0. split; [exact H0|]. split; [exact K0|].
            assert (EC : conc stF q = conc stS q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
          * inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
          * inversion E; subst. left. left. lia. }
    apply HK. unfold ras_post2.
    nexists 14%nat. exists m7, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). split; [reflexivity|].
    split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
    split; [exact MR7|].
    split; [eapply ticks_ok_same; [rewrite PF2; exact SHS| rewrite PF6; exact TKS'| exact TK3]|].
    split. { eapply (unk_agree_xfer o st2 m3 stF m7 UA3).
      - rewrite PF2. exact SHS.
      - intros rid r Hk Hr. rewrite PF1, REGS in Hr. exact Hr.
      - intros b. rewrite PF3, GRS. split; intros X; exact X.
      - intros rid r off h Hr Hk Ho Hc NG.
        pose proof MR3 as (WF3 & _). (nelimp WF3 4%nat; intros _ WR3 DJ3 _). (nelim (WR3 _ _ Hr) 5%nat; intros R0 _ _ RC _). unfold alloc_ceiling in RC.
        (nelim (rregion_facts st2 m3 rid r MR3 Hr) 5%nat; intros _ _ _ RI1 RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
        transitivity (m6 (wa (r_base r + off))).
        { apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
          pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
          - cbn in E1, E2. subst lo' hi'. rewrite CONCS in Ha.
            assert (MSq2 : meta_slot st2 q) by (eapply meta_slot_same_areas; [symmetry; exact ARS| exact MSq]).
            (nelim (rmeta_chunk_facts st2 m3 q MR3 MSq2) 7%nat; intros _ _ _ _ _ GRG _). destruct (GRG rid r Hr Hk); lia.
          - inversion E; subst. unfold RCTX in Ha. lia.
          - inversion E; subst. lia. }
        transitivity (m4 (wa (r_base r + off))).
        { apply MU6. rewrite wa_unsigned by lia. cbn. lia. }
        apply MU4. rewrite wa_unsigned by lia. unfold rseqW, RCTX. cbn. lia. }
    split; [exact PE07|].
    split. { split; [| rewrite PF7, NRS, <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite PF8, RSS, (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
             intros rid r Hr. rewrite <- REG1 in Hr. (nelim (amr_regions _ _ _ REL rid r Hr) 6%nat; intros r' H' K' B' L' _). exists r'. rewrite PF1, REGS. auto. }
    split. { unfold brk_link_ps in *. rewrite PF11, BRKS. destruct (c_brk (ctx st2)) as [| |rid off]; auto.
             unfold conc, get_region. rewrite PF1, REGS. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite PF9, ACTS, (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ARS. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF6, TKS', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split; [rewrite PF12, CTRS; exact FC1|].
    left. reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (nelim PO 22%nat; intros v0' v1 v2 v3 v4' v5 v6 v7 v8 v9 v10 v11 v12 v13 m6 -> MU6 WM6 MI6 ST6 ERR6 AOK).
    cbn [mmap_val]. unfold mm_after. fold stS.
    destruct (mmap_answer_ok (live_ranges stS) nd xa) eqn:VOK. 2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    (nelim (mmap_answer_ok_addr (live_ranges stS) nd xa ltac:(lia) AOK VOK) 5%nat; intros X0 XA XC XRF ISE). rewrite ISE.
    rewrite SP' in MU6, ST6.
    assert (RU : round_up_pg nd = nd) by (unfold round_up_pg; change (PGSZ - 1) with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; Z.div_mod_to_equations; lia).
    rewrite RU in XC, XRF.
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR4| exact MU6| exact WM6|]. cbn. lia. }
    assert (MR6 : rmrep stS m6).
    { eapply (rmrep_transport_high stS m4 m6); [exact MR4| exact MU6| exact WM6| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid stS). set (r0 := {| r_kind := RKGroup; r_base := xa; r_len := nd |}).
    set (stN := set_next_rid (N.succ rid) (set_regions (<[rid:=r0]> (s_regions stS)) stS)).
    assert (EstN : stN = fst (new_region RKGroup xa nd stS)) by reflexivity.
    pose proof (mf_ptrs _ _ MF2) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) stS).
    { rewrite ES. apply ptrs_in_upd_ctx_scalar; try (intros cc; (nelimp (HS cc) 14%nat; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ?); assumption).
      eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. rewrite NRS. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; rewrite NRS; lia)) as [FRr FRs].
    unfold F_mm_syscalls.mmap_raw in ST6 |- *. cbn [negb] in ST6 |- *. rewrite mmap_len_round_up, RU in ST6 |- *.
    unfold alloc_ceiling in XC.
    set (mz := apply_zeros m6 [(wa xa, Z_to_bv 64 nd)]) in *.
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + nd <= a) -> mz (wa a) = m6 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + nd -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m6 xa nd); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep stN mz).
    { rewrite EstN. eapply (rmrep_new_region stS m6 mz xa nd RKGroup MR6 PT1 ltac:(rewrite SHS; exact FRs) X0 XA ltac:(lia));
        rewrite ?mmap_len_round_up, ?RU; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    pose proof MR6 as (WF6 & _). (nelimp WF6 4%nat; intros RS6 WR6 DJ6 _).
    assert (XI : xa + nd <= 0x10000 \/ 0x56000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa nd = true).
      { apply ranges_free_intro. intros b kk HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS6. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv usegs mz).
    { unfold mz. apply (mem_inv_zeros usegs m6 xa nd); try lia; [exact MI6 | intros w Hw; apply ref_ro_addr_false; lia | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; lia]. }
    assert (MUz : munch [(xa, xa + nd)] m6 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono usegs m6 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m6 xa nd); try lia; exact Hw).
    assert (FRz : rw_cells usegs mz (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [exact FR6| exact MUz| exact WMz|]. cbn. lia. }
    assert (STz : stk usegs mz lo (bv_unsigned sp + -144)) by exact ST6.
    assert (ERRz : rw_cells usegs mz (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [exact ERR6| exact MUz| exact WMz|]. rewrite EA. cbn. lia. }
    (* [comment removed for export] *)
    assert (MSLN : meta_slot stN mm) by (eapply meta_slot_same_areas; [| exact MSLS]; rewrite EstN; reflexivity).
    assert (RECN : get_meta_rec stN mm = meta0) by (rewrite EstN; change (get_meta_rec (fst (new_region RKGroup xa nd stS)) mm) with (get_meta_rec stS mm); rewrite RECS; exact G0).
    assert (CTRN : c_mmap_counter (ctx stN) = c_mmap_counter (ctx st2)) by (rewrite EstN; change (ctx (fst (new_region RKGroup xa nd stS))) with (ctx stS); exact CTRS).
    assert (GCN : conc stN mm = conc st2 mm).
    { rewrite <- CONCS. rewrite EstN. apply nr_conc. cbn [fst].
      (nelim MSLS 6%nat; intros ar arr kk Ha Hk ->). unfold aadd. cbn [fst]. intros E.
      (nelim PT1 10%nat; intros _ _ _ _ _ _ _ _ P9 _). destruct (P9 _ _ Ha) as [X _]. exact (X E). }
    replace (ret_pc (Z_to_bv 64 0x17814)) with (Z_to_bv 64 0x17814) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    riprefixT.
    eapply evt_cut.
    { rewrite <- GCN. subst sp'.
      assert (XC' : xa + nd <= alloc_ceiling) by (unfold alloc_ceiling; exact XC).
      eapply (rmm_ret_ok_walk stN sc c size nd xa (c_mmap_counter (ctx st2)) mm SC ltac:(lia) SZ ltac:(lia) NDM X0 XC' MSLN RECN CTRN FC1);
        [exact MRz| exact MIz]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 9%nat; intros xa3 xa4 m8 -> MU8 WM8 MI8 MR8 CTR8).
    set (stT := mm_st4 stN nd mm) in *.
    (* [comment removed for export] *)
    assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (ML : 0 <= Z.shiftr nd 12 < 2^52) by (rewrite ND12; Z.div_mod_to_equations; lia).
    assert (RECT : get_meta_rec stT mm = {| m_prev := None; m_next := None; m_mem := None; m_avail := 0; m_freed := 0; m_last_idx := 0; m_freeable := 0; m_sizeclass := 0; m_maplen := Z.shiftr nd 12 |}).
    { unfold stT, mm_st4. rewrite rec_upd_ctx. unfold upd_meta. rewrite get_meta_rec_put_same, RECN. unfold m_set_maplen, meta0. cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass].
      f_equal. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    assert (HrT : (s_regions stT) !! rid = Some r0) by (unfold stT, mm_st4, upd_meta; cbn; first [apply lookup_insert_eq | rewrite EstN; apply nr_lookup_new]).
    assert (GNT : forall off, (s_groups stT) !! (rid, off) = None).
    { intros off. change (s_groups stT) with (s_groups stS). destruct ((s_groups stS) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
      (nelim PT1 10%nat; intros _ _ _ _ _ _ _ _ _ P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
    assert (SHT : (s_shadow stT) !! rid = None) by (change (s_shadow stT) with (s_shadow stS); rewrite SHS; exact FRs).
    assert (ACTT : active stT sc = None).
    { unfold stT, mm_st4. unfold active, ctx, upd_ctx, upd_meta. cbn. change (c_active (s_ctx stS) !! sc) with (active stS sc). rewrite ACTS, (amr_active _ _ _ REL). exact ACT0. }
    assert (TKT : ticks_ok stT).
    { eapply ticks_ok_same; [| | exact TK3]; [change (s_shadow stT) with (s_shadow stS); exact SHS| change (s_tick stT) with (s_tick stS); exact TKS']. }
    pose proof (mm_ai_range stN c size nd mm ltac:(lia) SZ) as AIR.
    eapply evt_cut.
    { replace (Z_to_bv 64 xa) with (Z_to_bv 64 (conc stT (rid, 0))) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; f_equal; lia).
      change (conc stN mm) with (conc stT mm).
      eapply (rtail_walk stT sc c (mm_ai c size) (Z.shiftr nd 12) mm (rid, 0) r0 SC ltac:(lia) AIR ML);
        [eapply meta_slot_same_areas; [| exact MSLN]; reflexivity| exact RECT| exact HrT| reflexivity| cbn; lia| cbn; reflexivity
        | cbn [snd r_len r0]; rewrite RU; lia| apply GNT
        | intros b' gh Hb' Hf'; exfalso; destruct b' as [b1 b2]; cbn in Hf'; subst b1; rewrite GNT in Hb'; discriminate
        | intros o' v t Ho Hc; exfalso; unfold get_shadow in Hc; rewrite SHT in Hc; cbn in Hc; rewrite lookup_empty in Hc; discriminate
        | change (usage stT sc) with (usage stS sc); rewrite US; apply URall
        | exact ACTT| exact TKT| exact MR8| exact MI8]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros s0x a1x a2x a3x a4x m9 -> MU9 WM9 MI9 MR9 TK9).
    assert (GT : conc stT mm = conc st2 mm) by (change (conc stT mm) with (conc stN mm); exact GCN).
    assert (PT : conc stT (rid, 0) = xa) by (rewrite (conc_region stT rid 0 r0 HrT); cbn [r_base r0]; lia).
    (* [comment removed for export] *)
    assert (FR9 : rw_cells usegs m9 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply rw_cells_transport; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia].
      eapply rw_cells_transport; [exact FRz| exact MU8| exact WM8|]. rewrite GCN. unfold RCTX. cbn. unfold alloc_ceiling in GC. lia. }
    assert (ST9 : stk usegs m9 lo (bv_unsigned sp + -144)).
    { eapply stk_transport_disjoint; [| exact MU9| exact WM9| unfold rtailW; rewrite GT, PT; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia].
      eapply stk_transport_disjoint; [exact STz| exact MU8| exact WM8| rewrite GCN; unfold RCTX; cbn; unfold alloc_ceiling in GC; lia]. }
    eapply evt_cut. { unfold rFRM in FR9. eapply (ras_ret0 sp gp tp); [exact MR9| exact MI9| exact FR9| exact ST9| exact CLO| lia]. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 4%nat; intros a1y a2y -> ST10). apply evt_done.
    rewrite (ag_tail_kq_eq sc k bail stT mm (rid, 0) c (mm_ai c size)); [| rewrite RECT; reflexivity| rewrite RECT; reflexivity| exact ACTT].
    apply HK.
    (* [comment removed for export] *)
    set (ai := mm_ai c size) in *. set (ml := Z.shiftr nd 12) in *.
    set (stF := st_model stT sc c ai mm (rid, 0)).
    assert (C32 : 1 <= c <= 32) by lia.
    assert (EML : nd = 4096 * ml) by (subst ml; rewrite ND12; Z.div_mod_to_equations; lia).
    assert (ML28 : 1 <= ml < 2^28) by lia.
    assert (Hk0 : r_kind r0 = RKGroup) by reflexivity.
    assert (LEN0 : r_len r0 = nd) by reflexivity.
    assert (MST : meta_slot stT mm) by (eapply meta_slot_same_areas; [| exact MSLN]; reflexivity).
    assert (Esz : size = 16 * size_class sc) by reflexivity.
    assert (NDC' : c = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * c + 16 <= nd /\ nd < 16 * size_class sc * c + 16 + 4096).
    { pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 _]. pose proof (round_up_pg_props (size * c + 16) ltac:(apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia| lia])) as [N1 _].
      rewrite <- Esz. destruct NDC as [[Ec En]|[LE En]]; [left; split; [exact Ec| rewrite En; lia] | right; split; [exact LE| rewrite En at 1; lia]]. }
    (nelim (sm_slot_ok stT sc c ai ml mm rid r0 SC C32 AIR ML28 RECT HrT Hk0 SHT GNT req nd RQ FIT LEN0 EML NDR ltac:(lia) NDC' MST) 4%nat; intros SO STR S16 SND).
    fold stF in SO, STR, S16, SND.
    (nelimp (sm_proj stT sc c ai mm rid) 10%nat; intros PF1 PF2 PF3 PF4 PF5 PF6 PF7 PF8 PF9 PF10).
    fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10.
    assert (MRF : rmrep stF m9) by (exact (rmrep_st_model stT sc c ai ml mm (rid, 0) SC C32 RECT ltac:(cbn; lia) m9 MR9)).
    assert (TKF : ticks_ok stF) by (eapply ticks_ok_same; [| | exact TK9]; reflexivity).
    assert (MSF : meta_slot stF mm) by (apply (proj1 (sm_meta_slot stT sc c ai mm rid mm)); exact MST).
    (* [comment removed for export] *)
    assert (REGT : s_regions stT = <[rid:=r0]> (s_regions stS)) by reflexivity.
    assert (SHT' : s_shadow stT = s_shadow st2) by (transitivity (s_shadow stS); [reflexivity| exact SHS]).
    assert (GRT : s_groups stT = s_groups st2) by (transitivity (s_groups stS); [reflexivity| exact GRS]).
    assert (ART : s_areas stT = s_areas st2) by (transitivity (s_areas stS); [reflexivity| exact ARS]).
    assert (TKT' : s_tick stT = s_tick st2) by (transitivity (s_tick stS); [reflexivity| exact TKS']).
    assert (NRT : s_next_rid stT = N.succ rid) by reflexivity.
    assert (RST : s_reserved stT = s_reserved st2) by (transitivity (s_reserved stS); [reflexivity| exact RSS]).
    assert (BRKT : c_brk (ctx stT) = c_brk (ctx st2)) by (transitivity (c_brk (ctx stS)); [reflexivity| exact BRKS]).
    assert (ACTT' : forall c', active stT c' = active st2 c') by (intros c'; transitivity (active stS c'); [reflexivity| apply ACTS]).
    assert (GF : conc stF mm = conc st2 mm) by (rewrite (sm_conc stT sc c ai mm rid); exact GT).
    assert (HOLD : forall q rq, (s_regions st2) !! q = Some rq -> (s_regions stF) !! q = Some rq /\ q <> rid).
    { intros q rq Hq. assert (NE : q <> rid) by (intros ->; rewrite FRr in Hq; discriminate).
      split; [| exact NE]. rewrite PF1, REGT, lookup_insert_ne, REGS by congruence. exact Hq. }
    assert (MREL0S : forall q rq, (s_regions st0) !! q = Some rq ->
              exists r', (s_regions stS) !! q = Some r' /\ r_kind r' = r_kind rq /\ r_base r' = r_base rq /\ r_len rq <= r_len r').
    { intros q rq Hq. (nelim (mrel_regions _ _ (er_mrel _ _ ER) q rq Hq) 5%nat; intros r1 H1 K1 B1 L1). rewrite <- REG1 in H1.
      (nelim (amr_regions _ _ _ REL q r1 H1) 6%nat; intros r2 H2 K2 B2 L2 _). exists r2. rewrite REGS. repeat split; auto; try congruence. lia. }
    assert (FRESH : forall a, xa <= a < xa + nd -> fresh_addr st0 a).
    { intros a Ha. eapply (fresh_addr_anti st0 stS); [| exact MREL0S|].
      - rewrite RS6, <- RS0. exact (mrel_reserved _ _ (er_mrel _ _ ER)).
      - split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa nd); [exact XRF| lia| lia| lia]. }
    assert (HFP2 : forall a, rmalloc_fp st0 st2 lo (bv_unsigned sp) a -> rmalloc_fp st0 stF lo (bv_unsigned sp) a).
    { intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros q rq Hq. exists rq. split; [apply (proj1 (HOLD q rq Hq))|]. repeat split; auto. lia. }
    (* [comment removed for export] *)
    assert (OLDW : forall q rq off, (s_regions st2) !! q = Some rq -> r_kind rq = RKGroup -> 0 <= off < round_up_pg (r_len rq) ->
              m9 (wa (r_base rq + off)) = m3 (wa (r_base rq + off))).
    { intros q rq off Hq Hk Ho.
      assert (HqS : (s_regions stS) !! q = Some rq) by (rewrite REGS; exact Hq).
      (nelim (WR6 _ _ HqS) 5%nat; intros R0 _ _ RC _). unfold alloc_ceiling in RC.
      (nelim (rregion_facts st2 m3 q rq MR3 Hq) 5%nat; intros _ _ _ RI1 RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      (nelim (rmeta_chunk_facts st2 m3 mm MR3 MSL) 7%nat; intros _ _ _ _ _ GRG _). pose proof (GRG q rq Hq Hk) as GRq.
      pose proof (In_live_ranges stS q rq HqS) as HIq. unfold region_live_range in HIq. rewrite Hk in HIq.
      pose proof (ranges_free_In _ _ _ _ _ XRF HIq) as DJq.
      pose proof (lr_lo_group rq Hk) as LRq.
      (* [comment removed for export] *)
      transitivity (m8 (wa (r_base rq + off))). { apply MU9. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rtailW. rewrite GT, PT. cbn. unfold RCTX. clear - Ho R0 RC RI2 GRq DJq SC SND S16; lia. }
      transitivity (mz (wa (r_base rq + off))). { apply MU8. rewrite wa_unsigned by (clear - Ho R0 RC; lia). rewrite GCN. cbn. unfold RCTX. clear - Ho R0 RI2 GRq; lia. }
      transitivity (m6 (wa (r_base rq + off))). { apply ZO; [clear - Ho R0 RC; lia | clear - Ho R0 DJq; lia]. }
      transitivity (m4 (wa (r_base rq + off))). { apply MU6. rewrite wa_unsigned by (clear - Ho R0 RC; lia). cbn. clear - Ho R0 RC CLO' LO ASG; lia. }
      apply MU4. rewrite wa_unsigned by (clear - Ho R0 RC; lia). unfold rseqW, RCTX. cbn. clear - Ho R0 RI2; lia. }
    assert (UAF : unk_agree stF o m9).
    { eapply (unk_agree_transfer st2 stF o m3 m9 UA3). intros q rq Hq Hk.
      rewrite PF1, REGT, REGS in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      - right. rewrite lookup_insert_eq in Hq. inversion Hq; subst rq. cbn [r_len r_base]. intros off h Ho Hc.
        rewrite (sm_cell_read stT sc c ai mm rid SHT off ltac:(lia)) in Hc.
        destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T. apply (sm_grp_hdr_cov stT sc c ai mm rid SC). lia.
      - left. rewrite lookup_insert_ne in Hq by congruence.
        split; [exact Hq|].
        split. { rewrite (sm_shadow_other stT sc c ai mm rid q NE). unfold get_shadow. rewrite SHT'. reflexivity. }
        split. { intros off X. apply (sm_grp_hdr_cov_old stT sc c ai mm rid GNT). eapply rgrp_hdr_cov_same; [exact GRT| exact X]. }
        intros off h Ho Hc NG. exact (OLDW q rq off Hq Hk Ho). }
    assert (PE09 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m9).
    { eapply rpres_except_trans. { eapply rpres_except_mono; [exact PE04| exact HFP2]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU6| exact WM6|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. left. left. lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC. do 4 right. apply FRESH. lia. }
      eapply rpres_except_trans.
      { eapply rpres_except_of_munch; [exact MU8| exact WM8|]. intros a Ha NC. rewrite GCN. cbn. split; [|split; [|exact I]]; intros X; apply NC.
        - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
          exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
        - left. right. right. left. unfold RCTX in *. lia. }
      eapply rpres_except_of_munch; [exact MU9| exact WM9|]. intros a Ha NC. unfold rtailW. rewrite GT, PT. cbn.
      split; [|split; [|split; [|split; [|exact I]]]]; intros X; apply NC.
      - left. right. right. left. unfold RCTX in *. lia.
      - left. do 3 right. destruct (rmeta_chunk_facts stF m9 mm MRF MSF) as (_ & _ & _ & _ & _ & _ & (rid0 & rr0 & H0 & K0 & L0 & H0')).
        exists rid0, rr0. split; [exact H0|]. split; [exact K0|]. rewrite GF in L0, H0'. lia.
      - do 4 right. apply FRESH. lia.
      - left. right. right. left. unfold RCTX in *. lia. }
    assert (ERR9 : rw_cells usegs m9 (errno_addr tp) [C4 errv']).
    { eapply rw_cells_transport; [| exact MU9| exact WM9|].
      - eapply rw_cells_transport; [exact ERRz| exact MU8| exact WM8|]. rewrite EA, GCN. cbn. unfold RCTX. lia.
      - unfold rtailW. rewrite GT, PT, EA. cbn. unfold RCTX. lia. }
    unfold ras_post2.
    nexists 14%nat. exists m9, errv'. split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST10|]. split; [exact ERR9|].
    split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m9); [exact MRF| exact AUX| exact PE09| exact CLO| lia]|].
    split; [exact MRF|]. split; [exact TKF|]. split; [exact UAF|]. split; [exact PE09|].
    split. { split.
      - intros q rq Hq. rewrite <- REG1 in Hq. (nelim (amr_regions _ _ _ REL q rq Hq) 6%nat; intros r' H' K' B' L' _).
        exists r'. split; [apply (proj1 (HOLD q r' H'))|]. repeat split; auto.
      - rewrite PF6, NRT. pose proof (amr_next_rid _ _ _ REL) as NX1. pose proof (tr_next _ _ _ TR) as NX0. subst rid. rewrite NRS. lia.
      - rewrite PF7, RST, (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
    split. { unfold brk_link_ps in BL2 |- *. rewrite PF8, BRKT. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:EB; auto.
             rewrite (sm_conc stT sc c ai mm rid). rewrite <- (CONCS (brid, boff)) in BL2.
             replace (conc stT (brid, boff)) with (conc stS (brid, boff)); [exact BL2|].
             change (conc stT (brid, boff)) with (conc stN (brid, boff)). rewrite EstN. symmetry. apply nr_conc. cbn [fst].
             (nelim PT1 8%nat; intros _ _ _ _ _ _ P7 _). rewrite BRKS in P7. first [rewrite EB in P7; exact P7 | exact P7]. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c' Hc'. rewrite (sm_active stT sc c ai mm rid). replace (c' =? sc) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite ACTT', (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. rewrite PF4, ART. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite PF5, TKT', (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros _ rid' S len RS o' v t Ho Hc. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        rewrite (sm_cells_none stT sc c ai mm rid SHT) in Hc. discriminate.
      - intros _ _ rid' S len RS o' Ho. destruct (sm_ret_span stT sc c ai ml mm rid SC C32 RECT rid' S len RS) as [-> ->].
        split; [apply (sm_cells_none stT sc c ai mm rid SHT)|].
        split; [apply (sm_hav_none stT sc c ai mm rid SHT); lia| apply (sm_havp_none stT sc c ai mm rid SHT)]. }
    split. { rewrite PF9, CTR8. unfold u32. Z.div_mod_to_equations. lia. }
    right. split; [lia|]. exists mm, (rid, 0), r0.
    split; [rewrite (sm_active stT sc c ai mm rid), Z.eqb_refl; reflexivity|]. split; [exact SO|]. split.
    + intros a Ha. replace (r_base r0) with xa in Ha by reflexivity. cbn [fst snd] in Ha. do 4 right. apply FRESH. rewrite Z.mul_0_r in Ha. lia.
    + intros _. cbn [fst snd]. replace (0 + (16 + get_stride (get_meta_rec stF mm) * 0) + -3) with 13 by lia.
      apply (sm_rdv stT sc c ai mm rid SHT).
Qed.
End LEVEL.


End CeilWrap.
End RASlot_M4.

(* [comment removed for export] *)
Module RASlot_M6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_AB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS.MallocNat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.ASlot_W1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_W9 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M3 RASlot_M4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M5D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F RASlot_M5S OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_M5F.RASlot_M5.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Theorem ralloc_slot_ok (ram_pre : mstate -> Prop) :
  ralloc_meta_stmt ram_pre -> RAMP_AS ram_pre -> forall f, ralloc_slot_stmt2 f.
Proof using .
  intros AM AMP f. induction f as [|f IHf].
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    cbn [alloc_slot]. apply rimplT_undef.
  - intros R k bail o s Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st lo sc req errv
           PRE MR TK UA BL AUX ST CLO LO ERR MI TP A0 A1 HK.
    destruct PRE as ((LB & AR & IS) & ER & AC & SC & RQ & FIT).
    pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st AR IS) as F0.
    pose proof (RAS_STACK_ge sc) as ASG.
    rewrite (alloc_slot_S full_lay f sc req k bail st). subst a0.
    eapply (rta_phase (as_k full_lay f sc req k bail) bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              (rtaf_of_facts st LB sc F0 SC) SC CLO ltac:(lia)).
    + (* [comment removed for export] *)
      intros stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
      exact (rhk1_ok f k bail o s Q ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK stX g3 msk kk m' t0' t1' a1' a2' a3' a4' a5' a6' a7' TR HA GM MSK MR0 LBK KK MR' MI' ST' PE).
    + reflexivity.
    + exact MR.
    + exact MI.
    + exact ST.
    + (* [comment removed for export] *)
      intros st1 m' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' junk TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
      unfold as_k. cbn [Z.eqb negb].
      eapply (rag_phase f k bail o s Q ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st0 st LB lo sc req errv
                AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK ram_pre AM AMP); [| exact TF| exact TR| exact ACT0| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      (* [comment removed for export] *)
      refine (rhag_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req AR SC RQ FIT _ _).
      * (* [comment removed for export] *)
        exact (rhmm_ok k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req
                 AR ER SC RQ FIT MR AUX CLO LO TP A1 HK).
      * (* [comment removed for export] *)
        refine (rhnest_ok f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc AR ER SC MR CLO LO TP IHf _ _).
        -- exact (rnfail_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ MR AUX CLO LO ERR TP HK).
        -- exact (rnsucc_ok f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st LB lo sc req errv
                   AR IS ER SC RQ FIT MR AUX CLO LO ERR TP HK).
Qed.


End CeilWrap.
End RASlot_M6.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMalloc_ifaceP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv2.
Module RF_malloc_top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM usegs (membed t1) s Q1 ms ->
  implM usegs (membed t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    exists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl usegs (at_node usegs) (ITree.bind _ (Ret Unr) f) Qx msx = impl usegs (at_node usegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; intros nelH_; (nelim nelH_ 6%nat; intros r1' ans F1 F2 HR HQ);
         exists r1', (z :: ans); cbn; auto.
Qed.

Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
  strip st = ps_m s ->
  rimplT o (malloc st n) s Q1 ms ->
  (forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
     Q1 (st', p) s' ms' -> ptr_rel p r ->
     follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
     follow (cmalloc (strip st) n) ans = Some (cst, c) ->
     cst = strip st' ->
     r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
     Q r (set_m (strip st') s') ms') ->
  implM usegs (raw_malloc n) s Q ms.
Proof.
  intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
  eapply (implM_bind usegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind usegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
             /\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
  { rewrite <- Hst. unfold rimplT in H.
    eapply implM_mono.
    - eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
      unfold mrun. apply malloc_control. apply pans_mem_range.
    - intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
      exists st', p, ans, o1. auto. }
  intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
  eapply (implM_bind usegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
  eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
  destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

(* [comment removed for export] *)
Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt usegs (Q x s) ms.
Proof using . intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - (nelim (rblock_inside st LB m blk MF MR Hin) 12%nat; intros r g idx Hr Hk SL LOB HIB BZ R4 RC RI1).
    unfold alloc_ceiling in *.
    pose proof MR' as (WF' & _). (nelimp WF' 4%nat; intros _ WR' DISJ' _).
    pose proof MR as (WF & _). (nelimp WF 4%nat; intros _ WR DISJ _).
    destruct REL as [RREG _ _]. (nelim (RREG _ _ Hr) 5%nat; intros r1 Hr1 K1 B1 L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        (nelim (HB blk Hin (eq_sym E)) 3%nat; intros r'' Hr'' DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells usegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof using .
  intros MR Hr Hk P0 PN N0.
  (nelimp MR 6%nat; intros WF _ _ _ _ SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  (nelimp (rregion_addr_facts st' m' (fst p) r MR Hr) 4%nat; intros R4 _ RC RI). unfold alloc_ceiling in RC.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at usegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  (nelim (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) 3%nat; intros bs L B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
  (nelim HEAP 6%nat; intros st LB0 HPERM Hst MR [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind usegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind usegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  (nelim MQ 9%nat; intros st2 r ans o1 Ecs Ec F1 F2 CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind usegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 40%nat; intros b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO MREL BL2 PSM PSF PSO)
.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    (nelimp (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) 4%nat; intros R4 RAL RC RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    (nelim EP 25%nat; intros st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF).
    (nelim LEAF 7%nat; intros off OFF0 FIT Ep Est' Ep2 Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    (nelimp (strip_eq_proj _ _ SE) 8%nat; intros Ec Er En Em _ _ Esl Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. nexists 15%nat. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - clear - Ha X RI1 SPAN SKL SK B0 S16. first [heap_lia_imp | lia]. }   (* [comment removed for export] *)
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { unfold rblock_range, alloc_ceiling. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). clear - N0' RC RI1 SPAN SKL SK B0 FIT OFF0 S16. lia. }  (* [comment removed for export] *)
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 29%nat; intros m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO)
.
    apply evt_done. unfold rmalloc_post. nexists 15%nat. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL.



End CeilWrap.
End RF_malloc_top.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_alloc_meta.
Module RF_alloc_slot.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_M5D.ASlot_M0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta RASlot_M6.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


(* [comment removed for export] *)
Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof using .
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4.ist_ampre_proof fuel).
Qed.


End CeilWrap.
End RF_alloc_slot.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RF_malloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core RF_malloc_top OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RF_alloc_slot RF_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Theorem rmalloc_spec : rmalloc_stmt.
Proof using .
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.



End CeilWrap.
End RF_malloc_spec.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_fentry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
Module CJ_heap_inst0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_Geom.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP RF_malloc_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bview (b : block) : cblock := (blk_addr b, blk_size b).

Definition LHEAPd (SPB : Z) (LB : list cblock) (m : mem) (mo : Model) : Prop :=
  exists s LBi B, RHEAP s LBi m /\ LB = map bview LBi /\ AOWN (map blk_slot LBi) s mo /\ MOK mo
                  /\ rauxv_ok m B /\ SPB <= B.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lhd_mok : forall SPB LB m mo, LHEAPd SPB LB m mo -> MOK mo.
Proof using . intros SPB LB m mo nelH_; (nelim nelH_ 8%nat; intros s LBi B _ _ _ HM _). exact HM. Qed.

Lemma lhd_lower : forall SPB SPB' LB m mo, LHEAPd SPB LB m mo -> SPB' <= SPB -> LHEAPd SPB' LB m mo.
Proof using . intros SPB SPB' LB m mo (s & LBi & B & H1 & H2 & H3 & H4 & H5 & H6) HS. exists s, LBi, B. splits; auto. lia. Qed.

Lemma lhd_perm : forall SPB LB LB' m mo, LHEAPd SPB LB m mo -> Permutation LB LB' -> LHEAPd SPB LB' m mo.
Proof using .
  intros SPB LB LB' m mo (s & LBi & B & HR & -> & HO & HM & HA & HS) HP.
  (nelim (Permutation_map_inv _ _ (Permutation_sym HP)) 3%nat; intros LBi' -> HP').
  exists s, LBi', B. splits; auto.
  - eapply RHEAP_perm; [exact HR| exact HP'].
  - eapply AOWN_perm; [apply Permutation_map; exact HP'| exact HO].
Qed.

Lemma in_bview : forall LBi A n, In (A, n) (map bview LBi) -> exists b, In b LBi /\ blk_addr b = A /\ blk_size b = n.
Proof using .
  intros LBi A n H. apply in_map_iff in H as (b & E & Hb). exists b. unfold bview in E. injection E as E1 E2. auto.
Qed.

Lemma lhd_block_range : forall SPB LB m mo A n, LHEAPd SPB LB m mo -> In (A, n) LB -> cblock_range A n.
Proof using .
  intros SPB LB m mo A n (s & LBi & B & HR & -> & _) Hin. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  exact (RHEAP_block_range_proof s LBi m b HR Hb).
Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof using .
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma lhd_blocks_disjoint : forall SPB LB m mo A1 n1 A2 n2,
  LHEAPd SPB LB m mo -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 -> A1 + n1 <= A2 \/ A2 + n2 <= A1.
Proof.
  intros SPB LB m mo A1 n1 A2 n2 (s & LBi & B & HR & -> & _) H1 H2 NE.
  (nelim (in_bview _ _ _ H1) 4%nat; intros b1 Hb1 <- <-). (nelim (in_bview _ _ _ H2) 4%nat; intros b2 Hb2 <- <-).
  apply (RHEAP_blocks_disjoint_proof s LBi m b1 b2 HR Hb1 Hb2). intros E. apply NE.
  rewrite (nodup_map_inj blk_id LBi b1 b2 (RHEAP_blocks_nodup_proof s LBi m HR) Hb1 Hb2 E). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma RHEAP_addr_nodup : forall s LBi m, RHEAP s LBi m -> List.NoDup (map blk_addr LBi).
Proof.
  intros s LBi m nelH_; (nelim nelH_ 6%nat; intros st LB0 HP _ _ [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  apply MallocFacts_inv2.NoDup_map_on.
  - intros x y Hx Hy E. destruct (decide (blk_slot x = blk_slot y)) as [ES|NS].
    + exact (nodup_map_inj blk_slot LB0 x y ND Hx Hy ES).
    + exfalso. pose proof (areach_blocks_apart st LB0 x y AR Hx Hy NS) as D.
      (nelim (areach_block_span st LB0 x AR Hx) 9%nat; intros r1 lo1 hi1 _ _ _ _ Z1 _).
      (nelim (areach_block_span st LB0 y AR Hy) 9%nat; intros r2 lo2 hi2 _ _ _ _ Z2 _).
      unfold IB in D. lia.
  - eapply NoDup_map_inv. exact ND.
Qed.

Lemma map_fst_bview : forall LBi, map fst (map bview LBi) = map blk_addr LBi.
Proof using . intros LBi. rewrite map_map. apply map_ext. intros [[p A] n]. reflexivity. Qed.

Lemma lhd_nodup : forall SPB LB m mo, LHEAPd SPB LB m mo -> NoDup (map fst LB).
Proof using . intros SPB LB m mo nelH_; (nelim nelH_ 6%nat; intros s LBi B HR -> _). apply NoDup_ListNoDup. rewrite map_fst_bview. eapply RHEAP_addr_nodup. exact HR. Qed.

Lemma lhd_ssp : forall SPB LB m mo, LHEAPd SPB LB m mo ->
  rw_cells usegs m PGOT_SSP [C8 (wz PSSP)] /\ exists canary : word, rw_cells usegs m PSSP [C8 canary].
Proof using .
  intros SPB LB m mo (s & LBi & B & (st & LB0 & _ & _ & MR & _) & _).
  destruct MR as (_ & _ & (_ & _ & _ & G1 & G2) & _). split; [exact G1| eexists; exact G2].
Qed.

(* [comment removed for export] *)
Lemma RHEAP_block_region : forall s LBi m b, RHEAP s LBi m -> In b LBi ->
  exists base top, base <= blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b + IB <= top /\ top mod 8 = 0
    /\ wr_at usegs m base (top - base) /\ (top <= 0x10000 \/ 0x56000 <= base) /\ 0 <= base /\ top <= alloc_ceiling.
Proof.
  intros s LBi m b (st & LB0 & HP & _ & MR & [_ AR]) Hin.
  assert (Hin0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
  (nelim (areach_block_span st LB0 b AR Hin0) 12%nat; intros r lo hi Hr Kr Hlo A1 Z1 A2 Hhi M1 M2).
  (nelimp MR 6%nat; intros WF _ _ _ _ SH). (nelimp WF 3%nat; intros _ WR _).
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF). destruct (SH _ _ Hr Kr) as [W _].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (RP : 0 < round_up_pg (r_len r)) by (unfold IB in A2; lia).
  pose proof (rreserved_disjoint1 _ _ RF RP) as D.
  exists (r_base r), (r_base r + hi). splits; try lia.
  (nelim W 3%nat; intros W0 W1 W2). split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
Qed.

Lemma lhd_block_wr : forall SPB LB m mo A n, LHEAPd SPB LB m mo -> In (A, n) LB -> wr_at usegs m A n.
Proof using .
  intros SPB LB m mo A n (s & LBi & B & HR & -> & _) Hin. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  destruct (RHEAP_block_region s LBi m b HR Hb) as (base & top & H1 & H2 & H3 & H4 & (W0 & W1 & W2) & H5 & H6 & H7).
  split; [lia|]. split; [unfold IB in H3; pose proof KStep.alloc_ceiling_lt; lia|]. intros i Hi.
  replace (blk_addr b + i) with (base + (blk_addr b + i - base)) by lia. apply W2. unfold IB in H3. lia.
Qed.

Lemma lhd_block_slack : forall SPB LB m mo A n i, LHEAPd SPB LB m mo -> In (A, n) LB ->
  0 <= i -> (A + n + i) < (A + n + 7) / 8 * 8 -> m (wa (A + n + i)) <> None.
Proof using .
  intros SPB LB m mo A n i (s & LBi & B & HR & -> & _) Hin Hi Hlt. (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-).
  destruct (RHEAP_block_region s LBi m b HR Hb) as (base & top & H1 & H2 & H3 & H4 & (W0 & W1 & W2) & H5 & H6 & H7).
  pose proof KStep.alloc_ceiling_lt as Hcl. unfold IB in H3.
  assert (Htop : (blk_addr b + blk_size b + 7) / 8 * 8 <= top).
  { pose proof (Z_div_mod_eq_full (blk_addr b + blk_size b + 7) 8). pose proof (Z.mod_pos_bound (blk_addr b + blk_size b + 7) 8).
    pose proof (Z_div_mod_eq_full top 8). lia. }
  specialize (W2 (blk_addr b + blk_size b + i - base) ltac:(lia)).
  replace (base + (blk_addr b + blk_size b + i - base)) with (blk_addr b + blk_size b + i) in W2 by lia.
  rewrite ref_wview_overlay in W2; [exact W2|]. unfold wa. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nonempty_ivs (W : list ivl) : list ivl := List.filter (fun iv => fst iv <? snd iv) W.

Lemma outside_nonempty : forall W x, outside (nonempty_ivs W) x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exact I|]. cbn [nonempty_ivs List.filter fst snd] in H.
  destruct (Z.ltb_spec lo hi); cbn in H |- *.
  - destruct H as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact H].
Qed.

Lemma munch_nonempty : forall W m m', munch W m m' -> munch (nonempty_ivs W) m m'.
Proof using . intros W m m' H. eapply munch_weaken; [| exact H]. intros x Hx. apply outside_nonempty. exact Hx. Qed.

(* [comment removed for export] *)
Definition ivs_disjoint (W : list ivl) (a n : Z) : Prop :=
  forall lo hi, In (lo, hi) W -> lo < hi -> a + n <= lo \/ hi <= a.

Lemma disjoint_from_nonempty : forall W a n, ivs_disjoint W a n -> disjoint_from (nonempty_ivs W) a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; [exact I|]. cbn [nonempty_ivs List.filter fst snd].
  destruct (Z.ltb_spec lo hi).
  - cbn. split; [apply (H lo hi); [left; reflexivity| lia]|]. apply IH. intros lo' hi' Hin Hlt. apply H; [right; exact Hin| exact Hlt].
  - apply IH. intros lo' hi' Hin Hlt. apply H; [right; exact Hin| exact Hlt].
Qed.

Lemma munch_eq_at : forall W m m' x, munch W m m' -> ivs_disjoint W x 1 -> 0 <= x < 2^64 -> m' (wa x) = m (wa x).
Proof using .
  intros W m m' x HM HD Hx. apply (munch_nonempty _ _ _ HM). unfold wa. rewrite unsigned_lit by lia.
  eapply disjoint_outside; [apply disjoint_from_nonempty; exact HD| lia].
Qed.

Lemma bytes_at_munch : forall W m m' a bs, munch W m m' -> bytes_at usegs m a bs -> ivs_disjoint W a (Z.of_nat (length bs)) ->
  bytes_at usegs m' a bs.
Proof using .
  intros W m m' a bs HM (H0 & H1 & HB) HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  rewrite (munch_eq_at W m m' (a + Z.of_nat i) HM); [reflexivity| | lia].
  intros lo hi Hin Hlt. pose proof (HD lo hi Hin Hlt). lia.
Qed.

Lemma rw_cells_munch : forall W m m' a cs, munch W m m' -> wmono usegs m m' -> rw_cells usegs m a cs ->
  ivs_disjoint W a (Z.of_nat (cells_size cs)) -> rw_cells usegs m' a cs.
Proof using .
  intros W m m' a cs HM HW [[Hwf HB] HWR] HD. split; [split; [exact Hwf|]|].
  - eapply bytes_at_munch; eauto. rewrite cells_bytes_length by assumption. exact HD.
  - eapply wr_at_transport; eauto.
Qed.

Lemma rauxv_ok_munch : forall W m m' B, munch W m m' -> wmono usegs m m' -> rauxv_ok m B ->
  (forall lo hi, In (lo, hi) W -> lo < hi -> (alloc_ceiling <= lo /\ hi <= B) \/ (hi <= RLIBC /\ lo < alloc_ceiling) \/ (0x56000 <= lo /\ hi <= alloc_ceiling)) ->
  rauxv_ok m' B.
Proof using .
  intros W m m' B HM HW (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H1 & H2 & H3 & H4) HWok.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H4]]].
  - eapply rw_cells_munch; eauto. cbn [cells_size csize Nat.add]. unfold RAUXV_CELL. intros lo hi Hin Hlt.
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite u64s_length. unfold auxv_list. rewrite length_map. cbn [length Nat.mul Nat.add].
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
  - eapply bytes_at_munch; eauto. intros lo hi Hin Hlt. rewrite length_le8. (* [comment removed for export] *)
    destruct (HWok lo hi Hin Hlt) as [D|[D|D]]; unfold alloc_ceiling, RLIBC in *; lia.
Qed.

Lemma lhd_frame : forall SPB LB m m' mo W,
  LHEAPd SPB LB m mo -> munch W m m' -> wmono usegs m m' -> Forall (cj_write_ok SPB LB) W -> LHEAPd SPB LB m' mo.
Proof using .
  intros SPB LB m m' mo W (s & LBi & B & HR & -> & HO & HM & HA & HS) MU WM FW.
  pose proof (proj1 (Forall_forall _ _) FW) as FW'.
  assert (HB : alloc_ceiling <= B) by ((nelim HA 15%nat; intros ? ? ? ? ? ? ? ? ? ? _ _ _ HB _); exact HB).
  exists s, LBi, B. splits; auto.
  - apply (RHEAP_frame_proof s LBi m m' (nonempty_ivs W) HR (munch_nonempty _ _ _ MU) WM).
    apply Forall_forall. intros [lo hi] Hin. unfold nonempty_ivs in Hin. apply List.filter_In in Hin as [Hin Hlt]. cbn [fst snd] in Hlt. apply Z.ltb_lt in Hlt.
    specialize (FW' _ Hin). unfold cj_write_ok, rclient_write_ok in *. cbn [fst snd] in *. (* [comment removed for export] *)
    unfold PERRNO, PGERROR, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    right; right. (nelim (in_bview _ _ _ HinB) 4%nat; intros b Hb <- <-). exists b. auto.
  - eapply rauxv_ok_munch; eauto. intros lo hi Hin Hlt. specialize (FW' _ Hin).
    unfold cj_write_ok in FW'. cbn [fst snd] in FW'. (* [comment removed for export] *) unfold PERRNO, PGERROR, RLIBC, alloc_ceiling in *.
    destruct FW' as [E|[ST|[ER|[GE|(A & n & HinB & HA1 & HA2)]]]]; [lia| left; lia| right; left; lia| right; left; lia|].
    (nelim (in_bview _ _ _ HinB) 4%nat; intros b Hb <- <-).
    (nelimp (RHEAP_block_range_proof s LBi m b HR Hb) 5%nat; intros R1 R2 R3 R4 R5). unfold alloc_ceiling in R4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lb_remove_cons : forall p b LB, lb_remove p (b :: LB) = if bptr_eqb (blk_id b) p then lb_remove p LB else b :: lb_remove p LB.
Proof using . intros p b LB. unfold lb_remove. cbn. destruct (bptr_eqb (blk_id b) p); reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true <-> p = q.
Proof using .
  intros [c o] [c' o']. unfold bptr_eqb. cbn [fst snd]. rewrite andb_true_iff, MI_Kit.aptr_eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros E; injection E as -> ->; auto].
Qed.

Lemma RHEAP_slot_nodup : forall s LBi m, RHEAP s LBi m -> List.NoDup (map blk_slot LBi).
Proof.
  intros s LBi m nelH_; (nelim nelH_ 6%nat; intros st LB0 HP _ _ [_ AR]). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP| exact ND].
Qed.

Lemma lb_remove_notin : forall p LBi, ~ In (fst p) (map blk_slot LBi) -> lb_remove p LBi = LBi.
Proof using .
  intros p LBi. induction LBi as [|b LBi IH]; intros Hni; [reflexivity|]. rewrite lb_remove_cons.
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - exfalso. apply bptr_eqb_eq in E. apply Hni. left. unfold blk_slot, blk_id in *. rewrite E. reflexivity.
  - rewrite IH; [reflexivity|]. intros Hin. apply Hni. right. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_views : forall LBi p A n,
  List.NoDup (map blk_slot LBi) -> List.NoDup (map blk_addr LBi) -> In (p, A, n) LBi ->
  map blk_slot (lb_remove p LBi) = ap_remove (fst p) (map blk_slot LBi)
  /\ map bview (lb_remove p LBi) = cb_remove A (map bview LBi)
  /\ (forall b, In b (lb_remove p LBi) <-> In b LBi /\ b <> (p, A, n)).
Proof using .
  induction LBi as [|b LBi IH]; intros p A n NDs NDa Hin; [destruct Hin|].
  cbn [map] in NDs, NDa. inversion NDs as [|? ? Hs NDs']; subst. inversion NDa as [|? ? Ha NDa']; subst.
  rewrite lb_remove_cons. cbn [map ap_remove cb_remove bview].
  destruct Hin as [->|Hin].
  - cbn [blk_id blk_slot blk_addr blk_size fst snd]. rewrite (proj2 (bptr_eqb_eq p p) eq_refl), MI_Kit.aptr_eqb_refl, Z.eqb_refl.
    cbn [blk_slot blk_addr fst snd] in Hs, Ha. rewrite (lb_remove_notin p LBi Hs).
    splits; [reflexivity| reflexivity|]. intros b'. split.
    + intros Hb'. split; [right; exact Hb'|]. intros ->. apply Hs. apply in_map_iff. exists (p, A, n). auto.
    + intros [[<-|Hb'] Hne]; [congruence| exact Hb'].
  - assert (Hsl : blk_slot b <> fst p). { intros E. apply Hs. rewrite E. apply in_map_iff. exists (p, A, n). auto. }
    assert (Had : blk_addr b <> A). { intros E. apply Ha. rewrite E. apply in_map_iff. exists (p, A, n). auto. }
    destruct (bptr_eqb (blk_id b) p) eqn:E.
    { exfalso. apply bptr_eqb_eq in E. apply Hsl. unfold blk_slot, blk_id in *. rewrite E. reflexivity. }
    destruct (aptr_eqb (blk_slot b) (fst p)) eqn:E2. { exfalso. apply MI_Kit.aptr_eqb_eq in E2. exact (Hsl E2). }
    destruct b as [[q B] k]. cbn [blk_addr fst snd] in Had |- *. rewrite (proj2 (Z.eqb_neq B A) Had).
    (nelim (IH p A n NDs' NDa' Hin) 3%nat; intros IH1 IH2 IH3). cbn [map]. rewrite IH1, IH2. splits; [reflexivity| reflexivity|].
    intros b'. split.
    + intros [<-|Hb']; [split; [left; reflexivity| intros E3; injection E3 as -> -> ->; exact (Had eq_refl)]|].
      apply IH3 in Hb'. destruct Hb'. split; [right; assumption| assumption].
    + intros [[<-|Hb'] Hne]; [left; reflexivity| right]. apply IH3. auto.
Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_rheap_pres : forall LBi SP m m', rheap_pres LBi SP m m' -> cj_pres (map bview LBi) SP m m'.
Proof.
  intros LBi SP m m' H a Ha Hc. apply H; [exact Ha|].
  unfold cj_client_addr, rclient_addr, palloc_static, ralloc_static, in_cblock, in_block in *.
  unfold PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP, PDATA_LO, PIMG_HI, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct Hc as [Hc|[Hc|(A & n & Hin & Hr)]]; [left; exact Hc| right; left; exact Hc| right; right].
  (nelim (in_bview _ _ _ Hin) 4%nat; intros b Hb <- <-). exists b. auto.
Qed.

Lemma errno_addr_PTP : bv_unsigned (wz PTP) + -164 = PERRNO.
Proof using . reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem lhd_malloc : malloc_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) HSP ST Hlo Hlo2 ER MI Htp Ha0 Hn.
  (* [comment removed for export] *)
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi n lo B errv
                HR HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Hn) as Himpl.
  pose proof (raw_malloc_etwf (map blk_slot LBi) s mo n HO ltac:(lia)) as Hwf.
  eapply scps_mono; [apply (implM_scps usegs (raw_malloc n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  (nelim HQ 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv' -> MI' ST' ER' HA' HP _ _ Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  split; [apply cj_pres_of_rheap_pres; exact HP|].
  destruct r as [[c off]|].
  - (nelim Hr 7%nat; intros A junk -> HRng HR' RW _). (nelim HRr 4%nat; intros HO' Hni _ _). cbn [fst snd] in HO'.
    right. exists A, junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + rewrite map_fst_bview. pose proof (RHEAP_addr_nodup _ _ _ HR') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; assumption.
    + split; [| exact RW]. exists s'. exists (((c, off), A, n) :: LBi). exists B. splits; auto.
  - destruct Hr as [-> HR']. left. split; [reflexivity|]. exists s', LBi, B. splits; auto.
Qed.

Theorem lhd_free : free_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB A n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) Hin HSP ST Hlo Hlo2 ER MI Htp Ha0.
  (* [comment removed for export] *)
  destruct (in_bview _ _ _ Hin) as ([[p A'] n'] & Hb & E1 & E2). cbn [blk_addr blk_size fst snd] in E1, E2. subst A' n'.
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi p A n lo B errv
                HR Hb HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0) as Himpl.
  assert (Hinp : In (fst p) (map blk_slot LBi)). { apply in_map_iff. exists (p, A, n). auto. }
  pose proof (raw_free_etwf (map blk_slot LBi) s mo p HO Hinp) as Hwf.
  (nelim (lb_remove_views LBi p A n (RHEAP_slot_nodup _ _ _ HR) (RHEAP_addr_nodup _ _ _ HR) Hb) 3%nat; intros V1 V2 V3).
  eapply scps_mono; [apply (implM_scps usegs (raw_free p) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & _ & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  (nelim HQ 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ER' HA' HP _ _ HR').
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  rewrite <- V2. split; [apply cj_pres_of_rheap_pres; exact HP|].
  exists s', (lb_remove p LBi), B. rewrite V1. splits; auto.
Qed.

Theorem lhd_free_null : free_null_stmt.
Proof using . exact rfree_null_spec. Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End CJ_heap_inst0.

(* [comment removed for export] *)
Module CJ_heap_inst.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP RF_malloc_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface.
Import CJ_heap_inst0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Theorem lhd_realloc_null : rrealloc_null_stmt -> realloc_null_stmt LHEAPd.
Proof.
  intros RN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB n lo errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) HSP ST Hlo Hlo2 ER MI Htp Ha0 Ha1 Hn.
  (* [comment removed for export] *)
  pose proof (RN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi n lo B errv
                HR HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Ha1 Hn) as Himpl.
  pose proof (raw_malloc_etwf (map blk_slot LBi) s mo n HO ltac:(lia)) as Hwf.
  eapply scps_mono; [apply (implM_scps usegs (raw_malloc n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ER' & HA' & HP & _ & _ & Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  split; [apply cj_pres_of_rheap_pres; exact HP|].
  destruct r as [[c off]|].
  - destruct Hr as (A & junk & -> & HRng & HR' & RW & _). destruct HRr as (HO' & Hni & _ & _). cbn [fst snd] in HO'.
    right. exists A, junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + rewrite map_fst_bview. pose proof (RHEAP_addr_nodup _ _ _ HR') as ND. cbn [map blk_addr fst snd] in ND. inversion ND; assumption.
    + split; [| exact RW]. exists s'. exists (((c, off), A, n) :: LBi). exists B. splits; auto.
  - destruct Hr as [-> HR']. left. split; [reflexivity|]. exists s', LBi, B. splits; auto.
Qed.

(* [comment removed for export] *)
Definition PHI (Hrealloc : realloc_scps_stmt LHEAPd) (Hrealloc_null : rrealloc_null_stmt) : cj_heap_iface :=
  mkCJHI LHEAPd
    lhd_mok lhd_frame lhd_perm lhd_lower lhd_block_range lhd_blocks_disjoint lhd_nodup lhd_block_wr lhd_block_slack lhd_ssp
    lhd_malloc lhd_free lhd_free_null Hrealloc (lhd_realloc_null Hrealloc_null).


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
End CJ_heap_inst.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module RF_realloc_mentry.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.F_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_get_meta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMalloc_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_malloc_enf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RAllocSlot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B.RF_malloc_entry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_join OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core.RF_malloc_small OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_malloc_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
(* [comment removed for export] *)

Import RF_malloc_top.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.ASlot_I OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RASlot_I RF_alloc_slot RF_malloc_big OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta.RF_am_P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_alloc_meta.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition RMALLOC_ESTACK : Z := 8128.

(* [comment removed for export] *)
Definition rmalloc_entry_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_ESTACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM usegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).

Section CORE8128.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Lemma rmalloc_core_implT8128 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
  RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
  rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8128 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
  rimplT m (malloc_core full_lay (set_tick t st) n) s
        (rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Proof.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. (nelimp (rregion_facts st m rid r1 MR H1) 4%nat; intros X1 _ X2 _). unfold alloc_ceiling in X2. lia. }
  (nelimp MR 4%nat; intros WF0 CX0 GL0 _). (nelim GL0 3%nat; intros _ NL _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. unfold alloc_ceiling in CLO.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
    split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
    split. { eapply unk_agree_munch; [| exact MU| |].
             - eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
             - intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
             - intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
  destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
  - (* [comment removed for export] *)
    riprefixT. eapply evt_cut.
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI]. }
    intros ms' nelH_; (nelim nelH_ 8%nat; intros a1' m1 -> FR ST1 MU WM MI1).
    (nelim (PREP m1 MU WM) 6%nat; intros MR1 TK1 UA1 ERR1 AUX1 PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
    intros ms' nelH_; (nelim nelH_ 11%nat; intros a0' a1' a2' a3' m1 -> FR ST1 MU WM MI1).
    (nelim (PREP m1 MU WM) 6%nat; intros MR1 TK1 UA1 ERR1 AUX1 PE1).
    (nelimp (size_to_class_props n ltac:(lia)) 3%nat; intros SCR SFIT _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE8128.

Local Set Keyed Unification.
Section TOPLEVEL8128.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQe (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_entry_spec_proof : rmalloc_entry_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_ESTACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
  (nelim HEAP 6%nat; intros st LB0 HPERM Hst MR [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  unfold raw_malloc.
  eapply (implM_bind usegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  eapply (implM_bind usegs _ _ _ (rmidQe m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT8128 as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQe. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  (nelim MQ 9%nat; intros st2 r ans o1 Ecs Ec F1 F2 CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind usegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 40%nat; intros b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO MREL BL2 PSM PSF PSO)
.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    (nelimp (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) 4%nat; intros R4 RAL RC RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    unfold alloc_ceiling in RC, CLO. unfold RMALLOC_ESTACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    (nelim EP 25%nat; intros st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF).
    (nelim LEAF 7%nat; intros off OFF0 FIT Ep Est' Ep2 Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    (nelimp (strip_eq_proj _ _ SE) 8%nat; intros Ec Er En Em _ _ Esl Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. nexists 15%nat. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - clear - Ha X RI1 SPAN SKL SK B0 S16. first [heap_lia_imp | lia]. }   (* [comment removed for export] *)
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { unfold rblock_range, alloc_ceiling. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). clear - N0' RC RI1 SPAN SKL SK B0 FIT OFF0 S16. lia. }  (* [comment removed for export] *)
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    (nelim CQ 29%nat; intros m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO)
.
    apply evt_done. unfold rmalloc_post. nexists 15%nat. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL8128.


Theorem rmalloc_entry_spec : rmalloc_entry_stmt.
Proof.
  exact (rmalloc_entry_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.


End CeilWrap.
End RF_realloc_mentry.

(* [comment removed for export] *)
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSoundMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocksR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_mremap.
Module RF_realloc_G1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma implM_msys_of_impl {A} n (dec : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms :
  impl usegs (at_node usegs) (enode n dec) (epost P) ms ->
  implM usegs (msys n dec) s (fun a s' ms' => s' = s /\ P a ms') ms.
Proof.
  intros H. unfold implM, msys. cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (dec rsp) as [a|]; cbn in Hk |- *.
  - eapply evt_mono; [exact Hk|]. intros ms' HP. split; [reflexivity| exact HP].
  - exact Hk.
Qed.

(* [comment removed for export] *)
Lemma idx_land i res : 0 <= i < 32 -> 0 <= res -> Z.land (i + 32 * Z.min res 5) 31 = i.
Proof using .
  intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
  replace (i + 32 * Z.min res 5) with (i + Z.min res 5 * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma rsv_shiftr i res : 0 <= i < 32 -> 0 <= res -> Z.shiftr (i + 32 * Z.min res 5) 5 = Z.min res 5.
Proof using .
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. replace (i + 32 * Z.min res 5) with (i + Z.min res 5 * 32) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma addr_mod16 rb sb st i off : rb mod 4096 = 0 -> sb mod 16 = 0 -> st mod 16 = 0 -> (rb + sb + 16 + st * i + 16 * off) mod 16 = 0.
Proof using .
  intros H H0 H1. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide in H0; [|lia]. apply Z.mod_divide in H1; [|lia].
  destruct H as [x ->]. destruct H0 as [y ->]. destruct H1 as [z ->].
  apply Z.mod_divide; [lia|]. exists (x * 256 + y + 1 + z * i + off). lia.
Qed.
Lemma q_small_class (stride sz i off k q : Z) : 0 <= i -> 0 <= off -> 0 <= k -> 16 * off + k <= stride - 4 ->
  16 * q = stride * i + 16 * off -> (stride = 16 * sz \/ (i = 0 /\ (stride <= 16 * sz \/ 256 <= sz))) -> off <= 255 ->
  sz * i <= q < sz * (i + 1).
Proof using .
  intros Hi Ho Hk Hfit EQ D O255. destruct D as [->|[-> D]].
  - assert (Hq : q = sz * i + off) by nia. subst q. clear EQ. assert (off < sz) by lia. nia.
  - rewrite Z.mul_0_r, Z.add_0_l in EQ. assert (q = off) by lia. subst q. lia.
Qed.
Lemma q_maplen (stride i off k q maplen : Z) : 0 <= i -> 0 <= off -> 0 <= k -> 16 * off + k <= stride - 4 ->
  16 * q = stride * i + 16 * off -> 16 + stride * (i + 1) <= maplen * 4096 -> q <= maplen * 256 - 1.
Proof using . intros. nia. Qed.

(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac liac := clear_complex; lia.

Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at usegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.

(* [comment removed for export] *)
Definition Xstride : Z := get_stride (MR st g).
Definition XP0 : Z := conc st (fst p).
Definition XE : Z := XP0 + Xstride - IB.
Definition Xres : Z := XE - A - k.
Definition XB : Z := conc st b.
Definition XG : Z := conc st g.
Definition Xmword : Z := meta_word (MR st g).
Definition Xsc : Z := m_sizeclass (MR st g).
Definition Xq : Z := (snd (fst p) + UNIT * off - snd b - UNIT) / UNIT.

(* [comment removed for export] *)
Definition rr_mid_post : machine_state -> Prop :=
  fun ms' => exists m1 t3' t4',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 XE) (Z_to_bv 64 (XB + Xstride * i + 16)) (wz 0)
                  s0 (wz XG) a0 a1 (wz XB) (Z_to_bv 64 Xsc) (wz Xmword) (Z_to_bv 64 RSIZE_CLASSES) (Z_to_bv 64 (XE + 4)) (Z_to_bv 64 (XE + - bv_unsigned a0))
                  (Z_to_bv 64 (XE - Xres)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
             F (Z_to_bv 64 0x17eb8) fc None m1 (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
    /\ stk usegs m1 lo (bv_unsigned sp + -64)
    /\ rw_cells usegs m1 (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6).

Lemma rr_prefix :
  evt usegs rr_mid_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).
Proof using A0 A1 LEN LO MI N RF SLO ST.
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH _].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. unfold alloc_ceiling in LO, RC, G40.
  (* [comment removed for export] *)
  unfold RREALLOC_SYM. step. change (Z_to_bv 64 97492) with (Z_to_bv 64 rrealloc_entry).
  pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr. pose proof (go_freeable _ _ _ GOK) as FB.
  pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. pose proof (go_stride _ _ _ GOK) as [S16 SM]. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in LI, AVr, FRr, FB, GSC, ML, S16, SM, TOP.
  unfold rr_mid_post, XE, Xres, XP0, XB, XG, Xmword, Xsc, Xstride.
  set (mr := MR st g) in *.
  set (stride := get_stride mr) in *. assert (Estride : stride = get_stride mr) by reflexivity.
  set (sc := m_sizeclass mr) in *. assert (Esc : sc = m_sizeclass mr) by reflexivity.
  set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (EG : G = conc st g) by reflexivity. assert (EB : B = conc st b) by reflexivity. assert (EP0 : P0 = conc st (fst p)) by reflexivity.
  set (q := (snd (fst p) + UNIT * off - snd b - UNIT) / UNIT) in *.
  set (res := P0 + stride - IB - A - k) in *. assert (Eres : res = P0 + stride - IB - A - k) by reflexivity.
  clearbody stride sc P0 B G q res.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; liac).
  assert (SIL : stride * i + stride <= stride * (m_last_idx mr + 1)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; liac).
  set (si := stride * i) in *. assert (Esi : si = stride * i) by reflexivity. clearbody si.
  set (sl := stride * (m_last_idx mr + 1)) in *. assert (Esl : sl = stride * (m_last_idx mr + 1)) by reflexivity. clearbody sl.
  assert (HP0 : P0 = B + 16 + si) by (rewrite Cc, Cb, Ec; cbn [snd]; unfold UNIT; liac).
  assert (RES : 0 <= res /\ res = stride - IB - UNIT * off - k) by (rewrite Eres, EA; unfold UNIT, IB in *; liac).
  pose proof (idx_land i res ltac:(liac) ltac:(liac)) as IDX.
  assert (B3' : 0 <= i + 32 * Z.min res 5 < 256) by liac.
  assert (AMOD : A mod 16 = 0) by (rewrite EA, HP0, Cb, Esi; unfold UNIT in *; apply addr_mod16; assumption).
  assert (HDR : bytes_at usegs m (A - 4) ([b8 0; b8 (i + 32 * Z.min res 5)] ++ le2 (wz q))).
  { change ([b8 0; b8 (i + 32 * Z.min res 5)] ++ le2 (wz q)) with ([b8 0] ++ ([b8 (i + 32 * Z.min res 5)] ++ le2 (wz q))).
    apply bytes_at_app. split; [exact B4|]. cbn [length]. change (Z.of_nat 1%nat) with 1. replace (A - 4 + 1) with (A - 3) by lia.
    apply bytes_at_app. split; [exact B3|]. cbn [length]. change (Z.of_nat 1%nat) with 1. replace (A - 3 + 1) with (A - 2) by lia. exact B2. }
  assert (MM' : rw_cells usegs m G [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz B); C4 (wz (m_avail mr)); C4 (wz (m_freed mr));
                                  C8 (wz (m_last_idx mr + 32 * m_freeable mr + 64 * sc + 4096 * m_maplen mr))]).
  { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. rewrite <- EB in MM. rewrite Esc. exact MM. }
  unfold alloc_ceiling, UNIT, IB in *.
  assert (SC64 : 0 <= sc < 64) by (clear -GSC; lia).
  assert (SC63 : 48 <= sc -> sc = 63) by (clear -GSC; lia).
  assert (QSC : sc < 48 -> size_class sc * i <= q < size_class sc * (i + 1)).
  { intros Hsc; apply (q_small_class stride (size_class sc) i off k q); try liac.
    destruct (Z.eqb_spec (m_last_idx mr) 0) as [L0|L0].
    + right; split; [liac|]. destruct (SC28 Hsc) as [X|X]; [left; liac| right]. pose proof (MI_WFree.size_class_28 sc ltac:(liac)). liac.
    + left. rewrite Estride. unfold get_stride. replace (m_last_idx mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0). cbn [andb]. rewrite <- Esc. unfold UNIT. lia. }
  eapply evt_cut.
  { eapply (rr_hdr1_walk ra sp gp tp) with (P := A) (n := n) (G := G) (B := B) (A := G - G mod 4096) (b3 := i + 32 * Z.min res 5) (off16 := q)
      (avail := m_avail mr) (freed := m_freed mr) (last_idx := m_last_idx mr) (freeable := m_freeable mr) (sc := sc) (maplen := m_maplen mr) (secret := secret)
      (prev := pw st (m_prev mr)) (next := pw st (m_next mr)) (lo := lo);
    rewrite ?IDX; first [eassumption | idtac].
    all: unfold alloc_ceiling; try first [ match goal with
                 | |- bv_unsigned a0 = A => rewrite A0; apply unsigned_lit; liac
                 | |- bv_unsigned a1 = n => rewrite A1; apply unsigned_lit; liac
                 end
               | liac ].
  }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 7%nat; intros m1 H1 MU1 WM1 MI1 ST1 FR1). (nelim H1 3%nat; intros t3' t4' ->).
  assert (XP : forall a bs, bytes_at usegs m a bs -> a + Z.of_nat (length bs) <= lo -> bytes_at usegs m1 a bs).
  { intros a bs Ha Hl. eapply bytes_at_transport; [exact Ha| exact MU1|]. cbn [disjoint_from]. split; [left; clear -Hl SLO; lia| exact I]. }
  assert (ALE : A + 16 * 0 <= P0 + stride - 4 - k) by liac.
  assert (ELO : P0 + stride - 4 + 1 <= lo) by liac.
  assert (Estr2 : (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - UNIT else UNIT * size_class sc) = stride).
  { rewrite Estride, Esc. reflexivity. }
  assert (RSV : (if 160 <=? i + 32 * Z.min res 5 then res else Z.shiftr (i + 32 * Z.min res 5) 5) = res).
  { destruct (Z.leb_spec 160 (i + 32 * Z.min res 5)); [reflexivity|]. rewrite rsv_shiftr by liac. liac. }
  eapply evt_mono.
  { eapply (rr_hdr2_walk ra) with (P := A) (G := G) (r32 := res); rewrite ?IDX, ?Estr2, ?RSV; first [eassumption| idtac]; unfold UNIT, IB, alloc_ceiling; rewrite <- ?Esi, <- ?HP0.
    - rewrite A0; apply unsigned_lit; liac.
    - liac.
    - liac.
    - liac.
    - intros H160. assert (R5 : 5 <= res) by liac. split; [rewrite rsv_shiftr by liac; liac|]. split; [split; [exact R5| apply BF; exact R5]|].
      split; (apply XP; [apply BF; exact R5| rewrite ?length_le4; cbn [length]; liac]).
    - liac.
    - destruct (Z.eq_dec res 0) as [R0'|R0'].
      + rewrite R0', Z.sub_0_r. apply XP; [exact BE| cbn [length]; liac].
      + apply XP; [apply BC; liac| cbn [length]; liac].
    - apply XP; [exact BE| cbn [length]; liac].
    - liac.
    - liac.
    - liac.
    - liac.
    - intros Hml. destruct (TOP Hml) as [Hb2 Hml2]. apply (q_maplen stride i off k q (m_maplen mr)); liac.
    - intros HH. clear -HH GSC. lia.
  }
  cbv beta. intros ms2 nelH_; (nelim nelH_ 3%nat; intros t3'' t4'' ->). unfold rr_mid_post.
  exists m1, t3'', t4''. split; [| auto 10].
  f_equal. f_equal.
  all: rewrite ?IDX, ?Estr2, ?RSV; unfold XE, XP0, Xstride, UNIT, IB; fold mr; rewrite <- ?EP0, <- ?Estride, <- ?Esi, <- ?HP0.
  all: try reflexivity. all: try (f_equal; liac).
  unfold meta_word. rewrite Esc. reflexivity.
Qed.
Definition Xkb : Z := i + 32 * Z.min Xres 5.
Definition Xup : aptr := aadd (fst p) (UNIT * off).

Lemma brk_link_strip_eq (st1 st2 : mstate) pb : strip st2 = strip st1 -> brk_link st1 pb -> brk_link st2 pb.
Proof.
  intros E H. change (brk_link (strip st2) pb). rewrite E. change (brk_link st1 pb). exact H.
Qed.

Lemma perm_blocks n' : Permutation ((p, A, n') :: lbrm LB0 (p, A, k)) ((p, A, n') :: lb_remove p LB).
Proof using Hin PERM RF.
  apply perm_skip. rewrite (lb_remove_lbrm LB p A k); [apply lbrm_perm; exact PERM| | exact Hin].
  eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ (rf_C _ _ _ _ _ _ _ _ _ _ _ RF))].
Qed.

Lemma rplan_eq : rplan_of (ps_m s) (fst p) A n =
  if (n <=? Xstride - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (Xsc <=? size_to_class n + 1) then RPInPlace
  else if (48 <=? Xsc) && (MMAP_THRESHOLD <=? n)
       then (if negb (Xsc =? 63) then RPUndef else RPRemap (fst b) g XB (m_maplen (MR st g) * 4096) (rr_needed n (UNIT * off)))
       else RPFallback.
Proof using Hst RF old.
  rewrite <- Hst, rplan_of_strip. unfold rplan_of. rewrite (rf_slot _ _ _ _ _ _ _ _ _ _ _ RF).
  change (get_meta_rec st g) with (MR st g). rewrite (rf_mem _ _ _ _ _ _ _ _ _ _ _ RF).
  replace (A - conc st (fst p)) with (UNIT * off) by (rewrite (rf_A _ _ _ _ _ _ _ _ _ _ _ RF); lia).
  reflexivity.
Qed.

Lemma rss_mem_wmono mx P E nn kk : wmono usegs mx (rss_mem mx P E nn kk).
Proof using .
  unfold rss_mem. destruct (5 <=? E - P - nn); destruct (E - P - nn =? 0); repeat apply wmono_write; apply wmono_refl.
Qed.

Lemma rr_inplace_final : forall m1 ms' (errv' : word),
  munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
  n <= XE - A -> XE - A - n < 2^32 ->
  rw_cells usegs m1 (errno_addr tp) [C4 errv'] ->
  rr_ret_post (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 A lo (rss_mem m1 A XE n Xkb) ms' ->
  rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m (Some p) s ms'.
Proof.
  intros m1 ms' errv' MU1 WM1 NFIT RS ERR1 nelH_; (nelim nelH_ 17%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 -> MI' ST').
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO'.
  unfold alloc_ceiling in RC, G40.
  (nelimp MRP 6%nat; intros WF _ _ _ _ SH). (nelimp WF 5%nat; intros Hres WR DJ WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. change (get_meta_rec st g) with (MR st g) in S16, SM.
  unfold XE, XP0, Xstride in *. unfold Xkb, Xres, XE, XP0, Xstride.
  set (stride := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *.
  set (m' := rss_mem m1 A (P0 + stride - IB) n (i + 32 * Z.min (P0 + stride - IB - A - k) 5)) in *.
  unfold IB, UNIT in *.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; liac).
  assert (SIL : stride * i + stride <= stride * (m_last_idx (MR st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; liac. }
  assert (HP0 : P0 = r_base r + snd b + 16 + stride * i) by (rewrite Cc, Ec; cbn [snd]; lia).
  assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> m1 (wa a) = m (wa a)).
  { intros a Ha Na. apply MU1. rewrite wa_unsigned by lia. cbn. lia. }
  assert (AG2 : forall a, 0 <= a < 2^64 -> a <> A - 3 -> ~ (A + n <= a < P0 + stride - 4) -> m' (wa a) = m1 (wa a)).
  { intros a Ha N1 N2. unfold m'. apply rss_mem_outside; rewrite ?wa_unsigned by lia; liac. }
  assert (WMM : wmono usegs m m') by (eapply wmono_trans; [exact WM1| apply rss_mem_wmono]).
  (* [comment removed for export] *)
  set (FP := fun a => (bv_unsigned sp - 64 <= a < bv_unsigned sp) \/ a = A - 3 \/ (A + n <= a < P0 + stride - 4)).
  assert (PE : rpres_except FP m m').
  { intros a Ha NC. subst FP. cbv beta in NC. split.
    - rewrite AG2 by liac. apply AG1; liac.
    - apply WMM. }
  assert (AMOD : A mod 16 = 0) by (rewrite EA, HP0; apply addr_mod16; assumption).
  assert (SP' : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) + 64) = sp).
  { rewrite unsigned_lit by liac. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  rewrite SP'. rewrite unsigned_lit in ST' by liac. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in ST' by lia.
  unfold rrealloc_post. exists w0, w1, w2, (Z_to_bv 64 A), w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rrw_cells_agree'; [exact ERR1|]. intros a Ha. rewrite TP in Ha. unfold RATP in Ha. rewrite unsigned_lit in Ha by lia. cbn in Ha. apply AG2; destruct RI as [RI'|RI']; liac. }
  split. { eapply rauxv_ok_pres_B; [exact AV| exact PE| |]; subst FP; cbv beta; intros a Ha; unfold RAUXV_CELL in *; destruct RI as [RI'|RI']; liac. }
  split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n /\ (Z.to_nat mn <= length old)%nat) by (subst mn; liac).
  assert (W' : wr_at usegs m' A n).
  { eapply wr_at_transport; [| exact WMM]. eapply wr_at_sub; [exact HWr| liac| liac]. }
  (nelim (rwr_at_bytes_exist m' (A + mn) (n - mn) ltac:(eapply wr_at_sub; [exact W'| liac| liac]) ltac:(liac) ltac:(destruct RI as [RI'|RI']; liac)) 3%nat; intros junk JL JB).
  assert (OB : bytes_at usegs m' A (firstn (Z.to_nat mn) old)).
  { eapply rbytes_at_agree with (m := m).
    - pose proof BA as BA'. rewrite <- (firstn_skipn (Z.to_nat mn) old) in BA'. apply bytes_at_app in BA'. exact (proj1 BA').
    - intros a Ha. rewrite firstn_length_le in Ha by (clear - MN; lia).
      rewrite AG2 by (clear - Ha MN EA Ho Hk Hfit HP0 R0 B0 SI0 SIL SPAN RC N NFIT; lia).
      apply AG1; clear - Ha MN EA Ho Hk Hfit HP0 R0 B0 SI0 SIL SPAN RC N NFIT LO' SLO; lia. }
  exists A, junk. split; [reflexivity|].
  split. { unfold rblock_range, alloc_ceiling. split; [liac|]. split; [exact AMOD|]. split; [liac|]. split; [liac|]. destruct RI as [RI'|RI']; [left|right]; liac. }
  split.
  2:{ split; [| split; [| left; reflexivity]].
      - intros a Ha CA. apply PE; [exact Ha|]. subst FP; cbv beta.
        destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]]; [liac| destruct RI as [RI'|RI']; liac|].
        rewrite (lb_remove_lbrm LB p A k) in Hb' by (first [exact Hin | eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ C)]]).
        apply (In_lbrm_perm LB LB0) in Hb'; [| apply Permutation_sym; exact PERM].
        unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [HinL NEQ].
        assert (NES : blk_slot blk' <> fst p). { intros E. cbn [blk_slot fst] in NEQ. rewrite E, MI_Kit.aptr_eqb_refl in NEQ. exact NEQ. }
        destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
        (nelim (WR _ _ Hrg) 5%nat; intros _ _ _ RGC _). unfold alloc_ceiling in RGC.
        destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EQR|NER].
        + destruct (OTH blk' HinL NES EQR) as [O|O]; clear - Hab O EA Ho Hk Hfit NFIT AEND RGC LO' SLO N; lia.
        + destruct (DJ _ _ _ _ Hrg Hr NER) as [D|D]; rewrite ?(lr_lo_group _ Krg), ?(lr_lo_group _ Kr) in D; clear - Hab A16 AEND D HP0 B0 SI0 SIL SPAN EA Ho Hk Hfit N NFIT RGC LO' SLO; lia.
      - apply rw_cells_of_bytes.
        + cbn. rewrite firstn_length_le by liac. split; [reflexivity|]. split; [exact JL| exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OB|]. rewrite firstn_length_le by liac. rewrite Z2Nat.id by liac. exact JB.
        + cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_add, !Z2Nat.id by liac. replace (mn + (n - mn)) with n by lia. exact W'. }
  exists (rr_inplace_full st (fst p) Xup n), ((p, A, n) :: lbrm LB0 (p, A, k)).
  split; [apply perm_blocks|].
  split; [rewrite strip_rr_inplace_full; exact Hst|].
  pose proof (go_li _ _ _ GOK) as LI. change (get_meta_rec st g) with (MR st g) in LI.
  split.
  - (* [comment removed for export] *)
    unfold rr_inplace_full. rewrite Hs. cbv zeta.
    set (st1 := set_tick (N.succ (s_tick st)) st).
    set (e := aadd (fst p) (get_stride (get_meta_rec st g) - IB)).
    set (kb := i + 32 * Z.min (P0 + stride - 4 - A - k) 5) in *.
    assert (MR1 : rmrep st1 m1).
    { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MRP| exact MU1| exact WM1|].
      intros lo' hi' [E|[]]. injection E as <- <-. unfold alloc_ceiling. clear - LO' SLO; lia. }
    assert (TK1 : ticks_ok st1) by (apply ticks_ok_set_tick; [cbn; lia| exact (ci_ticks _ _ C)]).
    assert (Hr1 : s_regions st1 !! (fst Xup) = Some r). { unfold Xup, aadd. cbn [fst s_regions set_tick st1]. rewrite Ec. exact Hr. }
    assert (Fe : fst e = fst Xup) by reflexivity.
    assert (P4 : 4 <= snd Xup). { unfold Xup, aadd. rewrite Ec. cbn [fst snd]. unfold UNIT. clear - B0 SI0 Ho; lia. }
    assert (PNE : snd Xup + n <= snd e). { unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - NFIT EA; lia. }
    assert (EHI : snd e + 1 <= round_up_pg (r_len r)). { unfold e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - SIL SPAN SI0 B0; lia. }
    assert (RS' : snd e - snd Xup - n < 2^32). { unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. rewrite Ec. cbn [fst snd]. unfold IB, UNIT. clear - RS EA; lia. }
    assert (IDX : 0 <= i < 32) by (clear - Hi LI; lia).
    assert (KB : 0 <= kb < 256 /\ Z.land kb 31 = i). { subst kb. split; [clear - IDX EA Hfit Hk; lia| apply idx_land; [exact IDX| clear - EA Hfit Hk; lia]]. }
    assert (NOGRP : forall b' gh, s_groups st1 !! b' = Some gh -> fst b' = fst Xup -> snd b' + 9 <= snd Xup - 3 \/ snd e + 1 <= snd b').
    { intros b' gh Hb' Eb'. unfold Xup, e, aadd. change (get_meta_rec st g) with (MR st g). fold stride. unfold IB.
      unfold Xup, aadd in Eb'. rewrite Ec in Eb'. cbn [fst] in Eb'.
      destruct (NOG b' gh Hb' Eb') as [O|O]; rewrite Ec; cbn [fst snd]; unfold UNIT; [left| right]; clear - O HP0 Cc Ho Hk Hfit N; lia. }
    pose proof (rmrep_set_size_i st1 m1 Xup e r n i kb MR1 TK1 Hr1 Kr Fe P4 (proj1 N) PNE EHI RS' IDX KB NOGRP) as SS.
    replace (r_base r + snd Xup) with A in SS by (unfold Xup, aadd; cbn [snd]; unfold UNIT; clear - EA Cc HP0; lia).
    replace (r_base r + snd e) with (P0 + stride - 4) in SS by (unfold e, aadd; cbn [snd]; change (get_meta_rec st g) with (MR st g); fold stride; unfold IB; clear - Cc HP0; lia).
    destruct SS as [R1 T1]. exact (proj1 (rmrep_havoc _ _ Xup n R1 T1)).
  - split.
    + eapply brk_link_strip_eq; [| exact BLK]. rewrite strip_rr_inplace_full. reflexivity.
    + eapply areach_ext; [exact AR|]. apply (aext_inplace ref_reserved st LB0 p A k n off Hin0 (proj1 Ho)).
      * exact EA.
      * liac.
      * intros g' i' E. rewrite Hs in E. injection E as <- <-. fold stride. unfold UNIT, IB. clear - NFIT RS EA; lia.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Notation RAREACH := (AREACH_from ref_reserved).
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac liac := clear_complex; lia.
End RF_realloc_G1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_P.
Module RF_realloc_G2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_P RF_realloc_G1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.
Ltac clear_keep := repeat match goal with K : keep _ |- _ => clear K end.
(* [comment removed for export] *)
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; clear_keep; lia.
Ltac liak1 H := prune; unfold keep in H; clear_keep; lia.
Ltac liak2 H1 H2 := prune; unfold keep in H1, H2; clear_keep; lia.
Ltac liak3 H1 H2 H3 := prune; unfold keep in H1, H2, H3; clear_keep; lia.

Notation RAREACH := (AREACH_from ref_reserved).

Lemma mod16_d d off : d mod 4096 = 0 -> (d + 16 * off + 16) mod 16 = 0.
Proof using .
  intros H. apply Z.mod_divide in H; [|lia]. destruct H as [x ->]. apply Z.mod_divide; [lia|]. exists (256 * x + off + 1). lia.
Qed.

Lemma ctx_cs_remap cs rid g d nn : ctx (cs_remap cs rid g d nn) = ctx cs.
Proof using . unfold cs_remap, upd_meta, upd_region, get_region, ctx. cbn. destruct (s_regions cs !! rid); reflexivity. Qed.

Lemma ticks_ok_of_TKS st : TKS st (s_tick st) -> ticks_ok st.
Proof using .
  intros T. split.
  - intros rid sh u hl ch Hsh Hu Hin. exact (proj1 (proj2 (T rid sh Hsh)) u hl ch Hu Hin).
  - intros rid sh pg t Hsh Hpg. exact (proj2 (proj2 (T rid sh Hsh)) pg t Hpg).
Qed.

(* [comment removed for export] *)
Lemma bytes_at_shift m m' a a' bs :
  bytes_at usegs m a bs -> 0 <= a' -> a' + Z.of_nat (length bs) <= 2^64 ->
  (a + Z.of_nat (length bs) <= 0x10000 \/ 0x56000 <= a) -> (a' + Z.of_nat (length bs) <= 0x10000 \/ 0x56000 <= a') ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> m' (wa (a' + j)) = m (wa (a + j))) ->
  bytes_at usegs m' a' bs.
Proof using .
  intros (A0 & A1 & HB) H0 H1 Hi Hi' E. split; [lia|]. split; [lia|].
  intros i Hi2. specialize (HB i Hi2).
  rewrite ref_mrd_overlay in HB by (rewrite wa_unsigned by lia; lia).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). rewrite E by lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma meta_word_remap mr nn : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  0 <= nn < 2^62 -> nn mod 4096 = 0 ->
  meta_word (m_set_maplen (nn / 4096) mr) = Z.lor (Z.land (meta_word mr) 4095) nn.
Proof using .
  intros. unfold meta_word. destruct mr; cbn in *.
  rewrite MI_WRemap.land_ones52 by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (lo := m_last_idx + 32 * m_freeable + 64 * m_sizeclass). assert (Hlo : 0 <= lo < 4096) by lia.
  replace (Z.land (lo + 4096 * m_maplen) 4095) with lo.
  2:{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
      replace (lo + 4096 * m_maplen) with (lo + m_maplen * 4096) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  replace nn with ((nn / 4096) * 2^12) at 2 by (change (2^12) with 4096; pose proof (Z_div_mod_eq_full nn 4096); lia).
  rewrite ASlot_W14.lor_small_shl by (first [apply Z.div_pos; lia | lia]). pose proof (Z_div_mod_eq_full nn 4096). lia.
Qed.
Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at usegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.

(* [comment removed for export] *)
Definition Xstride : Z := get_stride (MR st g).
Definition XP0 : Z := conc st (fst p).
Definition XE : Z := XP0 + Xstride - IB.
Definition Xres : Z := XE - A - k.
Definition XB : Z := conc st b.
Definition XG : Z := conc st g.
Definition Xmword : Z := meta_word (MR st g).
Definition Xsc : Z := m_sizeclass (MR st g).
Definition Xkb : Z := i + 32 * Z.min Xres 5.
Definition Xup : aptr := aadd (fst p) (UNIT * off).

(* [comment removed for export] *)
Variables (d : Z) (m2 mX : mem) (errv2 : word).
Definition Xon : Z := m_maplen (MR st g) * 4096.
Definition Xnn : Z := rr_needed n (UNIT * off).
Hypothesis BIGN : MMAP_THRESHOLD <= n.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Hypothesis D0 : 0 < d.
Hypothesis DA : d mod 4096 = 0.
Hypothesis DCE : d + Xnn <= alloc_ceiling.
Hypothesis DRF : ranges_free ref_reserved d Xnn = true.
Hypothesis DJ : forall q rq, s_regions st !! q = Some rq -> q <> fst b ->
  r_base rq + round_up_pg (r_len rq) <= d \/ d + Xnn <= lr_lo rq.
Hypothesis DISJ : d = XB \/ (XB + Xon <= d \/ d + Xnn <= XB).
Hypothesis MU2 : munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m2.
Hypothesis WM2 : wmono usegs m m2.
Hypothesis ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 errv2].
Hypothesis FR2 : rw_cells usegs m2 (bv_unsigned sp - 64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6).
Hypothesis X1 : forall a, 0 <= a < 2^64 -> ~ (XB <= a < XB + Xon) -> ~ (d <= a < d + Xnn) -> mX (wa a) = m2 (wa a).
Hypothesis X2 : forall j, 0 <= j < Z.min Xon Xnn -> mX (wa (d + j)) = m2 (wa (XB + j)).
Hypothesis X3 : forall j, Z.min Xon Xnn <= j < Xnn -> mX (wa (d + j)) = Some (b8 0).
Hypothesis X4 : wr_at usegs mX d Xnn.
Hypothesis MIX : mem_inv usegs mX.
Hypothesis STX : stk usegs mX lo (bv_unsigned sp + -64).

Lemma perm_blocks' A' n' : Permutation ((p, A', n') :: lbrm LB0 (p, A, k)) ((p, A', n') :: lb_remove p LB).
Proof using Hin PERM RF.
  apply perm_skip. rewrite (lb_remove_lbrm LB p A k); [apply lbrm_perm; exact PERM| | exact Hin].
  eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ (rf_C _ _ _ _ _ _ _ _ _ _ _ RF))].
Qed.

(* [comment removed for export] *)
Lemma rr_remap_final : forall (vra t0' t1' t2' a3' a4' a5' a6' a7' s2' u5 u6 t3' t4' t5' t6' : word),
  evt usegs (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m
               (Some p) (set_m (cs_remap (ps_m s) (fst b) g d Xnn) s))
      (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' (Z_to_bv 64 Xnn) (wz XG) a0 a1 (Z_to_bv 64 d) a3' a4' a5' a6' a7'
               s2' (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) u5 u6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x17fc4) fc None mX (seg_rom usegs)).
Proof using A0 A1 AR AV BA BIGN BLK D0 DA DCE DISJ DJ DRF ERR2 FR2 HB Hin Hin0 Hst LEN LO MIX MRP MU2 N PERM RF SC63 SLO STX TP WM2 X1 X2 X3 X4.
  intros.
  destruct RF as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO', RC, G40, DCE.
  (nelimp MRP 6%nat; intros WF _ _ _ _ SH). (nelimp WF 5%nat; intros Hres WR DJR WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. change (get_meta_rec st g) with (MR st g) in S16, SM.
  pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr. pose proof (go_freeable _ _ _ GOK) as FB.
  pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in LI, AVr, FRr, FB, GSC, ML, TOP.
  (nelimp (rreserved_disjoint _ _ DRF) 4%nat; intros DI1 DI2 DI3 DI4).
  (* [comment removed for export] *)
  assert (L0 : m_last_idx (MR st g) = 0) by (clear -GSC SC63; lia).
  assert (MLP : 0 < m_maplen (MR st g)) by (clear -GSC SC63; lia).
  destruct (TOP ltac:(liac)) as [Hb0 EON].
  assert (I0 : i = 0) by (clear -Hi L0; lia).
  unfold Xon, Xnn, XB, XG, XE, XP0, Xstride, Xres, Xkb, Xup in *.
  set (on := m_maplen (MR st g) * 4096) in *. set (nn := rr_needed n (UNIT * off)) in *.
  set (stride := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (Estride : stride = on - 16).
  { subst stride on. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st g)) 0); [liac|]. cbn. unfold UNIT. liac. }
  assert (HP0 : P0 = B + 16) by (rewrite Cc, Cb, Ec, I0; cbn [snd]; unfold UNIT; liac).
  assert (HBr : B = r_base r) by (rewrite Cb; liac).
  pose proof (rr_needed_facts n (UNIT * off) (proj1 N) ltac:(unfold UNIT; clear -Ho; lia)) as NN. fold nn in NN. unfold UNIT, IB in NN.
  assert (N62 : nn < 2^62) by (clear -NN N Ho; lia).
  unfold UNIT, IB in *.
  set (kb := i + 32 * Z.min (P0 + stride - 4 - A - k) 5) in *.
  assert (KB8 : 0 <= kb < 256 /\ Z.land kb 31 = i) by (subst kb; split; [liac| apply idx_land; liac]).
  (* [comment removed for export] *)
  (nelim MSL 6%nat; intros aa ar kk Haa Hkk Eg).
  (nelim (WA aa ar Haa) 7%nat; intros rga Hra A0a A4096 AMOD NKa LRa).
  assert (HG : G = r_base rga + snd aa + (24 + 40 * kk)).
  { subst G. rewrite Eg. rewrite (conc_region' st (aadd aa (AREA_HDR + META_SIZE * kk)) rga Hra). unfold aadd, AREA_HDR, META_SIZE. cbn [snd]. liac. }
  unfold NSLOTS in Hkk.
  (nelim (WR _ _ Hra) 5%nat; intros Ra0 _ _ RaC RaF). unfold alloc_ceiling in RaC.
  assert (NEa : fst aa <> fst b) by (intros E; rewrite E, Hr in Hra; injection Hra as <-; exact (NKa Kr)).
  pose proof (lr_lo_ge rga) as LRG.
  assert (GND : keep (G + 40 <= d \/ d + nn <= G)) by (unfold keep; destruct (DJ _ _ Hra NEa) as [GD|GD]; liac).
  assert (GNB : keep (G + 40 <= B \/ B + on <= G)).
  { unfold keep. destruct (DJR _ _ _ _ Hra Hr NEa) as [GB|GB]; rewrite ?(lr_lo_group _ Kr) in GB; liac. }
  assert (GNI : keep (G + 40 <= 0x10000 \/ 0x56000 <= G)).
  { unfold keep. destruct (rreserved_disjoint1 _ _ RaF ltac:(liac)) as [X|X]; liac. }
  assert (DNI : keep (d + nn <= 0x10000 \/ 0x56000 <= d)) by (unfold keep; exact (rreserved_disjoint1 _ _ DRF ltac:(liac))).
  assert (RNI : keep (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x56000 <= r_base r)) by exact RI.
  assert (KDISJ : keep (d = B \/ (B + on <= d \/ d + nn <= B))) by exact DISJ.
  clear LRG.
  assert (AG1 : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp) -> m2 (wa a) = m (wa a))
    by (intros a Ha Na; apply MU2; rewrite wa_unsigned by liac; cbn; liac).
  (* [comment removed for export] *)
  assert (MMX : rw_cells usegs mX G [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g))); C8 (wz B); C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g))); C8 (wz (meta_word (MR st g)))]).
  { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. fold B in MM.
    eapply rrw_cells_agree'; [exact MM|]. cbn. intros a Ha. Time rewrite X1 by first [liac | liak1 GNB | liak1 GND]. Time apply AG1; liac. }
  (* [comment removed for export] *)
  assert (BKX : bytes_at usegs mX (d + 16 * off + 16 - 3) [b8 kb]).
  { Time (eapply (bytes_at_shift m mX (A - 3)); [exact B3| liac| cbn; liac| cbn; liak1 RNI| cbn; liak1 DNI|]).
    cbn. intros j Hj. replace (d + 16 * off + 16 - 3 + j) with (d + (16 * off + 13 + j)) by liac. Time rewrite X2 by liac.
    Time replace (B + (16 * off + 13 + j)) with (A - 3 + j) by liac. Time (apply AG1; liac). }
  Time assert (WRX : wr_at usegs mX (d + 16 * off + 16 - 3) (d + nn - 4 - (d + 16 * off + 16) + 4)) by (eapply wr_at_sub; [exact X4| liac| liac]).
  assert (SP' : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (rewrite unsigned_lit by liac; liac).
  assert (FRX : rw_cells usegs mX (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { rewrite SP'. eapply rrw_cells_agree'; [exact FR2|]. cbn. intros a Ha. apply X1; liac. }
  assert (MWR : 0 <= meta_word (MR st g) < 2^64) by (unfold meta_word; liac).
  eapply evt_mono.
  { eapply (rr_fin2_walk (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s2' s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
      with (P := A) (n := n) (G := G) (k := kb) (Bold := B) (mword := meta_word (MR st g)) (avail := m_avail (MR st g)) (freed := m_freed (MR st g))
           (prev := pw st (m_prev (MR st g))) (next := pw st (m_next (MR st g)));
      first [exact MMX | exact BKX | exact WRX | exact FRX | exact MIX | idtac].
    - rewrite A0. apply unsigned_lit. liac.
    - rewrite A1. apply unsigned_lit. liac.
    - unfold wz. apply unsigned_lit. liac.
    - exact D0.
    - liac.
    - liac.
    - liac.
    - liac.
    - liac.
    - liac.
    - exact MWR.
    - liac.
    - liac.
    - liac.
    - liak1 GND.
    - rewrite SP'. exact STX.
    - liac. }
  cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros mF RET MUF WMF MIF CH BEF).
  (nelim RET 17%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 EMS MI' ST').
  rewrite SP' in EMS, ST'. replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in EMS, ST' by liac. rewrite Z_to_bv_bv_unsigned in EMS. subst ms'.
  set (m' := rss_mem mF (d + 16 * off + 16) (d + nn - 4) n kb) in *.
  set (P' := d + 16 * off + 16) in *. assert (EP' : P' = d + 16 * off + 16) by reflexivity. clearbody P'.
  (* [comment removed for export] *)
  assert (AGF : forall a, 0 <= a < 2^64 -> ~ (G + 16 <= a < G + 24) -> ~ (G + 32 <= a < G + 40) -> a <> d + nn - 4 -> mF (wa a) = mX (wa a)).
  { intros a Ha N1 N1' N2. apply MUF. rewrite wa_unsigned by liac. cbn. liac. }
  assert (AGR : forall a, 0 <= a < 2^64 -> a <> P' - 3 -> ~ (P' + n <= a < d + nn - 4) -> m' (wa a) = mF (wa a)).
  { intros a Ha N1 N2. unfold m'. apply rss_mem_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - N EP' D0 Ho NN DCE Ha N1 N2; lia. }
  assert (WMM : wmono usegs mX m') by (eapply wmono_trans; [exact WMF| apply rss_mem_wmono]).
  set (FP := fun a => (bv_unsigned sp - 176 <= a < bv_unsigned sp) \/ (B <= a < B + on) \/ (d <= a < d + nn) \/ (G + 16 <= a < G + 40)).
  assert (PE : rpres_except FP m m').
  { intros a Ha NC. subst FP. cbv beta in NC.
    assert (E1 : mX (wa a) = m (wa a)) by (rewrite X1 by (clear - Ha NC; lia); apply AG1; clear - Ha NC; lia).
    split.
    - rewrite AGR by (clear - Ha NC EP' Ho NN N D0; lia). rewrite AGF by (clear - Ha NC NN; lia). exact E1.
    - intros W. apply WMM. rewrite (rwview_ext m mX) by exact E1. exact W. }
  unfold rrealloc_post. exists w0, w1, w2, (Z_to_bv 64 P'), w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, m', errv2.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rrw_cells_agree'; [exact ERR2|]. intros a Ha. rewrite TP in Ha. unfold RATP in Ha. rewrite unsigned_lit in Ha by liac. cbn in Ha.
           rewrite AGR by (unfold keep in DNI; clear - Ha EP' Ho NN N DNI D0; lia). rewrite AGF by (unfold keep in GNI, DNI; clear - Ha GNI DNI NN; lia).
           apply X1; [clear - Ha; lia| unfold keep in RNI; clear - Ha RNI HBr EON; lia| unfold keep in DNI; clear - Ha DNI; lia]. }
  split. { eapply rauxv_ok_pres_B; [exact AV| exact PE| |]; subst FP; cbv beta; intros a Ha; unfold RAUXV_CELL in *;
           [clear - Ha HB RC HBr EON LO' SLO DCE G40 NN; lia| unfold keep in GNI, DNI, RNI; clear - Ha LO' SLO RNI HBr EON DNI GNI NN; lia]. }
  split; [reflexivity|]. split; [reflexivity|].
  (* [comment removed for export] *)
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n) by (subst mn; clear -Hk N; lia).
  assert (MNL : (Z.to_nat mn <= length old)%nat) by (clear -MN LEN; lia).
  assert (W' : wr_at usegs m' P' n).
  { eapply wr_at_transport; [| exact WMM]. eapply wr_at_sub; [exact X4| liac| liac]. }
  (nelim (rwr_at_bytes_exist m' (P' + mn) (n - mn) ltac:(eapply wr_at_sub; [exact W'| liac| liac]) ltac:(liac) ltac:(liak1 DNI)) 3%nat; intros junk JL JB).
  assert (OB : bytes_at usegs m' P' (firstn (Z.to_nat mn) old)).
  { pose proof BA as BA'. rewrite <- (firstn_skipn (Z.to_nat mn) old) in BA'. apply bytes_at_app in BA'. apply proj1 in BA'.
    eapply (bytes_at_shift m m' A P'); [exact BA'| liac| rewrite firstn_length_le by exact MNL; liac
      | rewrite firstn_length_le by exact MNL; liak1 RNI| rewrite firstn_length_le by exact MNL; liak1 DNI|].
    rewrite firstn_length_le by exact MNL. intros j Hj. rewrite Z2Nat.id in Hj by (clear -MN; lia).
    rewrite AGR by liac. rewrite AGF by liak1 GND. replace (P' + j) with (d + (16 * off + 16 + j)) by liac. rewrite X2 by liac.
    replace (B + (16 * off + 16 + j)) with (A + j) by liac. apply AG1; liac. }
  exists P', junk. split; [reflexivity|].
  split. { unfold rblock_range, alloc_ceiling. split; [liac|]. split; [| split; [liac|]; split; [liac| unfold keep in DNI; destruct DNI as [X|X]; [left|right]; liac]].
           rewrite EP'. apply mod16_d. exact DA. }
  (* [comment removed for export] *)
  (nelim IV 9%nat; intros L LS BL INV LIVE RESV SEC CORR HkBL).
  assert (Eb : b = (fst (fst p), 0)) by (rewrite Ec; cbn [fst]; rewrite <- Hb0; destruct b; reflexivity).
  set (st1 := set_tick (N.succ (s_tick st)) st).
  set (sA := pa_s5 st1 (fst p) g d nn).
  assert (Hs1 : s_slots st1 !! (fst p) = Some (g, 0)) by (rewrite <- I0; exact Hs).
  assert (Hgb1 : s_groups st1 !! (fst (fst p), 0) = Some (mkGhdr (Some g) ai)) by (rewrite <- Eb; exact Hgb).
  assert (Hsc1 : 48 <= m_sizeclass (MR st1 g)) by (change (MR st1 g) with (MR st g); liac).
  assert (Hr1 : s_regions st1 !! (fst (fst p)) = Some r) by (rewrite Ec; cbn [fst]; exact Hr).
  assert (DA' : d mod PGSZ = 0) by exact DA.
  assert (Hnn1 : PGSZ <= nn) by (unfold PGSZ; clear - NN N Ho; lia).
  assert (Hnn2 : 2 * PGSZ <= nn) by (unfold PGSZ, MMAP_THRESHOLD in *; liac).
  assert (Hnna : nn mod PGSZ = 0) by (unfold PGSZ; exact (proj1 (proj2 NN))).
  assert (HnnM : nn < LEN_MAX) by (unfold LEN_MAX; liac).
  assert (Hfree : forall q rq, s_regions st !! q = Some rq -> q <> fst (fst p) ->
            d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d).
  { intros q rq Hq NE. rewrite Ec in NE. cbn [fst] in NE. destruct (DJ q rq Hq NE) as [X|X]; unfold region_live_range, lr_lo in *;
      destruct (r_kind rq); cbn [fst snd]; unfold PGSZ; liac. }
  pose proof (rm_INV_removed st L BL LS (fst p) off k d nn INV HkBL) as INV1. fold st1 in INV1.
  pose proof (pa_facts2 st1 L (bl_remove (fst p) BL) LS (fst p) g ai d nn INV1 Hgb1 Hsc1 D0 DA' Hnn1 Hnn2 Hnna) as PAF.
  pose proof (pa_INVL st1 L (bl_remove (fst p) BL) LS (fst p) g ai r d nn INV1 Hgb1 Hs1 Hsc1 Hr1 D0 DA' Hnn1 Hnn2 Hnna HnnM DCE Hfree) as INVA.
  fold sA in PAF, INVA.
  assert (TKA : ticks_ok sA) by (apply ticks_ok_of_TKS; exact (TKS_of _ _ _ _ _ INVA)).
  assert (MR2 : rmrep st1 m2).
  { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MRP| exact MU2| exact WM2|].
    intros lo' hi' [E|[]]. injection E as <- <-. unfold alloc_ceiling. clear -SLO LO'. lia. }
  assert (PTR : rr_ptrs (fst (fst p)) g st1).
  { rewrite Ec. cbn [fst]. exact (rr_ptrs_intro st LB0 L BL LS b g r m C INV MRP (ex_intro _ ai Hgb) Hsc1 Hr Kr Hb0). }
  assert (MW : 0 <= m_avail (MR st1 g) < 2^32 /\ 0 <= m_freed (MR st1 g) < 2^32 /\ 0 < m_maplen (MR st1 g)) by (change (MR st1 g) with (MR st g); liac).
  assert (DJ1 : forall q rq, s_regions st1 !! q = Some rq -> q <> fst (fst p) -> r_base rq + round_up_pg (r_len rq) <= d \/ d + nn <= lr_lo rq).
  { intros q rq Hq NE. rewrite Ec in NE. cbn [fst] in NE. exact (DJ q rq Hq NE). }
  assert (RM : remap_mem m2 mF B d on nn (pa_len st1 g nn) G).
  { change (pa_len st1 g nn) with (Z.min on nn). split; [| split; [| split; [| split]]].
    - intros a Ha N1 N2 N3 N4. rewrite AGF by (clear - Ha N2 N3 N4 NN; lia). apply X1; [exact Ha| exact N1| exact N2].
    - intros j Hj NE. unfold IB in NE. rewrite AGF by (clear - Hj NE GND D0 DCE; unfold keep in GND; lia). apply X2. exact Hj.
    - (nelimp BEF 3%nat; intros _ _ BB). specialize (BB 0%nat ltac:(cbn; lia)). cbn [Z.of_nat nth_error] in BB. rewrite Z.add_0_r in BB.
      rewrite ref_mrd_overlay in BB by (rewrite wa_unsigned by (clear - D0 DCE NN; lia); clear - DNI NN; unfold keep in DNI; lia).
      unfold IB. replace (d + (nn - 4)) with (d + nn - 4) by (clear; lia). exact BB.
    - intros j Hj. (nelimp (wr_at_transport usegs mX mF d nn X4 WMF) 3%nat; intros _ _ W). specialize (W j Hj).
      rewrite ref_wview_overlay in W by (rewrite wa_unsigned by (clear - D0 DCE Hj; lia); clear - DNI Hj; unfold keep in DNI; lia). exact W.
    - intros j Hj NE. unfold IB in NE. rewrite AGF by (clear - Hj NE GND D0 DCE MLP NN; unfold keep in GND; lia). apply X3. exact Hj. }
  assert (CH' : rw_cells usegs mF G (rr_newcells st1 g d nn)).
  { unfold rr_newcells. change (MR st1 g) with (MR st g). change (pw st1) with (pw st).
    rewrite (meta_word_remap (MR st g) nn) by (clear - LI FB SC63 ML NN N62; lia). exact CH. }
  assert (Hmem1 : m_mem (MR st1 g) = Some (fst (fst p), 0)) by (rewrite <- Eb; exact Hmem).
  rewrite HBr in RM.
  pose proof (rmrep_remap st1 m2 mF (fst p) g r d nn MR2 PAF Hr1 Kr (eq_sym EON) Hmem1 ltac:(exists aa, ar, kk; auto) PTR MW D0 DA Hnn2 Hnna DCE DRF DJ1 RM CH') as MRA.
  fold sA in MRA.
  (* [comment removed for export] *)
  set (e' := aadd (fst (fst p), 0) (nn - 4)).
  assert (HrA : s_regions sA !! (fst Xup) = Some (pa_r' r d nn)).
  { unfold sA, Xup, aadd. cbn [fst]. rewrite (pa_lookup st1 (fst p) g r d nn Hr1). rewrite N.eqb_refl. reflexivity. }
  assert (KrA : r_kind (pa_r' r d nn) = RKGroup) by exact Kr.
  assert (FeA : fst e' = fst Xup) by reflexivity.
  assert (XU2 : snd Xup = 16 + 16 * off). { unfold Xup, aadd. rewrite Ec, I0, Hb0. cbn [snd]. unfold UNIT. clear; lia. }
  assert (P4 : 4 <= snd Xup) by (rewrite XU2; clear - Ho; lia).
  assert (PNE : snd Xup + n <= snd e') by (rewrite XU2; unfold e', aadd; cbn [snd]; clear - NN; lia).
  assert (EHI : snd e' + 1 <= round_up_pg (r_len (pa_r' r d nn))).
  { unfold e', aadd, pa_r'. cbn [snd r_len]. rewrite KStep.round_up_pg_aligned by exact (proj1 (proj2 NN)). clear; lia. }
  assert (RSA : snd e' - snd Xup - n < 2^32) by (rewrite XU2; unfold e', aadd; cbn [snd]; clear - NN N; lia).
  assert (IDX0 : 0 <= 0 < 32) by (clear; lia).
  assert (KB0 : 0 <= kb < 256 /\ Z.land kb 31 = 0) by (destruct KB8 as [K1 K2]; split; [exact K1| rewrite K2; exact I0]).
  assert (NOGRP : forall b0 gh, s_groups sA !! b0 = Some gh -> fst b0 = fst Xup -> snd b0 + 9 <= snd Xup - 3 \/ snd e' + 1 <= snd b0).
  { intros b0 gh Hb0g Efb. left. rewrite XU2.
    (nelim PAF 5%nat; intros _ _ _ GR5 _). rewrite GR5 in Hb0g. change (s_groups st1) with (s_groups st) in Hb0g.
    (nelim (ci_grps _ _ C b0 gh Hb0g) 3%nat; intros g0 Hg0 _).
    assert (HH : hosts st b0 g0). { destruct gh as [gm ai0]. cbn in Hg0. subst gm. exists ai0. exact Hb0g. }
    unfold Xup, aadd in Efb. cbn [fst] in Efb. rewrite Ec in Efb. cbn [fst] in Efb.
    destruct (alone x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 b0 g0 HH Efb) as [_ ->]. rewrite Hb0. clear - Ho; lia. }
  pose proof (rmrep_set_size_i sA mF Xup e' (pa_r' r d nn) n 0 kb MRA TKA HrA KrA FeA P4 (proj1 N) PNE EHI RSA IDX0 KB0 NOGRP) as SS.
  cbn [r_base pa_r'] in SS. rewrite XU2 in SS. unfold e', aadd in SS. cbn [snd] in SS.
  replace (d + (16 + 16 * off)) with P' in SS by (clear - EP'; lia). replace (d + (0 + (nn - 4))) with (d + nn - 4) in SS by (clear; lia).
  fold m' in SS. destruct SS as [R1 T1].
  assert (EFULL : rr_remap_full st (fst p) Xup n d nn = havoc Xup n (set_size_i Xup (aadd (fst (fst p), 0) (nn - 4)) n 0 sA)).
  { unfold rr_remap_full. rewrite Hs. cbv zeta. change (get_meta_rec st g) with (MR st g). rewrite Hmem. cbn [default]. rewrite Eb, I0.
    unfold sA, pa_s5, pa_s4, pa_s3, pa_s2, pa_len, IB. reflexivity. }
  (* [comment removed for export] *)
  assert (HEAP : RHEAP (set_m (cs_remap (ps_m s) (fst b) g d nn) s) ((p, P', n) :: lb_remove p LB) m').
  { exists (rr_remap_full st (fst p) Xup n d nn), ((p, P', n) :: lbrm LB0 (p, A, k)).
    split; [apply perm_blocks'|].
    split. { rewrite strip_rr_remap_full, Hs, Hst. cbn [ps_m set_m]. rewrite Ec. reflexivity. }
    split. { rewrite EFULL. exact (proj1 (rmrep_havoc _ _ Xup n R1 T1)). }
    split.
    - (* [comment removed for export] *)
      change (brk_link (strip (rr_remap_full st (fst p) Xup n d nn)) (ps_brk s)). rewrite strip_rr_remap_full, Hs.
      unfold brk_link. rewrite ctx_cs_remap. change (ctx (strip st)) with (ctx st).
      pose proof BLK as BL0. unfold brk_link in BL0.
      (nelim PTR 8%nat; intros _ _ _ _ _ _ PB _). change (ctx st1) with (ctx st) in PB.
      destruct (c_brk (ctx st)) as [| |rid' boff] eqn:HBK; try exact I.
      rewrite conc_cs_remap by (cbn; rewrite Ec; cbn [fst]; rewrite Hr; discriminate).
      cbn [fst snd]. rewrite (proj2 (N.eqb_neq _ _) PB). exact BL0.
    - (* [comment removed for export] *)
      eapply areach_ext; [exact AR|].
      replace P' with (d + UNIT + UNIT * off) by (rewrite EP'; unfold UNIT; clear; lia).
      apply (aext_remap ref_reserved st LB0 p A k n off d nn g i Hin0 (proj1 Ho) EA (proj1 N));
        first [exact Hs| exact Hs1| exact Hsc1| exact D0| exact DA'| exact Hnn2| exact Hnna| exact HnnM| exact DCE| exact Hfree| unfold UNIT, IB; clear - NN N; lia]. }
  split; [exact HEAP|].
  split.
  { (* [comment removed for export] *)
    intros a Ha CA. apply PE; [exact Ha|]. subst FP; cbv beta.
    destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
    - clear - CA Ha SPR LO' SLO RC HBr EON DCE G40. lia.
    - clear - CA Ha SPR LO' SLO RNI HBr EON DNI GNI. unfold keep in *. lia.
    - rewrite (lb_remove_lbrm LB p A k) in Hb' by (first [exact Hin | eapply NoDup_map_perm; [exact PERM| exact (ci_nodup _ _ C)]]).
      apply (In_lbrm_perm LB LB0) in Hb'; [| apply Permutation_sym; exact PERM].
      unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [HinL NEQ].
      assert (NES : blk_slot blk' <> fst p). { intros E. cbn [blk_slot fst] in NEQ. rewrite E, MI_Kit.aptr_eqb_refl in NEQ. exact NEQ. }
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
      (nelim (WR _ _ Hrg) 5%nat; intros _ _ _ RGC RGF). unfold alloc_ceiling in RGC.
      destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EQR|NER].
      + (* [comment removed for export] *)
        exfalso. destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL) as [(g0 & i0 & bg0 & Hs0 & _) _ _].
        (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (blk_slot blk') g0 i0 Hs0 EQR) 3%nat; intros _ _ EQS).
        (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (fst p) g i Hs ltac:(rewrite Ec; reflexivity)) 3%nat; intros _ _ EQP).
        apply NES. rewrite EQS, <- EQP. reflexivity.
      + assert (NEa' : fst (blk_slot blk') <> fst aa) by (intros E; rewrite E, Hra in Hrg; injection Hrg as <-; exact (NKa Krg)).
        destruct (DJR _ _ _ _ Hrg Hr NER) as [D1|D1]; rewrite ?(lr_lo_group _ Krg), ?(lr_lo_group _ Kr) in D1;
        destruct (DJ _ _ Hrg NER) as [D2|D2]; rewrite ?(lr_lo_group _ Krg) in D2;
        destruct (DJR _ _ _ _ Hrg Hra NEa') as [D3|D3]; rewrite ?(lr_lo_group _ Krg) in D3;
        clear - Ha Hab A16 AEND RGC D1 D2 D3 HBr EON HG Hkk A0a A4096 LRa SPR LO' SLO; lia. }
  split.
  { apply rw_cells_of_bytes.
    - cbn. rewrite firstn_length_le by exact MNL. split; [reflexivity|]. split; [exact JL| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OB|]. rewrite firstn_length_le by exact MNL. rewrite Z2Nat.id by (clear - MN; lia). exact JB.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_add, !Z2Nat.id by (clear - MN N; lia). replace (mn + (n - mn)) with n by (clear; lia). exact W'. }
  (* [comment removed for export] *)
  unfold keep in KDISJ. destruct KDISJ as [ED|SEP].
  - left. rewrite EP', EA, HP0, ED. unfold UNIT. clear; lia.
  - right. intros b0 Hb0L E0.
    assert (Hb00 : In b0 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb0L]).
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) b0 Hb00) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
    destruct (N.eq_dec (fst (blk_slot b0)) (fst b)) as [EQR|NER].
    + (* [comment removed for export] *)
      destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b0 Hb00) as [(g0 & i0 & bg0 & Hs0 & _) _ _].
      (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (blk_slot b0) g0 i0 Hs0 EQR) 3%nat; intros _ _ EQS).
      (nelim (alone_slot x0 st L BL LS INV g b (ex_intro _ ai Hgb) Hsc1 (fst p) g i Hs ltac:(rewrite Ec; reflexivity)) 3%nat; intros _ _ EQP).
      assert (EB0 : b0 = (p, A, k)).
      { apply (NoDup_map_inj_in blk_slot LB0 (ci_nodup _ _ C) b0 (p, A, k) Hb00 Hin0). cbn [blk_slot fst]. rewrite EQS, <- EQP. reflexivity. }
      rewrite EB0 in E0. cbn [blk_addr fst snd] in E0.
      clear - E0 EP' EA HP0 HBr EON SEP NN Ho NFa MLP Hfit Estride. lia.
    + pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) b0 Hb00)) as SZ0.
      destruct (DJ _ _ Hrg NER) as [D2|D2]; rewrite ?(lr_lo_group _ Krg) in D2.
      * clear - E0 EP' A16 AEND D2 NN Ho N SZ0. lia.
      * clear - E0 EP' A16 AEND D2 NN Ho N SZ0. lia.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac clear_keep := repeat match goal with K : keep _ |- _ => clear K end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; clear_keep; lia.
Ltac liak1 H := prune; unfold keep in H; clear_keep; lia.
Ltac liak2 H1 H2 := prune; unfold keep in H1, H2; clear_keep; lia.
Ltac liak3 H1 H2 H3 := prune; unfold keep in H1, H2, H3; clear_keep; lia.
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_G2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_ifaceP.
Module RF_realloc_G3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.



Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry RF_realloc_G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma rheap_pres_of_munch LB SP W m m' :
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros MU WM H a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. apply H; assumption.
Qed.

Lemma In_lb_remove b p LB : In b (lb_remove p LB) -> In b LB.
Proof using . unfold lb_remove. intros H. apply In_filter_iff in H. exact (proj1 H). Qed.

Section RR.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (s : PState) (LB : list block) (p : bptr) (A k n lo Bx : Z) (old : list byte) (errv : word).
Variables (st : mstate) (LB0 : list block) (g b : aptr) (r : region) (i off : Z).
Hypothesis PERM : Permutation LB0 LB.
Hypothesis Hst : strip st = ps_m s.
Hypothesis MRP : rmrep st m.
Hypothesis BLK : brk_link st (ps_brk s).
Hypothesis AR : RAREACH st LB0.
Hypothesis RF : rrF st m LB0 p A k g b r i off.
Hypothesis Hin : In (p, A, k) LB.
Hypothesis Hin0 : In (p, A, k) LB0.
Hypothesis BA : bytes_at usegs m A old.
Hypothesis LEN : Z.of_nat (length old) = k.
Hypothesis AV : rauxv_ok m Bx.
Hypothesis HB : bv_unsigned sp <= Bx.
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis SLO : lo <= bv_unsigned sp - RREALLOC_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 A.
Hypothesis A1 : a1 = Z_to_bv 64 n.
Hypothesis N : 0 <= n < 2^32.


(* [comment removed for export] *)
Variables (mm : mem) (errvm : word).
Hypothesis MUm : munch [(bv_unsigned sp - 176, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)] m mm.
Hypothesis WMm : wmono usegs m mm.
Hypothesis MIm : mem_inv usegs mm.
Hypothesis STm : stk usegs mm lo (bv_unsigned sp + -64).
Hypothesis FRm : rw_cells usegs mm (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6).
Hypothesis ERRm : rw_cells usegs mm (errno_addr tp) [C4 errvm].

(* [comment removed for export] *)
Lemma rr_fallback_thm : forall (vra t0' t1' t2' s0' s1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' t3' t4' t5' t6' : word),
  implM usegs (rr_fallback p n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A k n lo Bx old m)
        (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2' s0' s1' a0 a1 a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 RR_MALLOC) fc None mm (seg_rom usegs)).
Proof using A0 A1 AR AV BA BLK ERRm FRm HB Hin Hst LEN LO MIm MRP MUm N PERM SLO STm TP WMm.
  intros.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK in SLO. pose proof LO as LO'. unfold alloc_ceiling in LO'.
  assert (ETP : bv_unsigned tp + -164 = RERRNO). { rewrite TP. unfold RATP, RERRNO. rewrite unsigned_lit by lia. reflexivity. }
  assert (HEAP : RHEAP s LB m). { exists st, LB0. split; [exact PERM|]. split; [exact Hst|]. split; [exact MRP|]. split; [exact BLK| exact AR]. }
  pose proof (RHEAP_block_range_proof s LB m (p, A, k) HEAP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR. unfold rblock_range, alloc_ceiling in BR.
  assert (ABx : alloc_ceiling <= Bx) by (pose proof AV as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & AB & _); exact AB). unfold alloc_ceiling in ABx.
  assert (HEAPm : RHEAP s LB mm).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MUm| exact WMm|].
    constructor; [left; cbn [fst snd]; unfold alloc_ceiling; lia|].
    constructor; [|constructor]. right; left. cbn [fst snd]. rewrite ETP. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
  assert (AVm : rauxv_ok mm Bx).
  { eapply rauxv_ok_frame; [exact AV| exact MUm| exact WMm|].
    constructor; [cbn [fst snd]; unfold RAUXV_CELL; lia|]. constructor; [|constructor]. cbn [fst snd]. rewrite ETP. unfold RERRNO, RAUXV_CELL. lia. }
  assert (PRESm : forall LB', (forall b0, In b0 LB' -> In b0 LB) -> rheap_pres LB' (bv_unsigned sp) m mm).
  { intros LB' HLB'. eapply rheap_pres_of_munch; [exact MUm| exact WMm|]. intros a Ha Hc. rewrite ETP. cbn [outside]. unfold RERRNO.
    destruct Hc as [Hc|[[Hc NS]|(b0 & Hb0 & Hab)]].
    - clear -Hc SLO LO'. lia.
    - unfold ralloc_static, RERRNO in NS. clear -Hc NS SLO LO'. lia.
    - pose proof (RHEAP_block_range_proof s LB m b0 HEAP (HLB' b0 Hb0)) as (_ & _ & _ & B1 & B2). unfold alloc_ceiling in B1. clear -Hab B1 B2 SLO LO'. lia. }
  assert (SP64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (rewrite unsigned_lit by lia; lia).
  unfold rr_fallback.
  eapply (implM_bind usegs).
  { eapply (implM_evt usegs).
    { unfold RR_MALLOC. step. step. step. step.
      lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms0 : machine_state => ms0 = ms) end.
      apply evt_done. reflexivity. }
    cbv beta. intros ms1 ->.
    change (Z_to_bv 64 93684) with (Z_to_bv 64 rmalloc_entry).
    eapply rmalloc_entry_spec; first [exact HEAPm| exact AVm| exact LO| exact ERRm| exact MIm| exact TP| exact A1| exact N| idtac].
    - rewrite SP64. lia.
    - rewrite SP64. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact STm.
    - rewrite SP64. unfold RMALLOC_ESTACK. lia. }
  cbv beta. intros rq s' ms' POST.
  destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AV' & PRES' & FA' & SO' & RES).
  rewrite SP64 in ST', PRES'. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST' by lia.
  replace (ret_pc (Z_to_bv 64 98412)) with (Z_to_bv 64 98412) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FR' : rw_cells usegs m' (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rheap_pres_rw_cells; [exact PRES'| exact FRm| left; lia]. }
  destruct rq as [q|].
  2:{ (* [comment removed for export] *)
    destruct RES as [-> HEAP'].
    apply implM_ret.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. 2:{ exfalso. clear -K1. cbn in K1. lia. }
    unfold RF_realloc_A.rr_frame in FR'.
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. unfold rrealloc_post. do 15 eexists. exists m', errv'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AV'|].
    split; [exact FA'|]. split; [exact SO'|]. split; [reflexivity|]. split; [exact HEAP'|].
    eapply rheap_pres_trans; [apply PRESm; auto|]. eapply rheap_pres_weaken; [exact PRES'| lia| auto]. }
  (* [comment removed for export] *)
  destruct RES as (A' & junk & -> & BR' & HEAP' & JK & _).
  pose proof BR' as BR2. unfold rblock_range, alloc_ceiling in BR2.
  pose proof (RHEAP_blocks_nodup_proof s' _ m' HEAP') as NDi. cbn [map blk_id fst] in NDi.
  pose proof (CJ_heap_inst0.RHEAP_addr_nodup s' _ m' HEAP') as NDa. cbn [map blk_addr fst snd] in NDa.
  apply List.NoDup_cons_iff in NDi as [Hq NDi2]. apply List.NoDup_cons_iff in NDa as [HA2 NDa2].
  assert (QP : q <> p). { intros ->. apply Hq. apply in_map_iff. exists (p, A, k). split; [reflexivity| exact Hin]. }
  assert (DISJ : forall b0, In b0 LB -> A' + n <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= A').
  { intros b0 Hb0. pose proof (RHEAP_blocks_disjoint_proof s' _ m' (q, A', n) b0 HEAP' (or_introl eq_refl) (or_intror Hb0)) as D.
    cbn [blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply Hq. rewrite E. apply in_map_iff. exists b0; auto. }
  pose proof (DISJ _ Hin) as DJp. cbn [blk_addr blk_size fst snd] in DJp.
  set (mn := Z.min k n).
  assert (MN : 0 <= mn <= k /\ mn <= n /\ (mn = k \/ mn = n)) by (subst mn; clear -BR N; lia).
  (* [comment removed for export] *)
  pose proof (rw_cells_split_CB usegs m' A' [] (Z.to_nat n) junk [] [Z.to_nat mn; Z.to_nat (n - mn)]%nat JK ltac:(cbn [sum_nat]; lia)) as JK2.
  cbn [app mk_CB_cells] in JK2.
  set (j1 := firstn (Z.to_nat mn) junk) in JK2. set (j2 := firstn _ _) in JK2.
  apply (proj1 (Malloc_ifaceP.rw_cells_app usegs m' A' [CB (Z.to_nat mn) j1] [CB (Z.to_nat (n - mn)) j2])) in JK2.
  destruct JK2 as [DST TAIL]. cbn [cells_size csize] in TAIL. rewrite Nat.add_0_r, Z2Nat.id in TAIL by lia.
  (* [comment removed for export] *)
  assert (OLD' : bytes_at usegs m' A old).
  { eapply rheap_pres_bytes_at; [exact PRES'| | right; right; exists (p, A, k); cbn [blk_addr blk_size fst snd]; split; [exact Hin| lia]].
    eapply bytes_at_transport; [exact BA| exact MUm|]. rewrite LEN, ETP. unfold RERRNO. cbn [disjoint_from]. clear -BR SLO LO'. lia. }
  assert (SRC : bytes_at usegs m' A (firstn (Z.to_nat mn) old)).
  { rewrite <- (firstn_skipn (Z.to_nat mn) old) in OLD'. apply bytes_at_app in OLD'. exact (proj1 OLD'). }
  assert (SRCL : length (firstn (Z.to_nat mn) old) = Z.to_nat mn) by (rewrite firstn_length_le; lia).
  eapply (implM_evt usegs _ _ _ (fun ms2 => exists (w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 : word) (m2 : mem),
     ms2 = MS (mkR (Z_to_bv 64 0x18094) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp w0 w1 w2 (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 A) wa1 wa2 wa3 wa4 wa5 wa6 wa7
                   (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 w3 w4 w5 w6) F (Z_to_bv 64 rfree_entry) fc None m2 (seg_rom usegs)
     /\ munch [(A', A' + mn)] m' m2 /\ wmono usegs m' m2 /\ mem_inv usegs m2
     /\ rw_cells usegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old)])).
  { rewrite A0, A1.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia. { exfalso. clear -K1 BR2. lia. }
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (A + k)), (unsigned_lit A) by lia. replace (A + k - A) with k by lia.
    lazymatch goal with |- evt _ ?P _ =>
      assert (JOIN : forall a2v : word, a2v = Z_to_bv 64 mn ->
        evt usegs P (MS (mkR (Z_to_bv 64 98412) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 A') (Z_to_bv 64 k) a2v ra3 ra4 ra5 ra6 ra7
                         (Z_to_bv 64 (A + k)) s3' s4' s5' s6' s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x18080) fc None m' (seg_rom usegs)))
    end.
    { intros a2v ->.
      (* [comment removed for export] *)
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec) with (src := firstn (Z.to_nat mn) old) (junk := j1);
          rewrite ?(unsigned_lit A), ?(unsigned_lit A'), ?(unsigned_lit mn) by lia.
        - exact SRC.
        - exact SRCL.
        - exact DST.
        - clear -DJp MN BR BR2. lia.
        - exact MI'. }
      cbv beta. intros ms2 (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & DST2 & SRC2).
      rewrite ?(unsigned_lit A), ?(unsigned_lit A'), ?(unsigned_lit mn) in MU2, DST2 by lia.
      replace (ret_pc (Z_to_bv 64 98444)) with (Z_to_bv 64 98444) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      step. step. apply evt_done. do 15 eexists. split; [reflexivity|]. auto. }
    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2.
    - apply JOIN. f_equal. subst mn. clear -K2 MN. lia.
    - step. apply JOIN. f_equal. subst mn. clear -K2 MN. lia. }
  cbv beta. intros ms2 (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & -> & MU2 & WM2 & MI2 & DST2).
  (* [comment removed for export] *)
  assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)).
  { eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN BR2 LO' SLO. lia. }
  assert (ERR2 : rw_cells usegs m2 (bv_unsigned tp + -164) [C4 errv']).
  { eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2|]. rewrite ETP. unfold RERRNO. cbn [disjoint_from cells_size csize Nat.add]. clear -MN BR2. lia. }
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rw_cells_transport; [exact FR'| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN BR2 LO' SLO. lia. }
  assert (TAIL2 : rw_cells usegs m2 (A' + mn) [CB (Z.to_nat (n - mn)) j2]).
  { eapply rw_cells_transport; [exact TAIL| exact MU2| exact WM2|]. cbn [disjoint_from]. clear -MN. lia. }
  assert (AV2 : rauxv_ok m2 Bx).
  { eapply rauxv_ok_frame; [exact AV'| exact MU2| exact WM2|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. clear -MN BR2 ABx. lia. }
  assert (HEAP2 : RHEAP s' ((q, A', n) :: LB) m2).
  { eapply RHEAP_frame_proof; [exact HEAP'| exact MU2| exact WM2|]. constructor; [|constructor].
    right; right. exists (q, A', n). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| clear -MN; lia]. }
  assert (LBeq : lb_remove p ((q, A', n) :: LB) = (q, A', n) :: lb_remove p LB).
  { rewrite CJ_heap_inst0.lb_remove_cons. cbn [blk_id fst]. destruct (bptr_eqb q p) eqn:E; [|reflexivity].
    exfalso. apply CJ_heap_inst0.bptr_eqb_eq in E. exact (QP E). }
  eapply (implM_bind usegs).
  { eapply rfree_entry_spec; [exact HEAP2| right; exact Hin| exact AV2| rewrite SP64; clear -HB; lia| rewrite SP64| exact LO| rewrite SP64; unfold RFREE_ESTACK; clear -SLO; lia| exact ERR2| exact MI2| exact TP| reflexivity].
    replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia. exact ST2. }
  cbv beta. intros [] s'' ms3 FP.
  destruct FP as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & ERR3 & AV3 & PRES3 & FA3 & SO3 & HEAP3).
  rewrite SP64 in ST3, PRES3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) in ST3 by lia.
  rewrite LBeq in PRES3, HEAP3.
  apply implM_ret.
  replace (ret_pc (Z_to_bv 64 98452)) with (Z_to_bv 64 98452) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (RF_realloc_A.rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
  { eapply rheap_pres_rw_cells; [exact PRES3| exact FR2| left; lia]. }
  unfold RF_realloc_A.rr_frame in FR3.
  (* [comment removed for export] *)
  step. step.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR3 ST3 (bv_unsigned sp).
  apply evt_done. unfold rrealloc_post. do 15 eexists. exists m3, errv'.
  split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AV3|].
  split; [rewrite FA3; exact FA'|]. split; [rewrite SO3; exact SO'|].
  fold mn.
  exists A', j2. split; [reflexivity|]. split; [exact BR'|]. split; [exact HEAP3|].
  split.
  { eapply rheap_pres_trans; [apply PRESm; intros b0 Hb0; exact (In_lb_remove _ _ _ Hb0)|].
    eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact (In_lb_remove _ _ _ Hb0)]|].
    eapply rheap_pres_trans.
    - eapply rheap_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc. cbn [outside]. split; [|exact I].
      destruct Hc as [Hc|[[Hc NS]|(b0 & Hb0 & Hab)]].
      + clear -Hc MN BR2 SLO LO'. lia.
      + clear -Hc MN BR2. lia.
      + pose proof (DISJ b0 (In_lb_remove _ _ _ Hb0)) as D. clear -Hab D MN. lia.
    - eapply rheap_pres_weaken; [exact PRES3| lia| intros b0 Hb0; right; exact Hb0]. }
  split.
  { assert (CH2 : rw_cells usegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old); CB (Z.to_nat (n - mn)) j2]).
    { apply (proj2 (Malloc_ifaceP.rw_cells_app usegs m2 A' [CB (Z.to_nat mn) (firstn (Z.to_nat mn) old)] [CB (Z.to_nat (n - mn)) j2])).
      split; [exact DST2|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact TAIL2. }
    eapply rheap_pres_rw_cells; [exact PRES3| exact CH2|]. right; right. exists (q, A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. clear -MN. lia. }
  right. intros b0 Hb0 E. apply HA2. rewrite E. apply in_map_iff. exists b0; auto.
Qed.
End RR.


End CeilWrap.
(* [comment removed for export] *)
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_G3.

(* [comment removed for export] *)
Module RF_realloc_null.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.
Import RF_realloc_mentry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem rrealloc_null_spec : rrealloc_null_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv
         HP AV HB ST LO SLO ERR MI TP A0 A1 N.
  eapply (implM_evt usegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs))).
  { unfold RREALLOC_SYM. subst a0. step. step. if_true. step. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (rmalloc_entry_spec ra sp gp tp t0 t1 t2 s0 s1 a1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv);
    try eassumption. unfold RMALLOC_STACK in SLO. unfold RMALLOC_ESTACK. lia.
Qed.


End CeilWrap.
End RF_realloc_null.

(* [comment removed for export] *)
Module RF_realloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import Stdlib.Logic.FunctionalExtensionality.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSoundMem.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2.MallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocKit_A2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.F_free_spec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.F_malloc_fast OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Realloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F.RMallocKit_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMalloc_ifaceP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocksR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_mremap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_F OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RF_realloc_K2 RF_realloc_mentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_P RF_realloc_G1 RF_realloc_G2 RF_realloc_G3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Local Ltac tclose_core :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; tclose_core
  | |- _ \/ _ => first [ left; tclose_core | right; tclose_core ]
  | |- _ = _ => reflexivity
  | |- _ => assumption
  end.
Local Ltac tclose := first [ tclose_core | tauto ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; lia.

Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Lemma andb3_true_iff_Z a1 b1 a2 b2 a3 b3 :
  (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = true <-> (a1 <= b1 /\ a2 < b2 /\ a3 <= b3).
Proof. rewrite !Bool.andb_true_iff, !Z.leb_le, Z.ltb_lt. tclose. Qed.
Lemma cond1_false a1 b1 a2 b2 a3 b3 : ~ (a1 <= b1 /\ a2 < b2 /\ a3 <= b3) -> (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = false.
Proof using . intros H. destruct ((a1 <=? b1) && (a2 <? b2) && (a3 <=? b3)) eqn:E; [|reflexivity]. exfalso. apply H. apply andb3_true_iff_Z. exact E. Qed.
Lemma cond1_true a1 b1 a2 b2 a3 b3 : a1 <= b1 -> a2 < b2 -> a3 <= b3 -> (a1 <=? b1) && (a2 <? b2) && (a3 <=? b3) = true.
Proof using . intros. apply andb3_true_iff_Z. auto. Qed.
Lemma cond2_false a1 b1 a2 b2 : ~ (a1 <= b1 /\ a2 <= b2) -> (a1 <=? b1) && (a2 <=? b2) = false.
Proof using . intros H. destruct (Z.leb_spec a1 b1); destruct (Z.leb_spec a2 b2); cbn; try reflexivity. exfalso. apply H. auto. Qed.
Lemma cond2_true a1 b1 a2 b2 : a1 <= b1 -> a2 <= b2 -> (a1 <=? b1) && (a2 <=? b2) = true.
Proof using . intros. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.leb_le _ _)) by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mem_ext (m1 m2 : mem) : (forall x, m1 x = m2 x) -> m1 = m2.
Proof using . intros H. apply functional_extensionality. exact H. Qed.

(* [comment removed for export] *)
Lemma bytes_at_same_byte m m' a bs (x : word) :
  bytes_at usegs m a bs -> bytes_at usegs m' a bs -> (a + Z.of_nat (length bs) <= 0x10000 \/ 0x56000 <= a) ->
  a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x.
Proof.
  intros (A0 & A1 & H1) (_ & _ & H2) Hi Hx.
  assert (E : x = wa (a + Z.of_nat (Z.to_nat (bv_unsigned x - a)))).
  { rewrite Z2Nat.id by lia. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  specialize (H1 (Z.to_nat (bv_unsigned x - a)) ltac:(lia)). specialize (H2 (Z.to_nat (bv_unsigned x - a)) ltac:(lia)).
  rewrite <- E in H1, H2. rewrite ref_mrd_overlay in H1, H2 by lia. rewrite H1, H2. reflexivity.
Qed.

Lemma mword_page mr : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  meta_word mr - meta_word mr mod 4096 = m_maplen mr * 4096.
Proof using .
  intros. unfold meta_word. set (L := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr).
  replace (L + 4096 * m_maplen mr) with (L + m_maplen mr * 4096) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mword_same mr : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^35 ->
  Z.lor (Z.land (meta_word mr) 4095) (m_maplen mr * 4096) = meta_word mr.
Proof using .
  intros. rewrite <- (meta_word_remap mr (m_maplen mr * 4096)); [| lia| lia| lia| lia| lia| apply Z_mod_mult].
  unfold meta_word. destruct mr; cbn in *. rewrite Z.div_mul by lia. rewrite MI_WRemap.land_ones52 by lia. reflexivity.
Qed.

Lemma rreserved_free_intro a n : 0 <= n -> (a + n <= 0x10000 \/ 0x56000 <= a) -> ranges_free ref_reserved a n = true.
Proof.
  intros Hn H. apply ranges_free_intro. intros b k Hin. unfold ref_reserved in Hin. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma wr_at_join segs m a n1 n2 : wr_at segs m a n1 -> wr_at segs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at segs m a (n1 + n2).
Proof using .
  intros (A0 & _ & W1) (_ & A2 & W2) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z_lt_dec i n1); [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Theorem rrealloc_spec : rrealloc_stmt.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A k n lo Bx old errv.
  intros HR Hin BA LEN AV HB ST LO SLO ERR MI TP A0 A1 N.
  (nelim HR 6%nat; intros st LB0 PERM Hst MRP [BLK AR]).
  assert (Hin0 : In (p, A, k) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  (nelim (rrF_intro st m LB0 p A k AR MRP Hin0) 6%nat; intros g b r i off RF).
  pose proof RF as RF'.
  destruct RF' as [C Hs [ai Hgb] Hmem GOK Hr Kr Ec Hi [NFa NFf] Ho Hk Hfit EA [Cc Cb] SPAN (R0 & RAL & RC & RFr & RI) S20 SC28 [B0 B16] BY GH [MM MSL] (secret & SECR & BAC & BCX) (G0 & G40 & G24) NOG OTH IV].
  cbv zeta in BY. (nelim BY 8%nat; intros B4 B3 B2 HQ EQ16 BF BC BE).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof SLO as SLO'. unfold RREALLOC_STACK in SLO'. pose proof LO as LO'. unfold alloc_ceiling in LO', RC, G40.
  (nelimp MRP 6%nat; intros WF _ GL _ _ SH). (nelimp WF 5%nat; intros Hres WR DJR WA WG).
  destruct (SH (fst b) r Hr Kr) as [HWr _].
  pose proof (go_stride _ _ _ GOK) as [S16 SM]. pose proof (go_li _ _ _ GOK) as LI. pose proof (go_avail _ _ _ GOK) as AVr. pose proof (go_freed _ _ _ GOK) as FRr.
  pose proof (go_freeable _ _ _ GOK) as FB. pose proof (go_sc _ _ _ GOK) as GSC. pose proof (go_maplen _ _ _ GOK) as ML. (nelimp (go_region _ _ _ GOK) 7%nat; intros rX HrX _ _ _ _ TOP).
  rewrite Hr in HrX. injection HrX as <-.
  change (get_meta_rec st g) with (MR st g) in S16, SM, LI, AVr, FRr, FB, GSC, ML, TOP.
  (* [comment removed for export] *)
  set (STR := get_stride (MR st g)) in *. set (P0 := conc st (fst p)) in *. set (B := conc st b) in *. set (G := conc st g) in *.
  assert (ESTR : STR = RF_realloc_G1.Xstride st g) by reflexivity. assert (EP0 : P0 = RF_realloc_G1.XP0 p st) by reflexivity.
  assert (EB : B = RF_realloc_G1.XB st b) by reflexivity. assert (EG : G = RF_realloc_G1.XG st g) by reflexivity.
  assert (EE : RF_realloc_G1.XE p st g = P0 + STR - 4) by reflexivity.
  assert (ERES : RF_realloc_G1.Xres p A k st g = P0 + STR - 4 - A - k) by reflexivity.
  assert (ESC : RF_realloc_G1.Xsc st g = m_sizeclass (MR st g)) by reflexivity.
  assert (EMW : RF_realloc_G1.Xmword st g = meta_word (MR st g)) by reflexivity.
  unfold UNIT, IB in *.
  assert (SI0 : 0 <= STR * i) by (apply Z.mul_nonneg_nonneg; clear - S16 Hi; lia).
  assert (SIL : STR * i + STR <= STR * (m_last_idx (MR st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - S16 Hi; lia. }
  assert (HP0 : P0 = r_base r + snd b + 16 + STR * i) by (rewrite Cc, Ec; cbn [snd]; clear; lia).
  assert (HBr : B = r_base r + snd b) by exact Cb.
  assert (ABND : r_base r + 16 <= A /\ 0 <= k /\ A + k + 4 <= P0 + STR /\ P0 + STR <= r_base r + round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling)
    by (clear - EA HP0 R0 B0 SI0 Ho RC SPAN SIL Hfit Hk; lia).
  (* [comment removed for export] *)
  unfold raw_realloc.
  eapply (implM_bind usegs _ _ _ (fun a s1' ms1 => a = s /\ s1' = s /\ ms1 = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s_ s1' ms1 nelH_; (nelim nelH_ 3%nat; intros -> -> ->). cbv beta.
  rewrite (rplan_eq m s p A k n old st LB0 g b r i off Hst RF). rewrite <- ESTR, ESC, <- EB.
  replace (16 * off) with (A - P0) by (clear - EA; lia).
  (* [comment removed for export] *)
  eapply implM_evt; [exact (rr_prefix ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p A k n lo old st LB0 g b r i off RF LEN ST LO SLO MI A0 A1 N)|].
  cbv beta. intros ms1 nelH_; (nelim nelH_ 9%nat; intros m1 t3' t4' -> MU1 WM1 MI1 ST1 FR1).
  rewrite EE, ERES, ESC, EMW, <- EB, <- EG, <- ESTR. unfold UNIT, IB.
  replace (16 * off) with (A - P0) by (clear - EA; lia).
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -64)) in *.
  set (E := P0 + STR - 4) in *.
  set (sc := m_sizeclass (MR st g)) in *.
  set (rom := seg_rom usegs) in *.
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 64) by (subst sp'; rewrite unsigned_lit by (clear - SPR SLO' LO'; lia); clear; lia).
  assert (XP1 : forall a bs, bytes_at usegs m a bs -> a + Z.of_nat (length bs) <= lo -> bytes_at usegs m1 a bs).
  { intros a bs Ha Hl. eapply bytes_at_transport; [exact Ha| exact MU1|]. cbn [disjoint_from]. split; [left; clear -Hl SLO'; lia| exact I]. }
  assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite TP. unfold RATP. rewrite unsigned_lit by (clear; lia). cbn. clear - SPR SLO' LO'. lia. }
  (* [comment removed for export] *)
  set (QIN := fun ms => exists t1'' t2'' t3'' a4' a5' a7',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1'' t2'' s0 (wz G) a0 a1 (Z_to_bv 64 (size_to_class n + 1)) (Z_to_bv 64 sc) a4' a5'
                   (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_INPLACE) fc None m1 rom
      /\ n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1).
  set (QMAL := fun ms => exists t1'' t2'' t3'' a2' a4' a5' a7',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1'' t2'' s0 (wz G) a0 a1 a2' (Z_to_bv 64 sc) a4' a5'
                   (Z_to_bv 64 (E + 4)) a7' (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_MALLOC) fc None m1 rom
      /\ ~ (n <= E - A /\ n < MMAP_THRESHOLD /\ sc <= size_to_class n + 1) /\ ~ (48 <= sc /\ MMAP_THRESHOLD <= n)).
  set (QBIG := fun ms => exists t2'' t3'' a5',
      ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz (meta_word (MR st g))) a5'
                   (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E + - bv_unsigned a0)) (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6) F (Z_to_bv 64 RR_BIG) fc None m1 rom
      /\ MMAP_THRESHOLD <= n /\ sc = 63).
  eapply implM_evt.
  { eapply (rr_decide_walk ra sp' gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz G) _ (wz B) (wz (meta_word (MR st g))) t4' F fc m1 A n sc E (E - A - k)
              (fun ms => QIN ms \/ QMAL ms \/ QBIG ms)).
    - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
    - rewrite A1. apply unsigned_lit. clear - N; lia.
    - exact N.
    - clear - ABND R0 Hk. subst E. lia.
    - clear - ABND R0 Hk. subst E. lia.
    - clear - GSC. subst sc. lia.
    - clear - GSC. subst sc. lia.
    - exact MI1.
    - intros C1 C2 C3 t1'' t2'' t3'' a4' a5' a7'. apply evt_done. left. exists t1'', t2'', t3'', a4', a5', a7'. split; [reflexivity| auto].
    - intros C1 C2 t1'' t2'' t3'' a2' a4' a5' a7'. apply evt_done. right. left. exists t1'', t2'', t3'', a2', a4', a5', a7'. split; [reflexivity| auto].
    - intros C1 C2 t2'' t3'' a5'. apply evt_done. right. right. exists t2'', t3'', a5'. split; [reflexivity| auto]. }
  cbv beta. intros ms2 [QI|[QM|QB]].
  - (* [comment removed for export] *)
    (nelim QI 10%nat; intros t1'' t2'' t3'' a4' a5' a7' -> C1 C2 C3).
    rewrite (cond1_true n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (first [exact C2 | exact C3 | subst E; clear - C1; lia]).
    apply implM_ret.
    assert (SC48 : sc < 48).
    { pose proof (F_malloc_entry.size_to_class_props n ltac:(clear - N C2; unfold MMAP_THRESHOLD in *; lia)) as (SCR & _). clear - SCR C3 GSC. subst sc. lia. }
    eapply evt_mono.
    { eapply (rr_ss1_walk sp' gp tp s0 (wz G) (Z_to_bv 64 (E - (E - A - k))) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
        with (P := A) (n := n) (k := i + 32 * Z.min (E - A - k) 5); rewrite ?SP'.
      - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
      - rewrite A1. apply unsigned_lit. clear - N; lia.
      - clear - N; lia.
      - clear - C1; subst E; lia.
      - specialize (S20 SC48). clear - S20 SIL SI0 Hk EA Ho N; subst E. lia.
      - clear - Hi LI Hfit Hk EA; subst E. lia.
      - clear - ABND R0; lia.
      - clear - ABND; subst E; lia.
      - exact MI1.
      - apply XP1; [exact B3|]. cbn [length]. change (Z.of_nat 1) with 1. clear - ABND LO'; lia.
      - eapply wr_at_transport; [| exact WM1]. eapply wr_at_sub; [exact HWr| clear - ABND; lia| clear - ABND; subst E; lia].
      - exact FR1.
      - exact ST1.
      - clear - ABND LO'; subst E; lia.
      - clear - SLO' LO'; lia. }
    cbv beta. intros ms' RET.
    eapply (rr_inplace_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
              PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP N m1 ms' errv MU1 WM1); [| | exact ERR1| exact RET].
    + clear - C1; subst E. exact C1.
    + specialize (S20 SC48). clear - S20 SIL SI0 Hk EA Ho N C1; subst E. unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. lia.
  - (* [comment removed for export] *)
    (nelim QM 10%nat; intros t1'' t2'' t3'' a2' a4' a5' a7' -> C1 C2).
    rewrite (cond1_false n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (intros X; apply C1; subst E; clear - X; lia).
    rewrite (cond2_false 48 sc MMAP_THRESHOLD n C2).
    replace (Z_to_bv 64 (E - (E - A - k))) with (Z_to_bv 64 (A + k)) by (f_equal; clear; lia).
    apply (rr_fallback_thm ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0
             PERM Hst MRP BLK AR Hin BA LEN AV HB LO SLO TP A0 A1 N m1 errv); [| exact WM1| exact MI1| exact ST1| exact FR1| exact ERR1].
    eapply munch_weaken; [| exact MU1]. intros x [X _]. cbn. split; [clear - X; lia| exact I].
  - (* [comment removed for export] *)
    (nelim QB 6%nat; intros t2'' t3'' a5' -> C1 C2).
    rewrite (cond1_false n (STR - 4 - (A - P0)) n MMAP_THRESHOLD sc (size_to_class n + 1)) by (clear - C1; unfold MMAP_THRESHOLD in *; lia).
    rewrite (cond2_true 48 sc MMAP_THRESHOLD n) by (clear - C1 C2; lia).
    rewrite C2. cbn [Z.eqb negb Pos.eqb].
    (* [comment removed for export] *)
    assert (L0 : m_last_idx (MR st g) = 0) by (clear -GSC C2; subst sc; lia).
    assert (MLP : 0 < m_maplen (MR st g)) by (clear -GSC C2; subst sc; lia).
    destruct (TOP ltac:(clear - MLP; lia)) as [Hb0 EON].
    assert (I0 : i = 0) by (clear -Hi L0; lia).
    set (on := m_maplen (MR st g) * 4096) in *.
    assert (ESTR63 : STR = on - 16).
    { subst STR on. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen (MR st g)) 0); [exfalso; clear - MLP e; lia|]. cbn. unfold UNIT. clear; lia. }
    assert (HPB : P0 = B + 16) by (rewrite HP0, HBr, Hb0, I0; clear; lia).
    replace (A - P0) with (16 * off) by (clear - EA; lia).
    set (nn := rr_needed n (16 * off)) in *.
    pose proof (rr_needed_facts n (16 * off) (proj1 N) ltac:(clear - Ho; lia)) as NN. fold nn in NN. unfold UNIT, IB in NN.
    assert (EBASE : A - (B + STR * i + 16) = 16 * off) by (clear - I0 HPB EA; lia).
    assert (MWR : 0 <= meta_word (MR st g) < 2^64) by (unfold meta_word; clear - LI FB GSC ML; lia).
    set (QB2 := fun ms => (on = nn /\ exists a3' a5'',
            ms = MS (mkR ra sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' (Z_to_bv 64 nn) (wz G) a0 a1 (wz B) a3' (Z_to_bv 64 on) a5''
                        (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3'' t4' t5 t6)
                    F (Z_to_bv 64 0x17fc4) fc None m1 rom)
        \/ (on <> nn /\ exists a5'',
            ms = MS (mkR (Z_to_bv 64 0x17fb8) sp' gp tp (Z_to_bv 64 E) (Z_to_bv 64 (B + STR * i + 16)) t2'' (Z_to_bv 64 nn) (wz G) (wz B) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 on) a5''
                        (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 t3'' t4' t5 t6)
                    F (Z_to_bv 64 rmremap_entry) fc None m1 rom)).
    eapply implM_evt.
    { eapply (rr_big_walk ra sp' gp tp s0 s7 s8 s9 s10 s11 t5 t6 a0 a1 (wz G) t2'' t3'' a5' s3 s4 s5 s6 t4' F fc m1 A n B 63 (meta_word (MR st g)) (m_maplen (MR st g)) E (E - A - k) STR i QB2).
      - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
      - rewrite A1. apply unsigned_lit. clear - N; lia.
      - exact N.
      - clear - HBr R0 B0; lia.
      - clear - HPB EA Ho I0; lia.
      - exact SI0.
      - clear - ABND R0 Hk; lia.
      - exact MWR.
      - apply mword_page; clear - LI FB GSC ML; lia.
      - intros EQ a3' a5''. apply evt_done. left. rewrite EBASE in EQ |- *. split; [exact EQ|]. exists a3', a5''. reflexivity.
      - intros NEQ a5''. apply evt_done. right. rewrite EBASE in NEQ |- *. split; [exact NEQ|]. exists a5''. reflexivity. }
    cbv beta. intros ms3 [[EQ (a3' & a5'' & ->)]|[NEQ (a5'' & ->)]].
    + (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq on nn) EQ). apply implM_ret.
      (* [comment removed for export] *)
      (nelim MSL 6%nat; intros aa ar kk Haa Hkk Eg).
      (nelim (WA aa ar Haa) 7%nat; intros rga Hra A0a A4096 AMOD NKa LRa).
      assert (HG : G = r_base rga + snd aa + (24 + 40 * kk)).
      { subst G. rewrite Eg. rewrite (conc_region' st (aadd aa (AREA_HDR + META_SIZE * kk)) rga Hra). unfold aadd, AREA_HDR, META_SIZE. cbn [snd]. clear; lia. }
      unfold NSLOTS in Hkk.
      (nelim (WR _ _ Hra) 5%nat; intros Ra0 _ _ RaC RaF). unfold alloc_ceiling in RaC.
      assert (NEa : fst aa <> fst b) by (intros X; rewrite X, Hr in Hra; injection Hra as <-; exact (NKa Kr)).
      assert (GNB : G + 40 <= B \/ B + on <= G).
      { destruct (DJR _ _ _ _ Hra Hr NEa) as [GB|GB]; rewrite ?(lr_lo_group _ Kr) in GB; clear - GB HG LRa Hkk A4096 HBr EON Hb0; lia. }
      assert (GNI : G + 40 <= 0x10000 \/ 0x56000 <= G).
      { destruct (rreserved_disjoint1 _ _ RaF ltac:(clear - A0a A4096; lia)) as [X|X]; clear - X HG LRa Hkk A4096 A0a; lia. }
      assert (MM1 : rw_cells usegs m1 G [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g))); C8 (wz B); C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g))); C8 (wz (meta_word (MR st g)))]).
      { unfold meta_cells in MM. rewrite Hmem in MM. unfold pw at 3 in MM. cbn [oconc] in MM. fold B in MM.
        eapply rw_cells_transport; [exact MM| exact MU1| exact WM1|]. cbn. clear - G40 LO' SLO'. lia. }
      assert (BE1 : bytes_at usegs m1 E [b8 0]) by (apply XP1; [exact BE| cbn [length]; change (Z.of_nat 1) with 1; clear - ABND LO'; subst E; lia]).
      eapply evt_mono.
      { eapply (rr_fin2_walk sp' gp tp (Z_to_bv 64 (E - (E - A - k))) s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 lo)
          with (P := A) (n := n) (G := G) (k := i + 32 * Z.min (E - A - k) 5) (Bold := B) (mword := meta_word (MR st g))
               (avail := m_avail (MR st g)) (freed := m_freed (MR st g)) (prev := pw st (m_prev (MR st g))) (next := pw st (m_next (MR st g)));
          rewrite ?SP'; first [exact MM1| exact MI1| exact FR1| exact ST1| exact MWR| idtac].
        - rewrite A0. apply unsigned_lit. clear - ABND R0 Hk; lia.
        - rewrite A1. apply unsigned_lit. clear - N; lia.
        - unfold wz. apply unsigned_lit. clear - G0 G40; lia.
        - clear - HBr R0 Hb0; lia.
        - clear - EQ EON HBr Hb0 RC LO'; lia.
        - clear - EQ EON HBr Hb0 RC; lia.
        - clear - Ho; lia.
        - clear - N; lia.
        - clear - NN; lia.
        - clear - NN N; lia.
        - clear - NN; lia.
        - clear - Hi LI ABND; subst E; lia.
        - clear - G40 LO'; lia.
        - clear - GNB EA HPB Ho EQ; lia.
        - replace (B + 16 * off + 16 - 3) with (A - 3) by (clear - EA HPB; lia). apply XP1; [exact B3|]. cbn [length]. change (Z.of_nat 1) with 1. clear - ABND LO'; lia.
        - eapply wr_at_transport; [| exact WM1]. eapply wr_at_sub; [exact HWr| clear - ABND HBr Hb0 EA HPB; lia| clear - EQ EON HBr Hb0 ABND EA HPB; lia].
        - clear - SLO' LO'; lia. }
      cbv beta. intros ms' nelH_; (nelim nelH_ 7%nat; intros mF RET MUF WMF MIF CH BEF).
      replace (B + 16 * off + 16) with A in RET by (clear - EA HPB; lia).
      replace (B + nn - 4) with E in RET, BEF by (clear - EQ ESTR63 HPB; subst E; lia).
      rewrite <- EQ in CH. cbv delta [on] in CH. rewrite mword_same in CH by (clear - LI FB GSC ML; lia).
      assert (EMF : mF = m1).
      { apply mem_ext. intros x. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR.
        destruct (Z_lt_dec (bv_unsigned x) G) as [L1|L1]; [| destruct (Z_lt_dec (bv_unsigned x) (G + 40)) as [L2|L2]].
        2:{ eapply (bytes_at_same_byte m1 mF G); [apply rw_cells_bytes_at; exact MM1| apply rw_cells_bytes_at; exact CH| cbn; exact GNI| cbn; clear - L1 L2; lia]. }
        all: destruct (Z.eq_dec (bv_unsigned x) E) as [L3|L3];
          [eapply (bytes_at_same_byte m1 mF E [b8 0]); [exact BE1| exact BEF| cbn [length]; change (Z.of_nat 1) with 1; clear - RI ABND; subst E; lia| cbn [length]; change (Z.of_nat 1) with 1; clear - L3; lia]|].
        all: apply MUF; cbn; refine (conj _ (conj _ (conj _ I))); (first [clear - L1 L2 L3 XR EQ ESTR63 HPB | clear - L1 L3 XR EQ ESTR63 HPB]; subst E; lia). }
      rewrite EMF in RET.
      eapply (rr_inplace_final ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP N m1 ms' errv MU1 WM1); [| | exact ERR1| exact RET].
      * unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. clear - NN EQ ESTR63 HPB EA; lia.
      * unfold RF_realloc_G1.XE, RF_realloc_G1.XP0, RF_realloc_G1.Xstride, IB. fold STR P0. clear - NN N EQ ESTR63 HPB EA; lia.
    + (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq on nn) NEQ).
      (nelimp GL 5%nat; intros _ _ _ GOT GRD).
      assert (GOT1 : rw_cells usegs m1 RGOT_SSP [C8 (wz RSSP_GUARD)]).
      { eapply rw_cells_transport; [exact GOT| exact MU1| exact WM1|]. unfold RGOT_SSP. cbn. clear - SPR SLO' LO'; lia. }
      assert (GRD1 : rw_cells usegs m1 RSSP_GUARD [C8 ssp_guard_val]).
      { eapply rw_cells_transport; [exact GRD| exact MU1| exact WM1|]. unfold RSSP_GUARD. cbn. clear - SPR SLO' LO'; lia. }
      assert (WR1 : wr_at usegs m1 B on). { rewrite HBr, Hb0, Z.add_0_r, EON. eapply wr_at_transport; [exact HWr| exact WM1]. }
      assert (BON : 0 < B /\ B mod 4096 = 0 /\ B + on <= alloc_ceiling /\ ranges_free ref_reserved B on = true /\ 4096 <= on /\ on mod 4096 = 0).
      { rewrite HBr, Hb0, Z.add_0_r, EON. split; [exact R0|]. split; [exact RAL|]. split; [exact RC|]. split; [exact RFr|].
        rewrite <- EON. subst on. split; [clear - MLP; lia| apply Z_mod_mult]. }
      (nelim BON 6%nat; intros BO0 BOA BOC BOF ON4 ONA).
      pose proof (rreserved_disjoint1 _ _ BOF ltac:(clear - ON4; lia)) as BNI.
      (nelim IV 9%nat; intros L LS BL INV LIVE RESV SEC CORR HkBL).
      eapply implM_bind.
      { apply implM_msys_of_impl.
        eapply rmremap_spec with (old := B) (on := on) (nn := nn) (errv := errv) (canary := ssp_guard_val) (lo := lo); rewrite ?SP';
          first [exact ERR1| exact GOT1| exact GRD1| exact MI1| exact WR1| exact TP| exact BO0| exact BOA| exact BOF| exact ONA| reflexivity| idtac].
        - exact ST1.
        - clear - ON4; lia.
        - clear - NN N Ho; lia.
        - clear - NN; lia.
        - exact BOC.
        - clear - SLO' LO'; lia.
        - exact LO. }
      cbv beta. intros a s' ms3 [-> HP]. destruct a as [e| |d].
      * (* [comment removed for export] *)
        (nelim HP 22%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m' -> MUE WME MIE STE ERRE HE).
        eapply (implM_evt usegs _ _ _ (fun ms => ms = MS (mkR (Z_to_bv 64 0x17fb8) sp' gp tp u0 u1 u2 (Z_to_bv 64 nn) (wz G) a0 a1 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) v4 v5 v6 v7
                     (Z_to_bv 64 (E - (E - A - k))) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 RR_MALLOC) fc None m' rom)).
        { rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
          step. step. step. step. step. if_cases K1; zify_cond K1.
          - apply evt_done. reflexivity.
          - exfalso. clear - K1. exact (K1 eq_refl). }
        cbv beta. intros ms4 ->.
        replace (Z_to_bv 64 (E - (E - A - k))) with (Z_to_bv 64 (A + k)) by (f_equal; clear; lia).
        rewrite SP' in STE.
        apply (rr_fallback_thm ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0
                 PERM Hst MRP BLK AR Hin BA LEN AV HB LO SLO TP A0 A1 N m' (Z_to_bv 64 e)); [| | exact MIE| exact STE| | exact ERRE].
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MUE]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X [Y _]]. rewrite SP'. cbn. split; [clear - X; lia|]. split; [exact Y| exact I].
        -- eapply wmono_trans; [exact WM1| exact WME].
        -- eapply rw_cells_transport; [exact FR1| exact MUE| exact WME|]. rewrite SP'. rewrite TP. unfold RATP. rewrite unsigned_lit by (clear; lia). cbn. clear - SPR SLO' LO'; lia.
      * (* [comment removed for export] *)
        destruct (remap_grow_ok (ps_m s) B on nn) eqn:GROW; [| apply implM_unr].
        assert (GF : nn <= on \/ (B + nn <= alloc_ceiling /\ ranges_free (live_ranges st) (B + on) (nn - on) = true)).
        { unfold remap_grow_ok in GROW. apply Bool.orb_true_iff in GROW. destruct GROW as [X|X].
          - left. apply Z.leb_le. exact X.
          - right. apply Bool.andb_true_iff in X. destruct X as [X Y]. apply Z.leb_le in X. rewrite <- Hst, live_ranges_strip in Y. unfold alloc_ceiling in X. auto. }
        assert (GF2 : on < nn -> forall q rq, s_regions st !! q = Some rq -> B + nn <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= B + on).
        { intros LT q rq Hq. destruct GF as [X|[_ Y]]; [exfalso; clear - X LT; lia|].
          pose proof (ranges_free_regions st _ _ q rq Y Hq) as Z1. pose proof (live_range_pos _ _ _ _ _ q rq INV Hq) as Z2.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z1, Z2; unfold PGSZ in *; clear - Z1 Z2 LT; lia. }
        assert (LRP : forall q rq, s_regions st !! q = Some rq -> lr_lo rq < r_base rq + round_up_pg (r_len rq)).
        { intros q rq Hq. pose proof (live_range_pos _ _ _ _ _ q rq INV Hq) as Z2.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z2; unfold PGSZ in *; clear - Z2; lia. }
        assert (GF3 : on < nn -> B + nn <= alloc_ceiling /\ ranges_free ref_reserved (B + on) (nn - on) = true).
        { intros LT. destruct GF as [X|[X Y]]; [exfalso; clear - X LT; lia|]. split; [exact X|].
          apply ranges_free_intro. intros b0 k0 Hin0'. apply (ranges_free_In _ _ _ _ _ Y). unfold live_ranges. apply in_or_app. left. rewrite Hres. exact Hin0'. }
        assert (GFB : nn <= on \/ B + nn <= alloc_ceiling) by (destruct GF as [X|[X _]]; [left| right]; exact X).
        assert (DNI2 : B + nn <= 0x10000 \/ 0x56000 <= B).
        { pose proof (rreserved_disjoint1 _ _ BOF ltac:(clear - ON4; lia)) as X.
          destruct (Z_lt_dec on nn) as [LT|GE]; [| clear - X GE; lia].
          destruct (GF3 LT) as [_ Y]. pose proof (rreserved_disjoint1 _ _ Y ltac:(clear - LT; lia)) as X2. clear - X X2 LT ON4; lia. }
        assert (SANE : mrm_sane_inplace B on nn).
        { intros LT. destruct (GF3 LT) as [X Y]. split; [exact X| exact Y]. }
        (nelim (HP SANE) 21%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 ST2 ERR2). clear HP.
        rewrite SP' in MU2, ST2.
        eapply (implM_bind usegs _ _ _ (fun _ sx msx => sx = set_m (cs_remap (ps_m s) (fst b) g B nn) s /\ msx = _)).
        { apply implM_upd. apply evt_done. split; reflexivity. }
        cbv beta. intros [] sx ms4 [-> ->]. apply implM_ret.
        rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
        step. step. step.
        assert (WR2 : wr_at usegs m2 B on) by (eapply wr_at_transport; [exact WR1| exact WM2]).
        eapply (rr_remap_final ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                  PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP A0 A1 N B m2 (mrm_inplace B on nn m2) errv C1).
        -- subst sc. exact C2.
        -- exact BO0.
        -- exact BOA.
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. destruct (Z_lt_dec on nn) as [LT|GE]; [exact (proj1 (GF3 LT))| clear - GE BOC; unfold alloc_ceiling; lia].
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. apply rreserved_free_intro; [clear - NN; lia| exact DNI2].
        -- unfold RF_realloc_G2.Xnn, UNIT. fold nn. intros q rq Hq NE.
           destruct (DJR _ _ _ _ Hq Hr NE) as [D1|D1]; rewrite ?(lr_lo_group _ Kr), <- ?HBr in D1.
           ++ left. clear - D1 HBr Hb0. lia.
           ++ destruct (Z_lt_dec on nn) as [LT|GE].
              ** destruct (GF2 LT q rq Hq) as [D2|D2]; [right; exact D2|]. pose proof (LRP q rq Hq) as L3. exfalso. clear - D1 D2 L3 HBr Hb0 EON LT. lia.
              ** right. clear - D1 GE HBr Hb0 EON. lia.
        -- left. reflexivity.
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
        -- eapply wmono_trans; [exact WM1| exact WM2].
        -- exact ERR2.
        -- eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR SLO' LO'; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros a' Ha N1 N2.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply unmaps_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - Ha N1 N2 HC BO0 BOC ON4 NN; lia.
           ++ apply zeros_outside; rewrite ?wa_unsigned by (clear - Ha; lia); clear - Ha N1 N2 HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply unmaps_outside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NN HC; lia); clear - Hj HC BO0 BOC ON4 NN; lia.
           ++ apply zeros_outside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NEQ GFB HC NN; lia); clear - Hj HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC]; [exfalso; clear - Hj HC; lia|].
           apply zeros_inside; rewrite ?wa_unsigned by (clear - Hj BO0 BOC ON4 NEQ GFB HC NN; lia); clear - Hj HC BO0 BOC ON4 NEQ GFB NN; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold nn B.
           unfold mrm_inplace. rewrite (proj2 (Z.eqb_neq nn on)) by (clear - NEQ; lia).
           destruct (Z.ltb_spec nn on) as [HC|HC].
           ++ apply wr_at_unmaps_other; [clear - BO0 BOC ON4 NN HC; lia| clear - BO0 BOC ON4 NN HC; lia| clear - BO0 BOC ON4 NN HC; lia| | clear; lia].
              eapply wr_at_sub; [exact WR2| clear; lia| clear - HC; lia].
           ++ replace nn with (on + (nn - on)) at 2 by (clear; lia). apply wr_at_join; [| | clear - ON4; lia| clear - HC; lia].
              ** apply wr_at_zeros; [clear - BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| exact WR2].
              ** apply wr_at_zeros_new; [clear - BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia| clear - HC NEQ GFB BO0 BOC ON4; lia].
        -- exact MI2.
        -- exact ST2.
      * (* [comment removed for export] *)
        destruct (remap_move_ok (ps_m s) nn d) eqn:MOVE; [| apply implM_unr].
        unfold remap_move_ok in MOVE. rewrite !Bool.andb_true_iff in MOVE. destruct MOVE as [[[MD0 MDA] MDC] MRF].
        apply Z.ltb_lt in MD0. apply Z.eqb_eq in MDA. apply Z.leb_le in MDC. rewrite <- Hst, live_ranges_strip in MRF. unfold alloc_ceiling in MDC.
        assert (MRR : ranges_free ref_reserved d nn = true).
        { apply ranges_free_intro. intros b0 k0 Hin0'. apply (ranges_free_In _ _ _ _ _ MRF). unfold live_ranges. apply in_or_app. left. rewrite Hres. exact Hin0'. }
        assert (MDJ : forall q rq, s_regions st !! q = Some rq -> r_base rq + round_up_pg (r_len rq) <= d \/ d + nn <= lr_lo rq).
        { intros q rq Hq. pose proof (ranges_free_regions st _ _ q rq MRF Hq) as Z1.
          unfold region_live_range, lr_lo in *. destruct (r_kind rq); cbn [fst snd] in Z1; unfold PGSZ in *; clear - Z1; lia. }
        assert (SANE : mrm_sane_moved B on nn d).
        { split; [exact MRR|]. destruct (MDJ _ _ Hr) as [X|X]; rewrite ?(lr_lo_group _ Kr) in X; clear - X HBr Hb0 EON; lia. }
        (nelim (HP SANE) 26%nat; intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 ST2 ERR2 ONN DNE D0' DA' DCE'). clear HP.
        rewrite SP' in MU2, ST2. unfold alloc_ceiling in DCE'.
        pose proof SANE as [_ DSEP].
        eapply (implM_bind usegs _ _ _ (fun _ sx msx => sx = set_m (cs_remap (ps_m s) (fst b) g d nn) s /\ msx = _)).
        { apply implM_upd. apply evt_done. split; reflexivity. }
        cbv beta. intros [] sx ms4 [-> ->]. apply implM_ret.
        rewrite ret_pc_even by (clear; first [lia| reflexivity]). subst rom.
        step. step. step.
        assert (WR2 : wr_at usegs m2 B on) by (eapply wr_at_transport; [exact WR1| exact WM2]).
        assert (HSRC : forall j, 0 <= j < on -> m2 (wa (B + j)) <> None).
        { intros j Hj. (nelim WR2 3%nat; intros _ _ W). specialize (W j Hj). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by (clear - Hj BO0 BOC; lia); clear - Hj BNI; lia). exact W. }
        eapply (rr_remap_final ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB p A k n lo Bx old st LB0 g b r i off
                  PERM Hst MRP BLK AR RF Hin Hin0 BA LEN AV HB LO SLO TP A0 A1 N d m2 (move_mem m2 B d on nn) errv C1).
        -- subst sc. exact C2.
        -- exact D0'.
        -- exact DA'.
        -- exact DCE'.
        -- exact MRR.
        -- intros q rq Hq NE. exact (MDJ q rq Hq).
        -- right. exact DSEP.
        -- eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
           ++ intros x [X _]. cbn. split; [clear - X; lia| exact I].
        -- eapply wmono_trans; [exact WM1| exact WM2].
        -- exact ERR2.
        -- eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR SLO' LO'; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros a' Ha N1 N2.
           apply (move_mem_outside m2 B d on nn); rewrite ?wa_unsigned by (clear - Ha; lia);
             clear - Ha N1 N2 BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           apply (move_mem_inside m2 B d on nn); clear - Hj BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xon, RF_realloc_G2.Xnn, RF_realloc_G2.XB, UNIT. fold on nn B. intros j Hj.
           apply (move_mem_tail m2 B d on nn); clear - Hj BO0 BOC ON4 NN D0' DCE' ONN DSEP; lia.
        -- (* [comment removed for export] *) unfold RF_realloc_G2.Xnn, UNIT. fold nn.
           apply (wr_at_mremap_move usegs m2 B d on nn); [clear - BO0 BOC ON4; lia| clear - NN D0' DCE'; lia| clear - ON4; lia| exact ONN| exact DSEP| exact HSRC].
        -- exact MI2.
        -- exact ST2.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac clear_complex :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : _ -> _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Ltac prune :=
  clear_complex;
  repeat match goal with H := ?b |- _ => lazymatch b with context [Z.min _ _] => clearbody H end end;
  repeat match goal with H : context [Z.to_nat _] |- _ => clear H end.
Ltac liac := prune; lia.
Notation RAREACH := (AREACH_from ref_reserved).
End RF_realloc_spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Frame SCPS NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KRaw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KRaw.ImplSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Export UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_A Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog KInv MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KInv2 KRaw Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocM.KRawR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import KB_ReallocR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMalloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMalloc_ifaceP.
Import RF_malloc_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_realloc_fentry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_realloc_fentry.RF_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RRealloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import CJ_iface.
Import CJ_heap_inst0.
Import CJ_heap_inst.
Import RF_realloc_null.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RF_realloc_F.
Import RF_realloc_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
Lemma RHEAP_addr_in_slot : forall s LBi m p A k,
  RHEAP s LBi m -> In (p, A, k) LBi -> addr_in_slot (ps_m s) (fst p) A.
Proof.
  intros s LBi m p A k (st & LB0 & HP & Hst & MRP & [_ AR]) Hin.
  assert (Hin0 : In (p, A, k) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hin]).
  destruct (rrF_intro st m LB0 p A k AR MRP Hin0) as (g & b & r & i & off & RF).
  pose proof (rf_slot _ _ _ _ _ _ _ _ _ _ _ RF) as Hs.
  pose proof (rf_A _ _ _ _ _ _ _ _ _ _ _ RF) as HA.
  pose proof (rf_off _ _ _ _ _ _ _ _ _ _ _ RF) as Ho.
  pose proof (rf_k _ _ _ _ _ _ _ _ _ _ _ RF) as Hk.
  pose proof (rf_fit _ _ _ _ _ _ _ _ _ _ _ RF) as Hfit.
  rewrite <- Hst. intros g' idx Hs'.
  rewrite s_slots_strip in Hs'. rewrite Hs in Hs'. injection Hs' as <- <-.
  rewrite conc_strip, get_meta_rec_strip. fold (MR st g). unfold UNIT, IB in *. lia.
Qed.

Theorem lhd_realloc : realloc_scps_stmt LHEAPd.
Proof using .
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo SPB LB A k n lo old errv.
  intros (s & LBi & B & HR & -> & HO & HM & HA & HS) Hin BY LEN HSP ST Hlo Hlo2 ER MI Htp Ha0 Ha1 Hn.
  (* [comment removed for export] *)
  destruct (in_bview _ _ _ Hin) as ([[p A'] k'] & Hb & E1 & E2). cbn [blk_addr blk_size fst snd] in E1, E2. subst A' k'.
  pose proof (rrealloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBi p A k n lo B old errv
                HR Hb BY LEN HA ltac:(lia) ST Hlo Hlo2 ltac:(rewrite Htp, errno_addr_PTP; exact ER) MI Htp Ha0 Ha1 Hn) as Himpl.
  assert (Hinp : In (fst p) (map blk_slot LBi)). { apply in_map_iff. exists (p, A, k). auto. }
  pose proof (raw_realloc_etwf_closed (map blk_slot LBi) s mo p A n HO Hinp Hn (RHEAP_addr_in_slot s LBi m p A k HR Hb)) as Hwf.
  destruct (lb_remove_views LBi p A k (RHEAP_slot_nodup _ _ _ HR) (RHEAP_addr_nodup _ _ _ HR) Hb) as (V1 & V2 & V3).
  eapply scps_mono; [apply (implM_scps usegs (raw_realloc p A n) s _ _ _ mo Himpl HM Hwf)|].
  intros ms' mo' (r & s' & HQ & (HRr & Hfa & Hso & Hvo) & HM'). cbn [fst snd] in HRr.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & -> & MI' & ST' & ER' & HA' & _ & _ & Hr).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [rewrite Htp, errno_addr_PTP in ER'; exact ER'|].
  destruct r as [q|].
  - destruct Hr as (A' & junk & -> & HRng & HR' & HP & RW & HA'A). destruct HRr as [HO' Hni].
    right. exists A', junk. split; [reflexivity|]. split; [exact HRng|]. split.
    + destruct HA'A as [E|NE]; [left; exact E| right]. rewrite map_fst_bview. intros HinA.
      apply in_map_iff in HinA as (b' & E & Hb'). exact (NE b' Hb' (eq_sym E)).
    + split; [| split; [rewrite <- V2; apply cj_pres_of_rheap_pres; exact HP| exact RW]].
      exists s', ((q, A', n) :: lb_remove p LBi), B. splits; auto.
      * cbn [map]. rewrite V2. reflexivity.
      * cbn [map]. rewrite V1. exact HO'.
  - destruct Hr as (-> & HR' & HP). left. split; [reflexivity|]. split; [| apply cj_pres_of_rheap_pres; exact HP].
    exists s', LBi, B. splits; auto.
Qed.

(* [comment removed for export] *)
Definition PHI0 : cj_heap_iface := PHI lhd_realloc rrealloc_null_spec.


End CeilWrap.
(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
