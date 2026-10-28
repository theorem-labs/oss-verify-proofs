(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs Virgin.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_A HP_RMalloc_fp HP_RF_malloc_enf HP_RAllocSlot_iface HP_RF_malloc_entry HP_RF_malloc_join.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_malloc_small () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_last_idx"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freeable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_sizeclass"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_maplen"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RP_1.rcoarse_post"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_small.coarse_sc"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RDEBRUIJN"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_wrap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_malloc_entry.rDB32"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_malloc_entry.rdbi"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.lowbit"; "RP_2.rfc_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_avail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctz32"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.under_virgin"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_to_class"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.FUEL"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.malloc_small_ctrl"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"].

Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rcoarse_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (st : mstate) (n sc' : Z) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3,
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                  (pw st (active st sc')) (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40830) fc None m (seg_rom rsegs)
    /\ a0 = wz (sxv (match active st sc' with Some g => m_avail (get_meta_rec st g) | None => 0 end)).

Section COARSE.
Variables (st : mstate) (LB : list block) (m1 : mem) (t : N).
Let st1 := set_tick t st.
Hypothesis MF : RMFACTS st LB.
Hypothesis MR : rmrep st1 m1.
Hypothesis MI : mem_inv rsegs m1.

#[using="LB m1 MF MR"] Lemma ractive_ptr_facts sc g : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "P,(0.$1.(2.Vst,O2.)(3.$4.O1.))(5.(6.=(7.Vst1,O1.))(5.(8.(9.(7.Vst1,O1.)+28.)(:.VhRP,))(5.(;.Vst1,O1.)(5.(<.$4.Lb,$4.(0.$1.(=.(>.Vst,O1.))(3.$4.R1.)))(5.(5.(8.=(?.(>.Vst,O1.)))(6.(?.(>.Vst,O1.))(10.+2.+20.)))(5.(5.(8.=(11.(>.Vst,O1.)))(6.(11.(>.Vst,O1.))(10.+2.+20.)))(5.(8.=(9.(9.(9.(12.(>.Vst,O1.))(13.+20.(14.(>.Vst,O1.))))(13.+40.(15.(>.Vst,O1.))))(13.+1000.(16.(>.Vst,O1.)))))(6.(9.(9.(9.(12.(>.Vst,O1.))(13.+20.(14.(>.Vst,O1.))))(13.+40.(15.(>.Vst,O1.))))(13.+1000.(16.(>.Vst,O1.))))(10.+2.+40.)))))))))")
(* [comment removed for export] *).
Proof.
  intros ACT.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  ddestruct (FA sc g ACT) as (SC48 & GSC & NN).
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hm; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hm). cbv zeta in FG. ddestruct FG as (MSL & AV & FR & LI & FB & SC & ML & _).
  dpose (rmeta_chunk_facts st1 m1 g MR MSL) as (_ & G0 & GC & _).
  split; [exact G0|]. split; [exact GC|]. split; [exact MSL|]. split; [exists b; reflexivity|]. split; [exact AV|]. split; [exact FR|].
  pose proof (mf_maplen _ _ MF g b Hm) as MP. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MP. lia.
Qed.

Ltac fin_coarse := apply evt_done; unfold rcoarse_post; deexists 4; split; [reflexivity|].

#[using="hRP LB MF MR"] Lemma rcoarse_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Psp,(17.&40.)Pgp,(17.&40.)Ptp,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa0,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps2,(17.&40.)Ps5,(17.&40.)Ps6,(17.&40.)Ps7,(17.&40.)Ps8,(17.&40.)Ps9,(17.&40.)Ps10,(17.&40.)Ps11,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pra',(17.&40.)PF,(18.&5.(17.&40.))Pfc,(17.&20.)Pn,$19.Psc,$19.P,(5.(8.=R1.)(6.R1.+30.))P,P,(6.R2.+20.)(5.(8.=(1:.R3.+1.))(6.(1:.R3.+1.)+30.))(1;.$1<.(1=.R21.R20.R1?.R12.R11.R10.R?.R>.R=.R<.R1>.R1=.R1<.R17.R16.R15.R14.R;.R:.R9.R8.R7.R6.R5.Vm1,Vst1,R4.(1>.Vst,R3.))(1?.(20.R7.(21.&40.(9.(22.&40.R21.)-30.))R20.R1?.R1>.R1=.R1<.(21.&40.R4.)(21.&40.$23.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.(21.&40.$24.)(21.&40.R3.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R6.(21.&40.+40774.)R5.(25.(17.&40.))Vm1,(26.$1<.)))")
(* [comment removed for export] *).
Proof.
  intros until sc. intros SC48 SC1.
  dpose MR as (WF & (CXH & CXA & CXU & _) & (ML & NL & _) & _).
  pose proof (mf_usage _ _ MF) as FU. change (fact_usage (strip st)) with (fact_usage st) in FU.
  unfold RNEED_LOCKS, RCTX, RMLOCK, RDEBRUIJN in *. rceilb.
  (* [comment removed for export] *)
  step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
  pose proof (actives_nth st1 sc ltac:(lia)) as NTH. change (active st1 sc) with (active st sc) in NTH.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (u64arr_read rsegs mc _ (actives st1) sc _ (wa (512968 + 80 + 8 * sc)) CXA NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  step.
  (* [comment removed for export] *)
  assert (J40 : forall (a0' a1' a2' a3' : word) (sc' : Z), 0 <= sc' < 48 ->
    evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960) a0' a1' a2' a3' a4 a5 a6 a7
               (pw st1 (active st sc')) (Z_to_bv 64 68135) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40820) fc None m1 (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc' SC'.
    destruct (active st sc') as [g|] eqn:ACT'.
    - ddestruct (ractive_ptr_facts sc' g ACT') as (G0 & GC & MSL & _ & AV & FR & MW). rceilb.
      pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & _).
      change (get_meta_rec st1 g) with (get_meta_rec st g) in MM. unfold meta_cells, meta_word in MM.
      unfold pw. cbn [oconc]. set (gw := wz (conc st1 g)) in *.
      assert (HG : bv_unsigned gw = conc st1 g) by (subst gw; apply wz_unsigned; lia).
      rewrite <- HG in MM.
      step. if_cases K; zify_cond K. { exfalso. rewrite HG in K. lia. }
      step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g))) by lia. step.
      apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. deexists 4. split; [subst gw; reflexivity| reflexivity].
    - unfold pw. cbn [oconc].
      step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
      step.
      apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. deexists 4. split; [reflexivity| reflexivity]. }
  (* [comment removed for export] *)
  assert (J4c : forall (a0' a1' a2' a3' : word) (sc' : Z), active st sc' = None ->
    evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960) a0' a1' a2' a3' a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 68135) (Z_to_bv 64 sc') s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4082c) fc None m1 (seg_rom rsegs))).
  { intros a0' a1' a2' a3' sc' ACT'. step.
    apply evt_done. unfold rcoarse_post. change (active st1 sc') with (active st sc'). rewrite ACT'. deexists 4. split; [reflexivity| reflexivity]. }
  (* [comment removed for export] *)
  assert (J2c : forall (a1' a2' a3' s4' : word) (sc' : Z), 0 <= sc' < 48 ->
    evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n sc')
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960) (Z_to_bv 64 sc') a1' a2' a3' a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 68135) s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x4080c) fc None m1 (seg_rom rsegs))).
  { intros a1' a2' a3' s4' sc' SC'.
    step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc'), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
    pose proof (actives_nth st1 sc' ltac:(lia)) as NTH'. change (active st1 sc') with (active st sc') in NTH'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read rsegs mc _ (actives st1) sc' _ (wa (512968 + 80 + 8 * sc')) CXA NTH' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD' end.
    step. step. apply J40. exact SC'. }
  (* [comment removed for export] *)
  step.
  destruct (active st sc) as [g|] eqn:ACT.
  - (* [comment removed for export] *)
    ddestruct (ractive_ptr_facts sc g ACT) as (G0 & GC & _). rceilb.
    unfold pw. cbn [oconc].
    if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    clear K1.
    replace (coarse_sc st sc) with sc by (unfold coarse_sc; rewrite ACT; reflexivity).
    change (wz (conc st1 g)) with (pw st1 (Some g)). rewrite <- ACT. apply J40. exact SC48.
  - (* [comment removed for export] *)
    unfold pw. cbn [oconc].
    if_cases K1; zify_cond K1. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
    clear K1.
    assert (CS : forall b : bool, (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = b ->
              coarse_sc st sc = if b then
                (let usage1 := usage st (Z.lor sc 1) in
                 let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
                 if usage1 <=? 12 then Z.lor sc 1 else sc) else sc).
    { intros b Hb. unfold coarse_sc. rewrite ACT, Hb. reflexivity. }
    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit sc) in K2 by lia.
    + (* [comment removed for export] *)
      rewrite (CS false) by (subst sc; reflexivity).
      change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
    + (* [comment removed for export] *)
      step. step. step. if_cases K3; zify_cond K3; rewrite (swrap32_small (sc + -4)), land_ones64 in K3 by lia.
      * (* [comment removed for export] *)
        rewrite (CS false). 2:{ destruct (Z.lt_ge_cases sc 4); [replace (4 <=? sc) with false by (symmetry; apply Z.leb_gt; lia); reflexivity|].
             replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). destruct (4 <=? sc); reflexivity. }
        change (wz 0) with (pw st1 None). rewrite <- ACT. apply J40. exact SC48.
      * assert (SC432 : 4 <= sc < 32) by (Z.div_mod_to_equations; lia). clear K3. rename K2 into NE6.
        (* [comment removed for export] *)
        step. step. if_cases K4; zify_cond K4; rewrite ?(unsigned_lit sc) in K4 by lia.
        -- (* [comment removed for export] *)
           rewrite (CS false).
           2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
               replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
               destruct (Z.even sc) eqn:EV; [|reflexivity]. exfalso. apply K4. apply (proj2 (land_1_even sc)). exact EV. }
           step. step. apply J4c. exact ACT.
        -- pose proof (proj1 (land_1_even sc) K4) as EV.
           (* [comment removed for export] *)
           pose proof (usages_nth st1 sc ltac:(lia)) as NTHU. change (usage st1 sc) with (usage st sc) in NTHU.
           lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
             pose proof (u64arr_read rsegs mc _ (usages st1) sc _ (wa (512968 + 464 + 8 * sc)) CXU NTHU ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU end.
           step. pose proof (FU sc) as FUsc.
           step. if_cases K6; zify_cond K6; rewrite ?wz_unsigned in K6 by lia.
           ** (* [comment removed for export] *)
              assert (COND : (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) = true).
              { replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia).
                replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
                replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
                rewrite EV. replace (usage st sc =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
              specialize (SC1 ltac:(lia)). set (sc1 := Z.lor sc 1) in *.
              (* [comment removed for export] *)
              step. rewrite (unsigned_lit sc) by lia. fold sc1.
              step. rewrite sextw_small by lia. step. rewrite (unsigned_lit sc1), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
              pose proof (actives_nth st1 sc1 ltac:(lia)) as NTH1. change (active st1 sc1) with (active st sc1) in NTH1.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
                pose proof (u64arr_read rsegs mc _ (actives st1) sc1 _ (wa (512968 + 80 + 8 * sc1)) CXA NTH1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD1 end.
              step.
              pose proof (usages_nth st1 sc1 ltac:(lia)) as NTHU1. change (usage st1 sc1) with (usage st sc1) in NTHU1.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
                pose proof (u64arr_read rsegs mc _ (usages st1) sc1 _ (wa (512968 + 464 + 8 * sc1)) CXU NTHU1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDU1 end.
              step. pose proof (FU sc1) as FU1.
              (* [comment removed for export] *)
              set (u1 := match active st sc1 with
                         | None => usage st sc1 + 3
                         | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st sc1)) in
                                     if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st sc1 + 3 else usage st sc1 end).
              assert (U1 : 0 <= u1 < 2^61).
              { unfold u1. destruct (active st sc1); [match goal with |- context [if ?c then _ else _] => destruct c end|]; lia. }
              assert (CS1 : coarse_sc st sc = if u1 <=? 12 then sc1 else sc).
              { rewrite (CS true COND). reflexivity. }
              clear CS.
              assert (J20 : forall (a2' a3' : word),
                evt rsegs (rcoarse_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m1 st1 n (coarse_sc st sc))
                  (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 512960) (Z_to_bv 64 sc1) (wz u1) a2' a3' a4 a5 a6 a7
                           (Z_to_bv 64 0) (Z_to_bv 64 68135) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40800) fc None m1 (seg_rom rsegs))).
              { intros a2' a3'. step. step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
                - (* [comment removed for export] *)
                  rewrite CS1. replace (u1 <=? 12) with true by (symmetry; apply Z.leb_le; lia). apply J2c. exact SC1.
                - (* [comment removed for export] *)
                  step. rewrite CS1. replace (u1 <=? 12) with false by (symmetry; apply Z.leb_gt; lia). apply J2c. exact SC48. }
              change (Z_to_bv 64 0) with (wz 0).
              destruct (active st sc1) as [g1|] eqn:ACT1.
              +++ (* [comment removed for export] *)
                  ddestruct (ractive_ptr_facts sc1 g1 ACT1) as (G10 & G1C & MSL1 & _ & AV1 & FR1 & MW1). rceilb.
                  pose proof (rmeta_chunk_facts st1 m1 g1 MR MSL1) as (MM1 & _).
                  change (get_meta_rec st1 g1) with (get_meta_rec st g1) in MM1. unfold meta_cells, meta_word in MM1.
                  unfold pw. cbn [oconc]. set (gw := wz (conc st1 g1)) in *.
                  assert (HG : bv_unsigned gw = conc st1 g1) by (subst gw; apply wz_unsigned; lia).
                  rewrite <- HG in MM1.
                  step. if_cases K7; zify_cond K7. { exfalso. rewrite HG in K7. lia. } clear K7.
                  cbn [default from_option id] in u1.
                  (* [comment removed for export] *)
                  step. rewrite (sx32_wz_sxv (m_avail (get_meta_rec st g1))) by lia.
                  pose proof (sxv_range (m_avail (get_meta_rec st g1))) as RA1.
                  step. if_cases K8; zify_cond K8; rewrite ?wz_unsigned in K8 by lia.
                  *** (* [comment removed for export] *)
                      assert (NA : m_avail (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K8; apply K8; reflexivity).
                      replace (wz (usage st sc1)) with (wz u1).
                      2:{ unfold u1. replace (m_avail (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NA). reflexivity. }
                      apply J20.
                  *** apply (proj1 (sxv_zero (m_avail (get_meta_rec st g1)) ltac:(lia))) in K8.
                      (* [comment removed for export] *)
                      step. rewrite (sx32_wz_sxv (m_freed (get_meta_rec st g1))) by lia.
                      pose proof (sxv_range (m_freed (get_meta_rec st g1))) as RF1.
                      step. if_cases K9; zify_cond K9; rewrite ?wz_unsigned in K9 by lia.
                      ---- assert (NF : m_freed (get_meta_rec st g1) <> 0) by (intros E; rewrite E in K9; apply K9; reflexivity).
                           replace (wz (usage st sc1)) with (wz u1).
                           2:{ unfold u1. rewrite K8. replace (m_freed (get_meta_rec st g1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NF). reflexivity. }
                           apply J20.
                      ---- apply (proj1 (sxv_zero (m_freed (get_meta_rec st g1)) ltac:(lia))) in K9.
                           (* [comment removed for export] *)
                           step. rewrite (wz_unsigned (usage st sc1)) by lia.
                           replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1).
                           2:{ unfold u1. rewrite K8, K9. reflexivity. }
                           apply J20.
              +++ (* [comment removed for export] *)
                  unfold pw. cbn [oconc].
                  step. if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K7 by lia. lia. } clear K7.
                  step. rewrite (wz_unsigned (usage st sc1)) by lia.
                  replace (Z_to_bv 64 (usage st sc1 + 3)) with (wz u1) by reflexivity.
                  apply J20.
           ** (* [comment removed for export] *)
              rewrite (CS false).
              2:{ replace (4 <=? sc) with true by (symmetry; apply Z.leb_le; lia). replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia).
                  replace (sc =? 6) with false by (symmetry; apply Z.eqb_neq; lia). rewrite EV.
                  replace (usage st sc =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
              step. step. apply J4c. exact ACT.
Qed.
End COARSE.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End RP_1.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Section RP_2. Context {hRP : run_params}.
#[using="Type"] Lemma mul_srliw27_sxv k : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "P,(5.(8.=O1.)(6.O1.+20.))(0.$19.(27.&20.(28.(29.&20.(22.&40.(21.&40.(13.(22.&40.(2:.(2;.(10.+2.O1.))))$2<.))))+1;.))(2=.O1.))")
(* [comment removed for export] *).
Proof.
  intros Hk. unfold rdbi. rewrite (wz_unsigned (sxv (2 ^ k))) by apply sxv_range.
  rewrite unsigned_lit_wrap. change (bv_wrap 32 ((sxv (2 ^ k) * rDB32) mod 2 ^ 64)) with (((sxv (2 ^ k) * rDB32) mod 2^64) mod 2^32).
  rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rfc_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 ra' nw gw s4v : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (G avail k : Z) (prev next memw : word) (freed mword : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Lms',$2>.(<.(17.&40.)La0,(17.&40.)(<.(17.&40.)La1,(17.&40.)(<.(17.&40.)La2,(17.&40.)(<.(17.&40.)La3,(17.&40.)(<.P,(17.&40.)(2?.(17.&8.))Lm3,P,(17.&40.)(2?.(17.&8.))(5.(0.$2>.R6.(1?.(20.O?.(21.&40.(9.(22.&40.O24.)-30.))O23.O22.O1:.O19.O18.O>.(21.&40.$23.)R5.R4.R3.R2.O17.O16.O15.O14.O=.(2:.O6.)O<.O21.O20.O1?.O1>.O1=.O1<.O1;.O13.O12.O11.O10.)O;.(21.&40.+4088<.)O:.(25.(17.&40.))R1.(26.$1<.)))(5.(0.P,(17.&40.)(2?.(17.&8.))R1.(30.O9.(31.(9.O8.+18.))(32.(2:.(33.O7.(10.+2.O6.))))))(5.(34.(35.(36.$19.$19.)(37.$19.$19.(9.O8.+18.)(9.O8.+1<.))(38.(36.$19.$19.)))O9.R1.)(5.(39.$1<.O9.R1.)(5.(3:.$1<.R1.)(3;.$1<.R1.(22.&40.O=.)(35.$3<.(3=.O5.)(35.$3<.(3=.O4.)(35.$3<.(3=.O3.)(35.$3<.(3>.(2:.(33.O7.(10.+2.O6.))))(35.$3<.(3>.(2:.O2.))(35.$3<.(3=.(2:.O1.))(38.$3<.))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma rfast_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Psp,(17.&40.)Pgp,(17.&40.)Ptp,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps4v,(17.&40.)Ps5,(17.&40.)Ps6,(17.&40.)Ps7,(17.&40.)Ps8,(17.&40.)Ps9,(17.&40.)Ps10,(17.&40.)Ps11,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pra',(17.&40.)Pnw,(17.&40.)Pgw,(17.&40.)Pprev,(17.&40.)Pnext,(17.&40.)Pmemw,(17.&40.)PF,(18.&5.(17.&40.))Pfc,(17.&20.)Pm,P,(17.&40.)(2?.(17.&8.))PG,$19.Pavail,$19.Pk,$19.Pfreed,$19.Pmword,$19.P,(0.$19.(22.&40.R<.)R5.)P,(3;.$1<.R7.(22.&40.R=.)(35.$3<.(3=.R<.)(35.$3<.(3=.R;.)(35.$3<.(3=.R:.)(35.$3<.(3>.(2:.R5.))(35.$3<.(3>.(2:.R3.))(35.$3<.(3=.(2:.R2.))(38.$3<.))))))))P,(3:.$1<.R8.)P,(3?.(8.(9.R8.+28.)+10000.)(8.+7>000.R8.))P,(5.(6.=R8.)(6.R8.(10.+2.+20.)))P,(5.(8.=R7.)(6.R7.(10.+2.+20.)))P,(5.(8.=R7.)(6.R7.(10.+2.+40.)))P,(5.(8.=R:.)(6.R:.+20.))P,(0.$19.(40.R<.)(10.+2.R;.))(1;.$1<.(41.R30.R2?.R2>.R22.R21.R20.R1?.R1>.R1=.R1<.R2=.R2<.R2;.R27.R26.R25.R24.R1;.R1:.R19.R18.R17.R16.R15.R23.R11.R10.R?.R>.R=.R<.R14.R13.R12.R;.R:.)(1?.(20.R17.(21.&40.(9.(22.&40.R30.)-30.))R2?.R2>.R2=.R2<.R2;.R16.(21.&40.$23.)(2:.(2;.R=.))R2:.R29.R28.R27.R26.R25.R24.R15.(21.&40.$24.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R11.(21.&40.+40830.)R10.(25.(17.&40.))R?.(26.$1<.)))")
(* [comment removed for export] *).
Proof.
  intros until mword. intros HG MM MI GRES AV FRr MW HK LB.
  pose proof (munch_refl [(G + 24, G + 28)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ gw) as GWR. change (bv_modulus 64) with (2^64) in GWR.
  unfold RMLOCK, RDEBRUIJN in *.
  assert (P2 : 0 < 2 ^ k <= avail).
  { ddestruct (lowbit_nonzero avail ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range avail) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv avail)))). rewrite (negw_and_lowbit avail) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8 by lia. clear DBR.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv avail)), (wz_unsigned (sxv (2 ^ k))) by assumption.
  rewrite (swrap_word (sxv avail - sxv (2 ^ k))).
  (* [comment removed for export] *)
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             [C8 prev; C8 next; C8 memw; C4 (wz (avail - 2 ^ k)); C4 (wz freed); C8 (wz mword)]) in H;
    [| cbn [cells_bytes cbytes]; rewrite (le4_avail_sub avail (2 ^ k)) by lia; reflexivity | reflexivity | cbn; tauto ]
  end.
  (* [comment removed for export] *)
  step.
  apply evt_done. unfold rfc_post.
  deexists 4.
  lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => exists mx end.
  split; [reflexivity|].
  split. { lazymatch goal with E : ?mx = write_to_mem m _ _ |- _ => rewrite E end.
           f_equal; [unfold wa; f_equal; lia | cbn [cbytes]; apply le4_avail_sub; lia]. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. assumption.
Qed.

(* [comment removed for export] *)
End RP_2.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Section RP_3. Context {hRP : run_params}.
#[using="Type"] Lemma rcore0_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Psp,(17.&40.)Pgp,(17.&40.)Ptp,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps2,(17.&40.)Ps3,(17.&40.)Ps4,(17.&40.)Ps5,(17.&40.)Ps6,(17.&40.)Ps7,(17.&40.)Ps8,(17.&40.)Ps9,(17.&40.)Ps10,(17.&40.)Ps11,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pra',(17.&40.)Pnw,(17.&40.)PF,(18.&5.(17.&40.))Pfc,(17.&20.)Pm,$42.(1;.$1<.Lms',$2>.(<.(17.&40.)La1',(17.&40.)(0.$2>.R2.(1?.(20.R7.(21.&40.(9.(22.&40.R22.)-30.))R21.R20.R1?.R1>.R1=.R6.(21.&40.$23.)(2:.(2;.=))R1.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R5.(21.&40.+40868.)R4.(25.(17.&40.))R3.(26.$1<.))))(1?.(20.R5.(21.&40.(9.(22.&40.R20.)-30.))R1?.R1>.R1=.R1<.R1;.R4.(21.&40.$23.)(2:.(2;.=))R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R3.(21.&40.+40830.)R2.(25.(17.&40.))R1.(26.$1<.)))")
(* [comment removed for export] *).
Proof.
  intros.
  step. step. try (rewrite (Z.land_comm (bv_unsigned (wz (sxv 0)))); rewrite (negw_and_lowbit 0) by lia; rewrite lowbit_0).
  step. try (if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity]).
  apply evt_done. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FASTCORE.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis FU : fact_under st.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48.
Hypothesis N0 : 0 <= n.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB HENF MF FU TP CLO LO N0 NT BL"] Lemma rfast_core_implT : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Pm1,$42.Perrv,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps4,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pra',(17.&40.)Psc,$19.Pg,$4.Zmr,$43.(>.Vst,R1.)Zmask,$19.(?.R1.)Zfirst,$19.(40.R1.)P,(44.VhRP,Vst1,R17.)P,(45.Vst1,)P,(46.Vst1,Vo,R19.)P,(3:.$1<.R1:.)P,(47.$1<.R1;.Vlo,(9.(22.&40.Vsp,)-30.))P,(3;.$1<.R1<.(9.(22.&40.Vsp,)-30.)(35.$3<.(3=.Vs4v,)(35.$3<.(3=.Vs3v,)(35.$3<.(3=.Vs2v,)(35.$3<.(3=.Vs1v,)(35.$3<.(3=.Vs0v,)(35.$3<.(3=.Vra,)(38.$3<.))))))))P,(3;.$1<.R1=.(9.(22.&40.Vtp,)-:4.)(35.$3<.(3>.R1<.)(38.$3<.)))P,(48.VhRP,R1>.(22.&40.Vsp,))P,(49.(4:.VhRP,Vst,Vst1,Vlo,(22.&40.Vsp,))Vm0,R1?.)P,(0.$1.(2.Vst,R>.)(3.$4.R=.))P,(6.=R<.)P,(8.(9.Vn,+4.)(13.+10.(4;.R10.)))(4<.VR,Vo,A2.VK,(4=.R10.(4>.(33.R>.R=.))Vst1,)(3.(36.$4.$19.)(37.$4.$19.R10.(4?.R=.)))Vs,VQ,(1?.(20.R12.(21.&40.(9.(22.&40.Vsp,)-30.))Vgp,Vtp,R21.R20.R1?.(21.&40.Vn,)(21.&40.$23.)(2:.(2;.R>.))R1>.R1=.R1<.R1;.R1:.R19.R18.(50.Vst1,(3.$4.R10.))(21.&40.$24.)R17.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(21.&40.+40830.)Vfc,(25.(17.&40.))R23.(26.$1<.)))")
(* [comment removed for export] *).
Proof.
  intros until g. intros mr mask first MR TK UA MI ST FR ERR AUX PE ACT AV NFIT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb.
  (* [comment removed for export] *)
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  ddestruct (FA sc g ACT) as (SC48 & GSC & _). change (get_meta_rec st g) with mr in GSC.
  pose proof (mf_gmeta _ _ MF) as FG0.
  assert (AVr : 0 <= mask < 2^32 /\ 0 <= m_freed mr < 2^32 /\ 0 <= m_last_idx mr < 32 /\ 0 <= m_freeable mr < 2 /\ 0 <= m_sizeclass mr < 64 /\ 0 <= m_maplen mr < 2^19).
  { change (fact_gmeta (strip st)) with (fact_gmeta st) in FG0.
    destruct (m_mem mr) as [b|] eqn:Hm.
    - specialize (FG0 g b Hm). change (get_meta_rec st g) with mr in FG0. cbv zeta in FG0.
      ddestruct FG0 as (_ & A1 & A2 & A3 & A4 & A5 & A6 & _). subst mask. clear - A1 A2 A3 A4 A5 A6 GSC SC48. lia.
    - exfalso. ddestruct (FA sc g ACT) as (_ & _ & NN). apply NN. exact Hm. }
  ddestruct AVr as (AVr & FRr & LIr & FBr & SCr & MPr).
  ddestruct (lowbit_facts mask ltac:(lia)) as (k & K32 & LBK). fold first in LBK.
  assert (P2k : 0 < 2 ^ k <= mask).
  { split; [apply Z.pow_pos_nonneg; lia|]. ddestruct (lowbit_pow2 mask AV) as (k' & _ & E' & LE'). unfold first, lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  ddestruct (rfast_slot_ok st LB sc n g k t MF ACT AV ltac:(lia) LBK N0 NFIT) as (b & r & SO & SPANFP & _ & Hmem & Hr).
  fold mr st1 in SO. change (get_meta_rec st g) with mr in Hmem.
  pose proof (mf_ctx _ _ MF) as FC. change (fact_ctx (strip st)) with (fact_ctx st) in FC. ddestruct FC as (CTR & SEC & INI & _).
  (* [comment removed for export] *)
  assert (MSL : meta_slot st1 g) by (exact (so_mslot _ _ _ _ _ _ SO)).
  dpose (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & (rid0 & r0 & Hr0 & Hk0 & GR0 & GR1)). rceilb.
  set (G := conc st1 g) in *.
  change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. fold mask in MM. unfold meta_word in MM.
  (* [comment removed for export] *)
  riprefixT.
  eapply evt_mono.
  { eapply (rfast_walk sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g))
              (pw st1 (m_prev mr)) (pw st1 (m_next mr)) (pw st1 (m_mem mr)) F fc m1 G mask k (m_freed mr)
              (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- bv_unsigned (pw _ _) = _ => unfold pw; cbn [oconc]; fold G; apply wz_unsigned; lia
         | |- _ => idtac end.
    all: try lia. all: try assumption. }
  intros ms' PO. cbv beta in PO. unfold rfc_post in PO.
  ddestruct PO as (v0 & v1 & v2 & v3 & m3 & -> & E3 & MU & WM & MI' & MM').
  (* [comment removed for export] *)
  pose proof (ctz32_pow2 k ltac:(lia)) as CTZ.
  replace (ctz32 first) with k by (rewrite LBK; symmetry; exact CTZ).
  replace (mask - first) with (mask - 2 ^ k) by (rewrite LBK; reflexivity).
  set (st2 := upd_meta g (m_set_avail (mask - 2 ^ k)) st1) in *.
  change (pw st1 (Some g)) with (pw st2 (Some g)).
  assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= rceil).
  { intros rid r1 H1. dpose (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). rceilb. lia. }
  assert (RB : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= 2^64).
  { intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
  eapply (HENF st2 g b r k m3 s errv).
  - (* [comment removed for export] *) rewrite E3. unfold st2. apply rmrep_meta_set_avail; [exact MR| exact MSL| lia].
  - apply ticks_ok_upd_meta. exact TK.
  - eapply unk_agree_munch; [| exact MU | |].
    + eapply unk_agree_ext; [exact UA| reflexivity| intros; reflexivity| reflexivity].
    + intros rid r1 H1 K1. change (s_regions st2) with (s_regions st1) in H1.
      pose proof (GDJ rid r1 H1 K1). pose proof (RB0 rid r1 H1). cbn. lia.
    + intros rid r1 H1. exact (RB rid r1 H1).
  - exact MI'.
  - eapply stk_transport; [exact ST| exact MU| exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia.
  - eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia.
  - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor.
  - eapply rpres_except_munch_frame; [| exact MU| exact WM|].
    + eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_mono; [|exact Ha].
      intros rid r1 H1. exists r1. repeat split; auto. lia.
    + intros x Hx NC. cbn. split; [|exact I].
      intros HX. apply NC. left. right. right. right. dexists rid0, r0. split; [exact Hr0|]. split; [exact Hk0|]. lia.
  - intros a Ha. right. right. left. apply SPANFP.
    replace (get_stride (get_meta_rec st2 g)) with (get_stride mr) in Ha; [exact Ha|].
    unfold st2. rewrite get_meta_rec_upd_same. reflexivity.
  - exact CTR.
  - exact SO.
  - (* [comment removed for export] *)
    intros UND. exfalso. revert UND. unfold undersized, st2. rewrite get_meta_rec_upd_same. change (get_meta_rec st1 g) with mr.
    replace (m_sizeclass (m_set_avail (mask - 2 ^ k) mr)) with (m_sizeclass mr) by (destruct mr; reflexivity).
    replace (get_stride (m_set_avail (mask - 2 ^ k) mr)) with (get_stride mr) by (destruct mr; reflexivity).
    intros UND. assert (SCm : m_sizeclass mr < 48) by (rewrite GSC; lia).
    destruct (FU g b Hmem SCm (UND SCm)) as [AV0 _]. clear -AV AV0. subst mask mr. lia.
  - intros [X|X]; [exfalso; lia|]. exfalso. change (s_regions st1) with (s_regions st) in Hr. rewrite X in Hr. rewrite lookup_empty in Hr. discriminate.
  - apply mrel_same; reflexivity.
  - exact BL.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
End FASTCORE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ASCALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_UV : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Pst0,$51.Pst,$51.Pst1,$51.Psc,$19.Pidx,$19.Pg,$4.Pb,$4.P,A5.Vas_inv,R7.R6.R5.R4.R3.P,(8.=R4.)P,(0.$1.(2.R7.R6.)(3.$4.R4.))P,(0.$1.(=.(>.R8.R5.))(3.$4.R4.))(52.R9.R6.R5.R7.)")
(* [comment removed for export] *).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis FU : fact_under st.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="as_inv RAS AS_UV HENF HFAIL MR0 TP CLO LO NT BL"] Lemma ras_call_implT :
  forall (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2r t3 t4 t5 t6 ra' : word) (sc : Z),
  as_pre st st1 sc n FUEL ->
  rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
  rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
  0 <= sc < 48 ->
  rimplT o (alloc_slot full_lay FUEL st1 sc n
             (fun st2 idx => if idx <? 0 then K st2 None
                             else match active st2 sc with
                                  | Some gp => K st2 (Some (gp, idx))
                                  | None => SVis (EUndef UBadPtr) (fun _ => bail)
                                  end) bail) s Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) a0 a1 a2 a3 a4 a5 a6 a7
                 s2r (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40868) fc None m1 (seg_rom rsegs)).
Proof.
  intros until sc. intros PRE MR TK UA MI ST FR ERR AUX PE SC48.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb. pose proof (RAS_STACK_ge sc) as ASG. pose proof (RAS_STACK_mono 0 sc ltac:(lia)) as ASM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  assert (RB0 : forall rid r1, (s_regions st1) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= rceil).
  { intros rid r1 H1. dpose (rregion_facts st1 m1 rid r1 MR H1) as (X1 & _ & X2 & _). rceilb. lia. }
  subst tp. unfold RATP in *. rewrite unsigned_lit in ERR by lia.
  unfold RMLOCK, RDEBRUIJN in *.
  riprefixT.
  (* [comment removed for export] *)
  step. rewrite sextw_small by lia. step. step.
  (* [comment removed for export] *)
  step. apply evt_done.
  eapply (RAS FUEL) with (st0 := st) (lo := lo).
  all: lazymatch goal with
       | |- as_pre _ _ _ _ _ => try exact PRE
       | |- rmrep _ _ => try exact MR
       | |- ticks_ok _ => try exact TK
       | |- unk_agree _ _ _ => try exact UA
       | |- brk_link_ps _ _ => try exact BL
       | |- rauxv_ok _ _ => try (rewrite unsigned_lit by lia; eapply rauxv_ok_weaken; [exact AUX| rceilb; lia])
       | |- stk _ _ _ _ => try (rewrite unsigned_lit by lia; exact ST)
       | |- mem_inv _ _ => try assumption
       | |- rw_cells _ _ _ [C4 _] => try (rewrite unsigned_lit by lia; exact ERR)
       | |- _ => idtac
       end.
  all: try (rewrite ?unsigned_lit by lia; rceilb; lia).
  all: try reflexivity.
  (* [comment removed for export] *)
  intros st2 idx s' ms' PO.
  ddestruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & MR' & TK' & UA' & PE' & MREL & BL' & PSM & PSF & PSO & INV' & CTR' & RES).
  replace (ret_pc (Z_to_bv 64 0x40878)) with (Z_to_bv 64 0x40878) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  rewrite ?unsigned_lit in ST', AUX', PE', RES by lia.
  (* [comment removed for export] *)
  pose proof (rframe_after_call st st2 lo _ m0 m1 m' m' _ _ MR0 MR' PE' FR ltac:(lia) ltac:(rceilb; lia)) as FR'.
  assert (AUX2' : rauxv_ok m' (bv_unsigned sp)) by (eapply (rauxv_ok_malloc_fp st st2 lo _ m0 m' m1 m'); [exact MR0| exact MR'| exact AUX| exact PE'| rceilb; lia| lia]).
  assert (PE2 : rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m').
  { eapply rpres_except_trans; [| eapply rpres_except_mono; [exact PE'|]; intros a Ha; eapply rmalloc_fp_sp_mono; [|exact Ha]; lia].
    eapply rpres_except_mono; [exact PE|]. intros a Ha. eapply rmalloc_fp_st_mono; [exact MREL|].
    eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. repeat split; auto. lia. }
  assert (MREL2 : mrel st st2) by (eapply mrel_trans; [|exact MREL]; apply mrel_same; reflexivity).
  dpose MR' as (_ & (CXH' & CXA' & _) & (ML' & _) & _). unfold RCTX in CXA'. unfold RMLOCK in ML'.
  clear MU WM PE AUX.
  destruct RES as [-> | (IDX0 & g & b & r & ACT2 & SO & SPANFP & EXPO)].
  - (* [comment removed for export] *)
    change (-1 <? 0) with true. cbv iota.
    riprefixT.
    step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
    clear KB.
    step. step.
    (* [comment removed for export] *)
    step.
    eapply evt_cut.
    { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact ML']. }
    intros ms'' ->.
    replace (ret_pc (Z_to_bv 64 0x408d4)) with (Z_to_bv 64 0x408d4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    release_frame FR' ST' (bv_unsigned sp).
    apply evt_done. eapply (HFAIL st2 m' s' errv').
    all: try assumption.
  - (* [comment removed for export] *)
    replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite ACT2.
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    riprefixT.
    step. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
    clear KB.
    step. step. rewrite (unsigned_lit sc), Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. step.
    pose proof (actives_nth st2 sc ltac:(lia)) as NTH. rewrite ACT2 in NTH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read rsegs mc _ (actives st2) sc (pw st2 (Some g)) (wa (512968 + 80 + 8 * sc)) CXA' NTH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    step.
    apply evt_done.
    change (Z_to_bv 64 idx) with (wz idx).
    eapply (HENF st2 g b r idx m' s' errv').
    all: try assumption.
    + intros a Ha. eapply rmalloc_fp_sp_mono; [|apply SPANFP; exact Ha]. lia.
    + exact (AS_UV _ _ _ _ _ _ _ INV' IDX0 ACT2 Hmem).
    + intros [X|X]; [exfalso; unfold MMAP_THRESHOLD in *; lia|]. apply EXPO. exact X.
Qed.
End ASCALL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section SMALL.
Context {R : Type}.
Variables (K : mstate -> option (aptr * Z) -> Malloc.M R) (bail : Malloc.M R) (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
          (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N).
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_UV : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Pst0,$51.Pst,$51.Pst1,$51.Psc,$19.Pidx,$19.Pg,$4.Pb,$4.P,A5.Vas_inv,R7.R6.R5.R4.R3.P,(8.=R4.)P,(0.$1.(2.R7.R6.)(3.$4.R4.))P,(0.$1.(=.(>.R8.R5.))(3.$4.R4.))(52.R9.R6.R5.R7.)")
(* [comment removed for export] *).
Hypothesis HENF : renf_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Hypothesis HFAIL : rfail_hyp K o m0 st s Q ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Hypothesis MF : RMFACTS st LB.
Hypothesis FU : fact_under st.
Hypothesis MR0 : rmrep st m0.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 48 - RAS_STACK 0.
Hypothesis N0 : 0 <= n < 2^32.
Hypothesis NT : n < MMAP_THRESHOLD.
Hypothesis BL : brk_link_ps st s.

Let st1 := set_tick t st.

#[using="LB as_inv RAS AS_UV HENF HFAIL MF FU MR0 TP CLO LO N0 NT BL"] Lemma rmalloc_small_implT : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_small ()) "Pm1,$42.Perrv,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Pa0,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps2r,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pra',(17.&40.)Psc,$19.P,(0.$19.R1.(53.Vn,))P,(5.(8.=R2.)(6.R2.+30.))P,(8.(9.Vn,+4.)(13.+10.(4;.R3.)))P,Psc',$19.P,(5.(8.=R1.)(6.R1.+30.))P,(8.(9.Vn,+4.)(13.+10.(4;.R2.)))A5.Vas_pre,Vst,Vst1,R3.Vn,$54.P,(44.VhRP,Vst1,R18.)P,(45.Vst1,)P,(46.Vst1,Vo,R1:.)P,(3:.$1<.R1;.)P,(47.$1<.R1<.Vlo,(9.(22.&40.Vsp,)-30.))P,(3;.$1<.R1=.(9.(22.&40.Vsp,)-30.)(35.$3<.(3=.Vs4v,)(35.$3<.(3=.Vs3v,)(35.$3<.(3=.Vs2v,)(35.$3<.(3=.Vs1v,)(35.$3<.(3=.Vs0v,)(35.$3<.(3=.Vra,)(38.$3<.))))))))P,(3;.$1<.R1>.(9.(22.&40.Vtp,)-:4.)(35.$3<.(3>.R1=.)(38.$3<.)))P,(48.VhRP,R1?.(22.&40.Vsp,))P,(49.(4:.VhRP,Vst,Vst1,Vlo,(22.&40.Vsp,))Vm0,R20.)(4<.VR,Vo,(55.VR,$56.Vst1,Vn,VK,Vbail,)Vs,VQ,(1?.(20.R?.(21.&40.(9.(22.&40.Vsp,)-30.))Vgp,Vtp,R1?.R1>.R1=.(21.&40.Vn,)(21.&40.$23.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.(21.&40.$24.)(21.&40.R>.)Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(21.&40.+40774.)Vfc,(25.(17.&40.))R21.(26.$1<.)))")
(* [comment removed for export] *).
Proof.
  intros until sc. intros SCE SC48 NFIT ASP MR TK UA MI ST FR ERR AUX PE.
  pose proof (RAS_STACK_ge 0) as ASG. unfold st1 in *.
  rewrite malloc_small_ctrl_eq. rewrite <- SCE. change (coarse_sc (set_tick t st) sc) with (coarse_sc st sc). cbv zeta.
  pose proof (coarse_sc_cases st sc SC48) as CC.
  assert (SC48' : 0 <= coarse_sc st sc < 48) by (destruct CC as [-> | (-> & H4 & EV)]; [lia| apply lor1_range; lia]).
  assert (NFIT' : n + 4 <= 16 * size_class (coarse_sc st sc)).
  { destruct CC as [-> | (E & H4 & EV)]; [lia|]. rewrite E. pose proof (size_class_lor1 sc H4 EV). lia. }
  set (sc' := coarse_sc st sc) in *.
  change (active (set_tick t st) sc') with (active st sc').
  riprefixT. eapply evt_cut.
  { eapply (rcoarse_walk st LB m1 t MF MR); [exact SC48| intros; apply lor1_range; lia]. }
  fold sc'. (intros ms' dd_H; ddestruct dd_H as (a0' & a1' & a2' & a3' & -> & HA0)).
  change (active (set_tick t st) sc') with (active st sc') in HA0 |- *.
  destruct (active st sc') as [g|] eqn:ACT'.
  - cbn iota. change (get_meta_rec (set_tick t st) g) with (get_meta_rec st g) in HA0 |- *. subst a0'.
    destruct (Z.eq_dec (m_avail (get_meta_rec st g)) 0) as [AZ|ANZ].
    + (* [comment removed for export] *)
      rewrite AZ, lowbit_0. cbn.
      eapply evt_cut. { apply rcore0_walk. }
      intros ms'' (a1'' & ->). apply evt_done.
      eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
    + (* [comment removed for export] *)
      apply evt_done.
      ddestruct (ractive_ptr_facts st LB m1 t MF MR sc' g ACT') as (_ & _ & _ & _ & AVr & _).
      ddestruct (lowbit_facts (m_avail (get_meta_rec st g)) ltac:(lia)) as (k & K32 & LBK).
      assert (P2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
      replace (lowbit (m_avail (get_meta_rec st g)) =? 0) with false by (rewrite LBK; symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      change (pw (set_tick t st) (Some g)) with (pw (set_tick t st) (Some g)).
      eapply rfast_core_implT; try eassumption; try lia.
  - cbn iota. subst a0'.
    eapply evt_cut. { change (pw (set_tick t st) None) with (pw (set_tick t st) (@None aptr)). apply rcore0_walk. }
    intros ms'' (a1'' & ->). apply evt_done.
    eapply ras_call_implT; try eassumption; try lia. apply ASP; [exact SC48'| exact NFIT'].
Qed.
End SMALL.

End RP_3.
