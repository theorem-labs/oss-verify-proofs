(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W11 ASlot_I ASlot_M0 ASlot_M3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W11 HP_RASlot_M0 HP_RASlot_M2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_M3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.ta_fail"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W0.ta_rel"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.kS"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.IST"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ENTRY_REL"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ALLC"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.am_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta0"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_M2.rFRM"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.usage"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "Corelib.Init.Datatypes.list"; "RP_1.LEVEL.rag_ctx"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ag_mmap"; "RP_1.LEVEL.rcnt_state"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ag_nest"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_M2.rHAG_stmt"].


Section RP_1. Context {hRP : run_params}.
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
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)
Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "(6.(7.Vsc,Vst,O8.)(6.(8.Vsc,Vst,O8.)(6.(9.$:.(;.O8.Vsc,)(<.$=.))(6.(>.(?.(10.$0.$:.))O1.(11.(?.(10.$0.$:.))O8.(12.$0.$:.)(13.(10.$0.$:.)))(14.(10.$0.(?.$=.))(15.$0.(?.$=.)O7.(14.$=.O6.))))(6.(16.Vst0,O7.)(6.(17.Vst0,O7.)(6.(18.O7.)(6.(19.O8.O7.(14.$=.O6.))(6.(9.$1:.(1;.O7.O6.)$1<.)(6.(1=.O7.O6.)(6.(1>.VhRP,O7.O5.)(6.(1?.O7.)(6.(20.O7.Vo,O5.)(6.(21.$22.O5.)(6.(23.$22.O5.Vlo,(24.(25.&40.Vsp,)-90.))(6.(26.$22.O5.(24.(25.&40.Vsp,)-90.)(27.VhRP,Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,O2.))(6.(26.$22.O5.(24.(25.&40.Vtp,)-:4.)(28.$29.(2:.O3.)(2;.$29.)))(6.(2<.VhRP,O5.(25.&40.Vsp,))(6.(2=.(2>.VhRP,Vst0,O7.Vlo,(25.&40.Vsp,))Vm,O5.)(6.(2?.O7.O4.)(6.(9.$0.(30.O4.)(30.Vs,))(6.(9.(10.$1.$1.)(31.O4.)(31.Vs,))(9.$32.(33.O4.)(33.Vs,))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "(34.(35.(36.&40.+40:=0.)(36.&40.(24.(25.&40.Vsp,)-90.))Vgp,Vtp,O:.O9.O8.(36.&40.Vsc,)(36.&40.(37.O=.O<.))(38.(39.O=.Vsc,))(38.+1000.)(38.(24.(3:.(3;.Vsc,)$3<.)+10.))(38.+800.)(38.(3:.(3:.(3;.Vsc,)$3<.)O;.))(38.(24.(3:.(3:.(3;.Vsc,)$3<.)O;.)+10.))O7.O6.Va1,(38.O;.)(36.&40.$3=.)(36.&40.(24.(24.$3>.+50.)(3:.+8.Vsc,)))(36.&40.$3?.)(36.&40.(24.$3?.(3:.+8.Vsc,)))(38.(3:.(3;.Vsc,)$3<.))(36.&40.$40.)Vs10,Vs11,O5.O4.O3.O2.)VF,(36.&40.O>.)Vfc,(<.(41.&40.))O1.(42.$22.))")
(* [comment removed for export] *).

Definition rHMM_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "Pst1,$0.Pst2,$0.Pmm,$=.Pm3,$43.Ps',$2.Perrv',(41.&40.)Pjunk,(44.(41.&8.))Poo,$43.Pcnt1,$1.Pt0',(41.&40.)Pt1',(41.&40.)Pt2',(41.&40.)Pa6',(41.&40.)Pa7',(41.&40.)Pt3',(41.&40.)Pt4',(41.&40.)Pt5',(41.&40.)Pt6',(41.&40.)P,(45.R12.R11.R10.R?.R>.R=.R<.R;.)P,(6.(46.+1.R;.)(46.R;.+20.))P,(47.+800.(24.(3:.(3:.(3;.Vsc,)$3<.)R<.)$3<.))(5.VR,Vo,(48.VR,Vsc,Vreq,Vk,Vbail,R14.R13.R=.)R11.VQ,(49.+40;:4.R14.R13.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R12.))")
(* [comment removed for export] *).

Definition rHNEST_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "Pst1,$0.Pst2,$0.Pmm,$=.Pm3,$43.Ps',$2.Perrv',(41.&40.)Pjunk,(44.(41.&8.))Poo,$43.Pcnt1,$1.Pt0',(41.&40.)Pt1',(41.&40.)Pt2',(41.&40.)Pa6',(41.&40.)Pa7',(41.&40.)Pt3',(41.&40.)Pt4',(41.&40.)Pt5',(41.&40.)Pt6',(41.&40.)P,(45.R12.R11.R10.R?.R>.R=.R<.R;.)P,(6.(46.+1.R;.)(46.R;.+20.))P,(46.(24.(3:.(3:.(3;.Vsc,)$3<.)R<.)$3<.)+800.)(5.VR,Vo,(4:.VR,Vf,Vsc,Vk,Vbail,R14.R13.R=.)R11.VQ,(49.+40;>8.R14.R13.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R12.))")
(* [comment removed for export] *).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M3 ()) "(4;.VhRP,VR,Vf,Vk,Vbail,Vo,Vs,VQ,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Va1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vst0,Vst,Vlo,Vsc,Vreq,)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
  intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
  assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  rceilb.
  pose proof (MallocFacts_inv4.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
  pose proof (size_class_range sc SC) as SZR.
  rewrite (ag_body_eq f sc req k bail st2 mm).
  riprefixT. unfold rag_regs.
  eapply evt_cut.
  { eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a2'' & a3'' & a4'' & ->)).
  set (size := size_class sc * UNIT).
  set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
  assert (C0R : 1 <= cnt0 <= 32).
  { pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
    subst cnt0. destruct (Z.ltb_spec sc 9).
    - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
      destruct (negb _); [lia|]. destruct (negb _); lia.
    - apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
      pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
  eapply evt_cut.
  { eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
  cbv beta. intros ms' ->. unfold rcnt_regs.
  set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
  assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
  assert (EC : ag_cnt1 sc st2 = cnt1).
  { unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
  rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
  apply evt_done.
  destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
  - pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
  - pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.

End RP_1.
