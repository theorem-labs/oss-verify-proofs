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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W9 HP_RASlot_W12 HP_RASlot_W19 HP_RASlot_M0.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RKitE4.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_M2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.ta_fail"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W0.ta_rel"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.kS"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.IST"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ENTRY_REL"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ALLC"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.am_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta0"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RP_1.LEVEL.rFRM"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ag_body"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RP_1.LEVEL.rag_regs"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.mrel"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_W9.rta_fp"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Logic.iff"; "stdpp.base.is_Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.grp_hdr_cov"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.as_grp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"].


(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

(* [comment removed for export] *)
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "(6.O14.(7.&40.(8.(9.&40.Vsp,)-90.))Vgp,Vtp,O13.O12.O11.(7.&40.Vsc,)O10.O?.O>.O=.O<.O;.O:.O9.O8.Va1,O7.(7.&40.$:.)(7.&40.(8.(8.$;.+50.)(<.+8.Vsc,)))(7.&40.$=.)(7.&40.(8.$=.(<.+8.Vsc,)))O6.O5.Vs10,Vs11,O4.O3.O2.O1.)")
(* [comment removed for export] *).
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Definition rHAG_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "Pst1,$0.Pst2,$0.Pmm,$>.Pm3,P,(?.&40.)(10.(?.&8.))Ps',$2.Perrv',(?.&40.)Pt0',(?.&40.)Pt1',(?.&40.)Pt2',(?.&40.)Pa1',(?.&40.)Pa2',(?.&40.)Pa3',(?.&40.)Pa4',(?.&40.)Pa5',(?.&40.)Pa6',(?.&40.)Pa7',(?.&40.)Pt3',(?.&40.)Pt4',(?.&40.)Pt5',(?.&40.)Pt6',(?.&40.)Pjunk,(11.(?.&8.))Poo,$12.P,(13.Vsc,Vst,R16.)P,(14.Vsc,Vst,R17.)P,(15.$16.(17.R18.Vsc,)(18.$>.))P,(19.(10.(1:.$0.$16.))R4.(1;.(10.(1:.$0.$16.))R19.(1<.$0.$16.)(1=.(1:.$0.$16.)))(1>.(1:.$0.(10.$>.))(1?.$0.(10.$>.)R18.(1>.$>.R17.))))P,(20.Vst0,R19.)P,(21.Vst0,R1:.)P,(22.R1;.)P,(23.R1=.R1<.(1>.$>.R1;.))P,(15.$24.(25.R1=.R1<.)$26.)P,(27.R1>.R1=.)P,(28.VhRP,R1?.R1=.)P,(29.R20.)P,(2:.R21.Vo,R1?.)P,(2;.$2<.R20.)P,(2=.$2<.R21.Vlo,(8.(9.&40.Vsp,)-90.))P,(2>.$2<.R22.(8.(9.&40.Vsp,)-90.)(2?.R11.))P,(2>.$2<.R23.(8.(9.&40.Vtp,)-:4.)(30.$31.(32.R21.)(33.$31.)))P,(34.VhRP,R24.(9.&40.Vsp,))P,(35.(36.VhRP,Vst0,R27.Vlo,(9.&40.Vsp,))Vm,R25.)P,(37.R28.R25.)P,(15.$0.(38.R26.)(38.Vs,))P,(15.(1:.$1.$1.)(39.R27.)(39.Vs,))P,(15.$3:.(3;.R28.)(3;.Vs,))(5.VR,Vo,(3<.VR,Vf,Vsc,Vreq,Vk,Vbail,R2<.R2;.)R29.VQ,(3=.(3>.(7.&40.+40:=0.)R27.R26.R25.(7.&40.(3?.R2<.R2;.))(7.&40.-1.)R24.R23.R22.R21.R20.R1?.R1>.(7.&40.(<.Vsc,+2.))(40.(41.Vsc,))(7.&40.$42.)R1=.R1<.R1;.R1:.)VF,(7.&40.+40:=<.)Vfc,(18.(?.&40.))R2:.(43.$2<.)))")
(* [comment removed for export] *).
Hypothesis HAG : rHAG_stmt.

#[using="hRP TP"] Lemma rerrno_lit2 : errno_addr tp = 0x5d024.
Proof. rceilb. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="hRP m MR"] Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. rceilb.
  (intros REL dd_H; ddestruct dd_H as (ar & arr & kk & Ha & Hk & ->)). pose proof MR as (WF & _). dpose WF as (_ & _ & _ & WA & _).
  ddestruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

(* [comment removed for export] *)
#[using="m ER MR"] Lemma rta_fp_malloc_fp stE mE a : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "P,(28.VhRP,O3.O2.)P,(44.Vst,O3.)P,Pq,$>.P,(27.Vst,R1.)(27.O3.R2.)P,(45.Vst,Vlo,(9.&40.Vsp,)O1.)(36.VhRP,Vst0,O3.Vlo,(9.&40.Vsp,)O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - left. left. exact X.
  - left. right. right. left. exact X.
  - left. do 3 right.
    pose proof (AREAS q MSq) as MSq'.
    ddestruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
    dexists rid0, r0. split; [exact H0|]. split; [exact K0|].
    rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
  - do 3 right. left. pose proof MR as (WF & _).
    ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct ER as [_ EG EGR _ _ _ _ _].
    destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
    dexists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
    rewrite Cb in Xq. lia.
Qed.

(* [comment removed for export] *)
#[using="hRP m MR CLO"] Lemma rta_fp_not_image a : 0x10000 <= a < 0x7e000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. rceilb.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - rceilb. lia.
  - exact (Hc X).
  - ddestruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
  - pose proof MR as (WF & _). ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
    ddestruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
#[using="hRP m sc MR CLO LO"] Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof. rceilb.
  pose proof (RAS_STACK_ge sc) as ASG. rceilb.
  intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - unfold RCTX in X. lia.
  - ddestruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
  - pose proof MR as (WF & _). ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). rceilb. lia.
Qed.

(* [comment removed for export] *)
#[using="hRP UA"] Lemma runk_agree_keep stE mE : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "P,(15.(46.$47.$48.$49.$4:.)(4;.O2.)(4;.Vst,))P,Prid,$47.Pr,$4<.P,(15.$4=.(4>.R1.)$4?.)P,(15.(10.$4<.)(50.$47.$4<.(46.$47.$48.$49.$4<.)(51.$47.$48.$49.$4<.)R3.(52.O2.))(1>.$4<.R2.))(15.(10.$4<.)(50.$47.$4<.(46.$47.$48.$49.$4<.)(51.$47.$48.$49.$4<.)R4.(52.Vst,))(1>.$4<.R3.))P,Pb,$>.(53.(54.$55.(50.$>.$55.(46.$>.(56.$47.$48.$1.$57.)(58.$47.$48.$49.$1.$57.$59.)$55.)(51.$>.(56.$47.$48.$1.$57.)(58.$47.$48.$49.$1.$57.$59.)$55.)R1.(5:.O2.)))(54.$55.(50.$>.$55.(46.$>.(56.$47.$48.$1.$57.)(58.$47.$48.$49.$1.$57.$59.)$55.)(51.$>.(56.$47.$48.$1.$57.)(58.$47.$48.$49.$1.$57.$59.)$55.)R1.(5:.Vst,))))P,Prid,$47.Pr,$4<.Poff,$1.Ph,$1.P,(15.(10.$4<.)(50.$47.$4<.(46.$47.$48.$49.$4<.)(51.$47.$48.$49.$4<.)R4.(52.Vst,))(1>.$4<.R3.))P,(15.$4=.(4>.R4.)$4?.)P,(5;.(5<.=R4.)(5=.R4.(5>.(5?.R5.))))P,(15.$60.(61.(62.Vst,R7.)R5.)(63.R4.))P,(64.(65.Vst,R8.R6.))(15.(10.(?.&8.))A1.O1.(66.(8.(67.R8.)R7.))A1.Vm,(66.(8.(67.R8.)R7.)))(2:.O2.Vo,O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { (intros dd_H; ddestruct dd_H as (bq & gh & Hbq & Hf & Hoff)). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. dexists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
#[using="hRP m MR CLO"] Lemma rta_fp_not_inband rid r off : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "P,(15.(10.$4<.)(50.$47.$4<.(46.$47.$48.$49.$4<.)(51.$47.$48.$49.$4<.)O3.(52.Vst,))(1>.$4<.O2.))P,(15.$4=.(4>.O2.)$4?.)P,(5;.(5<.=O1.)(5=.O1.(5>.(5?.O2.))))P,(64.(65.Vst,O3.O1.))(64.(45.Vst,Vlo,(9.&40.Vsp,)(8.(67.O2.)O1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). dpose WF as (_ & WR & DJ & _).
  destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). rceilb.
  intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - ddestruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
  - ddestruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
  - ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
    destruct (N.eq_dec (fst bq) rid) as [E|NE].
    + apply NG. dexists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

#[using="st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG"] Lemma rag_phase : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M2 ()) "Pst1,$0.Pm1,P,(?.&40.)(10.(?.&8.))Pt0',(?.&40.)Pt1',(?.&40.)Pa0',(?.&40.)Pa1',(?.&40.)Pa2',(?.&40.)Pa3',(?.&40.)Pa4',(?.&40.)Pa5',(?.&40.)Pa6',(?.&40.)Pa7',(?.&40.)Pjunk,(11.(?.&8.))P,(13.Vsc,Vst,R=.)P,(14.Vsc,Vst,R>.)P,(15.$16.(17.R?.Vsc,)(18.$>.))P,(28.VhRP,R10.R?.)P,(2;.$2<.R10.)P,(2>.$2<.R11.(8.(9.&40.Vsp,)-90.)(2?.R6.))P,(2=.$2<.R12.Vlo,(8.(9.&40.Vsp,)-90.))P,(35.(45.Vst,Vlo,(9.&40.Vsp,))Vm,R13.)(5.VR,Vo,(68.VR,$69.Vf,Vsc,Vreq,Vk,Vbail,R15.)Vs,VQ,(3=.(3>.Vra,R13.R12.Vt2,Vs1,R11.R10.R?.R>.R=.R<.R;.R:.Vs3,Vs8,Vs9,Vt3,Vt4,Vt5,Vt6,)VF,(7.&40.+40:;8.)Vfc,(18.(?.&40.))R14.(43.$2<.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. rceilb.
  pose proof rerrno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  rewrite (as_grp_eq f sc req k bail st1).
  riprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
  { apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| rceilb; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply rta_fp_not_high. exact Ha.
    - intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
  assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
  eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  ddestruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x40ad0)) with (Z_to_bv 64 0x40ad0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). dpose WF3 as ((RS3 & RPRS3) & WR3 & DJ3 & _).
  (* [comment removed for export] *)
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x7e000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x5d024 <= a < 0x5d028)) ->
            ~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ rfresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold RCTX in *. lia.
    - destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). rceilb.
      pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. rceilb.
      pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }
  (* [comment removed for export] *)
  assert (REL02 : mrel st st2).
  { split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
    intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
  assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
  { (intros q dd_H; ddestruct dd_H as (ar & arr & kk & Ha & Hk & E)). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
    dexists ar, arr', kk. auto. }
  assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
    - eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
      + left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
      + do 4 right. eapply (rfresh_addr_anti st0 st1); [| | exact X].
        * rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
        * intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }
  (* [comment removed for export] *)
  assert (UA3 : unk_agree st2 o m3).
  { eapply (runk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). rceilb.
      transitivity (m1 (wa (r_base r + off))).
      + refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
        * lia.
        * rewrite unsigned_lit in X by lia. ddestruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
          specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
        * ddestruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
        * assert (Hr2 : (s_regions st2) !! rid = Some r).
          { rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
          assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
          pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
        * rewrite <- REG1 in Hr. pose proof (rfresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
      + refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
  destruct mo as [mm|].
  - (* [comment removed for export] *)
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    dpose (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [rceilb; lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  - (* [comment removed for export] *)
    cbn iota.
    riprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
    cbv beta. intros ms' ->. cbn [Z.eqb].
    eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1x & a2x & -> & ST4)). apply evt_done.
    apply HK. unfold ras_post2.
    deexists 14. dexists m3, errv3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
    split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
    split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
    split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia.
      - intros H; exfalso; lia. }
    split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
             pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
    left. reflexivity.
Qed.
End LEVEL.

End RP_1.
