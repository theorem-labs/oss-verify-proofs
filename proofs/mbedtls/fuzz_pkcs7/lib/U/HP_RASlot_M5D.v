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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M5D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_M0 HP_RASlot_M2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_M5D () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.le"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_M5D.ncls"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSIZE_CLASSES"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.ta_fail"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W0.ta_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.kS"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.IST"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ENTRY_REL"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ALLC"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.am_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta0"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_M5D.nreq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.mrel"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.as_inv2"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_mmap_counter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_M2.rFRM"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "Corelib.Init.Datatypes.list"; "RP_1.LEVEL.rnest_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.free_meta"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.as_kq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RP_1.LEVEL.rnest_regs"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.slot_ok"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_stride"; "stdpp.base.empty"; "stdpp.gmap.gmap_empty"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_enframe.rdv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pans_mem"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ag_tail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_maplen"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.nest_layout"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.slot_of"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. rceilb.
  (intros MR REL dd_H; ddestruct dd_H as (ar & arr & kk & Ha & Hk & ->)). pose proof MR as (WF & _). dpose WF as (_ & _ & _ & WA & _).
  ddestruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "P,(0.O2.O3.)P,Prid,$1.Pr,$2.P,(3.(4.$2.)(5.$1.$2.(6.$1.$7.$8.$2.)(9.$1.$7.$8.$2.)R2.(:.O6.))(;.$2.R1.))(<.$2.Lr',$2.(=.(3.(4.$2.)(5.$1.$2.(6.$1.$7.$8.$2.)(9.$1.$7.$8.$2.)R4.(:.O5.))(;.$2.R1.))(=.(3.$>.(?.R1.)(?.R3.))(=.(3.$10.(11.R1.)(11.R3.))(0.(12.R3.)(12.R1.))))))P,(13.VhRP,O7.O6.O4.O2.O1.)(13.VhRP,O7.O5.O4.O3.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rregion_byte_raw st m rid r off v : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "P,(14.VhRP,O6.O5.)P,(3.(4.$2.)(5.$1.$2.(6.$1.$7.$8.$2.)(9.$1.$7.$8.$2.)O4.(:.O6.))(;.$2.O3.))P,(3.$>.(?.O3.)$15.)P,(=.(0.=O2.)(16.O2.(17.(12.O3.))))P,(3.$18.(19.(1:.O6.O4.)O2.)(1;.O1.))(3.(4.(1<.&8.))A1.O5.(1=.(1>.(11.O3.)O2.))(;.(1<.&8.)(1?.O1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MR Hr Hk Ho Hc.
  destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  ddestruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

#[using="hRP"] Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x5d024.
Proof. rceilb. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "Pst1,$20.Pidx,$10.Ps',$21.Pms',$22.P,(23.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(24.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "(25.(26.&40.+40<;8.)(26.&40.(1>.(27.&40.Vsp,)-90.))Vgp,Vtp,O>.O=.O<.(26.&40.Vsc,)(26.&40.(28.O12.O11.))O?.O;.O:.O9.O8.O7.O6.O5.(26.&40.(29.Vsc,O10.))(2:.O10.)(26.&40.$2;.)(26.&40.(1>.(1>.$2<.+50.)(2=.+8.Vsc,)))(26.&40.$2>.)(26.&40.(1>.$2>.(2=.+8.Vsc,)))(2:.(2=.(2?.Vsc,)$30.))(26.&40.$31.)Vs10,Vs11,O4.O3.O2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "(=.(32.Vsc,Vst,O>.)(=.(33.Vsc,Vst,O>.)(=.(3.$34.(35.O>.Vsc,)(36.$37.))(=.(38.(4.(39.$20.$34.))O2.(3:.(4.(39.$20.$34.))O>.(3;.$20.$34.)(3<.(39.$20.$34.)))(;.(39.$20.(4.$37.))(3=.$20.(4.$37.)O=.(;.$37.O<.))))(=.(3>.Vst0,O=.)(=.(3?.Vst0,O=.)(=.(40.O=.)(=.(41.O>.O=.(;.$37.O<.))(=.(3.$42.(43.O=.O<.)$44.)(=.(45.O=.O<.)(=.(=.(0.+1.O;.)(0.O;.+20.))(=.(0.(1>.(2=.(2=.(2?.Vsc,)$30.)O;.)$30.)+800.)(=.(38.(4.(39.$20.$10.))O1.(46.(4.(39.$20.$10.))$47.Vf,O=.(29.Vsc,O;.)(48.Vsc,O;.)(3;.$20.$10.)(3<.(39.$20.$10.)))(;.(39.$20.$10.)(3=.$20.$10.O:.O9.)))(=.(49.$4:.O7.)(=.(4;.$4:.O7.Vlo,(4<.(27.&40.Vsp,)+90.))(=.(4=.$4:.O7.(1>.(27.&40.Vtp,)-:4.)(4>.$4?.(50.O4.)(51.$4?.)))(=.(52.VhRP,O7.(4<.(27.&40.Vsp,)+90.))(=.(14.VhRP,O:.O7.)(=.(53.O:.)(=.(54.O:.Vo,O7.)(=.(55.(13.VhRP,Vst0,O:.Vlo,(4<.(27.&40.Vsp,)+90.))O8.O7.)(=.(56.O=.O:.)(=.(57.O:.O5.)(=.(3.$20.(58.O5.)(58.Vs,))(=.(3.(39.$10.$10.)(59.O5.)(59.Vs,))(=.(3.$5:.(5;.O5.)(5;.Vs,))(=.(5<.Vst0,O=.O:.(29.Vsc,O;.)O9.)(=.(=.(0.=(5=.(5>.O:.)))(16.(5=.(5>.O:.))(5?.+2.+20.)))(=.(4=.$4:.O7.(4<.(27.&40.Vsp,)+90.)(60.VhRP,Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,O3.))(=.(55.(13.VhRP,Vst0,O=.Vlo,(27.&40.Vsp,))Vm,O8.)(14.VhRP,O=.O8.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rNFAIL_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "Pst1,$20.Pst2,$20.Pmm,$37.Pcnt1,$10.Pst3,$20.Pm4,$61.Pm'',$61.Ps',$21.Ps'',$21.Perrv'',(1<.&40.)Pjunk,(62.(1<.&8.))Poo,$61.Po3,$61.Pt0',(1<.&40.)Pt1',(1<.&40.)Pt2',(1<.&40.)Pa1',(1<.&40.)Pa2',(1<.&40.)Pa3',(1<.&40.)Pa4',(1<.&40.)Pa5',(1<.&40.)Pa6',(1<.&40.)Pa7',(1<.&40.)Pt3',(1<.&40.)Pt4',(1<.&40.)Pt5',(1<.&40.)Pt6',(1<.&40.)P,(63.R1;.R1:.R19.R18.R17.-1.R16.R15.R14.R13.R12.R11.R10.R?.)(24.VR,Vo,(64.VR,R1:.R18.Lst4,$20.(65.VR,Vsc,Vk,Vbail,R1.(36.$37.))Vbail,)R14.VQ,(66.(67.R1;.R1:.R19.(26.&40.-1.)R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)VF,(26.&40.+40=30.)Vfc,(36.(1<.&40.))R16.(68.$4:.)))")
(* [comment removed for export] *).

Definition rNSUCC_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M5D ()) "Pst1,$20.Pst2,$20.Pmm,$37.Pcnt1,$10.Pst3,$20.Pidx,$10.Pm4,$61.Pm'',$61.Ps',$21.Ps'',$21.Perrv'',(1<.&40.)Pjunk,(62.(1<.&8.))Poo,$61.Po3,$61.Pg3,$37.Pb3,$37.Pr3,$2.Pt0',(1<.&40.)Pt1',(1<.&40.)Pt2',(1<.&40.)Pa1',(1<.&40.)Pa2',(1<.&40.)Pa3',(1<.&40.)Pa4',(1<.&40.)Pa5',(1<.&40.)Pa6',(1<.&40.)Pa7',(1<.&40.)Pt3',(1<.&40.)Pt4',(1<.&40.)Pt5',(1<.&40.)Pt6',(1<.&40.)P,(63.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(0.=R1;.)P,(3.$34.(35.R1=.(29.Vsc,R1>.))(;.$37.R13.))P,(69.R1>.R14.R13.R12.R1=.(48.Vsc,R1?.))P,Pa,$10.P,(=.(0.(4<.(1>.(1>.(1>.(11.R14.)(6:.$1.$10.R15.))+10.)(2=.(6;.(43.R20.R16.))R1?.))+4.)R1.)(16.R1.(4<.(1>.(1>.(1>.(1>.(11.R14.)(6:.$1.$10.R15.))+10.)(2=.(6;.(43.R20.R16.))R1?.))(6;.(43.R20.R16.)))+4.)))(13.VhRP,Vst0,R21.Vlo,(4<.(27.&40.Vsp,)+90.)R2.)P,P,(3.(6.$1.$7.$8.$2.)(:.Vst0,)(6<.(6.$1.$7.$8.$2.)(6=.$1.$7.$8.$2.)))(3.$10.(6>.$61.$6?.Vo,R21.(3=.$1.$10.(70.$1.$10.R16.)(1>.(1>.(6:.$1.$10.R16.)(1>.+10.(2=.(6;.(43.R21.R17.))R20.)))-3.)))=)(24.VR,Vo,(71.VR,$47.(72.R23.(73.=)(74.R21.R17.R20.(29.Vsc,R22.)(2=.$30.(2?.Vsc,))R22.))Vsc,R23.(75.R21.R17.R20.)R22.(4<.R22.+1.)(65.VR,Vsc,Vk,Vbail,))R1<.VQ,(66.(67.R24.R23.R22.(26.&40.R20.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(26.&40.+40<;<.)Vfc,(36.(1<.&40.))R1>.(68.$4:.)))")
(* [comment removed for export] *).
End LEVEL.

End RP_1.
