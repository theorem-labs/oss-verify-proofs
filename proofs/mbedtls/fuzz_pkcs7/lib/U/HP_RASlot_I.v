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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W1 ASlot_I.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMalloc_fp HP_RAllocSlot_iface.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_I () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.AREACH_from"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.IST"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ENTRY_REL"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.ALLC"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.mrel"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_I.as_inv2"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_mmap_counter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.slot_ok"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_stride"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "stdpp.base.empty"; "stdpp.gmap.gmap_empty"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_enframe.rdv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pans_mem"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.M"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RP_1.ras_pre2"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.U.HP_RAllocSlot_iface.RAS_STACK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RATP"; "RP_1.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_slot_entry"; "RP_1.ralloc_slot_stmt2"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.leaf_of"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.kS"; "RocqVerifyHarness.AgentSubmission.Heap.MallocNat.bS"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.ralloc_meta_stmt"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.RAM_STACK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.ram_post"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_meta_entry"].


Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rimplT_steq {R} o (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
  intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

#[using="Type"] Lemma rimplT_nat2 {X Y R} o (P : forall R', (X -> Y -> Malloc.M R') -> Malloc.M R' -> Malloc.M R')
      (k : X -> Y -> Malloc.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
  steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
  rimplT o (P _ kS bS) s QS ms ->
  (forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
  (forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
  rimplT o (P R k bail) s Q ms.
Proof.
  intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
  eapply rimplT_bind; [eapply rimplT_reach; exact H|].
  intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_I ()) "(0.(1.(2.$3.)LLB,(2.$3.)(0.(4.$5.O5.R1.)(6.O5.O4.)))(0.(7.O5.O4.)(0.(8.O4.)(0.(0.(9.=O3.)(:.O3.+30.))(0.(0.(9.=O2.)(:.O2.(;.+2.+20.)))(9.(<.O2.+4.)(=.+10.(>.O3.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_I ()) "Lms',$?.(1.(10.&40.)Lt0,(10.&40.)(1.(10.&40.)Lt1,(10.&40.)(1.(10.&40.)Lt2,(10.&40.)(1.(10.&40.)La1,(10.&40.)(1.(10.&40.)La2,(10.&40.)(1.(10.&40.)La3,(10.&40.)(1.(10.&40.)La4,(10.&40.)(1.(10.&40.)La5,(10.&40.)(1.(10.&40.)La6,(10.&40.)(1.(10.&40.)La7,(10.&40.)(1.(10.&40.)Lt3,(10.&40.)(1.(10.&40.)Lt4,(10.&40.)(1.(10.&40.)Lt5,(10.&40.)(1.(10.&40.)Lt6,(10.&40.)(1.P,(10.&40.)(11.(10.&8.))Lm',P,(10.&40.)(11.(10.&8.))(1.(10.&40.)Lerrv',(10.&40.)(0.(12.$?.R11.(13.(14.O1=.O1<.O1;.O1:.R10.R?.R>.O19.O18.(15.&40.O2.)R=.R<.R;.R:.R9.R8.R7.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R6.R5.R4.R3.)O=.(16.O1=.)O<.(17.(10.&40.))R2.(18.$19.)))(0.(1:.$19.R2.)(0.(1;.$19.R2.O6.(1<.&40.O1<.))(0.(1=.$19.R2.(<.(1<.&40.O1:.)-:4.)(1>.$1?.(20.R1.)(21.$1?.)))(0.(22.VhRP,R2.(1<.&40.O1<.))(0.(23.VhRP,O3.R2.)(0.(24.O3.)(0.(25.O3.O;.R2.)(0.(26.(27.VhRP,O9.O3.O6.(1<.&40.O1<.))O:.R2.)(0.(28.O8.O3.)(0.(29.O3.O1.)(0.(12.$2:.(2;.O1.)(2;.O7.))(0.(12.(2<.$2=.$2=.)(2>.O1.)(2>.O7.))(0.(12.$2?.(30.O1.)(30.O7.))(0.(31.O9.O8.O3.O5.O2.)(0.(0.(9.=(32.(33.O3.)))(:.(32.(33.O3.))(;.+2.+20.)))(34.(12.$2=.O2.-1.)(0.(9.=O2.)(1.$35.Lg,$35.(1.$35.Lb,$35.(1.$36.Lr,$36.(0.(12.$37.(38.O3.O5.)(39.$35.R3.))(0.(3:.O3.R3.R2.R1.O2.O4.)(0.Pa,$2=.P,(0.(9.(3;.(<.(<.(<.(3<.R2.)(3=.$3>.$2=.R3.))+10.)(=.(3?.(40.O3.R4.))O2.))+4.)R1.)(:.R1.(3;.(<.(<.(<.(<.(3<.R2.)(3=.$3>.$2=.R3.))+10.)(=.(3?.(40.O3.R4.))O2.))(3?.(40.O3.R4.)))+4.)))(27.VhRP,O9.O3.O6.(1<.&40.O1<.)R2.)P,(12.(41.$3>.$42.$43.$36.)(44.O9.)(45.(41.$3>.$42.$43.$36.)(46.$3>.$42.$43.$36.)))(12.$2=.(47.$48.$49.O;.O3.(4:.$3>.$2=.(4;.$3>.$2=.R3.)(<.(<.(3=.$3>.$2=.R3.)(<.+10.(=.(3?.(40.O3.R4.))O2.)))-3.)))=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).


Definition ralloc_slot_stmt2 (fuel : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_I ()) "PR,StPk,P,$2:.P,$2=.(4<.R3.)Pbail,(4<.R2.)Po,$48.Ps,$4=.PQ,P,R5.P,$4=.P,$?.SpPra,(10.&40.)Psp,(10.&40.)Pgp,(10.&40.)Ptp,(10.&40.)Pt0,(10.&40.)Pt1,(10.&40.)Pt2,(10.&40.)Ps0,(10.&40.)Ps1,(10.&40.)Pa0,(10.&40.)Pa1,(10.&40.)Pa2,(10.&40.)Pa3,(10.&40.)Pa4,(10.&40.)Pa5,(10.&40.)Pa6,(10.&40.)Pa7,(10.&40.)Ps2,(10.&40.)Ps3,(10.&40.)Ps4,(10.&40.)Ps5,(10.&40.)Ps6,(10.&40.)Ps7,(10.&40.)Ps8,(10.&40.)Ps9,(10.&40.)Ps10,(10.&40.)Ps11,(10.&40.)Pt3,(10.&40.)Pt4,(10.&40.)Pt5,(10.&40.)Pt6,(10.&40.)PF,(4>.&5.(10.&40.))Pfc,(10.&20.)Pm,$48.Pst0,$2:.Pst,$2:.Plo,$2=.Psc,$2=.Preq,$2=.Perrv,(10.&40.)P,(4?.R6.R5.R3.R2.O1.)P,(23.VhRP,R6.R8.)P,(24.R7.)P,(25.R8.R2>.R:.)P,(29.R9.R2>.)P,(22.VhRP,R<.(1<.&40.R2<.))P,(1;.$19.R=.R:.(1<.&40.R2=.))P,(9.(50.VhRP,)R;.)P,(9.R<.(3;.(1<.&40.R2?.)(51.R;.)))P,(1=.$19.R10.(<.(1<.&40.R2>.)-:4.)(1>.$1?.(20.R:.)(21.$1?.)))P,(1:.$19.R11.)P,(12.(10.&40.)R30.(15.&40.$52.))P,(12.(10.&40.)R2;.(15.&40.R?.))P,(12.(10.&40.)R2;.(15.&40.R?.))P,Pst1,$2:.Pidx,$2=.Ps',$4=.Pms',$?.P,(53.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R3=.R19.R18.R17.R3<.R16.R15.R14.R4.R3.R2.R1.)(54.R41.R3>.A2.R40.R5.R4.R3.R3<.R2.)(54.R3=.R3:.(55.R3=.$56.O1.R14.R12.R11.R3<.R3;.)R39.R38.(13.(14.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(15.&40.$57.)R17.(17.(10.&40.))R16.(18.$19.)))")
(* [comment removed for export] *).


(* [comment removed for export] *)
#[using="Type"] Lemma ralloc_slot_stmtL (fuel : nat) : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_I ()) "P,(58.O1.)PR,StPk,P,$2:.P,$2=.(4<.R3.)Pbail,(4<.R2.)Po,$48.Ps,$4=.PQ,P,R5.P,$4=.P,$?.SpPra,(10.&40.)Psp,(10.&40.)Pgp,(10.&40.)Ptp,(10.&40.)Pt0,(10.&40.)Pt1,(10.&40.)Pt2,(10.&40.)Ps0,(10.&40.)Ps1,(10.&40.)Pa0,(10.&40.)Pa1,(10.&40.)Pa2,(10.&40.)Pa3,(10.&40.)Pa4,(10.&40.)Pa5,(10.&40.)Pa6,(10.&40.)Pa7,(10.&40.)Ps2,(10.&40.)Ps3,(10.&40.)Ps4,(10.&40.)Ps5,(10.&40.)Ps6,(10.&40.)Ps7,(10.&40.)Ps8,(10.&40.)Ps9,(10.&40.)Ps10,(10.&40.)Ps11,(10.&40.)Pt3,(10.&40.)Pt4,(10.&40.)Pt5,(10.&40.)Pt6,(10.&40.)PF,(4>.&5.(10.&40.))Pfc,(10.&20.)Pm,$48.Pst0,$2:.Pst,$2:.Plo,$2=.Psc,$2=.Preq,$2=.Perrv,(10.&40.)P,(4?.R6.R5.R3.R2.O1.)P,(23.VhRP,R6.R8.)P,(24.R7.)P,(25.R8.R2>.R:.)P,(29.R9.R2>.)P,(22.VhRP,R<.(1<.&40.R2<.))P,(1;.$19.R=.R:.(1<.&40.R2=.))P,(9.(50.VhRP,)R;.)P,(9.R<.(3;.(1<.&40.R2?.)(51.R;.)))P,(1=.$19.R10.(<.(1<.&40.R2>.)-:4.)(1>.$1?.(20.R:.)(21.$1?.)))P,(1:.$19.R11.)P,(12.(10.&40.)R30.(15.&40.$52.))P,(12.(10.&40.)R2;.(15.&40.R?.))P,(12.(10.&40.)R2;.(15.&40.R?.))P,Pst1,$2:.Pidx,$2=.Ps',$4=.Pms',$?.P,(53.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R3=.R19.R18.R17.R3<.R16.R15.R14.R4.R3.R2.R1.)P,(59.(11.(2<.$2:.$2=.))R3>.(55.(11.(2<.$2:.$2=.))$56.O1.R18.R16.R15.(5:.$2:.$2=.)(5;.(2<.$2:.$2=.)))(39.(2<.$2:.$2=.)(4:.$2:.$2=.R5.R4.)))(54.R42.R3?.A2.R41.R6.R5.R4.R3=.R3.)(54.R3=.R3:.(55.R3=.$56.O1.R14.R12.R11.R3<.R3;.)R39.R38.(13.(14.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(15.&40.$57.)R17.(17.(10.&40.))R16.(18.$19.)))")
(* [comment removed for export] *).
Proof.
  intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
                             | None => False end)).
  - apply alloc_slot_nat.
  - eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
  - intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
  - intros s' ms' [].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ralloc_meta_stmtL (am_pre : mstate -> Prop) : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_I ()) "P,(5<.VhRP,O1.)PR,StPk,P,$2:.P,$37.(4<.R3.)Pbail,(4<.R2.)Po,$48.Ps,$4=.PQ,P,R5.P,$4=.P,$?.SpPra,(10.&40.)Psp,(10.&40.)Pgp,(10.&40.)Ptp,(10.&40.)Pt0,(10.&40.)Pt1,(10.&40.)Pt2,(10.&40.)Ps0,(10.&40.)Ps1,(10.&40.)Pa0,(10.&40.)Pa1,(10.&40.)Pa2,(10.&40.)Pa3,(10.&40.)Pa4,(10.&40.)Pa5,(10.&40.)Pa6,(10.&40.)Pa7,(10.&40.)Ps2,(10.&40.)Ps3,(10.&40.)Ps4,(10.&40.)Ps5,(10.&40.)Ps6,(10.&40.)Ps7,(10.&40.)Ps8,(10.&40.)Ps9,(10.&40.)Ps10,(10.&40.)Ps11,(10.&40.)Pt3,(10.&40.)Pt4,(10.&40.)Pt5,(10.&40.)Pt6,(10.&40.)PF,(4>.&5.(10.&40.))Pfc,(10.&20.)Pm,$48.Pst,$2:.Plo,$2=.Perrv,(10.&40.)P,A1.O1.R3.P,(23.VhRP,R4.R5.)P,(24.R5.)P,(29.R6.R2:.)P,(22.VhRP,R8.(1<.&40.R28.))P,(1;.$19.R9.R7.(1<.&40.R29.))P,(9.(50.VhRP,)R8.)P,(9.R9.(3;.(1<.&40.R2;.)$5=.))P,(1=.$19.R<.(<.(1<.&40.R2:.)-:4.)(1>.$1?.(20.R9.)(21.$1?.)))P,(1:.$19.R=.)P,(12.(10.&40.)R2<.(15.&40.+5=0<8.))P,Pst1,$2:.Pmo,$37.Ps',$4=.Pms',$?.P,(5>.VhRP,R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R12.R36.R11.R13.R4.R3.R2.R1.)P,(29.R5.R3.)P,(59.(11.(2<.$2:.$37.))R39.(5?.(11.(2<.$2:.$37.))R14.(5:.$2:.$37.)(5;.(2<.$2:.$37.)))(39.(2<.$2:.$37.)(4:.$2:.$37.R6.R5.)))(54.R3=.R3:.A2.R3<.R7.R6.R5.R38.R4.)(54.R37.R34.(5?.R37.R?.R36.R35.)R33.R32.(13.(14.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(15.&40.$60.)R11.(17.(10.&40.))R10.(18.$19.)))")
(* [comment removed for export] *).
Proof.
  intros AM. intros until errv. intros PRE MR TK BL AUX ST CLO LO ER MI TP K.
  eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
            (fun r s' ms' => match r with
                             | Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
                             | None => False end)).
  - apply alloc_meta_nat.
  - eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
  - intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
  - intros s' ms' [].
Qed.

End RP_1.
