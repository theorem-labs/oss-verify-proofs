(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMalloc_fp.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RAllocSlot_iface () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.U.HP_F_syscalls.rsegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.U.HP_RMallocTree.rauxv_ok"; "OSSVerify.KrLib.U.HP_RMallocRep.rmrep"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.U.HP_RMallocTree.rpres_except"; "OSSVerify.KrLib.U.HP_RMalloc_fp.rmalloc_fp"; "OSSVerify.KrLib.Heap.Malloc_fp.mrel"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc_fp.slot_ok"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.snd"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "stdpp.base.empty"; "stdpp.gmap.gmap_empty"; "OSSVerify.KrLib.Heap.F_malloc_enframe.rdv"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.MallocTree.pans_mem"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Heap.RunParams.rceil"; "RP_1.RAS_STACK"; "OSSVerify.KrLib.U.HP_RMallocRep.RATP"; "RP_1.ras_post"; "OSSVerify.KrLib.U.HP_RMallocTree.rimplT"; "OSSVerify.KrLib.Heap.Malloc.alloc_slot"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.U.HP_RMallocRep.ralloc_slot_entry"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

#[using="Type"] Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. unfold RAS_STACK. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RAllocSlot_iface ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lerrv',(2.&40.)(4.(5.$0.R11.(6.(7.O1=.O1<.O1;.O1:.R10.R?.R>.O19.O18.(8.&40.O2.)R=.R<.R;.R:.R9.R8.R7.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R6.R5.R4.R3.)O=.(9.O1=.)O<.(:.(2.&40.))R2.(;.$<.)))(4.(=.$<.R2.)(4.(>.$<.R2.O6.(?.&40.O1<.))(4.(10.$<.R2.(11.(?.&40.O1:.)-:4.)(12.$13.(14.R1.)(15.$13.)))(4.(16.VhRP,R2.(?.&40.O1<.))(4.(17.VhRP,O3.R2.)(4.(18.O3.)(4.(19.O3.O;.R2.)(4.(1:.(1;.VhRP,O9.O3.O6.(?.&40.O1<.))O:.R2.)(4.(1<.O8.O3.)(4.(1=.O3.O1.)(4.(5.$1>.(1?.O1.)(1?.O7.))(4.(5.(20.$21.$21.)(22.O1.)(22.O7.))(4.(5.$23.(24.O1.)(24.O7.))(4.A5.O1>.O9.O8.O3.O5.O2.(4.(4.(25.=(26.(27.O3.)))(28.(26.(27.O3.))(29.+2.+20.)))(2:.(5.$21.O2.-1.)(4.(25.=O2.)(1.$2;.Lg,$2;.(1.$2;.Lb,$2;.(1.$2<.Lr,$2<.(4.(5.$2=.(2>.O3.O5.)(2?.$2;.R3.))(4.(30.O3.R3.R2.R1.O2.O4.)(4.Pa,$21.P,(4.(25.(31.(11.(11.(11.(32.R2.)(33.$34.$21.R3.))+10.)(35.(36.(37.O3.R4.))O2.))+4.)R1.)(28.R1.(31.(11.(11.(11.(11.(32.R2.)(33.$34.$21.R3.))+10.)(35.(36.(37.O3.R4.))O2.))(36.(37.O3.R4.)))+4.)))(1;.VhRP,O9.O3.O6.(?.&40.O1<.)R2.)P,(5.(38.$34.$39.$3:.$2<.)(3;.O9.)(3<.(38.$34.$39.$3:.$2<.)(3=.$34.$39.$3:.$2<.)))(5.$21.(3>.$3?.$40.O;.O3.(41.$34.$21.(42.$34.$21.R3.)(11.(11.(33.$34.$21.R3.)(11.+10.(35.(36.(37.O3.R4.))O2.)))-3.)))=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
                           (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RAllocSlot_iface ()) "Pfuel,$43.PR,StPk,P,$1>.P,$21.(44.R3.)Pbail,(44.R2.)Po,$3?.Ps,$45.PQ,P,R5.P,$45.P,$0.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(46.&5.(2.&40.))Pfc,(2.&20.)Pm,$3?.Pst0,$1>.Pst,$1>.Plo,$21.Psc,$21.Preq,$21.Perrv,(2.&40.)P,A5.O2.R6.R5.R3.R2.R2?.P,(17.VhRP,R6.R8.)P,(18.R7.)P,(19.R8.R2>.R:.)P,(1=.R9.R2>.)P,(16.VhRP,R<.(?.&40.R2<.))P,(>.$<.R=.R:.(?.&40.R2=.))P,(25.(47.VhRP,)R;.)P,(25.R<.(31.(?.&40.R2?.)(48.R;.)))P,(10.$<.R10.(11.(?.&40.R2>.)-:4.)(12.$13.(14.R:.)(15.$13.)))P,(=.$<.R11.)P,(5.(2.&40.)R30.(8.&40.$49.))P,(5.(2.&40.)R2;.(8.&40.R?.))P,(5.(2.&40.)R2;.(8.&40.R?.))P,Pst1,$1>.Pidx,$21.Ps',$45.Pms',$0.P,(4:.O1.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R3=.R19.R18.R17.R3<.R16.R15.R14.R4.R3.R2.R1.)(4;.R41.R3>.A2.R40.R5.R4.R3.R3<.R2.)(4;.R3=.R3:.(4<.R3=.$4=.R3>.R14.R12.R11.R3<.R3;.)R39.R38.(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(8.&40.$4>.)R17.(:.(2.&40.))R16.(;.$<.)))")
(* [comment removed for export] *).


End RP_1.
