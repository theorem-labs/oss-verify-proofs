(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W8 ASlot_W9 ASlot_W10 ASlot_W12 ASlot_I ASlot_M0 ASlot_M1.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M2 () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Heap.ASlot_I.as_post2"; "OSSVerify.KrLib.Heap.MallocTree.implT"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.MallocFacts_AS.ta_fail"; "OSSVerify.KrLib.Heap.ASlot_W0.ta_rel"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.MallocNat.kS"; "OSSVerify.KrLib.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.MallocFacts_AS.IST"; "OSSVerify.KrLib.Heap.ASlot_I.ENTRY_REL"; "OSSVerify.KrLib.Heap.ASlot_I.ALLC"; "OSSVerify.KrLib.Heap.MallocTree.am_rel"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.meta0"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Heap.ASlot_W10.ag_frame"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.MallocTree.auxv_ok"; "OSSVerify.KrLib.Heap.Malloc_iface.MEDTAB"; "OSSVerify.KrLib.Heap.Malloc_iface.medtab_cells"; "OSSVerify.KrLib.Heap.MallocTree.pres_except"; "OSSVerify.KrLib.Heap.Malloc_fp.malloc_fp"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "OSSVerify.KrLib.Heap.ASlot_I.ag_body"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Heap.MallocRep.CTX"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].



Section EPI2.
Variables (lo : Z).
Hypothesis CLO : ALLOC_CEIL_LO <= lo.   (* [comment removed for export] *)


End EPI2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : ALLOC_CEIL_LO <= lo.   (* [comment removed for export] *)
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_ASlot_M2 ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

(* [comment removed for export] *)
Definition HAG_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_M2 ()) "Pst1,$0.Pst2,$0.Pmm,$6.Pm3,P,(7.&40.)(8.(7.&8.))Ps',$2.Perrv',(7.&40.)Pt0',(7.&40.)Pt1',(7.&40.)Pt2',(7.&40.)Pa1',(7.&40.)Pa2',(7.&40.)Pa3',(7.&40.)Pa4',(7.&40.)Pa5',(7.&40.)Pa6',(7.&40.)Pt3',(7.&40.)Pt4',(7.&40.)Pt5',(7.&40.)Pt6',(7.&40.)Pj,(9.(7.&8.))Poo,$:.P,(;.Vsc,Vst,R15.)P,(<.Vsc,Vst,R16.)P,(=.$>.(?.R17.Vsc,)(10.$6.))P,(11.(8.(12.$0.$>.))R4.(13.(8.(12.$0.$>.))R18.(14.$0.$>.)(15.(12.$0.$>.)))(16.(12.$0.(8.$6.))(17.$0.(8.$6.)R17.(16.$6.R16.))))P,(18.Vst0,R18.)P,(19.Vst0,R19.)P,(1:.R1:.)P,(1;.R1<.R1;.(16.$6.R1:.))P,(=.$1<.(1=.R1<.R1;.)$1>.)P,(1?.R1=.R1<.)P,(20.R1>.R1<.)P,(21.R1?.)P,(22.R20.Vo,R1>.)P,(23.$24.R1?.)P,(25.$24.R20.Vlo,(26.(27.&40.Vsp,)-60.))P,(28.$24.R21.(26.(27.&40.Vsp,)-60.)(29.Vsc,R11.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))P,(28.$24.R22.(26.(27.&40.Vtp,)-:4.)(2:.$2;.(2<.R20.)(2=.$2;.)))P,(2>.R23.(27.&40.Vsp,))P,(28.$24.R24.$2?.$30.)P,(31.(32.Vst0,R27.Vlo,(27.&40.Vsp,))Vm,R25.)P,(33.R28.R25.)P,(=.$0.(34.R26.)(34.Vs,))P,(=.(12.$1.$1.)(35.R27.)(35.Vs,))P,(=.$36.(37.R28.)(37.Vs,))(5.VR,Vo,(38.VR,Vf,Vsc,Vreq,Vk,Vbail,R2<.R2;.)R29.VQ,(39.(3:.(3;.&40.+163?<.)(3;.&40.(26.(27.&40.Vsp,)-60.))Vgp,Vtp,R27.R26.R25.(3;.&40.Vsc,)(3;.&40.$3<.)(3;.&40.(3=.R2<.R2;.))R24.R23.R22.R21.R20.R1?.(3;.&40.(3=.R2<.R2;.))(3;.&40.(26.Vsc,+:.))(3>.(3?.Vsc,))Va1,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1>.R1=.R1<.R1;.)VF,(3;.&40.+16404.)Vfc,(10.(7.&40.))R2:.(40.$24.)))")
(* [comment removed for export] *).
Hypothesis HAG : HAG_stmt.


End LEVEL.
