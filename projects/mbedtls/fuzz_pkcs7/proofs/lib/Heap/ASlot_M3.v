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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M3 () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Heap.ASlot_I.as_post2"; "OSSVerify.KrLib.Heap.MallocTree.implT"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.MallocFacts_AS.ta_fail"; "OSSVerify.KrLib.Heap.ASlot_W0.ta_rel"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.MallocNat.kS"; "OSSVerify.KrLib.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.MallocFacts_AS.IST"; "OSSVerify.KrLib.Heap.ASlot_I.ENTRY_REL"; "OSSVerify.KrLib.Heap.ASlot_I.ALLC"; "OSSVerify.KrLib.Heap.MallocTree.am_rel"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.meta0"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Heap.ASlot_W10.ag_frame"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.MallocTree.auxv_ok"; "OSSVerify.KrLib.Heap.Malloc_iface.MEDTAB"; "OSSVerify.KrLib.Heap.Malloc_iface.medtab_cells"; "OSSVerify.KrLib.Heap.MallocTree.pres_except"; "OSSVerify.KrLib.Heap.Malloc_fp.malloc_fp"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "LEVEL.ag_ctx"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.ASlot_I.ag_mmap"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "OSSVerify.KrLib.Heap.MallocRep.CTX"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.MallocRep.SIZE_CLASSES"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Heap.ASlot_I.ag_nest"].


Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
  induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
  destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
  apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
  assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

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
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_ASlot_M3 ()) "Pst1,$0.Pidx,$1.Ps',$2.Pms',$3.P,(4.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(5.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

(* [comment removed for export] *)
Definition ag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (j : list byte) (oo : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_M3 ()) "(6.(7.Vsc,Vst,O8.)(6.(8.Vsc,Vst,O8.)(6.(9.$:.(;.O8.Vsc,)(<.$=.))(6.(>.(?.(10.$0.$:.))O1.(11.(?.(10.$0.$:.))O8.(12.$0.$:.)(13.(10.$0.$:.)))(14.(10.$0.(?.$=.))(15.$0.(?.$=.)O7.(14.$=.O6.))))(6.(16.Vst0,O7.)(6.(17.Vst0,O7.)(6.(18.O7.)(6.(19.O8.O7.(14.$=.O6.))(6.(9.$1:.(1;.O7.O6.)$1<.)(6.(1=.O7.O6.)(6.(1>.O7.O5.)(6.(1?.O7.)(6.(20.O7.Vo,O5.)(6.(21.$22.O5.)(6.(23.$22.O5.Vlo,(24.(25.&40.Vsp,)-60.))(6.(26.$22.O5.(24.(25.&40.Vsp,)-60.)(27.Vsc,O2.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))(6.(26.$22.O5.(24.(25.&40.Vtp,)-:4.)(28.$29.(2:.O3.)(2;.$29.)))(6.(2<.O5.(25.&40.Vsp,))(6.(26.$22.O5.$2=.$2>.)(6.(2?.(30.Vst0,O7.Vlo,(25.&40.Vsp,))Vm,O5.)(6.(31.O7.O4.)(6.(9.$0.(32.O4.)(32.Vs,))(6.(9.(10.$1.$1.)(33.O4.)(33.Vs,))(9.$34.(35.O4.)(35.Vs,)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition HMM_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_M3 ()) "Pst1,$0.Pst2,$0.Pmm,$=.Pm3,$36.Ps',$2.Perrv',(37.&40.)Pj,(38.(37.&8.))Poo,$36.Pcnt1,$1.Pt0',(37.&40.)Pt2',(37.&40.)Pa3',(37.&40.)Pt4',(37.&40.)Pt6',(37.&40.)P,(39.R>.R=.R<.R;.R:.R9.R8.R7.)P,(6.(3:.+1.R7.)(3:.R7.+20.))P,(3;.+800.(24.(3<.(3<.(3=.Vsc,)$3>.)R8.)$3>.))(5.VR,Vo,(3?.VR,Vsc,Vreq,Vk,Vbail,R10.R?.R9.)R=.VQ,(40.(41.(42.&40.+163?<.)(42.&40.(24.(25.&40.Vsp,)-60.))Vgp,Vtp,R8.(43.(3<.(3=.Vsc,)$3>.))R7.(42.&40.Vsc,)(42.&40.$44.)(43.+1000.)(43.(3<.(3<.(3=.Vsc,)$3>.)R9.))(43.(45.R10.Vsc,))R6.(42.&40.$46.)(43.+800.)(43.R9.)(42.&40.(47.R10.R?.))(42.&40.(24.Vsc,+:.))(43.(3=.Vsc,))Va1,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,(42.&40.(24.Vsc,+3:.))R5.(43.(3<.+4.R9.))R4.)VF,(42.&40.+16640.)Vfc,(<.(37.&40.))R>.(48.$22.)))")
(* [comment removed for export] *).

Definition HNEST_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_M3 ()) "Pst1,$0.Pst2,$0.Pmm,$=.Pm3,$36.Ps',$2.Perrv',(37.&40.)Pj,(38.(37.&8.))Poo,$36.Pcnt1,$1.Pt0',(37.&40.)Pt2',(37.&40.)Pa3',(37.&40.)Pt5',(37.&40.)Pt6',(37.&40.)P,(39.R>.R=.R<.R;.R:.R9.R8.R7.)P,(6.(3:.+1.R7.)(3:.R7.+20.))P,(3:.(24.(3<.(3<.(3=.Vsc,)$3>.)R8.)$3>.)+800.)(5.VR,Vo,(49.VR,Vf,Vsc,Vk,Vbail,R10.R?.R9.)R=.VQ,(40.(41.(42.&40.+163?<.)(42.&40.(24.(25.&40.Vsp,)-60.))Vgp,Vtp,R8.(43.(3<.(3=.Vsc,)$3>.))R7.(42.&40.Vsc,)(42.&40.$44.)(43.+1000.)(43.(3<.(3<.(3=.Vsc,)$3>.)R9.))(43.(45.R10.Vsc,))R6.(42.&40.$46.)(43.+800.)(43.R9.)(42.&40.(47.R10.R?.))(42.&40.(24.Vsc,+:.))(43.(3=.Vsc,))Va1,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,(42.&40.(24.Vsc,+3:.))(43.R9.)R5.R4.)VF,(42.&40.+16954.)Vfc,(<.(37.&40.))R>.(48.$22.)))")
(* [comment removed for export] *).

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.

End LEVEL.
