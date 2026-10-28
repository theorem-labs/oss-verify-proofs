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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_A HP_RMalloc_fp HP_RF_malloc_enf HP_RAllocSlot_iface HP_RF_malloc_entry HP_RF_malloc_join HP_RF_malloc_small.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_malloc_core () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.HP_RF_malloc_join.renf_hyp"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ret"; "Corelib.Init.Datatypes.pair"; "RP_2.rcoreQ"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_malloc_join.rfail_hyp"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_tick"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.AREACH_from"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_A.MFACTS_g"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RATP"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.RAM_STACK"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.MMAP_THRESHOLD"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_fp.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.malloc_core"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.NArith.BinNat.N.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_tick"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.size_class"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.FUEL"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.under_virgin"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmalloc_entry"].

Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

End RP_1.
Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
Section RP_2. Context {hRP : run_params}.
Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4088c) fc None m1 (seg_rom rsegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            rmalloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ under_virgin st2 g b idx
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom rsegs)
      /\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
      /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
      /\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.

#[using="Type"] Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "(0.VhRP,(1.$2.(3.(1.$4.$5.)))Lst1,$2.Lr,(3.(1.$4.$5.))(6.(1.$2.(3.(1.$4.$5.)))(7.$2.(3.(1.$4.$5.))R2.R1.))O18.O17.O16.O15.(8.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  dexists b, r, m1, errv. deexists 17. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

#[using="Type"] Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "(9.VhRP,(1.$2.(3.(1.$4.$5.)))Lst1,$2.Lr,(3.(1.$4.$5.))(6.(1.$2.(3.(1.$4.$5.)))(7.$2.(3.(1.$4.$5.))R2.R1.))O18.O17.O16.O15.(8.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
  apply rimplT_ret. apply evt_done. cbn [rcoreQ].
  dexists m1, errv. deexists 14. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

(* [comment removed for export] *)
Definition rbig_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "Po,$:.Pm0,$:.Pst,$2.PLB,(;.$<.)Ps,$=.Pra,(>.&40.)Psp,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Ps0v,(>.&40.)Ps1v,(>.&40.)Ps2v,(>.&40.)Ps3v,(>.&40.)Ps4v,(>.&40.)PF,(?.&5.(>.&40.))Pfc,(>.&20.)Pn,$5.Plo,$5.Pt,$10.Pm1,$:.Perrv,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2r,(>.&40.)Ps3r,(>.&40.)Ps4r,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pra',(>.&40.)Zst1,$2.(11.R15.R2<.)P,(12.$13.R2=.R2<.)P,(14.$13.R2>.R2=.)P,(15.VhRP,R2?.R30.)P,(16.(>.&40.)R2:.(17.&40.$18.))P,(19.(1:.VhRP,)R1;.)P,(19.R1<.(1;.(1;.(1<.&40.R2>.)+30.)$1=.))P,(1>.(19.$1?.R1>.)(20.R1>.(21.+2.+20.)))P,(22.R34.R32.)P,(15.VhRP,R9.R1=.)P,(23.R:.)P,(24.R;.R39.R1?.)P,(25.$26.R20.)P,(27.$26.R21.R23.(28.(1<.&40.R35.)-30.))P,(29.$26.R22.(28.(1<.&40.R36.)-30.)(2:.$2;.(2<.R28.)(2:.$2;.(2<.R29.)(2:.$2;.(2<.R2:.)(2:.$2;.(2<.R2;.)(2:.$2;.(2<.R2<.)(2:.$2;.(2<.R37.)(2=.$2;.))))))))P,(29.$26.R23.(28.(1<.&40.R35.)-:4.)(2:.$2;.(2>.R22.)(2=.$2;.)))P,(2?.VhRP,R24.(1<.&40.R38.))P,(30.(31.VhRP,R3=.R11.R27.(1<.&40.R39.))R3>.R25.)(32.(1.$2.(3.(1.$4.$5.)))R40.(33.$34.R12.R29.)R3<.(8.R40.R3?.R3>.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)(35.(36.R13.(17.&40.(28.(1<.&40.R3:.)-30.))R39.R38.R24.R23.R22.(17.&40.R29.)(17.&40.$37.)(17.&40.+1??><.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R37.R36.R35.R34.R33.R32.R31.R17.R16.R15.R14.)R2;.(17.&40.+405=<.)R2:.(38.(>.&40.))R26.(39.$26.)))")
(* [comment removed for export] *).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "Pst,$2.PLB,(;.$<.)Pt,$10.Psc,$5.Pn,$5.P,(12.$13.R5.R4.)P,(14.$13.R6.R5.)P,(3:.(3;.R7.)R5.)P,(1>.(19.=R5.)(20.R5.+30.))P,(1>.(19.=R5.)(20.R5.(21.+2.+20.)))P,(19.(28.R6.+4.)(3<.+10.(3=.R7.)))A5.Vas_pre,R;.(11.R9.R;.)R8.R7.$3>.")
(* [comment removed for export] *).
Hypothesis AS_UV : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "Pst0,$2.Pst,$2.Pst1,$2.Psc,$5.Pidx,$5.Pg,$4.Pb,$4.P,A5.Vas_inv,R7.R6.R5.R4.R3.P,(19.=R4.)P,(16.$3?.(40.R7.R6.)(41.$4.R4.))P,(16.$3?.(42.(43.R8.R5.))(41.$4.R4.))(44.R9.R6.R5.R7.)")
(* [comment removed for export] *).
Hypothesis RBIG : rbig_stmt.

#[using="as_pre as_inv RAS AS_PRE AS_UV RBIG"] Lemma rmalloc_core_implT : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_core ()) "Pra,(>.&40.)Psp,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)PF,(?.&5.(>.&40.))Pfc,(>.&20.)Pm,$:.Pst,$2.PLB,(;.$<.)Ps,$=.Pn,$5.Plo,$5.Perrv,(>.&40.)Pt,$10.P,(12.$13.R7.R6.)P,(14.$13.R8.R7.)P,(15.VhRP,R9.R:.)P,(22.R:.R8.)P,(2?.VhRP,R<.(1<.&40.R2<.))P,(27.$26.R=.R8.(1<.&40.R2=.))P,(19.(1:.VhRP,)R9.)P,(19.R:.(1;.(1<.&40.R2?.)+2000.))P,(29.$26.R10.(28.(1<.&40.R2>.)-:4.)(2:.$2;.(2>.R:.)(2=.$2;.)))P,(25.$26.R11.)P,(16.(>.&40.)R30.(17.&40.$18.))P,(16.(>.&40.)R2;.(17.&40.R?.))P,(1>.(19.=R10.)(20.R10.(21.+2.+20.)))P,(3:.(3;.R14.)R>.)(32.(1.$2.(3.(1.$4.$5.)))R16.(33.$34.(11.R?.R15.)R12.)R13.(8.R16.R16.R15.R13.R37.R36.R35.R34.R23.R22.R21.R20.R1?.R1>.R1=.R30.R2?.R26.R25.R24.R18.R17.R12.R11.)(35.(36.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(17.&40.$45.)R17.(38.(>.&40.))R16.(39.$26.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
  pose proof (areach_under st LB AR) as FU.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge 0) as ASG.
  assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= rceil).
  { intros rid r1 H1. dpose (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). rceilb. lia. }
  dpose MR as (WF0 & CX0 & GL0 & _). ddestruct GL0 as (_ & NL & _).
  assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
            rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
            /\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
  { intros m1 MU WM. rceilb.
    split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; rceilb; lia]. }
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
    { eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| rceilb; lia| lia| exact MI]. }
    (intros ms' dd_H; ddestruct dd_H as (a1' & m1 & -> & FR & ST1 & MU & WM & MI1)).
    ddestruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    apply evt_done.
    eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
    + unfold RAM_STACK. lia.
    + lia.
  - (* [comment removed for export] *)
    unfold malloc_core.
    replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    riprefixT. eapply evt_cut.
    { eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| rceilb; lia| lia| exact MI| exact NL]. }
    (intros ms' dd_H; ddestruct dd_H as (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1)).
    ddestruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
    dpose (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
    apply evt_done.
    eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS AS_UV).
    all: try eassumption.
    + apply renf_hyp_ret.
    + apply rfail_hyp_ret.
    + unfold RAS_STACK. lia.
    + reflexivity.
    + intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.

End RP_2.
