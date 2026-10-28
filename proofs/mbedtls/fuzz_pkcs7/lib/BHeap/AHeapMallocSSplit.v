(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX SysStep HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen APopSec. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvS AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AInstDepot AInstPop AInstGen AVst AVstT AInstSec
     AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotCfg AW_DepotTop AW_MallocA AW_AllocA AW_Poison
     AW_AllocB AW_MallocB AW_MallocC HMLib HM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_Large AW_CfgDefs AW_CfgS
     AW_LargeCfgS AW_MallocGenLib AW_MallocGen AW_SecB AW_SecC AW_MapOrDie AW_MmapDie AW_MallocSecS AW_MallocSecTop
     AW_LargeSplit AW_MallocSecSplit ASplit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PoisonBig AW_Blist AW_FakeDefs HMFrame AHeapR AHeapB AHeapL AMallocPost AHit AInstMallocG AInstMallocS
     ARoomL AInstSecRoom AMallocSplitPost.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SRz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ AKinvM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AHeapMallocSSplit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.dstat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocSecS.DIE_NEED"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocSplitPost.mallocH_postN"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocSplitPost.mallocH_postC"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AHit.A_WRAP_MALLOC"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma u64arr_cells8' : forall m A ws, u64arr asegs m A ws -> rw_cells asegs m A (map C8 ws).
Proof. intros m A ws H. exact (u64arr_cells m _ _ H). Qed.

#[using="Type"] Lemma wr_at_join : ltac2:(CDefT.buildp (gd_tbl_AHeapMallocSSplit ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pn1,$2.Pn2,$2.P,(3.$4.R4.R3.R2.)P,(3.$4.R5.(5.R4.R3.)R2.)P,(6.=R4.)P,(6.=R4.)(3.$4.R8.R7.(5.R6.R5.))")
(* [comment removed for export] *).
Proof. intros m A n1 n2 W1 W2 N1 N2. exact (proj2 (wr_at_app asegs m A n1 n2 N1 N2) (conj W1 W2)). Qed.

#[using="Type"] Lemma map_size_sec : forall n, map_size (needed2 n) = sec_map_size n.
Proof. intros n. unfold map_size, sec_map_size, round_up. replace (needed2 n + 4096 - 1) with (needed2 n + 4095) by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apart_of_fresh : ltac2:(CDefT.buildp (gd_tbl_AHeapMallocSSplit ()) "PP,P,$2.SpPa,$2.Pms,$2.Pmb,$2.Pmsz,$2.P,(7.=R3.)P,(7.=R2.)P,Py,$2.P,(8.(6.R5.R1.)(7.R1.(5.R5.R4.)))A1.R9.R2.P,Py,$2.P,A1.R9.R1.(9.(8.(6.R9.R2.)(7.R2.(5.R9.R8.))))(:.(6.(5.R6.R5.)R8.)(6.(5.R8.R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros P a ms mb msz M1 M2 IN OUT.
  destruct (Z.lt_ge_cases mb a) as [LT|GE].
  - left. destruct (Z.le_gt_cases (mb + msz) a) as [LE|GT]; [exact LE|]. exfalso. apply (OUT a (IN a ltac:(lia))). lia.
  - right. destruct (Z.le_gt_cases (a + ms) mb) as [LE|GT]; [exact LE|]. exfalso. apply (OUT mb (IN mb ltac:(lia))). lia.
Qed.

(* [comment removed for export] *)
Definition nzoneS : list (Z * Z) := [(A_SS, A_DEP_END); (A_INSTANCE + 112, A_INSTANCE + 720)].
Definition nzoneN : list (Z * Z) := [(A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)].

Section MSECSPLIT.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).
  Local Notation AL := AL0.

  #[using="Type"] Lemma IMG : asan_img_ok AL. Proof. exact AL0_img. Qed.
  #[using="Type"] Lemma ALWF : al_wf AL. Proof. exact AL0_wf. Qed.
  #[using="Type"] Lemma ASB : al_sb AL = 0x7fff8000. Proof. reflexivity. Qed.
    #[using="Type"] Lemma IMLO : al_img_lo AL = 0x10000. Proof. reflexivity. Qed.
  #[using="Type"] Lemma IMH : al_img_hi AL = 0x65f000. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Hypothesis MOD_DIE : ltac2:(CDefT.buildp (gd_tbl_AHeapMallocSSplit ()) "PCS,P,$2.SpPgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa6,(0.&40.)Pra,(0.&40.)PSP0,$2.PF,(;.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pmm,P,(0.&40.)(1.(0.&8.))Paddr,$2.Psize,$2.Plo0,$2.Pfr,(<.(0.&8.))P,(=.$>.R21.)P,(8.(6.=R5.)(7.R5.(?.+2.+2?.)))P,(8.(7.=R5.)(6.R5.(?.+2.+28.)))P,(10.$4.R8.(5.R<.-60.)(11.$12.(13.(14.&40.+32.))(11.$12.(15.#2<.R4.)(11.$12.(16.R1:.)(11.$12.(16.R1;.)(11.$12.(16.R1<.)(11.$12.(16.R1=.)(11.$12.(16.R1>.)(11.$12.(16.R=.)(17.$12.))))))))))P,(18.R9.)P,(19.$4.R:.R7.(5.R>.-60.))P,(6.+65?000.R8.)P,(6.R9.(1:.R10.$1;.))P,(6.R11.(?.+2.+3?.))P,(1<.(11.(1=.$2.$2.)(1>.$2.$2.R;.R12.)(17.(1=.$2.$2.)))R?.R>.)P,(1?.$4.R10.R?.)P,(20.$4.R10.)P,(21.R2=.R>.(1:.R15.R>.))(22.$4.$>.R2>.(23.R14.$24.)(25.(14.&40.(1:.(?.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="MOD_DIE"] Theorem malloc_sec_splitH : ltac2:(CDefT.buildp (gd_tbl_AHeapMallocSSplit ()) "PQA,$26.PQB,$26.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(;.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$27.Ph,$28.PLB,(<.(1=.$2.$2.))PLF,(<.(1=.$2.$2.))Pn,$2.Plo,$2.Pd,$2.P,(29.VhAR,VSTKLO,R6.)P,(2:.VhAR,R7.R6.R5.R9.)P,(2;.VhAR,$>.R8.R9.)P,(2<.R;.R:.)P,(19.$4.R<.R6.(2=.&40.R2<.))P,(6.VSTKLO,R7.)P,(6.R8.(1:.(2=.&40.R2>.)+1000.))P,(6.(2=.&40.R2?.)(2>.(2?.R=.)))P,(30.$2.(31.(2=.&40.R30.)+10.)=)P,(20.$4.R11.)P,(30.(0.&40.)R30.(14.&40.$32.))P,(30.(0.&40.)R2;.(14.&40.R>.))P,(8.(6.=R?.)(7.R?.(?.+2.+1<.)))P,(6.(5.(33.R13.)(34.+2.R10.))(?.+2.+24.))P,(6.(5.(33.R14.)(34.+2.R11.))(?.+2.+20.))P,(35.$4.R17.VSTKLO,(36.(2?.R15.))(2=.&40.R31.)(2=.&40.R37.)R10.)P,(6.(5.(37.R16.)(5.R11.+3.))$38.)P,(30.$39.(3:.R14.)$3;.)P,A1.R3=.(17.$3<.)P,A1.R3=.(17.$3<.)P,Pcf,$3=.P,(3>.VhAR,VSTKLO,R3>.R3<.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1;.R1:.R19.R18.R17.R16.(2=.&40.R3=.)R1=.R1<.R1.)(3?.$4.R2.R41.)P,Pcf,$3=.P,(40.VhAR,VSTKLO,R3?.R3=.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1<.R1;.R1:.R19.R18.R17.(2=.&40.R3>.)R1>.R1=.R1.)(3?.$4.R2.R41.)(3?.$4.(41.(42.(43.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(14.&40.$44.)R1?.(45.(0.&40.))R1>.(46.$4.))R1=.)(47.R41.R40.))")
(* [comment removed for export] *).
  Proof.
    intros QA QB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB LF n lo d
      HOK HM0 HK0 HJ0 ST STKLO' SPL SPTOP SPA MI TP A0 NB BUD BUD32 CH0 HFR FP A0n B0n HA HB.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ CH0) as D0.
    (* [comment removed for export] *)
    dpose HOK as (EL & _ & _).
    dpose HM0 as ((AWF & HLB) & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GEMB).
    dpose AWF as ([WL WLS] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    set (L := h_L h) in *. set (T := l_T L) in *. set (CTX := l_ctx L) in *. set (SB := l_sb L) in *. set (PA := l_pa L) in *.
    set (SP := bv_unsigned sp) in *.
    assert (ESP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof WL as WL'. unfold wf_L in WL'. fold L in WL'.
    aceilb.
    (* [comment removed for export] *)
    assert (NB32 : 0 <= n < 2^32) by (clear - NB; lia).
    dpose (sec_sizes n NB32 FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    dpose (sec_req_facts n NB FP) as (_ & _ & _ & _ & MSB & MSAL).
    set (ms := sec_map_size n) in *.
    assert (EMS : map_size (needed2 n) = ms) by (subst ms; apply map_size_sec).
    assert (MS8 : ms mod 8 = 0).
    { pose proof (Z.div_mod ms 4096 ltac:(clear; lia)) as D4. rewrite MSAL, Z.add_0_r in D4. rewrite D4.
      replace (4096 * (ms / 4096)) with ((512 * (ms / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
    pose proof (Z.div_mod ms 8 ltac:(clear; lia)) as DMS8. rewrite MS8, Z.add_0_r in DMS8.
    (* [comment removed for export] *)
    ddestruct WL' as (SB16 & B6A & B6B & B6AL & B6LO & B6HI & SEHI & TOPAL & TOP23 & TOPHI & STKLOE & S0TOP & HTOPLO & HTOPHI & HTOPAL & STKLO16 & STKLOC & STKHI47 & STKHIAL
                      & FSAL & FSLO & FSHI & TAL & TLO & THI & CXLO & CXHI & CXLEN & CXAL & PAAL & PALO & PAHI & NB0AL & SS0AL & EXTRA).
    fold SB T CTX PA in SB16, TAL, TLO, THI, CXLO, CXHI, CXAL, PAAL, PALO, PAHI. unfold kHighMemBeg in *. unfold space_end, kSpaceSize in SEHI. fold SB in SEHI.
    pose proof (lowhigh_Pimg _ _ TLO) as TI. pose proof (lowhigh_Pband _ _ TLO) as TB. pose proof (lowhigh_Pband _ _ CXLO) as CXB. pose proof (lowhigh_big _ _ CXLO ltac:(clear; lia)) as CX63.
    pose proof (lowhigh_Pband _ _ PALO) as PB. pose proof (lowhigh_big _ _ PALO ltac:(clear; lia)) as PA63.
    set (TOP := l_top L) in *.
    assert (SBLO : 0x10007fff8000 + 0x8000 <= SB) by (pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DQ; clear - B6A B6LO SB16 DQ; lia).
    (* [comment removed for export] *)
    assert (SLO : l_stk_lo L <= lo) by (rewrite EL; exact STKLO').
    assert (LOIMG : ACEIL <= lo) by (clear - SLO STKLOC; lia).
    assert (TOP0 : 2^23 <= TOP) by exact TOP23.
    assert (TOP1 : TOP <= 2^47) by (clear - TOPHI STKHI47; lia).
    assert (TOP2 : SP + 16 <= 2^47) by (clear - SPTOP HTOPHI STKHI47; lia).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    assert (ACE47 : ACEIL <= 2^47) by (clear - STKLOC STKHI47 HTOPLO HTOPHI; lia).
    (* [comment removed for export] *)
    assert (TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_ctx h)) as [E|[X|X]].
      - exfalso. injection E as E1 E2. change (h_L h) with L in E2. clear - E2 CXLEN. lia.
      - left. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T CTX in X. clear - X CXLEN. lia.
      - right. unfold t_hi in X. cbn [t_lo t_len] in X. change (h_L h) with L in X. fold T CTX in X. clear - X CXLEN. lia. }
    assert (TP' : T + 4096 <= PA \/ PA + 0x800000 <= T).
    { destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_T h) eq_refl ltac:(right; left; reflexivity)) as [X|X];
        unfold t_hi, kPaHullLen in X; cbn [t_lo t_len fst snd] in X; change (h_L h) with L in X; fold T PA in X; [left| right]; clear - X; lia. }
    assert (CP' : CTX + 0x10000 <= PA \/ PA + 0x800000 <= CTX).
    { destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_ctx h) eq_refl ltac:(right; left; reflexivity)) as [X|X];
        unfold t_hi, kPaHullLen in X; cbn [t_lo t_len fst snd] in X; change (h_L h) with L in X; fold CTX PA in X; rewrite ?CXLEN in X; [left| right]; clear - X CXLEN; lia. }
    pose proof (HK_vwf AL h mo HK0) as VWF0. dpose VWF0 as (_ & _ & _ & HAP & _).
    destruct (HAP (l_b6 L, kPrimHullLen) (l_pa L, kPaHullLen) ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as [E|HPA]; [exfalso; injection E; unfold kPrimHullLen, kPaHullLen; clear; intros; lia|].
    cbn [fst snd] in HPA. fold PA in HPA. unfold kPrimHullLen, kPaHullLen in HPA.
    set (nb := d_nb (h_dep h)). set (bl := d_bl (h_dep h)).
    assert (BLKn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> In (node_tr (dblk nb k0)) (tr_of h)) by (intros k0 Hk0; apply tr_of_node; unfold dblk; apply nth_In; clear - Hk0; subst nb; lia).
    assert (BLKs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> In (store_tr (sblk bl j0)) (tr_of h)) by (intros j0 Hj0; apply tr_of_store; unfold sblk; apply nth_In; clear - Hj0; subst bl; lia).
    assert (APTn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> T + 4096 <= dblk nb k0 \/ dblk nb k0 + 2^20 <= T).
    { intros k0 Hk0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (BLKn k0 Hk0)) as [E|[X|X]]; [discriminate E| left| right]; unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (APTs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> T + 4096 <= sblk bl j0 \/ sblk bl j0 + 2^23 <= T).
    { intros j0 Hj0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (BLKs j0 Hj0)) as [E|[X|X]]; [discriminate E| left| right]; unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (APCn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> CTX + 0x10000 <= dblk nb k0 \/ dblk nb k0 + 2^20 <= CTX).
    { intros k0 Hk0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_ctx h) (BLKn k0 Hk0)) as [E|[X|X]]; [exfalso; injection E as E1 E2; change (h_L h) with L in E2; clear - E2 CXLEN; lia| left| right];
        unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold CTX in X; clear - X CXLEN; lia. }
    assert (APCs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> CTX + 0x10000 <= sblk bl j0 \/ sblk bl j0 + 2^23 <= CTX).
    { intros j0 Hj0. destruct (tr_apart AL h mo _ _ HK0 (tr_of_ctx h) (BLKs j0 Hj0)) as [E|[X|X]]; [discriminate E| left| right];
        unfold t_hi in X; cbn [t_lo t_len node_tr store_tr] in X; change (h_L h) with L in X; fold CTX in X; clear - X CXLEN; lia. }
    (* [comment removed for export] *)
    assert (APPn : forall k0, 0 <= k0 < Z.of_nat (length nb) -> PA + 0x800000 <= dblk nb k0 \/ dblk nb k0 + 2^20 <= PA).
    { intros k0 Hk0. destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (BLKn k0 Hk0) eq_refl ltac:(right; left; reflexivity)) as [X|X];
        unfold t_hi, node_tr, kPaHullLen in X; cbn [t_lo t_len fst snd] in X; change (h_L h) with L in X; fold PA in X; [right| left]; clear - X; lia. }
    assert (APPs : forall j0, 0 <= j0 < Z.of_nat (length bl) -> PA + 0x800000 <= sblk bl j0 \/ sblk bl j0 + 2^23 <= PA).
    { intros j0 Hj0. destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (BLKs j0 Hj0) eq_refl ltac:(right; left; reflexivity)) as [X|X];
        unfold t_hi, store_tr, kPaHullLen in X; cbn [t_lo t_len fst snd] in X; change (h_L h) with L in X; fold PA in X; [right| left]; clear - X; lia. }
    (* [comment removed for export] *)
    pose proof WS as WSC. ddestruct WS as (WS1 & WS2 & WS3 & WS4 & WS5 & WS6 & WS7 & WS8).
    set (cks := s_chunks (h_sec h)) in *. set (nres := s_nres (h_sec h)) in *. set (ncks := Z.of_nat (length cks)) in *.
    unfold kPtrArrayChunks in WS2.
    set (r := r0h h).
    assert (ER : nres = 0x4000 * r).
    { subst r. unfold r0h. change (h_pa_committed h) with (8 * nres) || rewrite WS5. unfold kPaSlice.
      pose proof (Z.div_mod nres 16384 ltac:(clear; lia)) as DQ. rewrite WS2, Z.add_0_r in DQ. rewrite DQ at 2.
      replace (8 * (16384 * (nres / 16384))) with ((nres / 16384) * 131072) by (clear; lia). rewrite Z_div_mult by (clear; lia). exact DQ. }
    assert (HR0 : 0 <= r) by (clear - ER WS3; lia).
    dpose WX as (_ & _ & _ & WX4 & WX5). fold cks nres in WX4, WX5. fold ncks in WX4. unfold kPtrArrayChunks in WX5.
    assert (ROOM : 0x4000 * r + 0x4000 <= 2^20) by (clear - ER WX5 BUD NLO NB; lia).
    assert (ROOMS : h_pa_committed h + kPaSlice <= kPaHullLen) by (rewrite WS5; fold nres; unfold kPaSlice, kPaHullLen; clear - ER ROOM HR0; lia).
    assert (CSPAh : crange (vcs AL (vst_of h)) (l_pa (h_L h)) (h_pa_committed h)).
    { change (l_pa (h_L h)) with PA. intros x Hx.
      set (j := (x - PA) / kPaSlice).
      pose proof (Z.div_mod (x - PA) kPaSlice ltac:(unfold kPaSlice; clear; lia)) as DJ. pose proof (Z.mod_pos_bound (x - PA) kPaSlice ltac:(unfold kPaSlice; clear; lia)) as MJ. fold j in DJ.
      destruct (bwf_pa h (awf'_bwf h AWF)) as [_ PAMOD]. pose proof (Z.div_mod (h_pa_committed h) kPaSlice ltac:(unfold kPaSlice; clear; lia)) as DP. rewrite PAMOD, Z.add_0_r in DP.
      assert (HJ : 0 <= j < h_pa_committed h / kPaSlice).
      { subst j. unfold kPaSlice in *. split; [apply Z.div_pos; clear - Hx; lia| apply Z.div_lt_upper_bound; [clear; lia|]]. clear - Hx DP. lia. }
      apply (vcs_of_tr AL h (pa_tr L j)); [| reflexivity|].
      - unfold tr_of. rewrite !in_app_iff. do 5 right. left. apply in_map. apply in_zseq. exact HJ.
      - unfold pa_tr, t_hi. cbn [t_lo t_len]. fold PA. unfold kPaSlice in *. clear - DJ MJ Hx. lia. }
    pose proof (awf'_bwf h AWF) as BWF.
    assert (HVM : h_havol h <= AVOL_MAX) by (unfold AVOL_MAX; clear - BUD NB; lia).
    assert (HV32 : h_havol h <= 2^32) by (clear - BUD32 NB; lia).
    pose proof (wf_depot'_bounds h WD ltac:(clear - HFR D0; lia)) as [DNB DTF].
    (* [comment removed for export] *)
    assert (EU : U0h h = PA + 0x20000 * r) by (unfold U0h; change (l_pa (h_L h)) with PA; rewrite WS5; fold nres; clear - ER; lia).
    assert (A_LEDGER : forall sc r' mo', Gph h sc r' -> KsF h n mo sc r' nb bl mo' ->
              region_free (vm_reserved (m_vmmaps mo')) (Z_to_bv 64 (PA + 0x20000 * r')) (Z_to_bv 64 0x20000) = true
              /\ (map_contains (vm_maps (m_vmmaps mo')) (Z_to_bv 64 (PA + 0x20000 * r')) (Z_to_bv 64 0x20000) = true
                  \/ region_free (vm_reserved (m_vmmaps mo') ++ vm_maps (m_vmmaps mo')) (Z_to_bv 64 (PA + 0x20000 * r')) (Z_to_bv 64 0x20000) = true)).
    { intros sc r' mo' G K. pose proof (proj1 G) as Er. subst r'. change (r0h h) with r in G, K |- *. rewrite <- EU. exact (MS_LEDGER_P h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r mo' G K). }
    assert (A_TPC : forall sc r' mo', Gph h sc r' -> KsF h n mo sc r' nb bl mo' ->
              map_contains (vm_maps (m_vmmaps mo')) (Z_to_bv 64 (PA + 0x20000 * r')) (Z_to_bv 64 0x20000) = true ->
              KsF h n mo sc (r' + 1) nb bl (fixrw_commit 0x32 (PA + 0x20000 * r') 0x20000 mo') /\ crange (CSsh h n sc (r' + 1) nb bl) (PA + 0x20000 * r') 0x20000).
    { intros sc r' mo' G K. pose proof (proj1 G) as Er. subst r'. change (r0h h) with r in G, K |- *. rewrite <- EU. exact (MS_TP_commit h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r mo' G K). }
    assert (A_TPF : forall sc r' mo', Gph h sc r' -> KsF h n mo sc r' nb bl mo' ->
              region_free (vm_reserved (m_vmmaps mo') ++ vm_maps (m_vmmaps mo')) (Z_to_bv 64 (PA + 0x20000 * r')) (Z_to_bv 64 0x20000) = true ->
              KsF h n mo sc (r' + 1) nb bl (fixrw_fresh 0x32 (PA + 0x20000 * r') 0x20000 mo') /\ crange (CSsh h n sc (r' + 1) nb bl) (PA + 0x20000 * r') 0x20000).
    { intros sc r' mo' G K. pose proof (proj1 G) as Er. subst r'. change (r0h h) with r in G, K |- *. rewrite <- EU. exact (MS_TP_fresh h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r mo' G K). }
    assert (A_ROOMP : forall sc r' mo', Gph h sc r' -> KsF h n mo sc r' nb bl mo' -> fixrw_grantable 0x32 (PA + 0x20000 * r') 0x20000 mo').
    { intros sc r' mo' G K. pose proof (proj1 G) as Er. subst r'. change (r0h h) with r in G, K |- *. rewrite <- EU. exact (MS_ROOM_P h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r mo' G K). }
    assert (A_SCARP : forall sc r', Gph h sc r' -> hole_site AL (CSsh h n sc r' nb bl) (KsF h n mo sc r' nb bl) (PA + 0x20000 * r') 0x20000).
    { intros sc r' G. pose proof (proj1 G) as Er. subst r'. change (r0h h) with r in G |- *. rewrite <- EU. exact (MS_SCAR_P h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r G). }
    assert (A_SECAP : forall sc r' nb' bl' mo' p, KsF h n mo sc r' nb' bl' mo' -> In p sc -> fst p + snd p <= SB \/ SB + 2^37 + 4096 <= fst p).
    { intros sc r' nb' bl' mo' p K Hp. destruct (MS_SEC_APART h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r' nb' bl' mo' p K Hp) as [X|X]; change (h_L h) with L in X; unfold kPrimHullLen in X; [left| right]; clear - X B6A SEHI; lia. }
    assert (A_Gl : Glh h n [] r (map_size (needed2 n))) by (unfold Glh, AInstSec.Gl; split; [reflexivity| split; [reflexivity| rewrite EMS; reflexivity]]).
    assert (CSUF : forall y, vcs AL (vst_of h) y -> CSsh h n [] r nb bl y) by (intros y Hy; unfold CSsh, AInstSec.CSs, AInstSec.CSb; left; left; exact Hy).
    assert (CRI : forall sc r' nb' bl' A k0, crange (vcs AL (vst_of h)) A k0 -> crange (CSsh h n sc r' nb' bl') A k0) by (intros sc r' nb' bl' A k0 H; exact (MS_CSlift h n mo HK0 BWF HVM NB FP ROOMS CSPAh sc r' nb' bl' A k0 H)).
    (* [comment removed for export] *)
    dpose GRO as (MS8' & AS & PS & FS & DST & THRS & LGS & GPG & PGSZ & GCF & DEC & LIM & I40 & I56 & SBC & RIC & PPART & MH8 & QMX & MRN & TIDC & TH & THR & TSW & TFS & F88 & UARG & UARC & RSMR & SMS & F5W & T48 & MICF & MICR & B12S).
    fold L T CTX SB TOP PA in MS8', AS, SBC, TIDC, TH, THR, TSW, TFS, THRS, LGS.
    dpose FS as (_ & _ & _ & _ & GOTFL & _).
    dpose GRW as ((e0 & ERR) & (oomb & OOM) & FBM).
    ddestruct RSMR as (can & dd & madv & RS).
    (* [comment removed for export] *)
    assert (MWS : mwc_statics m).
    { dpose RS as (_ & _ & _ & _ & _ & _ & RS7 & _ & _ & RS10 & RS11 & _).
      exact (conj GPG (conj PGSZ (conj GCF (conj DEC (conj LIM (conj RS7 (conj RS10 RS11))))))). }
    dpose GT as (UNW & (ds & PCL) & (jq0 & jq1 & QT) & (xs & bs & STX & LXS & STB & HL)). fold L T in UNW, PCL, STX, STB, QT.
    (* [comment removed for export] *)
    destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 [|x13 [|x14 [|x15 [|x16 xs17]]]]]]]]]]]]]]]]]; try (cbn in LXS; discriminate).
    pose proof (u64arr_cells8' m _ _ STX) as STX'. cbn [map] in STX'.
    change ([C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9; C8 x10; C8 x11; C8 x12; C8 x13; C8 x14; C8 x15])
      with ([C8 x0; C8 x1] ++ [C8 x2; C8 x3; C8 x4] ++ [C8 x5; C8 x6; C8 x7; C8 x8; C8 x9; C8 x10] ++ [C8 x11; C8 x12] ++ [C8 x13; C8 x14] ++ [C8 x15]) in STX'.
    apply rw_cells_app in STX' as [_ STX']. apply rw_cells_app in STX' as [STH STX']. apply rw_cells_app in STX' as [_ STX']. apply rw_cells_app in STX' as [TJ STX']. apply rw_cells_app in STX' as [_ ST4].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length map app] in STH, TJ, ST4.
    match type of STH with rw_cells _ _ ?a _ => replace a with (T + 2800) in STH by (clear; lia) end.
    match type of TJ with rw_cells _ _ ?a _ => replace a with (T + 2872) in TJ by (clear; lia) end.
    match type of ST4 with rw_cells _ _ ?a _ => replace a with (T + 2904) in ST4 by (clear; lia) end.
    (* [comment removed for export] *)
    pose proof GS as GS0. unfold hm_sec in GS0. cbn zeta in GS0. fold L PA cks nres in GS0. fold ncks in GS0.
    ddestruct GS0 as (SC1 & (srt & SC2) & (st & SC3 & LST) & (bsl & SC4 & LBSL) & SC5 & (g0 & g1 & SC6) & HPS & (rest & HREST & PAL) & HD).
    set (ps := map (fun sh => Z_to_bv 64 (s_map_beg sh)) cks) in *.
    assert (LPS : Z.of_nat (length ps) = ncks) by (subst ps ncks; rewrite length_map; reflexivity).
    assert (LREST : Z.of_nat (length rest) = 0x4000 * r - ncks) by (rewrite WS5 in PAL; fold nres in PAL; clear - PAL ER; lia).
    assert (HNC : 0 <= ncks <= 0x4000 * r) by (clear - WS1 ER; subst ncks; lia).
    assert (LI : limg m (0x4000 * r) ncks srt 0).
    { split; [| split; [exists st; exact (conj SC3 LST)| split; [exists bsl; exact (conj SC4 LBSL)| split; [exact SC5| dexists g0, g1; exact SC6]]]].
      rewrite <- ER. apply (proj2 (rw_cells_app asegs m (A_INSTANCE + 112) [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 ncks)] [C1 srt])).
      split; [exact SC1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (A_INSTANCE + 112 + 16) with (A_INSTANCE + 128) by (clear; lia). exact SC2. }
    dpose GM as (SHLO & SHHI & STKW & TW & CTXW & FSW). fold L in SHLO, SHHI, STKW, TW, CTXW, FSW.
    assert (SHW : shadow_wr m).
    { split; [| exact SHHI]. exact (wr_at_sub m 0x7fff7000 0x10000000 0x7fff8000 0xffff000 SHLO ltac:(clear; lia) ltac:(clear; lia)). }   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (STT : stk asegs m SP TOP).
    { destruct (Z.le_gt_cases SP TOP) as [LEt|GTt].
      - apply wr_at_high_stk; [| clear - LOIMG SPL; lia| exact LEt].
        exact (wr_at_sub m (l_stk_lo L) _ SP (TOP - SP) STKW ltac:(clear - SLO SPL; lia) ltac:(clear - LEt TOPHI; lia)).
      - split; [clear - LOIMG SPL; lia|]. split; [clear - TOP1; lia|]. intros a Ha. exfalso. clear - Ha GTt. lia. }
    (* [comment removed for export] *)
    assert (GSB' : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ SB + 2^37 + 4096 <= ACEIL).
    { split; [clear - SBLO; lia|]. split; [| clear - SEHI B6HI; lia].
      pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DQ. rewrite SB16, Z.add_0_r in DQ. rewrite DQ.
      replace (2^16 * (SB / 2^16)) with ((16 * (SB / 2^16)) * 4096) by (clear; lia). apply Z_mod_mult. }
    assert (GT' : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0) by (split; [exact (conj TI TB)| split; [exact THI| exact TAL]]).
    assert (GCTX' : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL) by (split; [exact (conj CX63 CXB)| clear - CXHI CXLEN; lia]).
    assert (GPA' : (0x65f000 <= PA /\ Pband PA 0x800000) /\ PA + 0x800000 <= ACEIL /\ PA mod 4096 = 0) by (split; [exact (conj PA63 PB)| split; [exact PAHI| exact PAAL]]).
    assert (GSEP' : (T + 4096 <= SB \/ SB + 2^37 + 4096 <= T) /\ (CTX + 0x10000 <= T \/ T + 4096 <= CTX) /\ (CTX + 0x10000 <= SB \/ SB + 2^37 + 4096 <= CTX)
                    /\ (T + 4096 <= PA \/ PA + 0x800000 <= T) /\ (CTX + 0x10000 <= PA \/ PA + 0x800000 <= CTX)).
    { destruct (lit_apart_hull AL h mo _ (l_b6 L, kPrimHullLen) HK0 (tr_of_T h) eq_refl ltac:(left; reflexivity)) as [XT|XT];
      destruct (lit_apart_hull AL h mo _ (l_b6 L, kPrimHullLen) HK0 (tr_of_ctx h) eq_refl ltac:(left; reflexivity)) as [XC|XC];
      unfold t_hi, kPrimHullLen in XT, XC; cbn [t_lo t_len fst snd] in XT, XC; change (h_L h) with L in XT, XC; fold T in XT; fold CTX in XC; rewrite ?CXLEN in XC;
      (split; [clear - XT B6A SEHI; lia| split; [clear - TC; lia| split; [clear - XC B6A SEHI; lia| exact (conj TP' CP')]]]). }
    (* [comment removed for export] *)
    subst a0. rewrite ESP. rewrite TP.
    eapply (evtA_srzJ_KJ AL (CSsh h n [] r nb bl) (KsF h n mo [] r nb bl) _ (t_alt2 QA QB) _ mo
              (MS_KL h n mo HK0 BWF HVM NB FP ROOMS CSPAh [] r nb bl) (MS_entry h n mo HK0 BWF HVM NB FP ROOMS CSPAh)); [exact HJ0| |].
    { apply (wrap_step AL IMG ALWF). exact (MS_CSOK h n mo HK0 BWF HVM NB FP ROOMS CSPAh [] r nb bl). }
    cbn beta. intros ms1 mo1 -> K1 MM1 HJ1.
    eapply (malloc_sec_split AL IMG ALWF ASB (CSsh h n) (KsF h n mo)) with
        (nb0 := nb) (bl0 := bl) (SP := SP) (lo := lo) (T := T) (CTX := CTX) (TOP := TOP) (TID := 0) (SB := SB) (PA := PA)
        (LO := STKLO) (TOPU := l_stk_hi L) (d := d) (Gl := Glh h n) (Gp := Gph h) (Gn := Gnh h) (Gs := Gsh h)
        (can := can) (dd := dd) (madv := madv) (sc := []) (r := r)
        (N := d_n (h_dep h)) (tf := s_total (h_dep h)) (ncks := ncks) (ps := ps) (rest := rest)
        (j0 := x2) (jj1 := x3) (jj2 := x4) (j4 := x15) (js1 := x11) (js2 := x12) (e0 := e0) (oomb := oomb) (srt := srt).
    all: let mg L := exact (L h n mo HK0 BWF HVM NB FP ROOMS CSPAh) in
           lazymatch goal with
           | |- forall cf, _ -> srealizesJ _ _ _ => idtac
           | |- ?T [] => first [exact A0n | exact B0n]
           | |- forall _, _ => first [ first [ exact (MS_ROOM_l h n mo HK0 BWF HVM NB FP HV32) | mg MS_CSOK | mg MS_KL | mg MS_noshadow | mg MS_CSmono_l | mg MS_CSmono_p | mg MS_CSmono_n | mg MS_CSmono_s | mg MS_CSPA
                                       | mg MS_apart_l | mg MS_T_large | exact A_LEDGER | exact A_TPC | exact A_TPF | exact A_ROOMP | exact A_SCARP | exact A_SECAP
                                       | mg MS_apart | mg MS_T_node | mg MS_T_store | mg MS_ROOM_n | mg MS_ROOM_s | mg MS_Gp | mg MS_Gn | mg MS_Gs | mg MS_Gsx
                                       | exact (MS_PZ h n mo HK0 BWF HVM NB FP ROOMS CSPAh can dd madv) | exact MOD_DIE
                                       | exact APTn | exact APTs | exact APCn | exact APCs | exact APPn | exact APPs
                                       | (intros; apply CRI; first [apply crange_T | rewrite <- CXLEN; apply crange_ctx])
                                       | (intros; apply (MS_Gn h n mo HK0 BWF HVM NB FP ROOMS CSPAh)) | (intros; apply (MS_Gs h n mo HK0 BWF HVM NB FP ROOMS CSPAh))
                                       | (intros; apply (MS_Gsx h n mo HK0 BWF HVM NB FP ROOMS CSPAh))
                                       | match goal with |- ?G => fail 99 "UNSOLVED-forall" G end ]
               | match goal with |- ?G => fail 99 "UNSOLVED-BR1" G end ]
           | |- KsF _ _ _ _ _ _ _ _ => first [ exact K1
               | match goal with |- ?G => fail 99 "UNSOLVED-BR2" G end ]
           | |- J _ _ => first [ (cbn [ms_mem MS MSsvc] in HJ1; exact HJ1)
               | match goal with |- ?G => fail 99 "UNSOLVED-BR2J" G end ]
           | |- uwc _ _ _ _ _ _ _ => first [ first [exact CH0 | replace (l_stk_lo L) with STKLO by (symmetry; exact EL); exact CH0]
               | match goal with |- ?G => fail 99 "UNSOLVED-BR3" G end ]
           | |- depot_inv _ _ _ _ _ => first [ exact GD
               | match goal with |- ?G => fail 99 "UNSOLVED-BR4" G end ]
           | |- depot_cs _ _ _ => first [ split; [intros k0 Hk0; apply CRI; apply crange_node; exact Hk0| intros jj Hjj; apply CRI; apply crange_store; exact Hjj]
               | match goal with |- ?G => fail 99 "UNSOLVED-BR5" G end ]
           | |- Glh _ _ _ _ _ => first [ exact A_Gl
               | match goal with |- ?G => fail 99 "UNSOLVED-BR6" G end ]
           | |- limg _ _ _ _ _ => first [ exact LI
               | match goal with |- ?G => fail 99 "UNSOLVED-BR7" G end ]
           | |- shadow_wr _ => first [ exact SHW
               | match goal with |- ?G => fail 99 "UNSOLVED-BR8" G end ]
           | |- crange _ _ _ => first [ apply CRI;
               first [ apply crange_T
                     | rewrite <- CXLEN; apply crange_ctx
                     | apply crange_stack; change (h_L h) with L; [| clear - TOPHI; lia]; unfold stk64; pose proof (Z.mod_pos_bound (l_stk_lo L) 64 ltac:(clear; lia)); clear - H SLO SPL; lia
                     | apply crange_stack; change (h_L h) with L; [| clear - TOPHI SPTOP HTOPHI SPL; lia]; unfold stk64; pose proof (Z.mod_pos_bound (l_stk_lo L) 64 ltac:(clear; lia)); clear - H SLO; lia ]
               | match goal with |- ?G => fail 99 "UNSOLVED-BR9" G end ]
           | |- _ => idtac
           end.
    all: lazymatch goal with |- forall cf, _ -> srealizesJ _ _ _ => idtac | |- _ => first [ sassumption | cassumption | exact MS8' | exact AS | exact PS | exact FS | exact DST | exact RS | exact LGS | exact THRS | exact MWS | exact GOTFL | exact PPART | exact SBC
                 | exact OOM | exact MRN | exact ERR | exact THR | exact TSW | exact UNW | exact TH | exact TIDC
                 | exact STH | exact ST4 | exact TJ | exact HR0 | exact HNC | exact ROOM | exact LPS | exact LREST | exact HPS | exact HREST
                 | exact DTF | exact DNB | exact STT | exact ST | exact MI
                 | exact FP | exact LOIMG | exact SPL | exact SPA | exact TOP0 | exact TOP1 | exact TOP2
                 | exact GSB' | exact GT' | exact GCTX' | exact GPA' | exact GSEP'
                 | (clear - NB; lia) | (clear; lia) | (clear - STKLO' SPL; lia) | (clear - TOPHI STKHI47; lia)
                 | match goal with |- ?G => fail 99 "UNSOLVED" G end ] end.
    (* [comment removed for export] *)
    all: intros cf PO.
    { (* [comment removed for export] *)
    ddestruct PO as (ms1' & mo' & res & sc' & r' & nb' & bl' & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & PO).
    cbn zeta in PO.
    ddestruct PO as (-> & -> & KF' & HJ' & WM' & MI' & ST' & CSM & UNW' & NUL).
    pose proof GD as DI. unfold hm_depot in DI. fold nb bl in DI.
    dpose DI as (_ & _ & (_ & NBWF & _) & _ & _ & _ & _ & (_ & BLWF & _) & _).
    assert (NBLO : forall b, In b nb -> 0x65f000 <= b /\ b + 2^20 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) NBWF b Hb) as X; cbn beta in X; clear - X; lia).
    assert (BLLO : forall b, In b bl -> 0x65f000 <= b /\ b + 2^23 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) BLWF b Hb) as X; cbn beta in X; clear - X; lia).
    assert (OBn : forall t b A k0, In t (tr_of h) -> In b nb -> t <> node_tr b -> t_lo t <= A -> A + k0 <= t_hi t -> A + k0 <= b \/ b + 2^20 <= A).
    { intros t b A k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (node_tr b) HK0 Ht (tr_of_node h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, node_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (OBs : forall t b A k0, In t (tr_of h) -> In b bl -> t <> store_tr b -> t_lo t <= A -> A + k0 <= t_hi t -> A + k0 <= b \/ b + 2^23 <= A).
    { intros t b A k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (store_tr b) HK0 Ht (tr_of_store h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, store_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (BNDn : forall b, In b nb -> b + 2^20 <= 0x7fff7000 \/ 0x10007fff8000 <= b).
    { intros b Hb. pose proof (tr_wf AL h mo _ HK0 (tr_of_node h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, node_tr in W6. cbn [t_lo t_len] in W6. exact W6. }
    assert (BNDs : forall b, In b bl -> b + 2^23 <= 0x7fff7000 \/ 0x10007fff8000 <= b).
    { intros b Hb. pose proof (tr_wf AL h mo _ HK0 (tr_of_store h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, store_tr in W6. cbn [t_lo t_len] in W6. exact W6. }
    (* [comment removed for export] *)
    assert (NTD : TR T 4096 KEager true true <> TR (l_dtls L) 4096 KEager true true) by (change T with (l_T (h_L h)); change L with (h_L h); exact (T_ne_dtls AL h (HK_vwf AL h mo HK0))).
    assert (TDT : T + 4096 <= l_dtls L \/ l_dtls L + 4096 <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_dtls h)) as [E|[X|X]]; [exact (False_ind _ (NTD E))| left| right]; unfold t_hi in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (TFA : T + 4096 <= l_fs L \/ l_fs L + kFakeBytes <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_fs h)) as [E|[X|X]]; [exfalso; injection E; unfold kFakeBytes; clear; intros; lia| left| right]; unfold t_hi in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    pose proof (tr_wf AL h mo _ HK0 (tr_of_dtls h)) as (DT0 & _ & DTHI & _ & _ & DTI & _). unfold t_hi in DTHI, DTI. cbn [t_lo t_len] in DT0, DTHI, DTI. change (h_L h) with L in DT0, DTHI, DTI. rewrite IMH, IMLO in DTI.
    assert (HULLB : l_b6 L <= SB /\ SB + 2^37 + 4096 <= l_b6 L + kPrimHullLen /\ l_b6 L + kPrimHullLen <= ACEIL) by (unfold kPrimHullLen in *; clear - B6A SEHI B6HI; lia).
    assert (TSEC : forall sh, In sh cks -> T + 4096 <= s_map_beg sh \/ s_map_beg sh + s_map_size sh <= T).
    { intros sh Hsh. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _).
      destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_sec h sh Hsh)) as [E|[X|X]]; [exfalso; injection E; clear - BIG; intros; lia| left| right]; unfold t_hi, sec_tr in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    (* [comment removed for export] *)
    assert (SLOT0 : forall k', In k' (h_chunks h) ->
              ext_lo k' <= ck_ab k' /\ ck_ab k' + ck_rz k' = ck_user k' /\ ck_user k' + Z.max (ck_n k') 8 <= ext_hi k' /\ 16 <= ck_rz k'
              /\ 0x65f000 <= ext_lo k' /\ ext_hi k' <= ACEIL /\ (ext_hi k' <= 0x7fff7000 \/ 0x10007fff8000 <= ext_lo k')
              /\ (ext_hi k' <= T \/ T + 4096 <= ext_lo k')
              /\ ((l_b6 L <= ext_lo k' /\ ext_hi k' <= l_b6 L + kPrimHullLen /\ exists c', 1 <= c' <= 31 /\ region_beg L c' <= ext_lo k' /\ ext_hi k' <= region_beg L c' + r_mapped_user (h_reg h c'))
                  \/ (exists sh, In sh cks /\ ext_lo k' = s_map_beg sh /\ ext_hi k' = s_map_beg sh + s_map_size sh))).
    { dpose WK as (WKF & WKND & WKSEC). intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX).
      ddestruct (chunk_ext h k' AWF Hk') as (N0 & E1 & E2 & E3 & E4 & [E5 E5'] & E6 & ARMk). dpose (chunk_geom h k' AWF Hk') as (RZ16 & _ & _).
      assert (US8 : ck_user k' + Z.max (ck_n k') 8 <= ext_hi k').
      { unfold ext_hi, ck_user, ck_rz, ck_end, ck_map_beg. pose proof (rz_size_bound (ck_n k')) as RZ'. destruct (ck_prim k') eqn:PR.
        + ddestruct WCX as (WCLS & WC30 & _). rewrite WCLS. pose proof (needed_le_class (ck_n k') ltac:(clear - WN; lia) ltac:(rewrite <- WP; reflexivity)) as NC.
          unfold needed, rounded, round_up in NC. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          clear - RZ' NC H H0 WN. lia.
        + unfold ck_map_size, sec_map_size. pose proof (round_up_spec (needed2 (ck_n k')) 4096 ltac:(clear; lia)) as [RU _].
          unfold needed2, needed, rounded, round_up in RU |- *. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          destruct (from_primary (ck_n k')); clear - RZ' RU H H0 WN; lia. }
      split; [unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia|]. split; [reflexivity|]. split; [exact US8|]. split; [exact RZ16|].
      split; [exact E5|]. split; [exact E6|]. split; [unfold kHighMemBeg in E5'; exact E5'|].
      destruct ARMk as [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & Q1 & Q2)].
      - change (h_L h) with L in R1, R2. pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear - C30; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _ & _ & MULIM' & _). unfold kUserLimit in MULIM'.
        assert (RBLO' : SB <= region_beg L (ck_cls k')) by (unfold region_beg, kRegionSize; fold SB; clear - C30; nia).
        assert (RBHI' : region_beg L (ck_cls k') + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - C30; nia).
        split; [clear - R1 R2 AUMU' MULIM' RBLO' RBHI' GSEP'; lia|]. left. split; [clear - R1 RBLO' HULLB; lia|]. split; [clear - R2 AUMU' MULIM' RBHI' HULLB; lia|].
        exists (ck_cls k'). split; [clear - C30; lia|]. split; [exact R1| clear - R2 AUMU'; lia].
      - fold cks in Hsh. split; [pose proof (TSEC sh Hsh) as X; clear - X Q1 Q2; lia|]. right. exists sh. split; [exact Hsh| exact (conj Q1 Q2)]. }
    unfold kPrimHullLen in HULLB, SLOT0.
      ddestruct NUL as (Eres & Esc & Er' & Enb & Ebl & MU & OOM' & ERR').
      subst res sc' r' nb' bl'.
      ddestruct (MS_exit h n mo HK0 BWF HVM NB FP ROOMS CSPAh [] r nb bl mo' h KF') as (sn & sb & Esn & Esb & _ & _ & _ & _ & _ & FR' & EXIT).
      assert (sn = []) as -> by (clear - Esn; symmetry in Esn; rewrite <- (app_nil_r nb) in Esn at 1; apply app_inv_head in Esn; exact Esn).
      assert (sb = []) as -> by (clear - Esb; symmetry in Esb; rewrite <- (app_nil_r bl) in Esb at 1; apply app_inv_head in Esb; exact Esb).
      assert (RSEC : R_sec h n [] r [] [] h).
      { unfold R_sec. rewrite !app_nil_r. change (r0h h) with r. repeat split; try reflexivity. clear; lia. }
      destruct (EXIT RSEC) as [HK' CSE].
      (* [comment removed for export] *)
      assert (KEEPN : forall x : word, let y := bv_unsigned x in
                ~ (lo <= y < SP) -> ~ (T + 3168 <= y < T + 3169) -> ~ (A_OOM_CELL <= y < A_OOM_CELL + 1) -> ~ (A_ERRNO <= y < A_ERRNO + 4) -> m' x = m x).
      { intros x. cbn zeta. intros Q1 Q2 Q3 Q4. apply MU. cbn [outside]. repeat split; assumption. }
      assert (KIMGN : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 -> ~ in_rangesZ nzoneN (bv_unsigned x) -> m' x = m x).
      { intros x Hx Hz. unfold nzoneN in Hz. cbn [in_rangesZ] in Hz. unfold A_OOM_CELL, A_ERRNO in *. apply KEEPN; [clear - Hx LOIMG B6LO B6HI; lia| clear - Hx TI; lia| clear - Hz; lia| clear - Hz; lia]. }
      assert (KISH : forall x : word, 0x7fffa000 <= bv_unsigned x < 0x800c3e00 -> m' x = m x).
      { intros x Hx. unfold A_OOM_CELL, A_ERRNO in *. apply KEEPN; [clear - Hx LOIMG B6LO B6HI; lia| clear - Hx TB; lia| clear - Hx; lia| clear - Hx; lia]. }
      assert (IK : img_keep m m').
      { split; [| exact KISH]. intros x Hx Hz. apply KIMGN; [exact Hx|]. unfold awz, nzoneN, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_OOM_CELL, A_ERRNO in *. cbn [in_rangesZ] in Hz |- *. clear - Hz. lia. }
      assert (KLO : forall A k0, 0 <= A -> (A + k0 <= 0x10000 \/ 0x65f000 <= A) -> A + k0 <= ACEIL -> (A + k0 <= T + 3168 \/ T + 3169 <= A) -> kept m m' A k0).
      { intros A k0 A0 AI ACE' AT x Hx. unfold A_OOM_CELL, A_ERRNO in *. apply KEEPN; [clear - Hx ACE' LOIMG; lia| clear - Hx AT; lia| clear - Hx AI; lia| clear - Hx AI; lia]. }
      assert (LOWI : forall A k0, 0x10000 <= A -> A + k0 <= 0x65f000 -> (A + k0 <= A_OOM_CELL \/ A_OOM_CELL + 1 <= A) -> (A + k0 <= A_ERRNO \/ A_ERRNO + 4 <= A) -> kept m m' A k0).
      { intros A k0 H1 H2 H3 H4 x Hx. apply KIMGN; [clear - H1 H2 Hx; lia|]. unfold nzoneN. cbn [in_rangesZ]. clear - H3 H4 Hx. lia. }
      (* [comment removed for export] *)
      assert (KTP : forall A k0, T <= A -> A + k0 <= T + 3168 -> kept m m' A k0) by (intros A k0 A1 A2; apply KLO; [clear - A1 TI; lia| clear - A1 A2 TI; lia| clear - A2 THI; lia| left; exact A2]).
      assert (KHB : forall A k0, SB <= A -> A + k0 <= SB + 2^37 + 4096 -> kept m m' A k0) by (intros A k0 A1 A2; apply KLO; [clear - A1 SBLO; lia| right; clear - A1 SBLO; lia| clear - A2 HULLB; lia| clear - A1 A2 GSEP'; lia]).
      assert (KSB : forall B j, 0x800c3e00 <= B -> B + j <= 0x10007fff8000 -> kept m m' B j) by (intros B j B1 B2; apply KLO; [clear - B1; lia| right; clear - B1; lia| clear - B2 B6LO B6HI; lia| clear - B1 B2 TB; lia]).
      assert (KSL : forall k' A k0, In k' (h_chunks h) -> ext_lo k' <= A -> A + k0 <= ext_hi k' -> kept m m' A k0).
      { intros k' A k0 Hk' A1 A2. dpose (SLOT0 k' Hk') as (_ & _ & _ & _ & S5 & S6 & _ & S8 & _). apply KLO; [clear - A1 S5; lia| right; clear - A1 S5; lia| clear - A2 S6; lia| clear - A1 A2 S8; lia]. }
      assert (KSHS : forall A k0, 0x65f000 <= A -> A + k0 <= 2^47 -> 0 <= k0 -> A mod 8 = 0 -> kept m m' (shad A) ((k0 + 7) / 8)).
      { intros A k0 A63 ACE' K0 A8. unfold shad. pose proof (Z.div_mod A 8 ltac:(clear; lia)) as DA. rewrite A8, Z.add_0_r in DA.
        pose proof (Z.div_mod (k0 + 7) 8 ltac:(clear; lia)) as DK. pose proof (Z.mod_pos_bound (k0 + 7) 8 ltac:(clear; lia)) as MK.
        apply KSB; [clear - A63 DA; lia| clear - ACE' DA DK MK K0; lia]. }
      assert (KSH1 : forall c, 0x65f000 <= c -> c < 2^47 -> kept m m' (shad c) 1).
      { intros c C1 C2. unfold shad. pose proof (Z.div_mod c 8 ltac:(clear; lia)) as DC. pose proof (Z.mod_pos_bound c 8 ltac:(clear; lia)) as MC.
        apply KSB; [clear - C1 DC MC; lia| clear - C2 DC MC; lia]. }
      (* [comment removed for export] *)
      apply HA. unfold mallocH_postN.
      dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m', mo', h.
      split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact WM'|].
      split; [exact HK'|]. split; [exact HJ'|]. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - NB; lia|]. split; [clear - D0; lia|].
      split. { intros x Hx. apply (proj1 (CSE x)). apply CSM. apply CSUF. exact Hx. }
      split. { (* [comment removed for export] *)
        apply (presA_intro STKLO h LB LF m m' SP WM').
        - intros a Ha CA. unfold A_OOM_CELL, A_ERRNO in *.
          destruct CA as [S|[C|(b & Hb & Rb)]].
          + apply KEEPN; rewrite ?(wa_unsigned a Ha); [clear - S; lia| clear - S LOIMG SPL THI; lia| clear - S Ha LOIMG SPL; lia| clear - S Ha LOIMG SPL; lia].
          + cbn [hl_data_lo hl_data_hi hl_static HL0 arl_L R R0] in C. destruct C as [C1 C2]. unfold RT in C2. cbn [in_rangesZ] in C2.
            apply KIMGN; rewrite ?(wa_unsigned a Ha); [clear - C1; lia|]. unfold nzoneN, A_OOM_CELL, A_ERRNO. cbn [in_rangesZ]. clear - C1 C2. lia.
          + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
            * destruct b as [B j]. cbn [fst snd] in Rb. rewrite HLB in Hb. ddestruct (live_block h B j Hb) as (k & Hk & _ & EB & EJ).
              dpose (SLOT0 k Hk) as (S1 & S2 & S3 & S4 & _). apply (KSL k (bv_unsigned (wa a)) 1 Hk); rewrite ?(wa_unsigned a Ha); [clear - Rb EB EJ S1 S2 S3 S4; subst B j; lia| clear - Rb EB EJ S1 S2 S3 S4; subst B j; lia| clear; lia].
            * ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]);
                dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia]. change (h_L h) with L in G1, G2.
              apply (KLO (bv_unsigned (wa a)) 1); rewrite ?(wa_unsigned a Ha); unfold lowhigh, kFakeBytes in *; [clear - Rb F1 G1 FSLO; lia| right; clear - Rb F1 G1 FSLO; lia| clear - Rb F2 G2 FSHI; lia| clear - Rb F1 F2 G1 G2 TFA; lia| clear; lia].
        - intros c0 Hc Hr.
          assert (SHC : shadow_of AL0 c0 = shad c0) by reflexivity. rewrite SHC in *.
          destruct (cshd_cases STKLO h LB LF c0 Hc) as [S|[(A & n0 & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
          + dpose (hok_L STKLO h HOK) as (EL2 & _ & STC64 & SHI & _). change (h_L h) with L in SHI, STC64, S.
            apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); [clear - S EL STKLOC B6LO B6HI; lia| clear - S SHI; lia| clear; lia].
          + rewrite HLB in HIn. ddestruct (live_block h A n0 HIn) as (k & Hk & _ & EA & EN). dpose (SLOT0 k Hk) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
            apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); [clear - RA EA S1 S2 S4 S5; lia| clear - RA EA EN S2 S3 S6 ACE47; lia| clear; lia].
          + dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3). change (h_L h) with L in G1, G2.
            apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); unfold lowhigh, kFakeBytes in *; [clear - Rfb G1 FSLO; lia| clear - Rfb G2 FSHI ACE47; lia| clear; lia].
          + apply KISH. rewrite ?(wa_unsigned _ Hr). unfold shad. pose proof (Z.div_mod c0 8 ltac:(clear; lia)) as DC. pose proof (Z.mod_pos_bound c0 8 ltac:(clear; lia)) as MC. clear - C DC MC. lia. }
      split; [exact IK|].
      split; [intros jj _; reflexivity|].
      (* [comment removed for export] *)
      split; [exact (conj AWF HLB)|].
      split. { change (h_L h) with L. eapply hm_maps_frame; [exact GM| exact WM']. }
      split. { change (h_L h) with L. split.
        - eapply (hm_ro_frame m m' L GRO); [(eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN])| apply KTP; clear; lia| | |].
          + apply KLO; [clear - CX63; lia| right; clear - CX63; lia| clear - CXHI CXLEN; lia| clear - TC; lia].
          + apply KLO; [clear - CX63; lia| right; clear - CX63; lia| clear - CXHI CXLEN; lia| clear - TC CXLEN; lia].
          + apply KLO; [clear - DT0; lia| clear - DTI; lia| clear - DTHI; lia| clear - TDT; lia].
        - split; [exists (Z_to_bv 64 12); exact ERR'| split; [exists (Z_to_bv 8 1); exact OOM'|]].
          eapply keep_rw; [exact FBM| | exact WM']. apply LOWI; unfold A_FB_MUTEX, A_INSTANCE, A_OOM_CELL, A_ERRNO; cbn; clear; lia. }
      split. { (* [comment removed for export] *)
        eapply (hm_thread_frame_but m m' WM' h 1 (h_cache h 1) (ds 1) GT ltac:(clear; lia)).
        - exact UNW'.
        - intros c' Hc' _. change (l_T (h_L h)) with T. apply KTP; clear - Hc'; lia.
        - change (l_T (h_L h)) with T. apply KTP; clear; lia.
        - exact TW. - change (l_T (h_L h)) with T; exact TI.
        - eapply hm_pclass_frame; [exact WM'| exact (PCL 1 ltac:(clear; lia))| change (l_T (h_L h)) with T; apply KTP; clear; lia].
        - intros; reflexivity. - reflexivity. - reflexivity.
        - intros c'. destruct (Z.eqb_spec c' 1) as [->|]; reflexivity. }
      split. { (* [comment removed for export] *)
        apply (hm_depot_frame h m m' GD WM').
        - eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
        - intros b Hb. pose proof (NBLO b Hb) as [B1 B2]. fold nb in Hb. ddestruct (In_nth nb b 0 Hb) as (i & Hi & <-).
          pose proof (APTn (Z.of_nat i) ltac:(clear - Hi; lia)) as X. unfold dblk in X. rewrite Nat2Z.id in X. apply KLO; [clear - B1; lia| right; exact B1| exact B2| clear - X; lia].
        - intros b Hb. pose proof (BLLO b Hb) as [B1 B2]. fold bl in Hb. ddestruct (In_nth bl b 0 Hb) as (i & Hi & <-).
          pose proof (APTs (Z.of_nat i) ltac:(clear - Hi; lia)) as X. unfold sblk in X. rewrite Nat2Z.id in X. apply KLO; [clear - B1; lia| right; exact B1| exact B2| clear - X; lia]. }
      split. { (* [comment removed for export] *)
        apply (hm_chunks_frame m m' WM' h GC AWF). intros k' Hk'. dpose (SLOT0 k' Hk') as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _). dpose (chunk_geom h k' AWF Hk') as (_ & _ & U8).
        split; [| split].
        - apply (KSL k'); [exact Hk'| exact S1| clear - S2 S3; lia].
        - intros _. apply KSHS; [clear - S1 S2 S4 S5; lia| clear - S2 S3 S6 ACE47; unfold nfix; lia| unfold nfix; clear; lia| exact U8].
        - intros _. apply (KSL k'); [exact Hk'| clear - S1 S2 S4; lia| clear - S3; lia]. }
      split. { (* [comment removed for export] *)
        apply (hm_regions_frame m m' WM' h GR WR). intros c' Hc'. change (h_L h) with L.
        pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & AUCS' & MUAL' & MULIM' & _ & MFAL' & MFAB' & NF4' & _).
        unfold kUserLimit in MULIM'. unfold kFreeArrayMapSize, kFreeArraySize in MFAL', MFAB'.
        assert (RBLO' : SB <= region_beg L c') by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
        assert (RBHI' : region_beg L c' + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
        pose proof (class_size_range c' Hc') as CSR'.
        split; [| split; [| split]].
        + apply KHB; unfold ri_addr, ri_base, space_end, kSpaceSize; fold SB; clear - Hc'; lia.
        + apply KHB; unfold fa_beg, kFreeArrayOffset; [clear - RBLO'; lia| clear - RBHI' MFAB'; lia].
        + pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC'. rewrite C16', Z.add_0_r in DC'.
          pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(clear; lia)) as DMU'. unfold kUserMapSize in MUAL'. rewrite MUAL', Z.add_0_r in DMU'.
          assert (T8' : exists t, r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') = t * 8).
          { exists (2^15 * (r_mapped_user (h_reg h c') / 2^18) - 2 * (class_size c' / 16) * carved h c'). clear - DC' DMU' AUCS'. nia. }
          destruct T8' as [t ET].
          replace ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) / 8) with ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') + 7) / 8)
            by (rewrite ET, Z_div_mult, Z.div_add_l by (clear; lia); clear; cbn; lia).
          apply KSHS; [clear - RBLO' AUMU' SBLO; lia| clear - AUMU' MULIM' RBHI' HULLB ACE47; lia| clear - AUMU'; lia|].
          unfold region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DSB. rewrite SB16, Z.add_0_r in DSB. rewrite DSB.
          replace (2^16 * (SB / 2^16) + c' * 2^32 + r_alloc_user (h_reg h c')) with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + (class_size c' / 16) * carved h c' * 2)) by (clear - DC' AUCS'; nia).
          rewrite Z.mul_comm. apply Z_mod_mult.
        + intros k Hk.
          assert (AL8 : chunk_at L c' k mod 8 = 0).
          { unfold chunk_at, region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DSB. rewrite SB16, Z.add_0_r in DSB. rewrite DSB.
            pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC.
            rewrite C16', Z.add_0_r in DC. rewrite DC. replace (2^16 * (SB / 2^16) + c' * 2^32 + k * (16 * (class_size c' / 16))) with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + k * (class_size c' / 16) * 2)) by (clear; lia). rewrite Z.mul_comm. apply Z_mod_mult. }
          assert (KHI : (k + 1) * class_size c' <= r_alloc_user (h_reg h c')) by (rewrite AUCS'; rewrite AUCS' in Hk; rewrite Z.mul_comm in Hk; rewrite Z.div_mul in Hk by (clear - CSR'; lia); clear - Hk CSR'; nia).
          replace 1 with ((1 + 7) / 8) by reflexivity. apply KSHS; [ | | clear; lia| exact AL8].
          * unfold chunk_at. clear - RBLO' SBLO Hk CSR'. nia.
          * unfold chunk_at. clear - KHI AUMU' MULIM' RBHI' HULLB CSR' ACE47. nia. }
      split. { (* [comment removed for export] *)
        apply (hm_quar_frame m m' WM' h GQ).
        - eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
        - change (h_L h) with L. fold T. apply KTP; clear; lia.
        - intros b Hb. ddestruct WQ as ((T1q & _) & (G1q & _) & _).
          assert (WBA : wf_batch h b) by (apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) T1q b Hb)| exact (proj1 (Forall_forall _ _) G1q b Hb)]).
          ddestruct WBA as (_ & _ & _ & i & Hi & EB). rewrite EB. unfold kBatchClass in *. change (h_L h) with L in Hi, EB |- *.
          pose proof (WR 24 ltac:(unfold kNumClasses; clear; lia)) as WR24. cbn zeta in WR24. ddestruct WR24 as (_ & AUMU' & AUCS' & _ & MULIM' & _). unfold kUserLimit in MULIM'.
          assert (KHI : (i + 1) * 8192 <= r_alloc_user (h_reg h 24)) by (rewrite AUCS'; change (class_size 24) with 8192; clear - Hi; lia).
          apply KHB; unfold chunk_at, region_beg, kRegionSize; fold SB; change (class_size 24) with 8192; [clear - Hi; lia| clear - KHI AUMU' MULIM'; lia]. }
      split. { (* [comment removed for export] *)
        apply (hm_sec_frame m m' WM' h GS WSC).
        - eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
        - change (h_L h) with L. fold PA. rewrite WS5. fold nres. apply KLO; [clear - PA63; lia| right; exact PA63| clear - ER ROOM HR0 PAHI; lia| clear - TP' ER ROOM HR0; lia].
        - intros sh Hsh. fold cks in Hsh. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _). pose proof (TSEC sh Hsh) as X.
          pose proof (tr_wf AL h mo _ HK0 (tr_of_sec h sh Hsh)) as (W0 & _ & W2 & _ & _ & W5 & _). unfold t_hi, sec_tr in W0, W2, W5. cbn [t_lo t_len] in W0, W2, W5. rewrite IMH, IMLO in W5.
          apply KLO; [clear - W0; lia| clear - W5 BIG; lia| clear - W2 BIG; lia| clear - X BIG; lia]. }
      split. { (* [comment removed for export] *)
        apply (hm_fake_frame m m' WM' h LF GF); change (h_L h) with L.
        - unfold lowhigh in FSLO. clear - FSLO. lia.
        - apply KLO; unfold lowhigh, kFakeBytes in *; [clear - FSLO; lia| right; clear - FSLO; lia| clear - FSHI; lia| clear - TFA; lia].
        - intros FB nn IN. dpose (frame_bounds STKLO h LB LF m HOK HM0 (FB, nn) IN) as (G1 & G2 & G3). cbn [fst snd] in G1, G2, G3. change (h_L h) with L in G1, G2.
          apply KLO; unfold lowhigh, kFakeBytes in *; [clear - FSLO G1 G3; lia| right; clear - FSLO G1 G3; lia| clear - FSHI G2 G3; lia| clear - TFA G1 G2 G3; lia]. }
      (* [comment removed for export] *)
      split. { apply (hm_ia_frame m m' WM' h GI). eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN]. }
      (* [comment removed for export] *)
      apply (hm_emb_frame_i m m' WM' h _ GEMB); [reflexivity| reflexivity|]. eapply (iagree_of_windows2 _ nzoneN 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
    }
    (* [comment removed for export] *)
    ddestruct PO as (ms1' & mo' & res & sc' & r' & nb' & bl' & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & PO).
    cbn zeta in PO.
    ddestruct PO as (-> & -> & KF' & HJ' & WM' & MI' & ST' & CSM & UNW' & CHK).
    pose proof GD as DI. unfold hm_depot in DI. fold nb bl in DI.
    dpose DI as (_ & _ & (_ & NBWF & _) & _ & _ & _ & _ & (_ & BLWF & _) & _).
    assert (NBLO : forall b, In b nb -> 0x65f000 <= b /\ b + 2^20 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) NBWF b Hb) as X; cbn beta in X; clear - X; lia).
    assert (BLLO : forall b, In b bl -> 0x65f000 <= b /\ b + 2^23 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) BLWF b Hb) as X; cbn beta in X; clear - X; lia).
    assert (OBn : forall t b A k0, In t (tr_of h) -> In b nb -> t <> node_tr b -> t_lo t <= A -> A + k0 <= t_hi t -> A + k0 <= b \/ b + 2^20 <= A).
    { intros t b A k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (node_tr b) HK0 Ht (tr_of_node h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, node_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (OBs : forall t b A k0, In t (tr_of h) -> In b bl -> t <> store_tr b -> t_lo t <= A -> A + k0 <= t_hi t -> A + k0 <= b \/ b + 2^23 <= A).
    { intros t b A k0 Ht Hb NE A1 A2. destruct (tr_apart AL h mo t (store_tr b) HK0 Ht (tr_of_store h b Hb)) as [E|[X|X]]; [exact (False_ind _ (NE E))| |];
        unfold t_hi, store_tr in *; cbn [t_lo t_len] in X; clear - X A1 A2; lia. }
    assert (BNDn : forall b, In b nb -> b + 2^20 <= 0x7fff7000 \/ 0x10007fff8000 <= b).
    { intros b Hb. pose proof (tr_wf AL h mo _ HK0 (tr_of_node h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, node_tr in W6. cbn [t_lo t_len] in W6. exact W6. }
    assert (BNDs : forall b, In b bl -> b + 2^23 <= 0x7fff7000 \/ 0x10007fff8000 <= b).
    { intros b Hb. pose proof (tr_wf AL h mo _ HK0 (tr_of_store h b Hb)) as (_ & _ & _ & _ & _ & _ & W6). specialize (W6 eq_refl). unfold t_hi, store_tr in W6. cbn [t_lo t_len] in W6. exact W6. }
    (* [comment removed for export] *)
    assert (NTD : TR T 4096 KEager true true <> TR (l_dtls L) 4096 KEager true true) by (change T with (l_T (h_L h)); change L with (h_L h); exact (T_ne_dtls AL h (HK_vwf AL h mo HK0))).
    assert (TDT : T + 4096 <= l_dtls L \/ l_dtls L + 4096 <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_dtls h)) as [E|[X|X]]; [exact (False_ind _ (NTD E))| left| right]; unfold t_hi in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    assert (TFA : T + 4096 <= l_fs L \/ l_fs L + kFakeBytes <= T).
    { destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_fs h)) as [E|[X|X]]; [exfalso; injection E; unfold kFakeBytes; clear; intros; lia| left| right]; unfold t_hi in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    pose proof (tr_wf AL h mo _ HK0 (tr_of_dtls h)) as (DT0 & _ & DTHI & _ & _ & DTI & _). unfold t_hi in DTHI, DTI. cbn [t_lo t_len] in DT0, DTHI, DTI. change (h_L h) with L in DT0, DTHI, DTI. rewrite IMH, IMLO in DTI.
    assert (HULLB : l_b6 L <= SB /\ SB + 2^37 + 4096 <= l_b6 L + kPrimHullLen /\ l_b6 L + kPrimHullLen <= ACEIL) by (unfold kPrimHullLen in *; clear - B6A SEHI B6HI; lia).
    assert (TSEC : forall sh, In sh cks -> T + 4096 <= s_map_beg sh \/ s_map_beg sh + s_map_size sh <= T).
    { intros sh Hsh. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _).
      destruct (tr_apart AL h mo _ _ HK0 (tr_of_T h) (tr_of_sec h sh Hsh)) as [E|[X|X]]; [exfalso; injection E; clear - BIG; intros; lia| left| right]; unfold t_hi, sec_tr in X; cbn [t_lo t_len] in X; change (h_L h) with L in X; fold T in X; clear - X; lia. }
    (* [comment removed for export] *)
    assert (SLOT0 : forall k', In k' (h_chunks h) ->
              ext_lo k' <= ck_ab k' /\ ck_ab k' + ck_rz k' = ck_user k' /\ ck_user k' + Z.max (ck_n k') 8 <= ext_hi k' /\ 16 <= ck_rz k'
              /\ 0x65f000 <= ext_lo k' /\ ext_hi k' <= ACEIL /\ (ext_hi k' <= 0x7fff7000 \/ 0x10007fff8000 <= ext_lo k')
              /\ (ext_hi k' <= T \/ T + 4096 <= ext_lo k')
              /\ ((l_b6 L <= ext_lo k' /\ ext_hi k' <= l_b6 L + kPrimHullLen /\ exists c', 1 <= c' <= 31 /\ region_beg L c' <= ext_lo k' /\ ext_hi k' <= region_beg L c' + r_mapped_user (h_reg h c'))
                  \/ (exists sh, In sh cks /\ ext_lo k' = s_map_beg sh /\ ext_hi k' = s_map_beg sh + s_map_size sh))).
    { dpose WK as (WKF & WKND & WKSEC). intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (WN & WST & WP & WCX).
      ddestruct (chunk_ext h k' AWF Hk') as (N0 & E1 & E2 & E3 & E4 & [E5 E5'] & E6 & ARMk). dpose (chunk_geom h k' AWF Hk') as (RZ16 & _ & _).
      assert (US8 : ck_user k' + Z.max (ck_n k') 8 <= ext_hi k').
      { unfold ext_hi, ck_user, ck_rz, ck_end, ck_map_beg. pose proof (rz_size_bound (ck_n k')) as RZ'. destruct (ck_prim k') eqn:PR.
        + ddestruct WCX as (WCLS & WC30 & _). rewrite WCLS. pose proof (needed_le_class (ck_n k') ltac:(clear - WN; lia) ltac:(rewrite <- WP; reflexivity)) as NC.
          unfold needed, rounded, round_up in NC. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          clear - RZ' NC H H0 WN. lia.
        + unfold ck_map_size, sec_map_size. pose proof (round_up_spec (needed2 (ck_n k')) 4096 ltac:(clear; lia)) as [RU _].
          unfold needed2, needed, rounded, round_up in RU |- *. pose proof (Z.div_mod (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (Z.max (ck_n k') 8 + 8 - 1) 8 ltac:(clear; lia)).
          destruct (from_primary (ck_n k')); clear - RZ' RU H H0 WN; lia. }
      split; [unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia|]. split; [reflexivity|]. split; [exact US8|]. split; [exact RZ16|].
      split; [exact E5|]. split; [exact E6|]. split; [unfold kHighMemBeg in E5'; exact E5'|].
      destruct ARMk as [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & Q1 & Q2)].
      - change (h_L h) with L in R1, R2. pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear - C30; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _ & _ & MULIM' & _). unfold kUserLimit in MULIM'.
        assert (RBLO' : SB <= region_beg L (ck_cls k')) by (unfold region_beg, kRegionSize; fold SB; clear - C30; nia).
        assert (RBHI' : region_beg L (ck_cls k') + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - C30; nia).
        split; [clear - R1 R2 AUMU' MULIM' RBLO' RBHI' GSEP'; lia|]. left. split; [clear - R1 RBLO' HULLB; lia|]. split; [clear - R2 AUMU' MULIM' RBHI' HULLB; lia|].
        exists (ck_cls k'). split; [clear - C30; lia|]. split; [exact R1| clear - R2 AUMU'; lia].
      - fold cks in Hsh. split; [pose proof (TSEC sh Hsh) as X; clear - X Q1 Q2; lia|]. right. exists sh. split; [exact Hsh| exact (conj Q1 Q2)]. }
    unfold kPrimHullLen in HULLB, SLOT0.
    (* [comment removed for export] *)
    ddestruct CHK as (a & N' & tf' & id & b1' & pgb & sj0 & sj1 & sj2 & sj4 & rest' & CHK). cbn zeta in CHK. rewrite ?EMS in CHK.
    ddestruct CHK as (Eres & Esc & HR' & ROOMP & A68 & AAL & ACE & ALH & AP & AT & ACX & FRESH & CSA & KEEP & DI' & DCS' & DST' & IDB & NB' & TFB & POT
                     & (sn & sb & Enb & Ebl & APn & APs) & HDRA & ZA & MG' & ZAB & HDR' & B13 & B1R & UBF & ZU & SHA' & S1' & SUB' & PGS' & S2' & STH' & ST4' & LI' & HPS' & HREST' & LREST' & TJ').
    subst res sc' nb' bl'. rewrite ?RZ, ?NFX in *.
    set (AB := a + 4096) in *. set (UB := AB + 2048) in *. set (CHB := UB + -16) in *. set (SHA := 0x7fff8000 + a / 8) in *.
    pose proof (Z.div_mod a 4096 ltac:(clear; lia)) as DA. rewrite AAL, Z.add_0_r in DA.
    assert (A8 : a mod 8 = 0) by (rewrite DA; replace (4096 * (a / 4096)) with ((512 * (a / 4096)) * 8) by (clear; lia); apply Z_mod_mult).
    pose proof (Z.div_mod a 8 ltac:(clear; lia)) as DA8. rewrite A8, Z.add_0_r in DA8.
    pose proof (Z.div_mod n 8 ltac:(clear; lia)) as DN8. pose proof (Z.mod_pos_bound n 8 ltac:(clear; lia)) as MN8.
    assert (RR : r <= r' <= r + 1) by (clear - HR'; lia).
    assert (RMAX : 0x4000 * r' <= 2^20) by (clear - RR ROOM; lia).
    assert (UBLE : UB + n <= a + ms) by (subst UB AB; clear - MSB N2E RNB; lia).
    assert (A47 : a + ms <= 2^47) by (clear - ACE ACE47; lia).
    (* [comment removed for export] *)
    set (h' := sec_h h a n r' N' tf' (nb ++ sn) (bl ++ sb)).
    ddestruct (MS_exit h n mo HK0 BWF HVM NB FP ROOMS CSPAh ([] ++ [(a, ms)]) r' (nb ++ sn) (bl ++ sb) mo' h' KF') as (sn2 & sb2 & Esn & Esb & SANEn & SANEs & _ & _ & BS & FR' & EXIT).
    apply app_inv_head in Esn. subst sn2. apply app_inv_head in Esb. subst sb2.
    destruct BS as [[EB _]|(a' & Ea & SANE & _)]; [discriminate EB|]. cbn [app] in Ea. injection Ea as Ea1. subst a'.
    ddestruct SANE as (_ & _ & _ & _ & FRESHV & HULLS). change (mszh n) with ms in FRESHV, HULLS.
    assert (HB6 : a + ms <= l_b6 L \/ l_b6 L + kPrimHullLen <= a) by (exact (HULLS (l_b6 L, kPrimHullLen) ltac:(left; reflexivity))).
    unfold kPrimHullLen in HB6.
    assert (RSEC : R_sec h n ([] ++ [(a, ms)]) r' sn sb h').
    { unfold R_sec. cbv delta [h']. unfold sec_h. cbn [h_L h_reg h_dep h_sec h_acct h_pa_committed d_nb d_bl s_chunks app].
      split; [reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split. { dexists a, (needed2 n). split; [reflexivity|]. apply Permutation_sym. apply Permutation_cons_append. }
      rewrite WS5. fold nres. change (r0h h) with r. unfold kPaSlice. clear - ER. lia. }
    destruct (EXIT RSEC) as [HK' CSE].
    (* [comment removed for export] *)
    assert (CSUFx : forall y, vcs AL (vst_of h) y -> CSsh h n ([] ++ [(a, ms)]) r' nb bl y) by (intros y Hy; unfold CSsh, AInstSec.CSs, AInstSec.CSb; left; left; exact Hy).
    assert (NBn : forall b x, In b sn -> vcs AL (vst_of h) x -> ~ (b <= x < b + 2^20)) by (intros b x Hb Hx; pose proof (proj1 (Forall_forall _ _) APn b Hb) as X; cbn beta in X; apply X; apply CSUFx; exact Hx).
    assert (NBs : forall b x, In b sb -> vcs AL (vst_of h) x -> ~ (b <= x < b + 2^23)) by (intros b x Hb Hx; pose proof (proj1 (Forall_forall _ _) APs b Hb) as X; cbn beta in X; apply X; apply CSUFx; exact Hx).
    assert (SHn : forall b, In b sn -> 0x10007fff8000 <= b \/ b + 2^20 <= 0x7fff7000) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEn b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    assert (SHs : forall b, In b sb -> 0x10007fff8000 <= b \/ b + 2^23 <= 0x7fff7000) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEs b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    assert (LOn : forall b, In b sn -> 0x65f000 <= b /\ b + 2^20 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEn b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    assert (LOs : forall b, In b sb -> 0x65f000 <= b /\ b + 2^23 <= ACEIL) by (intros b Hb; pose proof (proj1 (Forall_forall _ _) SANEs b Hb) as SA; cbn beta in SA; unfold sane in SA; clear - SA; lia).
    (* [comment removed for export] *)
    assert (FSA : l_fs L + kFakeBytes <= a \/ a + ms <= l_fs L).
    { apply (apart_of_fresh (vcs AL (vst_of h)) a ms (l_fs L) kFakeBytes); [clear - MSB N2B; lia| unfold kFakeBytes; clear; lia| | exact FRESHV].
      intros y Hy. apply (vcs_of_tr AL h _ y (tr_of_fs h) eq_refl). unfold t_hi. cbn [t_lo t_len]. change (h_L h) with L. exact Hy. }
    assert (DTA : l_dtls L + 4096 <= a \/ a + ms <= l_dtls L).
    { apply (apart_of_fresh (vcs AL (vst_of h)) a ms (l_dtls L) 4096); [clear - MSB N2B; lia| clear; lia| | exact FRESHV].
      intros y Hy. apply (vcs_of_tr AL h _ y (tr_of_dtls h) eq_refl). unfold t_hi. cbn [t_lo t_len]. change (h_L h) with L. exact Hy. }
    assert (OLDAP : Forall (fun k' => ck_end k' <= a \/ a + APopSec.ms n <= (if ck_prim k' then ck_ab k' else ck_map_beg k')) (h_chunks h)).
    { apply Forall_forall. intros k' Hk'. change (APopSec.ms n) with ms. change (ck_end k') with (ext_hi k'). change (if ck_prim k' then ck_ab k' else ck_map_beg k') with (ext_lo k').
      dpose (SLOT0 k' Hk') as (_ & _ & _ & _ & _ & _ & _ & _ & [(H1 & H2 & _)|(sh & Hsh & Q1 & Q2)]); [clear - H1 H2 HB6; lia|].
      rewrite Q1, Q2. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _).
      apply (apart_of_fresh (vcs AL (vst_of h)) a ms (s_map_beg sh) (s_map_size sh)); [clear - MSB N2B; lia| clear - BIG; lia| | exact FRESHV].
      intros y Hy. apply (vcs_of_tr AL h _ y (tr_of_sec h sh Hsh) eq_refl). unfold t_hi, sec_tr. cbn [t_lo t_len]. exact Hy. }
    assert (SLOTS : forall k', In k' (h_chunks h) -> ext_hi k' <= a \/ a + ms <= ext_lo k').
    { intros k' Hk'. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as X. cbn beta in X. exact X. }
    (* [comment removed for export] *)
    assert (KEEPC : forall x : word, let y := bv_unsigned x in
              ~ (lo <= y < SP) -> ~ (A_SS <= y < A_DEP_END) -> ~ (T + 2784 <= y < T + 3169) ->
              ~ (a <= y < a + ms) -> ~ (SHA <= y < SHA + ms / 8) -> ~ (A_INSTANCE + 112 <= y < A_INSTANCE + 720) -> ~ (PA <= y < PA + 0x800000) ->
              (forall b, In b (nb ++ sn) -> ~ (b <= y < b + 2^20)) -> (forall b, In b (bl ++ sb) -> ~ (b <= y < b + 2^23)) -> m' x = m x).
    { intros x. cbn zeta. intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Qn Qs. apply KEEP.
      - unfold msec_cwin. cbn [outside]. rewrite ?EMS. subst SHA. repeat split;
          first [exact Q1 | exact Q2 | exact Q4 | exact Q5 | exact Q6 | (clear - Q3; lia) | (clear - Q7 HNC RMAX; lia)
                | match goal with |- ?G => fail 99 "KEEPC" G end].
      - intros k0 Hk0. apply Qn. unfold dblk. apply nth_In. clear - Hk0. lia.
      - intros jj Hjj. apply Qs. unfold sblk. apply nth_In. clear - Hjj. lia. }
    dpose DI' as (_ & _ & (_ & NBWF2 & NBL2) & _ & DWF2 & _ & _ & (_ & BLWF2 & BLL2) & _ & _ & BL2 & _).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (KIMGN : forall x : word, 0x10000 <= bv_unsigned x < 0x65f000 -> ~ in_rangesZ nzoneS (bv_unsigned x) -> m' x = m x).
    { intros x Hx Hz. unfold nzoneS in Hz. cbn [in_rangesZ] in Hz. unfold A_SS, A_DEP_END, A_INSTANCE in *.
      apply KEEPC; [clear - Hx LOIMG B6LO B6HI; lia| clear - Hz; lia| clear - Hx TI; lia| clear - Hx A68; lia| subst SHA; clear - Hx A68 DA8; lia| clear - Hz; lia| clear - Hx PA63; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (NBLO b Hb)| pose proof (LOn b Hb)]; clear - H Hx; lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (BLLO b Hb)| pose proof (LOs b Hb)]; clear - H Hx; lia. }
    (* [comment removed for export] *)
    assert (KISH : forall x : word, 0x7fffa000 <= bv_unsigned x < 0x800c3e00 -> m' x = m x).
    { intros x Hx. unfold A_SS, A_DEP_END, A_INSTANCE in *.
      apply KEEPC; [clear - Hx LOIMG B6LO B6HI; lia| clear - Hx; lia| clear - Hx TB; lia| clear - Hx ALH MSB N2B; lia| subst SHA; clear - Hx A68 DA8; lia| clear - Hx; lia| clear - Hx PB; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (BNDn b Hb)| pose proof (SHn b Hb)]; clear - H Hx; lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (BNDs b Hb)| pose proof (SHs b Hb)]; clear - H Hx; lia. }
    assert (IK : img_keep m m').
    { split; [| exact KISH]. intros x Hx Hz. apply KIMGN; [exact Hx|]. unfold awz, nzoneS, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END in *. cbn [in_rangesZ] in Hz |- *. clear - Hz. lia. }
    assert (LOWI : forall A k0, 0x10000 <= A -> A + k0 <= 0x65f000 -> (A + k0 <= A_SS \/ A_DEP_END <= A) -> (A + k0 <= A_INSTANCE + 112 \/ A_INSTANCE + 720 <= A) -> kept m m' A k0).
    { intros A k0 H1 H2 H3 H4 x Hx. apply KIMGN; [clear - H1 H2 Hx; lia|]. unfold nzoneS. cbn [in_rangesZ]. clear - H3 H4 Hx. lia. }
    (* [comment removed for export] *)
    assert (KTN : forall t A k0, In t (tr_of h) -> t_cs t = true ->
              (forall b, In b nb -> t <> node_tr b) -> (forall b, In b bl -> t <> store_tr b) ->
              t_lo t <= A -> A + k0 <= t_hi t -> 0 < k0 ->
              (A + k0 <= T \/ T + 4096 <= A) -> (A + k0 <= PA \/ PA + 0x800000 <= A) ->
              kept m m' A k0).
    { intros t A k0 Ht TCS NN NS A1 A2 K0 YT YP x Hx. dpose (tr_wf AL h mo t HK0 Ht) as (W0 & W1 & W2 & W3 & W4 & W5 & W6). specialize (W6 TCS). rewrite IMH, IMLO in W5.
      assert (XCS : vcs AL (vst_of h) (bv_unsigned x)) by (apply (vcs_of_tr AL h t _ Ht TCS); unfold t_hi in *; clear - Hx A1 A2; lia).
      pose proof (FRESHV _ XCS) as FX.
      unfold A_SS, A_DEP_END, A_INSTANCE in *.
      apply KEEPC; [unfold t_hi in *; clear - Hx A1 A2 W2 LOIMG; lia| unfold t_hi in *; clear - Hx A1 A2 W5; lia| clear - Hx YT; lia| exact FX
                   | unfold t_hi in *; subst SHA; clear - Hx A1 A2 W6 A68 A47 DA8 DMS8; lia| unfold t_hi in *; clear - Hx A1 A2 W5; lia| clear - Hx YP; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)]. pose proof (OBn t b A k0 Ht Hb (NN b Hb) A1 A2). clear - H Hx. lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)]. pose proof (OBs t b A k0 Ht Hb (NS b Hb) A1 A2). clear - H Hx. lia. }
    (* [comment removed for export] *)
    assert (KTP : forall A k0, T <= A -> A + k0 <= T + 2784 -> 0 < k0 -> kept m m' A k0).
    { intros A k0 A1 A2 K0 x Hx. unfold A_SS, A_DEP_END, A_INSTANCE in *.
      assert (XCS : vcs AL (vst_of h) (bv_unsigned x)) by (apply (vcs_of_tr AL h _ _ (tr_of_T h) eq_refl); unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - Hx A1 A2; lia).
      pose proof (FRESHV _ XCS) as FX.
      apply KEEPC; [clear - Hx A1 A2 THI LOIMG; lia| clear - Hx A1 A2 TI; lia| clear - Hx A2; lia| exact FX| subst SHA; clear - Hx A1 A2 TB A68 A47 DA8 DMS8; lia| clear - Hx A1 A2 TI; lia| clear - Hx A1 A2 TP'; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)].
        pose proof (OBn _ b A k0 (tr_of_T h) Hb ltac:(intros E; discriminate E) ltac:(cbn [t_lo]; change (h_L h) with L; fold T; clear - A1; lia) ltac:(unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - A2; lia)). clear - H Hx. lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)].
        pose proof (OBs _ b A k0 (tr_of_T h) Hb ltac:(intros E; discriminate E) ltac:(cbn [t_lo]; change (h_L h) with L; fold T; clear - A1; lia) ltac:(unfold t_hi; cbn [t_lo t_len]; change (h_L h) with L; fold T; clear - A2; lia)). clear - H Hx. lia. }
    (* [comment removed for export] *)
    assert (KU : forall c' A k0, 1 <= c' <= 31 -> region_beg L c' <= A -> A + k0 <= region_beg L c' + r_mapped_user (h_reg h c') -> 0 < k0 -> kept m m' A k0).
    { intros c' A k0 Hc' A1 A2 K0 x Hx. unfold A_SS, A_DEP_END, A_INSTANCE in *.
      pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & _ & MUAL' & MULIM' & _). unfold kUserLimit in MULIM'. unfold kUserMapSize in MUAL'.
      assert (XCS : vcs AL (vst_of h) (bv_unsigned x)) by (eapply (crange_user AL h c' A k0); [exact Hc'| exact MUAL'| exact A1| clear - K0; lia| exact A2| exact Hx]).
      pose proof (FRESHV _ XCS) as FX.
      assert (RBLO' : SB <= region_beg L c') by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
      assert (RBHI' : region_beg L c' + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
      assert (NUT' : forall j, 0 <= j < r_mapped_user (h_reg h c') / kUserMapSize -> TR T 4096 KEager true true <> uunit_tr L c' j) by (intros j _ E; discriminate E).
      pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_T h) Hc' MUAL' NUT' A1 K0 A2) as XT. unfold t_hi in XT. cbn [t_lo t_len] in XT. change (h_L h) with L in XT. fold T in XT.
      apply KEEPC; [clear - Hx A1 A2 RBHI' MULIM' HULLB LOIMG; lia| clear - Hx A1 RBLO' SBLO; lia| clear - Hx XT; lia| exact FX| subst SHA; clear - Hx A1 RBLO' SBLO A47 DA8 DMS8; lia| clear - Hx A1 RBLO' SBLO; lia
                   | clear - Hx A1 A2 RBLO' RBHI' MULIM' HULLB HPA; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBn b _ Hb XCS)].
        pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_node h b Hb) Hc' MUAL' ltac:(intros j _ E; discriminate E) A1 K0 A2) as X. unfold t_hi, node_tr in X. cbn [t_lo t_len] in X. clear - X Hx. lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (NBs b _ Hb XCS)].
        pose proof (tr_apart_user AL h mo _ c' A k0 HK0 (tr_of_store h b Hb) Hc' MUAL' ltac:(intros j _ E; discriminate E) A1 K0 A2) as X. unfold t_hi, store_tr in X. cbn [t_lo t_len] in X. clear - X Hx. lia. }
    (* [comment removed for export] *)
    assert (KSB : forall B j, 0x800c3e00 <= B -> B + j <= 0x10007fff8000 -> (B + j <= SHA \/ SHA + ms / 8 <= B) -> kept m m' B j).
    { intros B j B1 B2 B3 x Hx. unfold A_SS, A_DEP_END, A_INSTANCE in *.
      apply KEEPC; [clear - Hx B2 LOIMG B6LO B6HI; lia| clear - Hx B1; lia| clear - Hx B1 B2 TB; lia| clear - Hx B1 B2 ALH MSB N2B; lia| clear - Hx B3; lia| clear - Hx B1; lia| clear - Hx B1 B2 PB; lia| |].
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (BNDn b Hb)| pose proof (SHn b Hb)]; clear - H Hx B1 B2; lia.
      - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [pose proof (BNDs b Hb)| pose proof (SHs b Hb)]; clear - H Hx B1 B2; lia. }
    assert (KSHS : forall A k0, 0x65f000 <= A -> A + k0 <= 2^47 -> 0 <= k0 -> A mod 8 = 0 -> (A + k0 <= a \/ a + ms <= A) -> kept m m' (shad A) ((k0 + 7) / 8)).
    { intros A k0 A63 ACE' K0 A8' AP'. unfold shad. pose proof (Z.div_mod A 8 ltac:(clear; lia)) as DA'. rewrite A8', Z.add_0_r in DA'.
      pose proof (Z.div_mod (k0 + 7) 8 ltac:(clear; lia)) as DK. pose proof (Z.mod_pos_bound (k0 + 7) 8 ltac:(clear; lia)) as MK.
      apply KSB; [clear - A63 DA'; lia| clear - ACE' DA' DK MK K0; lia| subst SHA; clear - AP' DA' DA8 DMS8 DK MK K0; lia]. }
    assert (KSH1 : forall c, 0x65f000 <= c -> c < 2^47 -> (c < a \/ a + ms <= c) -> kept m m' (shad c) 1).
    { intros c C1 C2 C3. unfold shad. pose proof (Z.div_mod c 8 ltac:(clear; lia)) as DC. pose proof (Z.mod_pos_bound c 8 ltac:(clear; lia)) as MC.
      apply KSB; [clear - C1 DC MC; lia| clear - C2 DC MC; lia| subst SHA; clear - C3 DC MC DA8 DMS8; lia]. }
    (* [comment removed for export] *)
    assert (KSL : forall k' A k0, In k' (h_chunks h) -> ext_lo k' <= A -> A + k0 <= ext_hi k' -> 0 < k0 -> kept m m' A k0).
    { intros k' A k0 Hk' A1 A2 K0. dpose (SLOT0 k' Hk') as (_ & _ & _ & _ & _ & S6 & _ & S8 & [(H1 & H2 & c' & Hc' & R1 & R2)|(sh & Hsh & Q1 & Q2)]).
      - apply (KU c' A k0); [exact Hc'| clear - A1 R1; lia| clear - A2 R2; lia| exact K0].
      - rewrite Q1 in A1, S8. rewrite Q2 in A2, S6, S8. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _).
        destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_sec h sh Hsh) eq_refl ltac:(right; left; reflexivity)) as [XP|XP];
          unfold t_hi, sec_tr, kPaHullLen in XP; cbn [t_lo t_len fst snd] in XP; change (h_L h) with L in XP; fold PA in XP;
          (apply (KTN (sec_tr sh) A k0); try solve [intros; discriminate];
           [apply tr_of_sec; exact Hsh| reflexivity| intros b Hb; exact (sec_not_node AL h mo sh b HK0 Hsh Hb)
           | unfold sec_tr; cbn [t_lo]; exact A1| unfold sec_tr, t_hi; cbn [t_lo t_len]; exact A2| exact K0| clear - A1 A2 S8; lia| clear - A1 A2 XP; lia]). }
    assert (KCTX : kept m m' CTX 0x10000).
    { apply (KTN (TR CTX (l_ctxlen L) KEager true true)); try solve [intros; discriminate].
      - exact (tr_of_ctx h). - reflexivity. - intros b _ E. injection E. clear - CXLEN. lia.
      - cbn [t_lo]. clear. lia. - unfold t_hi. cbn [t_lo t_len]. rewrite CXLEN. clear. lia. - clear. lia.
      - clear - TC; lia. - exact CP'. }
    assert (KDT : kept m m' (l_dtls L + 24) 8).
    { destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_dtls h) eq_refl ltac:(right; left; reflexivity)) as [XP|XP];
        unfold t_hi, kPaHullLen in XP; cbn [t_lo t_len fst snd] in XP; change (h_L h) with L in XP; fold PA in XP;
        (apply (KTN (TR (l_dtls L) 4096 KEager true true)); try solve [intros; discriminate];
         [apply tr_of_dtls| reflexivity| cbn [t_lo]; clear; lia| unfold t_hi; cbn [t_lo t_len]; clear; lia| clear; lia| clear - TDT; lia| clear - XP; lia]). }
    assert (FSP : l_fs L + kFakeBytes <= PA \/ PA + 0x800000 <= l_fs L).
    { destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_fs h) eq_refl ltac:(right; left; reflexivity)) as [XP|XP];
        unfold t_hi, kPaHullLen in XP; cbn [t_lo t_len fst snd] in XP; change (h_L h) with L in XP; fold PA in XP; [left| right]; clear - XP; lia. }
    assert (KFS : forall A k0, l_fs L <= A -> A + k0 <= l_fs L + kFakeBytes -> 0 < k0 -> kept m m' A k0).
    { intros A k0 A1 A2 K0. apply (KTN (TR (l_fs L) kFakeBytes KEager true true) A k0); try solve [intros; discriminate];
        [exact (tr_of_fs h)| reflexivity| cbn [t_lo]; exact A1| unfold t_hi; cbn [t_lo t_len]; exact A2| exact K0| unfold kFakeBytes in *; clear - A1 A2 TFA; lia| unfold kFakeBytes in *; clear - A1 A2 FSP; lia]. }
    (* [comment removed for export] *)
    assert (WRUB : wr_at asegs m' UB n).
    { pose proof (rw_cells_wr_at asegs m' UB _ 4096 UBF ltac:(cbn; clear; lia)) as W1.
      pose proof (rw_cells_wr_at asegs m' (UB + 4096) _ (a + ms - UB - 4096) ZU ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - UBLE NLO; lia); clear; lia)) as W2.
      apply (wr_at_sub m' UB (4096 + (a + ms - UB - 4096)) UB n); [apply wr_at_join; [exact W1| exact W2| clear; lia| clear - UBLE NLO; lia]| clear; lia| clear - UBLE; lia]. }
    destruct (wr_at_high_CB m' UB n WRUB ltac:(subst UB AB; clear - A68; lia) ltac:(clear - NB; lia)) as (junk & JUNK).
    (* [comment removed for export] *)
    assert (AWF' : awf' h').
    { cbv delta [h'].
      apply (awf'_sec h a n r' N' tf' (nb ++ sn) (bl ++ sb) AWF NB FP A68 AAL ACE ALH OLDAP).
      all: lazymatch goal with
           | |- _ \/ _ => first [ change (APopSec.nres h) with nres; change (APopSec.ncks h) with ncks; clear - HR' ER; lia
               | match goal with |- ?G => fail 99 "AWFSEC-1" G end ]
           | |- APopSec.ncks _ + 1 <= _ => first [ change (APopSec.ncks h) with ncks; exact ROOMP
               | match goal with |- ?G => fail 99 "AWFSEC-2" G end ]
           | |- 16384 * _ <= 2^20 => first [ exact RMAX
               | match goal with |- ?G => fail 99 "AWFSEC-3" G end ]
           | |- APopSec.ncks _ + 16384 <= _ => first [ change (APopSec.ncks h) with ncks; clear - HNC ROOM; lia
               | match goal with |- ?G => fail 99 "AWFSEC-4" G end ]
           | |- d_n _ <= _ <= _ => first [ exact NB'
               | match goal with |- ?G => fail 99 "AWFSEC-5" G end ]
           | |- s_total _ <= _ => first [ clear - TFB; lia
               | match goal with |- ?G => fail 99 "AWFSEC-6" G end ]
           | |- Z.of_nat (length (_ ++ _)) = _ => first [ first [destruct DWF2 as [_ E]; exact E| exact BL2]
               | match goal with |- ?G => fail 99 "AWFSEC-7" G end ]
           | |- Forall _ (_ ++ _) => first [ first [exact NBWF2| exact BLWF2]
               | match goal with |- ?G => fail 99 "AWFSEC-8" G end ]
           | |- Z.of_nat (length (_ ++ _)) <= _ => first [ first [ destruct DWF2 as [N1 E]; rewrite E; clear - N1; pose proof (Z.div_mod N' 65536 ltac:(lia)); pose proof (Z.mod_pos_bound N' 65536 ltac:(lia)); lia
                     | rewrite BL2; pose proof (tf_after_put h d tf' HFR D0 (proj1 (proj2 (proj2 (proj2 WD)))) TFB POT) as TFX; clear - TFB TFX;
                       pose proof (Z.div_mod (tf' + 2^20 - 1) (2^20) ltac:(lia)); pose proof (Z.mod_pos_bound (tf' + 2^20 - 1) (2^20) ltac:(lia)); lia ]
               | match goal with |- ?G => fail 99 "AWFSEC-9" G end ]
           | |- ?G => fail 99 "AWFSEC" G
           end. }
    (* [comment removed for export] *)
    apply HB. unfold mallocH_postC.
    dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m', mo', h', UB.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact WM'|].
    split; [exact HK'|]. split; [exact HJ'|]. split; [reflexivity|]. split; [reflexivity|].
    split; [change (h_havol h') with (h_havol h + 2 * n); clear; lia|].
    split. { unfold hfr. cbv delta [h']. unfold sec_h. cbn [h_dep d_n s_total]. unfold sframes in *. clear - POT NB' D0 TFB. lia. }
    split. { intros x Hx. apply (proj1 (CSE x)). apply CSM. apply CSUF. exact Hx. }
    split. { (* [comment removed for export] *)
      apply (presA_intro STKLO h LB LF m m' SP WM').
      - intros ad Ha CA. unfold A_SS, A_DEP_END, A_INSTANCE in *.
        destruct CA as [S|[C|(b & Hb & Rb)]].
        + apply KEEPC; rewrite ?(wa_unsigned ad Ha).
          * clear - S. lia. * clear - S Ha LOIMG SPL. lia. * clear - S LOIMG SPL THI. lia. * clear - S LOIMG SPL ACE. lia.
          * subst SHA. clear - S LOIMG SPL A47 DA8 DMS8 B6LO B6HI. lia. * clear - S Ha LOIMG SPL. lia. * clear - S LOIMG SPL PAHI. lia.
          * intros b0 Hb0. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [pose proof (NBLO b0 Hb0)| pose proof (LOn b0 Hb0)]; clear - H S LOIMG SPL; lia.
          * intros b0 Hb0. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [pose proof (BLLO b0 Hb0)| pose proof (LOs b0 Hb0)]; clear - H S LOIMG SPL; lia.
        + cbn [hl_data_lo hl_data_hi hl_static HL0 arl_L R R0] in C. destruct C as [C1 C2]. unfold RT in C2. cbn [in_rangesZ] in C2.
          apply KIMGN; rewrite ?(wa_unsigned ad Ha); [clear - C1; lia|]. unfold nzoneS, A_SS, A_DEP_END, A_INSTANCE. cbn [in_rangesZ]. clear - C1 C2. lia.
        + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          * destruct b as [B j]. cbn [fst snd] in Rb. rewrite HLB in Hb. ddestruct (live_block h B j Hb) as (k' & Hk' & _ & EB & EJ).
            dpose (SLOT0 k' Hk') as (S1 & S2 & S3 & S4 & _).
            apply (KSL k' (bv_unsigned (wa ad)) 1 Hk'); rewrite ?(wa_unsigned ad Ha); [clear - Rb EB EJ S1 S2 S4; subst B j; lia| clear - Rb EB EJ S2 S3; subst B j; lia| clear; lia| clear; lia].
          * ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]);
              dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia]. change (h_L h) with L in G1, G2.
            apply (KFS (bv_unsigned (wa ad)) 1); rewrite ?(wa_unsigned ad Ha); [clear - Rb F1 G1; lia| clear - Rb F2 G2; lia| clear; lia| clear; lia].
      - intros c0 Hc Hr.
        assert (SHC : shadow_of AL0 c0 = shad c0) by reflexivity. rewrite SHC in *.
        destruct (cshd_cases STKLO h LB LF c0 Hc) as [S|[(A & n0 & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
        + dpose (hok_L STKLO h HOK) as (EL2 & _ & STC64 & SHI & _). change (h_L h) with L in SHI, STC64, S.
          apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); [clear - S EL STKLOC B6LO B6HI; lia| clear - S SHI; lia| right; clear - S EL STKLOC ACE; lia| clear; lia].
        + rewrite HLB in HIn. ddestruct (live_block h A n0 HIn) as (k' & Hk' & _ & EA & EN). dpose (SLOT0 k' Hk') as (S1 & S2 & S3 & S4 & S5 & S6 & _). pose proof (SLOTS k' Hk') as SA.
          apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); [clear - RA EA S1 S2 S4 S5; lia| clear - RA EA EN S2 S3 S6 ACE47; lia| clear - RA EA EN S1 S2 S3 S4 SA; lia| clear; lia].
        + dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3). change (h_L h) with L in G1, G2.
          apply (KSH1 c0); rewrite ?(wa_unsigned _ Hr); unfold lowhigh, kFakeBytes in *; [clear - Rfb G1 FSLO; lia| clear - Rfb G2 FSHI ACE47; lia| clear - Rfb G1 G2 FSA; lia| clear; lia].
        + apply KISH. rewrite ?(wa_unsigned _ Hr). unfold shad. pose proof (Z.div_mod c0 8 ltac:(clear; lia)) as DC. pose proof (Z.mod_pos_bound c0 8 ltac:(clear; lia)) as MC. clear - C DC MC. lia. }
    split; [exact IK|].
    split. { intros jj _. cbv delta [h']. unfold sec_h. reflexivity. }
    split. { subst UB AB. replace (a + 4096 + 2048) with ((256 * (a / 4096) + 384) * 16) by (clear - DA; lia). apply Z_mod_mult. }
    split. { (* [comment removed for export] *)
      split; [subst UB AB; clear - A68; lia|].
      split; [cbn [alloc_ceiling hl_ceil arl_L R R0 HL0]; clear - UBLE ACE; lia|].
      split; [cbn [hl_data_lo hl_data_hi arl_L R R0 HL0]; right; subst UB AB; clear - A68; lia|].
      intros B j HBj. apply in_app_iff in HBj. destruct HBj as [HBj|HBj].
      - rewrite HLB in HBj. ddestruct (live_block h B j HBj) as (k' & Hk' & _ & -> & ->).
        dpose (SLOT0 k' Hk') as (S1 & S2 & S3 & S4 & _). pose proof (SLOTS k' Hk') as SA. subst UB AB. clear - S1 S2 S3 S4 SA UBLE NB. lia.
      - ddestruct (fdata_sub LF B j HBj) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]); dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia]. change (h_L h) with L in G1, G2.
        subst UB AB. unfold kFakeBytes in *. clear - F1 F2 G1 G2 FSA UBLE NB. lia. }
    split; [left; subst UB AB; clear - UBLE ACE STKLOC EL; lia|].
    split. 2:{ exists junk. exact JUNK. }
    (* [comment removed for export] *)
    split. { split; [exact AWF'|]. cbv delta [h']. rewrite (blocks_sec h a n r' N' tf' (nb ++ sn) (bl ++ sb) NB FP), HLB. subst UB AB. reflexivity. }
    split. { change (h_L h') with L. eapply hm_maps_frame; [exact GM| exact WM']. }
    split. { change (h_L h') with L. split.
      - eapply (hm_ro_frame m m' L GRO); [(eapply (iagree_of_windows2 _ nzoneS 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN])| apply KTP; clear; lia| eapply kept_sub; [exact KCTX| clear; lia| clear; lia]| eapply kept_sub; [exact KCTX| clear; lia| clear; lia]| exact KDT].
      - eapply (hm_rwstat_frame m m' WM' GRW). eapply (iagree_of_windows2 _ nzoneS 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN]. }
    split. { (* [comment removed for export] *)
      change (hm_thread h' m') with (hm_thread h m').
      eapply (hm_thread_frame_but m m' WM' h 1 (h_cache h 1) (ds 1) GT ltac:(clear; lia)).
      - exact UNW'.
      - intros c' Hc' _. change (l_T (h_L h)) with T. apply KTP; clear - Hc'; lia.
      - change (l_T (h_L h)) with T. apply KTP; clear; lia.
      - exact TW. - change (l_T (h_L h)) with T; exact TI.
      - eapply hm_pclass_frame; [exact WM'| exact (PCL 1 ltac:(clear; lia))| change (l_T (h_L h)) with T; apply KTP; clear; lia].
      - intros; reflexivity. - reflexivity. - reflexivity.
      - intros c'. destruct (Z.eqb_spec c' 1) as [->|]; reflexivity. }
    split. { (* [comment removed for export] *) exact DI'. }
    split. { (* [comment removed for export] *)
      unfold hm_chunks. cbv delta [h']. unfold sec_h. cbn [h_chunks]. constructor.
      - (* [comment removed for export] *)
        unfold newks. set (nk := CK (a + 4096) n false 0 CHUNK_ALLOCATED).
        assert (EHDR : ck_hdr nk = CHB) by (subst nk CHB UB AB; unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize; cbn [ck_ab ck_n]; rewrite RZ; clear; lia).
        assert (EUSR : ck_user nk = UB) by (subst nk UB AB; unfold ck_user, ck_rz; cbn [ck_ab ck_n]; rewrite RZ; reflexivity).
        assert (EAB' : ck_ab nk = AB) by reflexivity.
        unfold hm_chunk. split; [| split].
        + unfold hm_hdr. dexists b1', id. rewrite EHDR. change (ck_st nk) with CHUNK_ALLOCATED. change (ck_n nk) with n. rewrite NFX.
          split; [| split; [exact B13| split; [exact B1R| clear - IDB NB' DNB; lia]]].
          apply (rw_cells_reshape asegs m' CHB _ _ HDR'). 1: { cbn [cells_wf cell_wf]. repeat split. }
          cbn [cells_bytes cbytes app]. rewrite ?Z.mul_0_l, ?Z.lor_0_l. rewrite ?(le8_split4 (Z_to_bv 64 id)).
          rewrite unsigned_lit by (clear - IDB NB' DNB; lia). rewrite (Z.div_small id) by (clear - IDB NB' DNB; lia). rewrite <- ?app_assoc. reflexivity.
        + unfold hm_magic. intros _. rewrite EHDR, EAB'. exact MG'.
        + replace (if ck_st nk =? CHUNK_ALLOCATED then hm_ushadow m' nk else hm_quser m' nk) with (hm_ushadow m' nk) by reflexivity.
          unfold hm_ushadow. rewrite EUSR. change (ck_n nk) with n. rewrite NFX. split.
          * unfold zeros, shad. rewrite Z_div_mult in SUB' by (clear; lia). exact SUB'.
          * intros M8. replace (shad (UB + n / 8 * 8)) with (0x7fff8000 + Z.shiftr (UB + n / 8 * 8) 3); [| unfold shad; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity].
            unfold pgv in PGS'. rewrite NFX in PGS'. destruct (Z.eqb_spec (n mod 8) 0) as [E0|NE0]; [exact (False_ind _ (M8 E0))| exact PGS'].
      - (* [comment removed for export] *)
        apply (hm_chunks_frame m m' WM' h GC AWF). intros k' Hk'. dpose (SLOT0 k' Hk') as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _). pose proof (SLOTS k' Hk') as SA.
        dpose (chunk_geom h k' AWF Hk') as (_ & _ & U8).
        split; [| split].
        + apply (KSL k'); [exact Hk'| exact S1| clear - S2 S3; lia| clear - S4; lia].
        + intros _. apply KSHS; [clear - S1 S2 S4 S5; lia| clear - S2 S3 S6 ACE47; unfold nfix; lia| unfold nfix; clear; lia| exact U8| clear - S1 S2 S3 S4 SA; unfold nfix; lia].
        + intros _. apply (KSL k'); [exact Hk'| clear - S1 S2 S4; lia| clear - S3; lia| clear; lia]. }
    split. { (* [comment removed for export] *)
      change (hm_regions h' m') with (hm_regions h m').
      apply (hm_regions_frame m m' WM' h GR WR). intros c' Hc'. change (h_L h) with L.
      pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as WRc'. cbn zeta in WRc'. ddestruct WRc' as (_ & AUMU' & AUCS' & MUAL' & MULIM' & _ & MFAL' & MFAB' & NF4' & _).
      unfold kUserLimit in MULIM'. unfold kFreeArrayMapSize, kFreeArraySize in MFAL', MFAB'. unfold kUserMapSize in MUAL'.
      assert (RBLO' : SB <= region_beg L c') by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
      assert (RBHI' : region_beg L c' + 2^32 <= SB + 2^37) by (unfold region_beg, kRegionSize; fold SB; clear - Hc'; nia).
      pose proof (class_size_range c' Hc') as CSR'.
      assert (ERI : ri_base L = SB + 2^37) by (unfold ri_base, space_end, kSpaceSize; fold SB; reflexivity).
      split; [| split; [| split]].
      + (* [comment removed for export] *)
        apply (KTN (ri_tr L)); try solve [intros; discriminate].
        * unfold tr_of. rewrite !in_app_iff. do 4 right. left. left. reflexivity. * reflexivity.
        * unfold ri_tr, ri_addr. cbn [t_lo]. clear - Hc'. lia. * unfold ri_tr, ri_addr, t_hi. cbn [t_lo t_len]. clear - Hc'. lia. * clear; lia.
        * destruct (tr_apart AL h mo _ _ HK0 ltac:(unfold tr_of; rewrite !in_app_iff; do 4 right; left; left; reflexivity) (tr_of_T h)) as [E|[XT|XT]]; [discriminate E| |];
            unfold t_hi, ri_tr, ri_addr in *; cbn [t_lo t_len] in XT; change (h_L h) with L in XT; fold T in XT; clear - XT Hc'; lia.
        * unfold ri_addr. rewrite ERI. clear - Hc' HULLB HPA. lia.
      + (* [comment removed for export] *)
        intros x Hx. set (j := (bv_unsigned x - fa_beg L c') / 2^18).
        pose proof (Z.div_mod (bv_unsigned x - fa_beg L c') (2^18) ltac:(clear; lia)) as DJ. pose proof (Z.mod_pos_bound (bv_unsigned x - fa_beg L c') (2^18) ltac:(clear; lia)) as MJ. fold j in DJ.
        pose proof (Z.div_mod (r_mapped_fa (h_reg h c')) (2^18) ltac:(clear; lia)) as DF.
        assert (HJ : 0 <= j < r_mapped_fa (h_reg h c') / kUserMapSize) by (unfold kUserMapSize; subst j; split; [apply Z.div_pos; clear - Hx; lia| apply Z.div_lt_upper_bound; [clear; lia|]; clear - Hx DF MFAL'; nia]).
        apply (KTN (funit_tr L c' j) (bv_unsigned x) 1); try solve [intros; discriminate].
        * apply tr_of_funit; [exact Hc'| exact HJ]. * reflexivity.
        * unfold funit_tr, kUserMapSize. cbn [t_lo]. clear - DJ MJ. lia. * unfold funit_tr, t_hi, kUserMapSize. cbn [t_lo t_len]. clear - DJ MJ. lia. * clear; lia.
        * destruct (tr_apart AL h mo _ _ HK0 (tr_of_funit h c' j Hc' HJ) (tr_of_T h)) as [E|[XT|XT]]; [discriminate E| |];
            unfold t_hi, funit_tr, kUserMapSize in *; cbn [t_lo t_len] in XT; change (h_L h) with L in XT; fold T in XT; clear - XT DJ MJ; lia.
        * unfold fa_beg, kFreeArrayOffset in *. clear - Hx MFAB' RBLO' RBHI' HULLB HPA. lia.
        * clear; lia.
      + (* [comment removed for export] *)
        pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC'. rewrite C16', Z.add_0_r in DC'.
        pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(clear; lia)) as DMU'. rewrite MUAL', Z.add_0_r in DMU'.
        assert (T8' : exists t, r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') = t * 8).
        { exists (2^15 * (r_mapped_user (h_reg h c') / 2^18) - 2 * (class_size c' / 16) * carved h c'). clear - DC' DMU' AUCS'. nia. }
        destruct T8' as [t ET].
        replace ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c')) / 8) with ((r_mapped_user (h_reg h c') - r_alloc_user (h_reg h c') + 7) / 8)
          by (rewrite ET, Z_div_mult, Z.div_add_l by (clear; lia); clear; cbn; lia).
        apply KSHS; [clear - RBLO' AUMU' SBLO; lia| clear - AUMU' MULIM' RBHI' HULLB ACE47; lia| clear - AUMU'; lia| | clear - RBLO' RBHI' AUMU' MULIM' HULLB HB6; lia].
        unfold region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DSB. rewrite SB16, Z.add_0_r in DSB. rewrite DSB.
        replace (2^16 * (SB / 2^16) + c' * 2^32 + r_alloc_user (h_reg h c')) with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + (class_size c' / 16) * carved h c' * 2)) by (clear - DC' AUCS'; nia).
        rewrite Z.mul_comm. apply Z_mod_mult.
      + (* [comment removed for export] *)
        intros k Hk.
        assert (AL8 : chunk_at L c' k mod 8 = 0).
        { unfold chunk_at, region_beg, kRegionSize. fold SB. pose proof (Z.div_mod SB (2^16) ltac:(clear; lia)) as DSB. rewrite SB16, Z.add_0_r in DSB. rewrite DSB.
          pose proof (class_size_mod16 c' Hc') as C16'. pose proof (Z.div_mod (class_size c') 16 ltac:(clear; lia)) as DC.
          rewrite C16', Z.add_0_r in DC. rewrite DC. replace (2^16 * (SB / 2^16) + c' * 2^32 + k * (16 * (class_size c' / 16))) with (8 * (SB / 2^16 * 2^13 + c' * 2^29 + k * (class_size c' / 16) * 2)) by (clear; lia). rewrite Z.mul_comm. apply Z_mod_mult. }
        assert (KHI : (k + 1) * class_size c' <= r_alloc_user (h_reg h c')) by (rewrite AUCS'; rewrite AUCS' in Hk; rewrite Z.mul_comm in Hk; rewrite Z.div_mul in Hk by (clear - CSR'; lia); clear - Hk CSR'; nia).
        replace 1 with ((1 + 7) / 8) by reflexivity. apply KSHS; [ | | clear; lia| exact AL8|].
        * unfold chunk_at. clear - RBLO' SBLO Hk CSR'. nia.
        * unfold chunk_at. clear - KHI AUMU' MULIM' RBHI' HULLB CSR' ACE47. nia.
        * unfold chunk_at. clear - KHI AUMU' MULIM' RBLO' RBHI' HULLB HB6 CSR' Hk. nia. }
    split. { (* [comment removed for export] *)
      change (hm_quar h' m') with (hm_quar h m').
      apply (hm_quar_frame m m' WM' h GQ).
      - eapply (iagree_of_windows2 _ nzoneS 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
      - change (h_L h) with L. fold T. apply KTP; clear; lia.
      - intros b Hb. ddestruct WQ as ((T1q & _) & (G1q & _) & _).
        assert (WBA : wf_batch h b) by (apply in_app_iff in Hb; destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) T1q b Hb)| exact (proj1 (Forall_forall _ _) G1q b Hb)]).
        ddestruct WBA as (_ & _ & _ & i & Hi & EB). rewrite EB. unfold kBatchClass in *. change (h_L h) with L in Hi, EB |- *.
        pose proof (WR 24 ltac:(unfold kNumClasses; clear; lia)) as WR24. cbn zeta in WR24. ddestruct WR24 as (_ & AUMU' & AUCS' & _ & MULIM' & _). unfold kUserLimit in MULIM'.
        assert (KHI : (i + 1) * 8192 <= r_alloc_user (h_reg h 24)) by (rewrite AUCS'; change (class_size 24) with 8192; clear - Hi; lia).
        apply (KU 24); [clear; lia| unfold chunk_at; change (class_size 24) with 8192; clear - Hi; lia| unfold chunk_at; change (class_size 24) with 8192; clear - KHI AUMU'; lia| clear; lia]. }
    split. { (* [comment removed for export] *)
      unfold hm_sec. cbv delta [h']. unfold sec_h. cbn [h_L h_sec h_pa_committed s_chunks s_nres]. change (Ls h) with L. cbn zeta. fold PA. change (APopSec.cks h) with cks.
      rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. fold ncks.
      ddestruct LI' as (LA & (st' & LB' & LST') & (bsl' & LC & LBSL') & LD & (g0' & g1' & LE)).
      apply (proj1 (rw_cells_app asegs m' (A_INSTANCE + 112) [C8 (Z_to_bv 64 (16384 * r')); C8 (Z_to_bv 64 (ncks + 1))] [C1 (Z_to_bv 8 0)])) in LA as [LA1 LA2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LA2. replace (A_INSTANCE + 112 + 16) with (A_INSTANCE + 128) in LA2 by (clear; lia).
      split; [exact LA1|]. split; [exists (Z_to_bv 8 0); exact LA2|]. split; [exists st'; exact (conj LB' LST')|]. split; [exists bsl'; exact (conj LC LBSL')|]. split; [exact LD|]. split; [dexists g0', g1'; exact LE|].
      split. { rewrite map_app. cbn [map s_map_beg newsh]. fold ps. exact HPS'. }
      split. { exists rest'. split; [exact HREST'| clear - LREST'; lia]. }
      intros i sh Hi. destruct (Nat.lt_ge_cases i (length cks)) as [LT|GE].
      - rewrite nth_error_app1 in Hi by exact LT. pose proof (nth_error_In _ _ Hi) as Hsh. destruct (HD i sh Hi) as [H1 H2]. pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & BIG & _).
        split; [| eapply wr_at_transport; [exact H2| exact WM']].
        eapply keep_rw; [exact H1| | exact WM']. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        pose proof (SLOT0) as _.
        destruct (lit_apart_hull AL h mo _ (l_pa L, kPaHullLen) HK0 (tr_of_sec h sh Hsh) eq_refl ltac:(right; left; reflexivity)) as [XP|XP];
          unfold t_hi, sec_tr, kPaHullLen in XP; cbn [t_lo t_len fst snd] in XP; change (h_L h) with L in XP; fold PA in XP;
          (apply (KTN (sec_tr sh) (s_map_beg sh) 32); try solve [intros; discriminate];
           [apply tr_of_sec; exact Hsh| reflexivity| intros b Hb; exact (sec_not_node AL h mo sh b HK0 Hsh Hb)
           | unfold sec_tr; cbn [t_lo]; clear; lia| unfold sec_tr, t_hi; cbn [t_lo t_len]; clear - BIG; lia| clear; lia| pose proof (TSEC sh Hsh) as X; clear - X BIG; lia| clear - XP BIG; lia]).
      - rewrite nth_error_app2 in Hi by exact GE. destruct (i - length cks)%nat as [|jx] eqn:EJ; [| cbn in Hi; destruct jx; discriminate Hi].
        cbn in Hi. injection Hi as <-. cbn [s_map_beg s_map_size s_size newsh]. change (APopSec.ms n) with ms.
        replace (Z.of_nat i) with ncks by (subst ncks; clear - GE EJ; lia).
        split; [exact HDRA|].
        (* [comment removed for export] *)
        pose proof (rw_cells_wr_at asegs m' a _ 32 HDRA ltac:(cbn; clear; lia)) as W0.
        pose proof (rw_cells_wr_at asegs m' (a + 32) _ 4064 ZA ltac:(cbn; clear; lia)) as W1.
        pose proof (rw_cells_wr_at asegs m' AB _ 16 MG' ltac:(cbn; clear; lia)) as W2.
        pose proof (rw_cells_wr_at asegs m' (AB + 16) _ 2016 ZAB ltac:(cbn; clear; lia)) as W3.
        pose proof (rw_cells_wr_at asegs m' CHB _ 16 HDR' ltac:(cbn; clear; lia)) as W4.
        pose proof (rw_cells_wr_at asegs m' UB _ 4096 UBF ltac:(cbn; clear; lia)) as W5.
        pose proof (rw_cells_wr_at asegs m' (UB + 4096) _ (a + ms - UB - 4096) ZU ltac:(cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - UBLE NLO; lia); clear; lia)) as W6.
        subst CHB UB AB.
        replace ms with (32 + (4064 + (16 + (2016 + (16 + (4096 + (a + ms - (a + 4096 + 2048) - 4096))))))) by (clear; lia).
        apply wr_at_join; [exact W0| | clear; lia| clear - UBLE NLO; lia].
        apply wr_at_join; [exact W1| | clear; lia| clear - UBLE NLO; lia]. replace (a + 32 + 4064) with (a + 4096) by (clear; lia).
        apply wr_at_join; [exact W2| | clear; lia| clear - UBLE NLO; lia].
        apply wr_at_join; [exact W3| | clear; lia| clear - UBLE NLO; lia]. replace (a + 4096 + 16 + 2016) with (a + 4096 + 2048 + -16) by (clear; lia).
        apply wr_at_join; [exact W4| | clear; lia| clear - UBLE NLO; lia]. replace (a + 4096 + 2048 + -16 + 16) with (a + 4096 + 2048) by (clear; lia).
        apply wr_at_join; [exact W5| exact W6| clear; lia| clear - UBLE NLO; lia]. }
    split. { (* [comment removed for export] *)
      change (hm_fake h' LF m') with (hm_fake h LF m').
      apply (hm_fake_frame m m' WM' h LF GF); change (h_L h) with L.
      - unfold lowhigh in FSLO. clear - FSLO. lia.
      - apply KFS; unfold kFakeBytes; clear; lia.
      - intros FB nn IN. dpose (frame_bounds STKLO h LB LF m HOK HM0 (FB, nn) IN) as (G1 & G2 & G3). cbn [fst snd] in G1, G2, G3. change (h_L h) with L in G1, G2.
        apply KFS; [clear - G1 G3; lia| clear - G2 G3; lia| clear; lia]. }
    (* [comment removed for export] *)
    split. { change (hm_ia h' m') with (hm_ia h m'). apply (hm_ia_frame m m' WM' h GI). eapply (iagree_of_windows2 _ nzoneS 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN]. }
    (* [comment removed for export] *)
    apply (hm_emb_frame_i m m' WM' h _ GEMB); [reflexivity| reflexivity|]. eapply (iagree_of_windows2 _ nzoneS 0x10000 0x65f000 m m'); [vm_compute; reflexivity| vm_compute; reflexivity| exact KIMGN].
  Qed.
End MSECSPLIT.

End ARUN_1.
