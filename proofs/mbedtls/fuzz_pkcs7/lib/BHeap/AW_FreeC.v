(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset AW_IAInit AW_Dealloc AW_FreeA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_FreeC () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MCS_CELL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_CF_FASTUNW"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.fsegA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE_RA2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_PC_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.A_ASAN_FREE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_W"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_cells"].

Section ARUN_1. Context {hAR : arun}.
Definition fsegA_statics (m : mem) (T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeC ()) "(0.(1.$2.O3.$3.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O3.$9.(4.$5.(:.(7.&40.+1>.))(8.$5.)))(0.(1.$2.O3.$;.(4.$5.(<.(7.&40.$=.))(8.$5.)))(0.(1.$2.O3.$>.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O3.$?.(4.$5.(<.(7.&40.$10.))(8.$5.)))(0.(1.$2.O3.$10.(4.$5.(<.(7.&40.+1000.))(8.$5.)))(0.(1.$2.O3.$11.(4.$5.(6.(7.&8.+1.))(4.$5.(12.#3.(4.(13.&8.)(7.&8.=)(4.(13.&8.)(7.&8.=)(4.(13.&8.)(7.&8.=)(8.(13.&8.))))))(4.$5.(:.(7.&40.=))(8.$5.)))))(0.(1.$2.O3.$14.(4.$5.(<.(7.&40.$15.))(8.$5.)))(0.(1.$2.O3.$15.(4.$5.(<.(7.&40.O1.))(8.$5.)))(1.$2.O3.(16.O1.+98.)(4.$5.(<.(7.&40.O2.))(8.$5.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma fsegA_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_FreeC ()) "PW,(17.$18.)Pm,P,(13.&40.)(19.(13.&8.))Pm',P,(13.&40.)(19.(13.&8.))PT,$1:.PCTX,$1:.P,(1;.R4.R2.R1.)P,(1<.R6.R5.R4.)P,PA,$1:.Pn,$1:.P,(1=.(0.(1>.+10000.R2.)(1>.(16.R2.R1.)$1?.))(1=.(0.(1>.(16.$1?.+81030.)R2.)(1>.(16.R2.R1.)$20.))(0.(1>.(16.$20.+4.)R2.)(1>.(16.R2.R1.)+65?000.))))(21.R:.R3.R2.)P,(21.R8.(16.R4.+98.)+8.)(1;.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' T CTX S MU DJ DJC. unfold fsegA_statics in *.
  unfold A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_GOT_PAGESZ, A_PAGESZ_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_IA, A_IA_INIT in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| first [exact DJC| apply DJ; cbn; lia]]).
Qed.


Section FreeC.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition fsegA_post (SP : Z) (gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 : word) (F : bvmap 5 word) (fc : bv 32)
      (p lo T TOP d : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeC ()) "Lms',$22.(23.(13.&40.)Lt0,(13.&40.)(23.(13.&40.)Lt1,(13.&40.)(23.(13.&40.)Lt2,(13.&40.)(23.(13.&40.)La3,(13.&40.)(23.(13.&40.)La4,(13.&40.)(23.(13.&40.)La5,(13.&40.)(23.(13.&40.)La6,(13.&40.)(23.(13.&40.)La7,(13.&40.)(23.(13.&40.)Lt3,(13.&40.)(23.(13.&40.)Lt4,(13.&40.)(23.(13.&40.)Lt5,(13.&40.)(23.(13.&40.)Lt6,(13.&40.)(23.P,(13.&40.)(19.(13.&8.))Lm',P,(13.&40.)(19.(13.&8.))(23.(17.(13.&40.))Lws,(17.(13.&40.))(23.$1:.Lsize,$1:.(23.(17.(13.&8.))Lfr1,(17.(13.&8.))(23.(17.(13.&8.))Lfr2,(17.(13.&8.))ZSTK,$1:.(16.O17.-850.)(0.(24.$22.R13.(25.(26.(7.&40.$27.)(7.&40.R1.)O16.(7.&40.$28.)R12.R11.R10.(7.&40.O17.)(7.&40.O6.)(7.&40.O6.)(7.&40.R1.)(7.&40.+1.)R?.R>.R=.R<.R;.(7.&40.$29.)(7.&40.+1.)(7.&40.R1.)(7.&40.(16.O17.-51.))O11.O10.O?.O>.O=.O<.R:.R9.R8.R7.)O8.(7.&40.$2:.)O7.(2;.(13.&40.))R6.(2<.$2.)))(0.(1<.(4.(2=.$1:.$1:.)(2>.$1:.$1:.(16.O4.+<60.)(16.O4.+<61.))(2?.O5.O17.))O1.R6.)(0.(30.$2.O1.R6.)(0.(31.$2.R6.)(0.(32.$2.R6.(16.O17.-38.)(4.$5.(<.O12.)(4.$5.(<.O13.)(4.$5.(<.O14.)(4.$5.(<.O15.)(4.$5.(<.O9.)(4.$5.(<.O:.)(4.$5.(<.O;.)(8.$5.)))))))))(0.(32.$2.R6.R1.(4.$5.(<.(7.&40.(16.R1.+10.)))(4.$5.(<.(7.&40.R4.))(8.$5.))))(0.(33.$2.R6.(16.R1.+10.)R5.)(0.(24.$34.(35.(13.&40.)R5.)#1>.)(0.(0.(1>.+1.R4.)(1>.R4.+1>.))(0.(1>.R4.(16.O2.+2.))(0.(32.$2.R6.(16.R1.+100.)(4.$5.(12.#708.R3.)(8.$5.)))(0.(32.$2.R6.(16.R1.+808.)(4.$5.(<.(7.&40.O17.))(8.$5.)))(0.(32.$2.R6.(16.R1.+810.)(4.$5.(12.#8.R2.)(8.$5.)))(0.(32.$2.R6.(16.O4.+<60.)(4.$5.(6.(7.&8.=))(8.$5.)))(0.(36.$2.R6.O5.R1.)(0.(36.$2.R6.(16.O17.-10.)(37.O3.O17.))(38.R6.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma fsegA : forall
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP p lo T CTX TOP LO TOPU d : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ia : bool) (cs2 cs4 cs5 : list cell) (p0 p1 : word),
      0 <= p < 2^47 ->
      (* [comment removed for export] *)
      rw_cells asegs m A_IA_INIT [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)] ->
      rw_cells asegs m A_IA [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))] ->
      rw_cells asegs m (A_IA + 0x40040) cs2 -> Z.of_nat (cells_size cs2) = 0xd80 ->
      rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] ->
      (ia = true -> p0 = Z_to_bv 64 4096 /\ p1 = Z_to_bv 64 (A_IA + 0x40dd0)) ->
      rw_cells asegs m (A_IA + 0x40dd0) cs4 -> Z.of_nat (cells_size cs4) = 0x40248 - 16 ->
      rw_cells asegs m (A_IA + 0x81008) cs5 -> Z.of_nat (cells_size cs5) = 40 ->
      fsegA_statics m T CTX ->
      ro_cells asegs m (T + 8) [C8 (Z_to_bv 64 TOP); C8 (Z_to_bv 64 (TOP - 2^23))] -> ro_cells asegs m (T + 40) [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
      2^23 <= TOP -> TOP <= 2^47 -> SP + 16 <= 2^47 ->
      Timg T -> T + 4096 <= ACEIL -> 0x65f000 <= CTX -> CTX + 0x10000 <= ACEIL ->
      (T + 4096 <= CTX \/ CTX + 0x10000 <= T) -> crange CS T 4096 -> crange CS CTX 0x10000 ->
      stk asegs m SP TOP -> crange CS SP (TOP - SP) ->
      LO <= lo -> TOP <= TOPU <= 2^64 -> uwc asegs m LO TOPU (bv_unsigned s0) SP d ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 4096 -> SP mod 16 = 0 ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (fsegA_post SP gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 F fc p lo T TOP d m)
        (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_FREE) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p lo T CTX TOP LO TOPU d F fc m ia cs2 cs4 cs5 p0 p1
      NB IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 MS8 THR TSW UNW TOP0 TOP1 TOP2 T0 T1 CX0 CX1 TC TCS CTXCS STT STCS LOB TOPUB UWC ST LOIMG SPL SPA SCS MI.
    facts. dpose MS8 as (INI & MCS & GOTF & FU & GOT & PGS & TSD & TPC & TSA & CTH).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (free_pro AL IMG ALWF CS CSOK ia ra gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p lo F fc m cs2 cs4 cs5 p0 p1);
        [exact NB | exact IA1 | exact IA2 | exact IA3 | exact IA4 | exact IS4 | exact IA5 | exact IP | exact IA6 | exact IS6 | exact IA7 | exact IS7
        | exact GOT | exact PGS | exact MCS | exact GOTF | exact FU | exact ST | exact LOIMG | exact SPL | exact SPH | exact SPA | exact SCS | exact MI]. }
    clear IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7.
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (a6x & m1 & ws & fr1 & fr2 & -> & MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL & F1800 & TFB & F8 & ST1 & IAC1)).
    assert (LO1 : forall A k, A + k <= lo -> ((A + k <= A_IA \/ A_IA + 0x81030 <= A) /\ (A + k <= A_IA_INIT \/ A_IA_INIT + 4 <= A)) -> disjoint_from (ia_W lo SP) A k)
      by (intros A k H [H1 H2]; unfold ia_W, A_IA, A_IA_INIT in *; cbn [disjoint_from]; clear - H H1 H2; repeat split; lia).
    assert (MS1 : fsegA_statics m1 T CTX).
    { eapply (fsegA_statics_transport _ m m1 T CTX MS8 MU1); [intros A k H; apply LO1; [unfold A_IA, A_IA_INIT in H; clear - H LOIMG; lia| unfold A_IA, A_IA_INIT in *; clear -H; lia]| apply LO1; [clear - CX1 LOIMG; lia| unfold A_IA, A_IA_INIT; clear -CX0; lia]]. }
    dpose MS1 as (INI1 & MCS1 & GOTF1 & FU1 & GOT1 & PGS1 & TSD1 & TPC1 & TSA1 & CTH1).
    assert (THR1 : ro_cells asegs m1 (T + 8) [C8 (Z_to_bv 64 TOP); C8 (Z_to_bv 64 (TOP - 2^23))])
      by (eapply ro_cells_transport; [exact THR| exact MU1| apply LO1; [cbn; clear - T1 LOIMG; lia| unfold A_IA, A_IA_INIT; cbn; clear -T0; lia]]).
    assert (TSW1 : ro_cells asegs m1 (T + 40) [C1 (Z_to_bv 8 0)])
      by (eapply ro_cells_transport; [exact TSW| exact MU1| apply LO1; [cbn; clear - T1 LOIMG; lia| unfold A_IA, A_IA_INIT; cbn; clear -T0; lia]]).
    assert (UNW1 : rw_cells asegs m1 (T + 3168) [C1 (Z_to_bv 8 0)])
      by (eapply rw_cells_transport; [exact UNW| exact MU1| exact WM1| apply LO1; [cbn; clear - T1 LOIMG; lia| unfold A_IA, A_IA_INIT; cbn; clear -T0; lia]]).
    assert (STT1 : stk asegs m1 SP TOP)
      by (eapply stk_transport_disjoint; [exact STT| exact MU1| exact WM1| unfold ia_W, A_IA, A_IA_INIT; cbn [disjoint_from]; clear -SPL LOIMG TOP2; repeat split; lia]).
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m1 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR7) as [_ FRhi0].
    cbn [cells_size csize Nat.add] in FRhi0. replace (SP + -56 + Z.of_nat 40) with (SP + -16) in FRhi0 by (clear; lia).
    pose proof (proj1 (rw_cells_app asegs m1 (SP + -16) [C8 s0] [C8 ra]) FRhi0) as [FS0 _].
    rewrite <- (Z_to_bv_bv_unsigned s0) in FS0.
    pose proof (bv_unsigned_in_range 64 s0) as VR. unfold bv_modulus in VR. change (2 ^ Z.of_N 64) with (2^64) in VR.
    assert (UWC1 : uwc asegs m1 LO TOPU (bv_unsigned s0) SP d).
    { eapply (uwc_munch asegs _ m m1); [exact UWC| exact MU1| clear - LOIMG SPL; lia| clear - TOPUB; lia|].
      intros a Ha. unfold ia_W, A_IA, A_IA_INIT. cbn [outside]. clear - Ha LOIMG SPL T1. repeat split; lia. }
    clear INI MCS GOTF FU GOT PGS TSD TPC TSA CTH THR TSW UNW STT MS8 FRhi0.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m1 (SP + -2128) [C8 _] _) STKC) as [SK0 SK1]. cbn [cells_size csize Nat.add] in SK1.
    pose proof (proj1 (rw_cells_app asegs m1 _ [C4 _] _) SK1) as [SK8 SK12]. cbn [cells_size csize Nat.add] in SK12. clear STKC SK1.
    replace (SP + -2128 + Z.of_nat 8) with (SP + -2128 + 8) in SK8 by lia. replace (SP + -2128 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2128 + 12) in SK12 by lia.
    (* [comment removed for export] *)
    assert (STT1' : stk asegs m1 SP (Z.max TOP SP)).
    { destruct (Z.le_gt_cases SP TOP) as [LE|GT]; [rewrite Z.max_l by (clear - LE; lia); exact STT1| rewrite Z.max_r by (clear - GT; lia); apply stk_empty; clear - TOP2 LOIMG SPL; lia]. }
    assert (SR1 : stk asegs m1 (SP + -16) (Z.max TOP SP)).
    { eapply stk_merge; [| exact STT1'| clear; lia].
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR7) as [_ FRhi].
      cbn [cells_size csize Nat.add] in FRhi. replace (SP + -56 + Z.of_nat 40) with (SP + -16) in FRhi by lia.
      pose proof (stk_of_rw_cells asegs m1 (SP + -16) _ FRhi) as X. cbn [cells_size csize Nat.add] in X.
      replace (SP + -16 + Z.of_nat 16) with SP in X by lia. exact X. }
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (unwind_impl_spec AL IMG ALWF CS CSOK (SP + -2128) A_PC_FREE SP TOP (TOP - 2^23) (SP + -16) (Z.max TOP SP) T CTX) with (LO := LO) (TOPU := TOPU);
        [ | | | | | | | | | | | clear - LOB SPL; lia | exact TOPUB | clear - T1 LOIMG SPL; lia
        | exact HL | exact SK8 | exact HTR | exact TFB | exact SR1 | exact (proj1 FS0) | exact UWC1 | exact VR
        | exact GOT1 | exact PGS1 | exact INI1 | exact TSD1 | exact TPC1 | exact TSA1 | exact CTH1 | exact THR1 | exact TSW1 | exact UNW1 | exact ST1 | clear - LOIMG; lia | clear - SPL; lia | clear; lia | | exact MI1 | reflexivity ].
      - clear - TOP2 TOP1 LOIMG SPL. lia.
      - intros x Hx. destruct (Z.lt_ge_cases x SP); [apply SCS; clear - Hx H SPL; lia| apply STCS; clear - Hx H; lia].
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear - SPL; lia| clear; lia].
      - clear - LOIMG SPL; lia.
      - clear - TOP0 TOP1; lia.
      - unfold A_PC_FREE. clear; lia.
      - clear - TOP1 TOP2 LOIMG SPL SPA. split; [lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as [q Hq]. exists (2 * q). lia.
      - exact TCS. - exact CTXCS.
      - clear - T0 T1 CX0 CX1. lia.
      - clear - T1 CX1 TC LOIMG. lia.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ws2 & size & -> &
                          MU2 & WM2 & MI2 & SZ2 & HTR2 & TFB2 & UNW2 & SZB & SZD & HL2 & ST2 & SR2)).
    replace (ret_pc (Z_to_bv 64 A_FREE_RA1)) with (Z_to_bv 64 A_FREE_RA1) by (unfold A_FREE_RA1; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    eapply evtA_cut. { eapply (free_mid AL IMG ALWF CS CSOK); clear -SPH SPL LOIMG; lia. }
    cbv beta. intros ms3 ->.
    (* [comment removed for export] *)
    assert (DJ2 : forall A k, (A + k <= lo \/ SP + -2128 + 2064 <= A) -> (A + k <= T + 3168 \/ T + 3169 <= A) ->
              disjoint_from [(SP + -2128 + 8, SP + -2128 + 12); (SP + -2128 + 16, SP + -2128 + 256); (SP + -2128 + 2056, SP + -2128 + 2064); (T + 3168, T + 3169); (lo, SP + -2128)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. clear - H1 H2 SPL. repeat split; lia. }
    assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR7| exact MU2| exact WM2| apply DJ2; cbn; clear - T1 LOIMG SPL; lia]).
    assert (SK0' : rw_cells asegs m2 (SP + -2128) [C8 (Z_to_bv 64 (SP + -2128 + 16))]).
    { eapply rw_cells_transport; [exact SK0| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (SK12' : rw_cells asegs m2 (SP + -2128 + 12) [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact SK12| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (F1800' : rw_cells asegs m2 (SP + -2128 + 256) [CB 1800 fr1])
      by (eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    assert (F8' : rw_cells asegs m2 (SP + -2128 + 2064) [CB 8 fr2])
      by (eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    clear FR7 SK0 SK12 F1800 F8 SK8 HTR TFB SR1 STT1 ST1 UNW1 FS0 UWC1.
    (* [comment removed for export] *)
    assert (STKC : rw_cells asegs m2 (SP + -2128) [C8 (Z_to_bv 64 (SP + -2128 + 16)); C8 (Z_to_bv 64 size)]).
    { apply (proj2 (rw_cells_app asegs m2 (SP + -2128) [C8 _] [C8 _])). split; [exact SK0'|]. cbn [cells_size csize Nat.add].
      eapply (rw_cells_reshape asegs m2 _ [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 0)]).
      - apply (proj2 (rw_cells_app asegs m2 _ [C4 _] [C4 _])). split; [replace (SP + -2128 + Z.of_nat 8) with (SP + -2128 + 8) by lia; exact SZ2|].
        cbn [cells_size csize Nat.add]. replace (SP + -2128 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2128 + 12) by lia. exact SK12'.
      - cbn. tauto.
      - cbn [cells_bytes cbytes]. rewrite (le8_split4 (Z_to_bv 64 size)). rewrite unsigned_lit by (clear - SZB; lia).
        rewrite Z.div_small by (clear - SZB; lia). rewrite <- app_assoc. reflexivity. }
    clear SK0' SK12' SZ2.
    (* [comment removed for export] *)
    apply evtA_done. unfold fsegA_post. deexists 12. dexists m2, ws2, size, fr1, fr2.
    split; [reflexivity|].
    split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
             eapply munch_weaken; [| exact MU2]. unfold sub_fp, ia_W; cbn [outside]. clear - SPL. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
    split; [exact FR7'|]. split; [exact STKC|]. split; [exact HTR2|]. split; [exact HL2|]. split; [exact SZB|]. split; [exact SZD|].
    split; [exact F1800'|]. split; [exact TFB2|]. split; [exact F8'|]. split; [exact UNW2|]. split; [exact ST2|]. split; [exact SR2|].
    eapply (ia_cells_transport _ _ _ IAC1 MU2 WM2); unfold A_IA, A_IA_INIT; cbn [disjoint_from]; clear -SPL LOIMG T0; repeat split; lia.
  Qed.
  #[using="IMG ALWF CSOK"] Lemma free_null_seg : forall
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP lo T CTX TOP : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ia : bool) (cs2 cs4 cs5 : list cell) (p0 p1 : word),
      (* [comment removed for export] *)
      rw_cells asegs m A_IA_INIT [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)] ->
      rw_cells asegs m A_IA [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (A_IA + 8) [CB (Z.to_nat 0x40000) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))] ->
      rw_cells asegs m (A_IA + 0x40040) cs2 -> Z.of_nat (cells_size cs2) = 0xd80 ->
      rw_cells asegs m (A_IA + 0x40dc0) [C8 p0; C8 p1] ->
      (ia = true -> p0 = Z_to_bv 64 4096 /\ p1 = Z_to_bv 64 (A_IA + 0x40dd0)) ->
      rw_cells asegs m (A_IA + 0x40dd0) cs4 -> Z.of_nat (cells_size cs4) = 0x40248 - 16 ->
      rw_cells asegs m (A_IA + 0x81008) cs5 -> Z.of_nat (cells_size cs5) = 40 ->
      fsegA_statics m T CTX ->
      ro_cells asegs m (T + 8) [C8 (Z_to_bv 64 TOP); C8 (Z_to_bv 64 (TOP - 2^23))] -> ro_cells asegs m (T + 40) [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
      2^23 <= TOP -> TOP <= 2^47 -> SP + 16 <= 2^47 ->
      Timg T -> T + 4096 <= ACEIL -> 0x65f000 <= CTX -> CTX + 0x10000 <= ACEIL ->
      (T + 4096 <= CTX \/ CTX + 0x10000 <= T) -> crange CS T 4096 -> crange CS CTX 0x10000 ->
      stk asegs m SP TOP -> crange CS SP (TOP - SP) ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 4096 -> SP mod 16 = 0 ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS
        (fun ms' => exists (m' : mem) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
           ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom asegs)
           /\ munch ((T + 3168, T + 3169) :: ia_W lo SP) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)] /\ stk asegs m' lo SP /\ stk asegs m' (SP + -16) (Z.max TOP SP) /\ ia_cells m')
        (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_FREE) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP lo T CTX TOP F fc m ia cs2 cs4 cs5 p0 p1
      IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 MS8 THR TSW UNW TOP0 TOP1 TOP2 T0 T1 CX0 CX1 TC TCS CTXCS STT STCS ST LOIMG SPL SPA SCS MI.
    eapply evtA_cut.
    { eapply (fsegA ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP 0 lo T CTX TOP lo TOP 28 F fc m ia cs2 cs4 cs5 p0 p1);
        [clear; lia | exact IA1 | exact IA2 | exact IA3 | exact IA4 | exact IS4 | exact IA5 | exact IP | exact IA6 | exact IS6 | exact IA7 | exact IS7
        | exact MS8 | exact THR | exact TSW | exact UNW | exact TOP0 | exact TOP1 | exact TOP2 | exact T0 | exact T1 | exact CX0 | exact CX1 | exact TC
        | exact TCS | exact CTXCS | exact STT | exact STCS | clear; lia | clear - TOP1; lia | apply uwc_cap; clear; lia
        | exact ST | exact LOIMG | exact SPL | exact SPA | exact SCS | exact MI]. }
    clear IA1 IA2 IA3 IA4 IS4 IA5 IP IA6 IS6 IA7 IS7 MS8 THR TSW UNW STT ST MI.
    cbv beta zeta. (intros ms1 dd_H; ddestruct dd_H as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & ws & size & fr1 & fr2 & -> &
                              MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL & SZB & SZD & F1800 & TFB & F8 & UNW1 & ST1 & SR1 & IAC1)).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dealloc_null AL IMG ALWF CS CSOK) with (lo := lo); [clear -SPL LOIMG SPH; lia| exact ST1| clear -LOIMG; lia| clear -SPL; lia| clear -SPH; lia| | exact MI1].
      eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (a0' & a1' & a2' & m2 & -> & MU2 & WM2 & MI2 & ST2)).
    replace (ret_pc (Z_to_bv 64 A_FREE_RA2)) with (Z_to_bv 64 A_FREE_RA2) by (unfold A_FREE_RA2; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (LO2 : forall A k, (A + k <= lo \/ SP + -2128 <= A) -> disjoint_from [(lo, SP + -2128)] A k) by (intros A k H; cbn [disjoint_from]; clear -H; lia).
    (* [comment removed for export] *)
    assert (CSJ : rw_cells asegs m2 (SP + -2128) ([C8 (Z_to_bv 64 (SP + -2128 + 16)); C8 (Z_to_bv 64 size)] ++ [CB 240 (u64s ws)] ++ [CB 1800 fr1] ++ [C8 (Z_to_bv 64 SP)] ++ [CB 8 fr2])).
    { apply (proj2 (rw_cells_app asegs m2 _ _ _)). split; [eapply rw_cells_transport; [exact STKC| exact MU2| exact WM2| apply LO2; cbn; clear; lia]|].
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m2 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16) with (SP + -2128 + 16) by (clear; lia).
        replace 240%nat with (length (u64s ws)) by (rewrite u64s_length, HL; reflexivity).
        apply rw_cells_of_u8arr. destruct HTR as [HB HW]. split.
        - eapply bytes_at_transport; [exact HB| exact MU2| apply LO2; rewrite u64s_length, HL; cbn; clear; lia].
        - rewrite u64s_length, HL. cbn [Nat.mul Z.of_nat]. eapply wr_at_transport; [| exact WM2]. rewrite HL in HW. exact HW. }
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m2 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240) with (SP + -2128 + 256) by (clear; lia).
        eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| apply LO2; cbn; clear; lia]. }
      cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app asegs m2 _ _ _)). split.
      { replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240 + Z.of_nat 1800) with (SP + -2128 + 2056) by (clear; lia).
        eapply rw_cells_transport; [exact TFB| exact MU2| exact WM2| apply LO2; cbn; clear; lia]. }
      cbn [cells_size csize Nat.add].
      replace (SP + -2128 + Z.of_nat 16 + Z.of_nat 240 + Z.of_nat 1800 + Z.of_nat 8) with (SP + -2128 + 2064) by (clear; lia).
      eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| apply LO2; cbn; clear; lia]. }
    cbn [app] in CSJ.
    assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR7| exact MU2| exact WM2| apply LO2; cbn; clear; lia]).
    eapply evtA_mono.
    { eapply (free_epi AL IMG ALWF CS CSOK ra gp (Z_to_bv 64 A_TP) t0' t1' t2' s0 s1 s2 s3 s4 s5 _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) (Z_to_bv 64 (SP + -2128)) (Z_to_bv 64 1) a6' a7'
                s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' SP lo F fc m2 m2 _ []);
        [exact CSJ| cbn; clear; lia| exact FR7'| exact ST2| clear -LOIMG; lia| exact SPL| exact SPH| apply munch_refl| apply wmono_refl| exact MI2| exact SCS]. }
    cbv beta. (intros ms3 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & ST3)).
    deexists 16. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU1|]. eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp, ia_W; cbn [outside]; clear -SPL; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
    split. { eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; clear -T1 LOIMG; lia]. eapply rw_cells_transport; [exact UNW1| exact MU2| exact WM2| apply LO2; cbn; clear -T1 LOIMG; lia]. }
    split; [exact ST3|].
    split. { destruct (stk_split asegs m3 lo (SP + -16) SP ST3 ltac:(clear -SPL LOIMG; lia)) as [_ ST3b].
             destruct (stk_split asegs m1 (SP + -16) SP (Z.max TOP SP) SR1 ltac:(clear; lia)) as [_ SR1b].
             eapply stk_merge; [exact ST3b| | clear -TOP2; lia].
             eapply stk_transport_disjoint; [| exact MU3| exact WM3| cbn; clear -TOP2; lia]. eapply stk_transport_disjoint; [exact SR1b| exact MU2| exact WM2| cbn; clear; lia]. }
    assert (MU13 : munch [(lo, SP); (T + 3168, T + 3169)] m1 m3).
    { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear -SPL; intros y Hy; lia. }
    eapply (ia_cells_transport _ _ _ IAC1 MU13); [eapply wmono_trans; [exact WM2| exact WM3] | unfold A_IA; cbn; clear -SPL LOIMG T0; lia | unfold A_IA_INIT; cbn; clear -SPL LOIMG T0; lia].
  Qed.
End FreeC.

End ARUN_1.
