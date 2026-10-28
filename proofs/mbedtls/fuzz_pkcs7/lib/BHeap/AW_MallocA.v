(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0252f2d0a2973a61 0 6 1 16 17 16 19 16 20 16 21 16 22 16P02be8f08163fa23d 0 4 0 16 18 16 20 16 21 16P02c688947571da14 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P02d13fd5e8d9aec0 0 4 0 16 18 16 20 16 21 16P02fedef9edd12d65 0 4 0 16 18 16 20 16 21 16P03c736af4ad4ea04 0 4 0 16 18 16 20 16 21 16P03d9c8d49714e47b 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P04d673946fe621ad 0 4 0 16 18 16 20 16 21 16P04d75214a8204d20 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P053b58346f07190f 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P07360ad7925d79a9 0 6 1 16 17 16 19 16 20 16 21 16 22 16P07f8377e1e55c1d5 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P080c1a3ba4b76c24 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P082d6a9924061e55 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P08bf57db3086999b 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P097291bb953dfcd8 0 6 1 16 17 16 19 16 20 16 21 16 22 16P09cc262096cc31ee 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P0c3b68d332b892c7 0 4 0 16 18 16 20 16 21 16P0c50df0ae67ec8ac 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P0dfa52ad95268122 0 4 0 16 18 16 20 16 21 16P0f3f9a415d767b8e 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P0fec7f977512a943 0 4 0 16 18 16 20 16 21 16P101bc61d4ed26505 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P104e2618defca055 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P10b03275fb3ddc0e 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P110bfb83929da72c 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P11b62add4a8caa64 0 6 1 16 17 16 19 16 20 16 21 16 22 16P120f910db84b8541 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P122a8b0975256a4e 0 4 0 16 18 16 20 16 21 16P128f7a27963fd620 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P13743cbae911ad6b 0 4 0 16 18 16 20 16 21 16P158523b0b906d6f0 0 4 0 16 18 16 20 16 21 16P1607eb26570b6d4e 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P163a5a4edc7b4b9f 0 4 0 16 18 16 20 16 21 16P16988c5214cd70ab 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P17401de98b9c3185 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P1757665a51943c2c 0 6 1 16 17 16 19 16 20 16 21 16 22 16P1971e5faa470767e 0 4 0 16 18 16 20 16 21 16P1bb5d89dc8604254 0 4 0 16 18 16 20 16 21 16P1c4d67c42f8808de 0 4 0 16 18 16 20 16 21 16P1cd047ea2fa98031 0 4 0 16 18 16 20 16 21 16P1d4296f4a56a0f4b 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P1e275659424e6e12 0 4 0 16 18 16 20 16 21 16P1ff477aba5e01e6b 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P20fed247cf457724 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P21e85eb4f10a330e 0 4 0 16 18 16 20 16 21 16P221d4c3e0ad292c3 0 4 0 16 18 16 20 16 21 16P228e146edef9dce0 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P23fb7647f080f86c 0 4 0 16 18 16 20 16 21 16P2403bf4f2556b62c 0 4 0 16 18 16 20 16 21 16P2441844271e910dc 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P2483154ec9820652 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P24edfa659ed0aaae 0 4 0 16 18 16 20 16 21 16P2508432b56f6f78b 0 4 0 16 18 16 20 16 21 16P269944348675d8d1 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P271a8c53fdf057bd 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P2724be7196d6be88 0 4 0 16 18 16 20 16 21 16P279e88d69ed7cce4 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P28dd4b9d76368c5b 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P29d89a655187ca0e 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P2b5330f4a9cb2bab 0 4 0 16 18 16 20 16 21 16P2bebdb0bdd541736 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P2d49c5f450bfe5dd 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P2e1601e7c736849a 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P2e6828ac34f86ca3 0 4 0 16 18 16 20 16 21 16P2e8b3227001eaed6 0 4 0 16 18 16 20 16 21 16P2f942f741a5f6b8e 0 4 0 16 18 16 20 16 21 16P3110d237d008fb6d 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P319d6c652760e994 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P3294de8df6ba40ab 1 2 16 2 0 1 22 1 16 2 1 1 21 1 2 23 1 24 1P331689b2f808f0b0 0 4 0 16 18 16 20 16 21 16P33a2ee8c6b4f97cd 0 6 1 16 17 16 19 16 20 16 21 16 22 16P33b905cbc89c6ceb 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P342ce2afadd6e374 0 6 1 16 17 16 19 16 20 16 21 16 22 16P34b8fc14528d99e2 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P39a25e93e8caf437 0 4 0 16 18 16 20 16 21 16P39c2469c2d139279 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P39e4d731b5f3d427 0 4 0 16 18 16 20 16 21 16P3abf3828075920f4 0 4 0 16 18 16 20 16 21 16P3d4ecb50a197ba59 1 1 16 2 1 1 21 1 5 17 1 19 1 20 1 22 1 23 16P3d6ea40c21664c1f 0 4 0 16 18 16 20 16 21 16P3f11522007e12bb3 0 4 0 16 18 16 20 16 21 16P3f3695462cfc5046 0 4 0 16 18 16 20 16 21 16"%lxh.
Ltac2 gd_tbl_AW_MallocA () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Nat.mul"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_PC_MALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_UNWIND_IMPL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "ARUN_1.A_MCS_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "ARUN_1.A_CF_FASTUNW"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MallocA.mpro_post"; "ARUN_1.A_MALLOC"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MALLOC : Z := 0x69658.          (* [comment removed for export] *)
Definition A_MCS_CELL : Z := 0x10a6fc.       (* [comment removed for export] *)
Definition A_PC_MALLOC : Z := 0x69720.       (* [comment removed for export] *)
Definition A_CF_FASTUNW : Z := 0x19b54a.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_as_u64s : ltac2:(CDefT.buildp (gd_tbl_AW_MallocA ()) "Pk,$0.Pbs,(1.(2.&8.))P,(3.$0.(4.(2.&8.)R1.)(5.#8.R2.))(6.(1.(2.&40.))Lws,(1.(2.&40.))(7.(3.(1.(2.&8.))R3.(8.R1.))(3.$0.(4.(2.&40.)R1.)R4.)))")
(* [comment removed for export] *).
Proof.
  induction k as [|k IH]; intros bs Hl.
  - exists []. destruct bs; [split; reflexivity| cbn in Hl; lia].
  - destruct (IH (skipn 8 bs)) as (ws & E & L). { rewrite skipn_length. lia. }
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [| cbn; lia].
    cbn [u64s flat_map]. change (flat_map le8 ws) with (u64s ws). rewrite <- E.
    rewrite le8_le_bytes_to_word by (rewrite firstn_length; lia). symmetry. apply firstn_skipn.
Qed.
Lemma u64arr_of_CB : ltac2:(CDefT.buildp (gd_tbl_AW_MallocA ()) "Pm,P,(2.&40.)(9.(2.&8.))PA,$:.Pbs,(1.(2.&8.))Pk,$0.P,(;.$<.R4.R3.(=.$>.(?.(5.#8.R1.)R2.)(10.$>.)))(6.(1.(2.&40.))Lws,(1.(2.&40.))(7.(11.$<.R6.R5.R1.)(3.$0.(4.(2.&40.)R1.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros m A bs k RC. pose proof RC as [[[Hl _] _] _]. cbn [cell_wf] in Hl.
  pose proof (u8arr_of_rw_cells asegs m A _ bs RC) as [Hb Hw].
  destruct (bytes_as_u64s k bs Hl) as (ws & -> & L).
  exists ws. split; [|exact L]. split; [exact Hb|]. rewrite u64s_length in Hw.
  replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact Hw.
Qed.

Section MallocA.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition mpro_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 ra : word) (n lo : Z)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocA ()) "Lms',$12.(6.P,(2.&40.)(9.(2.&8.))Lm',P,(2.&40.)(9.(2.&8.))(6.(1.(2.&40.))Lws,(1.(2.&40.))(6.(1.(2.&8.))Lfr1,(1.(2.&8.))(6.(1.(2.&8.))Lfr2,(1.(2.&8.))ZSTK,$:.(13.O1>.-850.)(7.(3.$12.R6.(14.(15.(16.&40.+6977<.)(16.&40.R1.)O1=.O1<.O1;.O1:.O19.(16.&40.O1>.)(16.&40.O5.)(16.&40.R1.)(16.&40.$17.)(16.&40.O1>.)(16.&40.=)(16.&40.+1.)(16.&40.+1>.)O<.O;.(16.&40.$17.)(16.&40.+1.)(16.&40.R1.)(16.&40.(13.O1>.-51.))O12.O11.O10.O?.O>.O=.O:.O9.O8.O7.)O3.(16.&40.$18.)O2.(19.(2.&40.))R5.(1:.$<.)))(7.(1;.(=.(1<.$:.$:.)(1=.$:.$:.O4.O1>.)(10.(1<.$:.$:.)))O1.R5.)(7.(1>.$<.O1.R5.)(7.(1?.$<.R5.)(7.(;.$<.R5.(13.O1>.-38.)(=.$>.(20.O13.)(=.$>.(20.O14.)(=.$>.(20.O15.)(=.$>.(20.O16.)(=.$>.(20.O17.)(=.$>.(20.O18.)(=.$>.(20.O6.)(10.$>.)))))))))(7.(;.$<.R5.R1.(=.$>.(20.(16.&40.(13.R1.+10.)))(=.$>.(21.(16.&40.=))(=.$>.(21.(16.&40.=))(10.$>.)))))(7.(11.$<.R5.(13.R1.+10.)R4.)(7.(3.$0.(4.(2.&40.)R4.)#1>.)(7.(;.$<.R5.(13.R1.+100.)(=.$>.(?.#708.R3.)(10.$>.)))(7.(;.$<.R5.(13.R1.+808.)(=.$>.(20.(16.&40.O1>.))(10.$>.)))(7.(;.$<.R5.(13.R1.+810.)(=.$>.(?.#8.R2.)(10.$>.)))(22.$<.R5.O4.R1.))))))))))))))))")
(* [comment removed for export] *).

  Lemma malloc_pro : ltac2:(CDefT.buildp (gd_tbl_AW_MallocA ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$:.Pn,$:.Plo,$:.PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(9.(2.&8.))P,(7.(24.=R5.)(25.R5.(26.+2.+40.)))P,(27.$<.R2.$28.(=.$>.(29.(16.&8.+1.))(10.$>.)))P,(27.$<.R3.$2:.(=.$>.(21.(16.&40.+1>.))(10.$>.)))P,(27.$<.R4.$2;.(=.$>.(20.(16.&40.$2<.))(10.$>.)))P,(27.$<.R5.$2=.(=.$>.(29.(16.&8.+1.))(10.$>.)))P,(22.$<.R6.R9.R;.)P,(24.(2>.VhAR,)R:.)P,(24.R;.(2?.R=.+1000.))P,(24.R>.(26.+2.+3>.))P,(3.$:.(30.R?.+10.)=)P,(31.VCS,R>.(2?.R10.R>.))P,(1?.$<.R<.)(32.$<.VAL,VCS,(33.R12.R2>.R2=.R2<.R2;.R2:.R29.R28.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R22.R21.R16.R15.R14.R13.R2?.R11.R10.R?.R>.R=.)(14.(15.R2?.(16.&40.R12.)R2>.R2=.R2<.R2;.R2:.R29.R28.(16.&40.R11.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R?.(16.&40.$34.)R>.(19.(2.&40.))R=.(1:.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP n lo F fc m
      NB INI MCS GOTF FU ST LOIMG SPL SPH SPA SCS MI.
    unfold A_MALLOC, A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x71360] [] 120%N); lx_tree.
    (* [comment removed for export] *)
    apply evtA_done. unfold mpro_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      match goal with ST1 : stk _ mx (SP + -2112) (SP + -72), ST2 : stk _ mx (SP + -64) (SP + -56), ST0 : stk _ mx lo (SP + -2144),
                      FRd : rw_cells _ mx (SP + -2144) _ |- _ =>
        destruct (stk_split _ mx (SP + -2112) (SP + -1872) (SP + -72) ST1 ltac:(clear; lia)) as [STa STb];
        destruct (stk_carve _ mx _ _ 240 STa ltac:(clear; lia)) as [_ [tr FTR]];
        destruct (stk_carve _ mx _ _ 1800 STb ltac:(clear; lia)) as [_ [fr1 FR1]];
        destruct (stk_carve _ mx _ _ 8 ST2 ltac:(clear; lia)) as [_ [fr2 FR2]];
        replace (SP + -1872 - Z.of_nat 240) with (SP + -2128 + 16) in FTR by (clear; lia);
        replace (SP + -72 - Z.of_nat 1800) with (SP + -2128 + 256) in FR1 by (clear; lia);
        replace (SP + -56 - Z.of_nat 8) with (SP + -2128 + 2064) in FR2 by (clear; lia);
        chunk_split FRd 2%nat FRx FR0; lx_release ST0 FRx STK0; clear FRx ST0 ST1 ST2 STa STb;
        replace (SP + -2144 + Z.of_nat 16) with (SP + -2128) in STK0 by (clear; lia);
        replace (SP + -2144 + 16) with (SP + -2128) in FR0 by (clear; lia);
        chunk_split FR0 1%nat FRp FRz;
        apply (rw_cells_reshape asegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in FRz; [| cbn; tauto| vm_compute; reflexivity];
        change 240%nat with (8 * 30)%nat in FTR; destruct (u64arr_of_CB _ _ _ 30 FTR) as (ws & HTR & HL)
      end
    end.
    lx_exs; cbv zeta; lx_ands;
      [> reflexivity | assumption | assumption | assumption | assumption
       | apply (proj2 (rw_cells_app asegs _ (SP + -2128) [C8 _] [C4 _; C4 _])); split;
           [replace (SP + -2128 + 16) with (SP + -2112) by (clear; lia); exact FRp| cbn [cells_size csize Nat.add]; exact FRz]
       | exact HTR | exact HL | exact FR1
       | match goal with H0 : rw_cells _ _ (SP + -72) _ |- _ => replace (SP + -2128 + 2056) with (SP + -72) by (clear; lia); exact H0 end
       | exact FR2 | exact STK0 ].
  Qed.
End MallocA.

End ARUN_1.
