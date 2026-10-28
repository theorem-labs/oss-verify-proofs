(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_Poison AW_AllocA AW_AllocB AW_MallocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0172f7c6b0ea2949 0 4 0 16 34 16 36 16 37 16P020dc47a28127ac7 0 4 0 16 34 16 36 16 37 16P025c83110c5890b4 0 4 0 16 34 16 36 16 37 16P02cc4f8ff97ea98f 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P034c04c04135f42f 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P03b8c01ceca571cd 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P03e3f65de47e1d57 0 4 0 16 34 16 36 16 37 16P0441ba6b81fa1f0d 0 4 0 16 34 16 36 16 37 16P05592cb4f76c6be3 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P062c0acbb16e2b69 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P065bbd11e8411dd4 0 4 0 16 34 16 36 16 37 16P07469808ddb4f565 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P0781383c363d7f05 0 6 1 16 33 16 35 16 36 16 37 16 38 16P07fd3ca10422bb08 0 4 0 16 34 16 36 16 37 16P08d0c150db8a0fef 0 4 0 16 34 16 36 16 37 16P08fded3dbb90f611 0 4 0 16 34 16 36 16 37 16P098fb82adc292540 0 4 0 16 34 16 36 16 37 16P0ab4521553623d15 0 4 0 16 34 16 36 16 37 16P0b0e7eaa21450225 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P0c2327c734d77b01 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P0c88d2651aa2c7e0 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P0cc75d0a6dfb333a 0 4 0 16 34 16 36 16 37 16P0d52a8214171ac42 0 4 0 16 34 16 36 16 37 16P0da33f4884148ee0 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P0dfe51bf4d0f0c7a 0 4 0 16 34 16 36 16 37 16P0e230b3b44cff942 0 4 0 16 34 16 36 16 37 16P0ed5d18099b3f887 0 4 0 16 34 16 36 16 37 16P0fc28d42cd1dfbec 0 4 0 16 34 16 36 16 37 16P11e01abb8d90d44d 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P121899b4dc90eb5e 0 4 0 16 34 16 36 16 37 16P12e3e4ec5b3cb618 0 4 0 16 34 16 36 16 37 16P133a034dc4542894 0 4 0 16 34 16 36 16 37 16P13977f479f1c597a 0 4 0 16 34 16 36 16 37 16P14904a8e26980a05 0 4 0 16 34 16 36 16 37 16P14b89eb4b465986c 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P15ab2c5096d56cf4 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P17375fbd4f0bee2e 0 6 1 16 33 16 35 16 36 16 37 16 38 16P17ce94254a9e279b 0 6 1 16 33 16 35 16 36 16 37 16 38 16P182ce0552a41d623 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P191642a24d807dfc 0 4 0 16 34 16 36 16 37 16P19fae484c63df7de 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P1a28790a1a498003 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P1b2195a3107e2550 0 4 0 16 34 16 36 16 37 16P1b3ae8d63c18e991 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P1b881937f49ed724 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P1bf63761c96bbd94 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P1c0fd9dc95eb95a3 0 4 0 16 34 16 36 16 37 16P1c300b617c94a3f7 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P1cf61225fa081da8 0 4 0 16 34 16 36 16 37 16P1fac3c7e80a3f47b 0 4 0 16 34 16 36 16 37 16P20446fab41233bb4 0 6 1 16 33 16 35 16 36 16 37 16 38 16P2190e273a592e86e 0 6 1 16 33 16 35 16 36 16 37 16 38 16P229d999e2c924cdd 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P24239419d2bb3639 0 4 0 16 34 16 36 16 37 16P255187fd9eef2db2 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P256cd00299526463 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P25d110d03357c918 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P26c4fcc936a4d17f 0 4 0 16 34 16 36 16 37 16P2d415d3377ef08fd 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P2de875aaeb05d09e 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P2e5709aff4629a9f 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P2ebc8c9e1ec89241 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P2f0108972b58dbd7 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P2f1f41f9a415580c 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P3197e5ebbf556e6b 0 4 0 16 34 16 36 16 37 16P3254b1ba2e339c2f 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P327f91d76a0dba33 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P33c4aa8ff159fbc2 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P343f816eba67ff92 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P34e5ff93adcdc71b 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P36a5c7757fbf595c 0 4 0 16 34 16 36 16 37 16P36ea7d8b5ae7cfe1 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P3742f80a6ec09da6 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P379ac9d2449bc115 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P38ae9e5abf8ad57f 0 4 0 16 34 16 36 16 37 16P38f35ab7c4241320 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P394b364ba5344d08 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P3991513d19208a16 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3998a1b9193571e6 0 6 1 16 33 16 35 16 36 16 37 16 38 16P39b0ec99ff10791e 0 4 0 16 34 16 36 16 37 16P3b0f4945640702d1 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3b1e6ecb55b07b0b 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P3be679906419dc22 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3bfd2380edb8eef5 0 4 0 16 34 16 36 16 37 16P3c491610209f0b3a 0 4 0 16 34 16 36 16 37 16P3d3629a810200de9 0 4 0 16 34 16 36 16 37 16P3efac594afb4e647 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3f5a901c7cdb0d3e 1 1 16 2 1 1 37 1 5 33 1 35 1 36 1 38 1 39 16P3fb7fb0141941ac2 0 4 0 16 34 16 36 16 37 16P3fd9bded3ecbc35d 0 4 0 16 34 16 36 16 37 16"%lxh.
Ltac2 gd_tbl_AW_CallocA () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_PC_CALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_UNWIND_IMPL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MCS_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_CF_FASTUNW"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.CallocA.cpro_post"; "ARUN_1.A_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Definition A_CALLOC : Z := 0x69880.          (* [comment removed for export] *)
Definition A_ASAN_CALLOC : Z := 0x4841c.     (* [comment removed for export] *)
Definition A_PC_CALLOC : Z := 0x69954.       (* [comment removed for export] *)

Section CallocA.
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
  Definition cpro_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 ra : word) (cnt sz lo : Z)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocA ()) "Lms',$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lws,(4.(2.&40.))(1.(4.(2.&8.))Lfr1,(4.(2.&8.))(1.(4.(2.&8.))Lfr2,(4.(2.&8.))(1.(4.(2.&8.))Lfr3,(4.(2.&8.))ZSTK,$5.(6.O1?.-858.)(7.(8.$0.R7.(9.(:.(;.&40.+699;0.)(;.&40.(6.O1?.-860.))O1>.O1=.O1<.O1;.O1:.(;.&40.O1?.)(;.&40.O5.)(;.&40.R1.)(;.&40.$<.)(;.&40.O1?.)(;.&40.=)(;.&40.+1.)(;.&40.+1>.)O=.O<.(;.&40.O6.)(;.&40.$<.)(;.&40.+1.)(;.&40.R1.)(;.&40.(6.O1?.-59.))O12.O11.O10.O?.O>.O;.O:.O9.O8.)O3.(;.&40.$=.)O2.(>.(2.&40.))R6.(?.$10.)))(7.(11.(12.(13.$5.$5.)(14.$5.$5.O4.O1?.)(15.(13.$5.$5.)))O1.R6.)(7.(16.$10.O1.R6.)(7.(17.$10.R6.)(7.(18.$10.R6.(6.O1?.-40.)(12.$19.(1:.O13.)(12.$19.(1:.O14.)(12.$19.(1:.O15.)(12.$19.(1:.O16.)(12.$19.(1:.O17.)(12.$19.(1:.O18.)(12.$19.(1:.O19.)(12.$19.(1:.O7.)(15.$19.))))))))))(7.(18.$10.R6.R1.(12.$19.(1:.(;.&40.(6.R1.+10.)))(12.$19.(1;.(;.&40.=))(12.$19.(1;.(;.&40.=))(15.$19.)))))(7.(1<.$10.R6.(6.R1.+10.)R5.)(7.(8.$1=.(1>.(2.&40.)R5.)#1>.)(7.(18.$10.R6.(6.R1.+100.)(12.$19.(1?.#708.R4.)(15.$19.)))(7.(18.$10.R6.(6.R1.+808.)(12.$19.(1:.(;.&40.O1?.))(15.$19.)))(7.(18.$10.R6.(6.R1.+810.)(12.$19.(1?.#8.R3.)(15.$19.)))(7.(18.$10.R6.(6.O1?.-860.)(12.$19.(1?.#8.R2.)(15.$19.)))(20.$10.R6.O4.(6.O1?.-860.)))))))))))))))))))")
(* [comment removed for export] *).

  Lemma calloc_pro : ltac2:(CDefT.buildp (gd_tbl_AW_CallocA ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$5.Pcnt,$5.Psz,$5.Plo,$5.PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(7.(22.=R6.)(23.R6.(24.+2.+40.)))P,(7.(22.=R6.)(23.R6.(24.+2.+40.)))P,(25.$10.R3.$26.(12.$19.(27.(;.&8.+1.))(15.$19.)))P,(25.$10.R4.$28.(12.$19.(1;.(;.&40.+1>.))(15.$19.)))P,(25.$10.R5.$29.(12.$19.(1:.(;.&40.$2:.))(15.$19.)))P,(25.$10.R6.$2;.(12.$19.(27.(;.&8.+1.))(15.$19.)))P,(20.$10.R7.R:.R=.)P,(22.(2<.VhAR,)R;.)P,(22.R<.(2=.R?.+1000.))P,(22.R10.(24.+2.+3>.))P,(8.$5.(2>.R11.+10.)=)P,(2?.VCS,R?.(2=.R12.R?.))P,(17.$10.R=.)(30.$10.VAL,VCS,(31.R14.R2?.R2>.R2=.R2<.R2;.R2:.R29.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R24.R23.R18.R17.R16.R15.R30.R13.R12.R11.R10.R?.R>.)(9.(:.R30.(;.&40.R14.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(;.&40.R13.)(;.&40.R12.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R10.(;.&40.$32.)R?.(>.(2.&40.))R>.(?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP cnt sz lo F fc m
      CB0 SZ0 INI MCS GOTF FU ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_CALLOC, A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x71360] [] 120%N).
    (* [comment removed for export] *)
    lx_stk_grow_to lo (SP + -2144).
    apply evtA_done. unfold cpro_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      match goal with ST1 : stk _ mx (SP + -2120) (SP + -80), ST2 : stk _ mx (SP + -72) (SP + -64), ST3 : stk _ mx (SP + -2144) (SP + -2136) |- _ =>
        destruct (stk_split _ mx (SP + -2120) (SP + -1880) (SP + -80) ST1 ltac:(clear; lia)) as [STa STb];
        destruct (stk_carve _ mx _ _ 240 STa ltac:(clear; lia)) as [_ [tr FTR]];
        destruct (stk_carve _ mx _ _ 1800 STb ltac:(clear; lia)) as [_ [fr1 FR1]];
        destruct (stk_carve _ mx _ _ 8 ST2 ltac:(clear; lia)) as [_ [fr2 FR2]];
        destruct (stk_carve _ mx _ _ 8 ST3 ltac:(clear; lia)) as [_ [fr3 FR3]];
        replace (SP + -1880 - Z.of_nat 240) with (SP + -2136 + 16) in FTR by (clear; lia);
        replace (SP + -80 - Z.of_nat 1800) with (SP + -2136 + 256) in FR1 by (clear; lia);
        replace (SP + -64 - Z.of_nat 8) with (SP + -2136 + 2064) in FR2 by (clear; lia);
        replace (SP + -2136 - Z.of_nat 8) with (SP + -2144) in FR3 by (clear; lia);
        clear ST1 ST2 ST3 STa STb;
        match goal with FR0 : rw_cells _ mx (SP + -2136) [C8 _; C8 _] |- _ =>
          chunk_split FR0 1%nat FRp FRz;
          apply (rw_cells_reshape asegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in FRz; [| cbn; tauto| vm_compute; reflexivity] end;
        change 240%nat with (8 * 30)%nat in FTR; destruct (u64arr_of_CB _ _ _ 30 FTR) as (ws & HTR & HL)
      end
    end.
    lx_exs; cbv zeta; lx_ands;
      [ lx_mseq | assumption | assumption | assumption | assumption
      | apply (proj2 (rw_cells_app asegs _ (SP + -2136) [C8 _] [C4 _; C4 _])); split;
          [replace (SP + -2136 + 16) with (SP + -2120) by (clear; lia); exact FRp| cbn [cells_size csize Nat.add]; exact FRz]
      | exact HTR | exact HL | exact FR1
      | match goal with H0 : rw_cells _ _ (SP + -80) _ |- _ => replace (SP + -2136 + 2056) with (SP + -80) by (clear; lia); exact H0 end
      | exact FR2 | exact FR3 | assumption ].
  Qed.

  (* [comment removed for export] *)
  Lemma calloc_epi : ltac2:(CDefT.buildp (gd_tbl_AW_CallocA ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Px1,(2.&40.)Pq0,(2.&40.)Pq1,(2.&40.)Pq2,(2.&40.)Pq3,(2.&40.)Pq4,(2.&40.)Pq5,(2.&40.)Pq6,(2.&40.)Pqra,(2.&40.)PSP,$5.Plo,$5.PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(18.$10.R1.(6.R5.-40.)(12.$19.(1:.R7.)(12.$19.(1:.R8.)(12.$19.(1:.R9.)(12.$19.(1:.R:.)(12.$19.(1:.R;.)(12.$19.(1:.R<.)(12.$19.(1:.R=.)(12.$19.(1:.R6.)(15.$19.))))))))))P,(20.$10.R2.R5.(6.R6.-40.))P,(22.(2<.VhAR,)R6.)P,(22.R7.(2=.R8.+860.))P,(22.R9.(24.+2.+3>.))P,(8.$5.(2>.R:.+10.)=)P,(2?.VCS,R:.(2=.R;.R:.))P,(17.$10.R8.)(30.$10.VAL,VCS,Lms',$0.(7.(8.$0.R1.(9.(:.R?.(;.&40.R>.)R34.R33.R32.R31.R30.R16.R15.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R14.R13.R12.R11.R10.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R<.(33.R?.)R;.(>.(2.&40.))R:.(?.$10.)))(20.$10.R:.R=.R>.))(9.(:.R16.(;.&40.(6.R=.-860.))R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R;.(;.&40.+699<4.)R:.(>.(2.&40.))R9.(?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 q0 q1 q2 q3 q4 q5 q6 qra SP lo F fc m
      FR ST LOIMG SPL SPH SPA SCS MI.
    facts.
    zstep. replace (SP + -2144 + 112) with (SP + -2032) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. replace (SP + -2032 + 2032) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. split; [reflexivity| exact ST].
  Qed.
End CallocA.
End ARUN_1.
