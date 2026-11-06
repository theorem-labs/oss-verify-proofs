(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Cells.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_fa_iface AF_huf_afa AF_huf_afa2 AF_huf_afa3 AF_huf_afa4 AF_huf_afa5.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_afa6 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z2ltI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8artcellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit6rcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4r_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9Stdio_kit4rrngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5nshadC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5BothW?AF_huf_fa_iface?fast_args_postAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib5BothW:AF_huf_afa6afa_dzC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5BothW:AF_huf_afa7afa_n10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa56afa_b3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa56AFA_J3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa56afa_b2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa56AFA_J2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa46afa_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa46AFA_J1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa46afa_b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa46AFA_J0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa47afa_f18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa48AFA_F18'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa37afa_e20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa38AFA_E20'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AF_huf_afa26afa_jtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AF_huf_afa8afa_mainC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5BothW?AF_huf_fa_iface?fast_args_stmtAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib5BothW9Stdio_kit6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW?AF_huf_fa_ifaceDAHUF_FAST_ARGS_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW?AF_huf_fa_ifaceCAHUF_FAST_ARGS_INITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

Theorem fast_args_proofA : fast_args_stmtA.
Proof.
  unfold fast_args_stmtA.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m A DST dcap S DT mtl tt tl mtl' src ja lo rstk.
  intros. subst a0 a1 a2 a3 a4 a5.
  destruct (Z.eq_dec dcap 0) as [DZ|DNZ].
  { eapply afa_dz; eassumption. }
  destruct (Z_lt_le_dec (zlen src) 10) as [N10|N10].
  { eapply afa_n10; try eassumption; lia. }
  eapply afa_main; try eassumption; try lia.
  intros TL. eapply afa_jt; try eassumption.
  eapply afa_e20; try eassumption.
  eapply afa_f18; try eassumption.
  eapply afa_b0; try eassumption.
  eapply afa_b1; try eassumption.
  eapply afa_b2; try eassumption.
  eapply afa_b3; eassumption.
Qed.

End CANSEC1.
