(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_env Pm_iface Cf_iface RT_fk RT_fk_iface
  Bi_iface Bi_fktw Bi_iface2 D_iface D_defs Po_rows Po_iface Po_rot90_defs Po_rot90_cw0 Po_rot90_cw16 Po_rot90_ccw0 Po_rot90_ccw16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_rot90 () := "C69OSSVerify5KrLib2K53A23<Po_rot90_cw09rot90_cw0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_rot90_ccw0:rot90_ccw0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_rot90_defsHpixRotate90_case_of_dirsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23=Po_rot90_cw16:rot90_cw16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23>Po_rot90_ccw16;rot90_ccw16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_rot90_defsDpixRotate90_of_casesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.

Section ROT90.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis CRE1 : pixCreate1_sure_cps RT.
Hypothesis PCC : pixCopyColormap_cpsF RT.
Hypothesis CPR : pixCopyResolution_po_cps RT.
Hypothesis CIF : pixCopyInputFormat_cps RT.
Hypothesis CSP : pixCopySpp_cps RT.

Theorem pixRotate90_ok : pixRotate90_cps RT.
Proof using AF GP FKC CRE1 PCC CPR CIF CSP.
ltac2:(KReplay.run1 (kr_t_Po_rot90 ()) ["ROT90"] "p;9p;4p;1p;3g0000l97Tg0012l96Tg0026j41Tg003Hj10Tg003mj15Tg004Kl94Tg005Ol93Tg006Uj32Tp,2RTR0P0g007cP0p,2AFR1p,2GPR2p,3FKCR3p,4CRE1R4p,3PCCR5p,3CPRR6p,3CIFR7p,3CSPR8M97P0P1P2P3P4P5P6P7P8M96C1P0g008A#0#0#0#0#5P0P1P2P3P4P5P6P7P8M94P0P1P2P3P4P5P6P7P8M93C132o"). Qed.
End ROT90.
