(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface RT_fk RT_fk_iface Bi_fktw Po_rows Po_iface Po_rb2_defs Po_casc_defs
  Po_casc_c0a Po_casc_c0b Po_casc_c0 Po_casc_c16a Po_casc_c16b Po_casc_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_casc () := "C69OSSVerify5KrLib2K53A23;Po_casc_c0a9casc_c0_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_casc_c0b9casc_c0_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_casc_c0<casc_c0_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_casc_defsXpixReduceRankBinaryCascade2_case_of_armsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23<Po_casc_c16a:casc_c16_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_casc_c16b:casc_c16_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_casc_c16=casc_c16_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_casc_defsTpixReduceRankBinaryCascade2_of_casesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CASC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis RB2 : pixReduceRankBinary22_cps RT.
Hypothesis DES : pixDestroy_cpsF RT.
Hypothesis DESN : pixDestroy_null_cpsF RT.

Theorem pixReduceRankBinaryCascade_ok : pixReduceRankBinaryCascade2_cps RT.
Proof using AF GP FKC RB2 DES DESN.
ltac2:(KReplay.run1 (kr_t_Po_casc ()) ["CASC"] "p;7p;5p;1p;3g0000j79Tg0011j78Tg0022j72Tg0035j51Tg004Vj10Tg005;j17Tg005Yj73Tg006\j74Tg007_j75Tg008dj36Tp,2RTR0P0g00:AP0p,2AFR1p,2GPR2p,3FKCR3p,3RB2R4p,3DESR5p,4DESNR6F9P0P1P2P3P4P5P6F8P0P1P2P3P4P5P6F2D1P0g00:_#0#0#0#0#7P0P1P2P3P4P5P6F3P0P1P2P3P4P5P6F4P0P1P2P3P4P5P6F5D136o"). Qed.
End CASC.
