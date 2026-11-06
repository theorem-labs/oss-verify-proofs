(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface RT_fk RT_fk_iface Bi_fktw Po_rows Po_iface Po_rb2_defs
  Po_rb2_c0n Po_rb2_c0a Po_rb2_c0b Po_rb2_c0 Po_rb2_c16n Po_rb2_c16a Po_rb2_c16b Po_rb2_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_rb2 () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib2K53A23:Po_rb2_c0n;rb2_c0_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_rb2_c0a9rb2_c0_hsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_rb2_c0b9rb2_c0_wsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A239Po_rb2_c0;rb2_c0_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defsRpixReduceRankBinary22_case_of_armsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23;Po_rb2_c16n<rb2_c16_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_c16a:rb2_c16_hsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_c16b:rb2_c16_wsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Po_rb2_c16<rb2_c16_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_rb2_defsNpixReduceRankBinary22_of_casesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RB2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PAD : pixSetPadBits_cpsF RT.
Hypothesis CRE : pixCreate_res0_cpsF RT.
Hypothesis CRE1 : pixCreate1_sure_cps RT.
Hypothesis CPR : pixCopyResolution_po_cps RT.
Hypothesis SCR : pixScaleResolution_cps RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.
Hypothesis LIT1 : exists l, In (A_MSG_RB2_NULL, l) LEPT_LITS.
Hypothesis LIT2 : exists l, In (A_MSG_RB2_HS, l) LEPT_LITS.
Hypothesis LIT3 : exists l, In (A_MSG_RB2_PIXD, l) LEPT_LITS.
Hypothesis LIT4 : exists l, In (A_PROC_RB2, l) LEPT_LITS.

Theorem pixReduceRankBinary2_ok : pixReduceRankBinary22_cps RT.
Proof using AF GP FKC PAD CRE CRE1 CPR SCR RERR LIT1 LIT2 LIT3 LIT4.
ltac2:(KReplay.run1 (kr_t_Po_rb2 ()) ["RB2"] "p;7p;9p;>p;6p;1p;3p-1p10000p4p710p8g000Gj7;Tg001Ij7:Tg002Il93Tg003Il>2Tg004Jj61Tg005dj10Tg006Ij19Tg006gj74Tg007kj75Tg008ml96Tg009ol>7Tg00;2j38Tp,2RTR0P0g00<HP0p,2AFR1p,2GPR2p,3FKCR3p,4RERRR4p,4LIT1R5p,4LIT4R6F;P0P1P2P3P4p,4LIT2R7P6F:P0P1P2P3p,3PADR8p,3CRER9P4p,4LIT3R:P6M93P0P1P2P3P8P9p,4CRE1R;p,3CPRR<p,3SCRR=P4P5P7P:P6M>2E1P0g00<f#0#0#0#0#9P0P1P2P3P4P5P6F4P0P1P2P3P4P7P6F5P0P1P2P3P8P9P4P:P6M96P0P1P2P3P8P9P;P<P=P4P5P7P:P6M>7E138o"). Qed.
End RB2.
