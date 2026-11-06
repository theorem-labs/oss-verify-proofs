(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Bi_fktw RT23_iface Po_rows Po_iface Po_mod_defs Po_udd_defs Po_oc_defs Po_oc_c0 Po_oc_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_oc () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib2K53B238Po_oc_c05oc_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B239Po_oc_c166oc_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_oc_defsJpixOrientCorrect2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis LSTD : lept_stderr_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.
Hypothesis LIT1 : exists l, In (A_OC_ERRMSG, l) LEPT_LITS.
Hypothesis LIT2 : exists l, In (A_OC_PROC, l) LEPT_LITS.
Hypothesis UDD : pixUpDownDetect2_cps RT.
Hypothesis R90 : pixRotate90_cps RT.
Hypothesis DES : pixDestroy_cpsF RT.
Hypothesis MOD : makeOrientDecision2_cps RT.
Hypothesis ORTH : pixRotateOrth_cps RT.
Hypothesis PCPY : pixCopyNew1_sure_cps RT.

Theorem pixOrientCorrect_ok : pixOrientCorrect2_cps RT.
Proof using AF GP FKC LSTD RERR LIT1 LIT2 UDD R90 DES MOD ORTH PCPY.
ltac2:(KReplay.run1 (kr_t_Po_oc ()) ["OC"] "p;>p;3p-1p10000p4p710p8g000Gl>2Tg001Al>1Tg002=j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,4LSTDR4p,4RERRR5p,4LIT1R6p,4LIT2R7p,3UDDR8p,3R90R9p,3DESR:p,3MODR;p,4ORTHR<p,4PCPYR=M>2P0P1P2P3P4P5P6P7P8P9P:P;P<P=M>130o"). Qed.
End OC.
