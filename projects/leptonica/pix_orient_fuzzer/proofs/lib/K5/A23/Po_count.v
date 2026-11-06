(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface RT_fk RT_fk_iface Bi_fktw Po_rows Po_iface Po_count_defs Po_count_c0 Po_count_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_count () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib2K53A23;Po_count_c08count_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23<Po_count_c169count_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_count_defsHpixCountPixels2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section COUNT.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorInt.
Hypothesis LIT1 : exists l, In (A_MSG_COUNT, l) LEPT_LITS.
Hypothesis LIT2 : exists l, In (A_PROC_COUNT, l) LEPT_LITS.

Theorem pixCountPixels_ok : pixCountPixels2_cps RT.
Proof using AF GP FKC RERR LIT1 LIT2.
ltac2:(KReplay.run1 (kr_t_Po_count ()) ["COUNT"] "p;7p;3p-1p10000p4p710p8g000Gj72Tg001Gj71Tg002Ij30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,4RERRR4p,4LIT1R5p,4LIT2R6F2P0P1P2P3P4P5P6F130o"). Qed.
End COUNT.
