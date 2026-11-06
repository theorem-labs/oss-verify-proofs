(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface RT_fk RT_fk_iface Bi_fktw Po_rows Po_iface Po_pma1_defs Po_dilate_defs Po_pma12_defs Po_pma1_c0 Po_pma1_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_pma1 () := "C69OSSVerify5KrLib2K53A23:Po_pma1_c07pma1_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Po_pma1_c168pma1_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23=Po_pma12_defsKprocessMorphArgs12_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PMA1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SGP : selGetParameters_sxsy_cps RT.
Hypothesis RSZ : pixResizeImageData_same_cps RT.
Hypothesis PCL : pixClone_cpsF RT.
Hypothesis PTM : pixCreateTemplate1_sure_cps RT.

Theorem processMorphArgs1_ok : processMorphArgs12_cps RT.
Proof using AF GP FKC SGP RSZ PCL PTM.
ltac2:(KReplay.run1 (kr_t_Po_pma1 ()) ["PMA1"] "p;8p;3g0000j82Tg000nj81Tg001nj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3SGPR4p,3RSZR5p,3PCLR6p,3PTMR7G2P0P1P2P3P4P5P6P7G130o"). Qed.
End PMA1.
