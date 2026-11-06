(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 D_iface D_defs Bi_pb_defs Bi_pbil_defs Bi_pbil0 Bi_pbil16 LeptB_guard LeptB_guard2 LeptB_guard3.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_pbil () := "C69OSSVerify5KrLib2K53B028Bi_pbil0>pixBilateral_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029Bi_pbil16?pixBilateral_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<Bi_pbil_defsEpixBilateral_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PBILTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PBG : pixBilateralGray_cps RT.
Hypothesis PGRGB : pixGetRGBComponent_cps RT.
Hypothesis PCRGB : pixCreateRGBImage_cps RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis PXDN : pixDestroy_null_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.
Hypothesis LSTD : lept_stderr_cpsF RT.
Hypothesis PCOPY : pixCopy_nn_cpsF RT.

Theorem pixBilateral_ok : pixBilateral_cps2 RT.
Proof using AF GP FKC PBG PGRGB PCRGB PXD PXDN RERR LSTD PCOPY.
ltac2:(KReplay.run1 (kr_t_Bi_pbil ()) ["PBILTOP"] "p;<p;3g0000l<2Tg0013l<1Tg0028j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3PBGR4p,5PGRGBR5p,5PCRGBR6p,3PXDR7p,4PXDNR8p,4RERRR9p,4LSTDR:p,5PCOPYR;M<2P0P1P2P3P4P5P6P7P8P9P:P;M<130o"). Qed.
End PBILTOP.
