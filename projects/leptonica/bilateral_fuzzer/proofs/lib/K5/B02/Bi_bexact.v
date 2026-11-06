(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 Bi_bexact_defs Bi_bexact0 Bi_bexact16 LeptB_guard LeptB_guard2 LeptB_guard3.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import BiV_defs BiV_iface BiV_iface3 BiV_bexact_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bexact () := "C69OSSVerify5KrLib2K53B02:Bi_bexact0CpixBilateralExact_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;Bi_bexact16DpixBilateralExact_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?BiV_bexact_defsKpixBilateralExact_of_casesVC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BEXACTTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PBGEV : pixBilateralGrayExact_cps2V RT.
Hypothesis PGRGB : pixGetRGBComponent_cps RT.
Hypothesis PCRGB : pixCreateRGBImage_cps RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis PXDN : pixDestroy_null_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.

Theorem pixBilateralExact_okV : pixBilateralExact_cps2V RT.
Proof using AF GP FKC PBGEV PGRGB PCRGB PXD PXDN RERR.
ltac2:(KReplay.run1 (kr_t_Bi_bexact ()) ["BEXACTTOP"] "p;:p;3g0000l:2Tg001:l:1Tg002Fj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,5PBGEVR4p,5PGRGBR5p,5PCRGBR6p,3PXDR7p,4PXDNR8p,4RERRR9M:2P0P1P2P3P4P5P6P7P8P9M:130o"). Qed.
End BEXACTTOP.
