(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_iface2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import BiV_defs BiV_iface BiV_bgexact_defs Bi_bgexact0 Bi_bgexact16.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bgexact () := "C69OSSVerify5KrLib2K53B02;Bi_bgexact0GpixBilateralGrayExact_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<Bi_bgexact16HpixBilateralGrayExact_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02@BiV_bgexact_defsOpixBilateralGrayExact_of_casesVC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BGEXACTTOPV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis KGP : kernelGetParameters_cps RT.
Hypothesis KINVV : kernelInvert_cpsV RT.
Hypothesis PAMB : pixAddMirroredBorder_cps2 RT.
Hypothesis PCREATE : pixCreate_nn_cpsF RT.
Hypothesis PCOPY : pixCopy_nn_cpsF RT.
Hypothesis KDEST : kernelDestroy_cpsF RT.
Hypothesis PXD : pixDestroy_cpsF RT.
Hypothesis LSTDERR : lept_stderr_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.

Theorem pixBilateralGrayExact_okV : pixBilateralGrayExact_cps2V RT.
Proof using AF GP FKC KGP KINVV PAMB PCREATE PCOPY KDEST PXD LSTDERR RERR.
ltac2:(KReplay.run1 (kr_t_Bi_bgexact ()) ["BGEXACTTOPV"] "p;=p;3g0000l=2Tg001?l=1Tg002Pj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3KGPR4p,5KINVVR5p,4PAMBR6p,7PCREATER7p,5PCOPYR8p,5KDESTR9p,3PXDR:p,7LSTDERRR;p,4RERRR<M=2P0P1P2P3P4P5P6P7P8P9P:P;P<M=130o"). Qed.
End BGEXACTTOPV.
