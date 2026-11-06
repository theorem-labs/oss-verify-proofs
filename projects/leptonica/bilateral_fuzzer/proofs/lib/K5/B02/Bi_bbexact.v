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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 Bi_bbexact_kit Bi_bbexact_defs Bi_bbexact0 Bi_bbexact16 LeptB_guard LeptB_guard2 LeptB_guard3.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import BiV_defs BiV_iface BiV_iface3 BiV_kit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_bbexact () := "C69OSSVerify5KrLib2K53B02;Bi_bbexact0HpixBlockBilateralExact_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02<Bi_bbexact16IpixBlockBilateralExact_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02?Bi_bbexact_defsOpixBlockBilateralExact_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BBEXACTTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis MGKV : makeGaussianKernel_cpsV RT.
Hypothesis MRKV : makeRangeKernel_cpsV RT.
Hypothesis PBEXV : pixBilateralExact_cps2V RT.
Hypothesis KDEST : kernelDestroy_cpsF RT.
Hypothesis RERR : returnError_cpsF RT e_returnErrorPtr.

Theorem pixBlockBilateralExact_ok : pixBlockBilateralExact_cps2 RT.
Proof using AF GP FKC MGKV MRKV PBEXV KDEST RERR.
ltac2:(KReplay.run1 (kr_t_Bi_bbexact ()) ["BBEXACTTOP"] "p;9p;3g0000l92Tg001@l91Tg002Rj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,4MGKVR4p,4MRKVR5p,5PBEXVR6p,5KDESTR7p,4RERRR8M92P0P1P2P3P4P5P6P7P8M9130o"). Qed.
End BBEXACTTOP.
