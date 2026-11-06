(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 Bi_applyloop Bi_rgbloop Bi_rgb_defs Bi_getrgb0 Bi_getrgb16.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_getrgb () := "C69OSSVerify5KrLib2K53A02:Bi_getrgb0DpixGetRGBComponent_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;Bi_getrgb16EpixGetRGBComponent_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02;Bi_rgb_defsKpixGetRGBComponent_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section GETRGBTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PCREATE : pixCreate_nn_cpsF RT.
Hypothesis PCRES : pixCopyResolution_cps RT.

Theorem pixGetRGBComponent_ok : pixGetRGBComponent_cps RT.
Proof using AF GP FKC PCREATE PCRES.
ltac2:(KReplay.run1 (kr_t_Bi_getrgb ()) ["GETRGBTOP"] "p;6p;3g0000j62Tg001;j61Tg002Hj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,7PCREATER4p,5PCRESR5E2P0P1P2P3P4P5E130o"). Qed.
End GETRGBTOP.
