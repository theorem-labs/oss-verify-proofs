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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 PmF_kit Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_relkit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bgexact_loop Bi_bgenv Bi_bgexact_defs Bi_iface3 Bi_bexact_kit Bi_bexact_kit2 Bi_bexact_kit3 Bi_applyloop Bi_rgbloop Bi_rgb_defs Bi_crgb0 Bi_crgb16 LeptB_guard LeptB_guard2 LeptB_guard3.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_crgb () := "C46Stdlib5Lists4List2hdC69OSSVerify5KrLib2K53B028Bi_crgb0CpixCreateRGBImage_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029Bi_crgb16DpixCreateRGBImage_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02;Bi_rgb_defsJpixCreateRGBImage_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CRGBTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis RERRP : returnError_cpsF RT e_returnErrorPtr.
Hypothesis LIT_R : exists l, In (0x26460, l) LEPT_LITS.
Hypothesis LIT_G : exists l, In (0x264e0, l) LEPT_LITS.
Hypothesis LIT_B : exists l, In (0x26520, l) LEPT_LITS.
Hypothesis LIT_FN : exists l, In (0x264a0, l) LEPT_LITS.
Hypothesis LIT_NM : exists l, In (0x26320, l) LEPT_LITS.
Hypothesis PCREATE : pixCreate_cpsF RT.
Hypothesis PCRES : pixCopyResolution_cps RT.
Hypothesis PSRGB : pixSetRGBComponent_cps2 RT.

Theorem pixCreateRGBImage_ok : pixCreateRGBImage_cps RT.
Proof using AF GP FKC RERRP LIT_R LIT_G LIT_B LIT_FN LIT_NM PCREATE PCRES PSRGB.
ltac2:(KReplay.run1 (kr_t_Bi_crgb ()) ["CRGBTOP"] "p;=p;3p-1p10000p4p710p8g000Gl=2Tg001Ol=1Tg002Yj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,5RERRPR4p,5LIT_RR5p,5LIT_GR6p,5LIT_BR7p,6LIT_FNR8p,6LIT_NMR9p,7PCREATER:p,5PCRESR;p,5PSRGBR<M=2P0P1P2P3P4P5P6P7P8P9P:P;P<M=130o"). Qed.
End CRGBTOP.
