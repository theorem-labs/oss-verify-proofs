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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptM_destroy_defs LeptB_guard RT_fk RT_fk_iface Bi_fktw Bi_fkkit Bi_fkweak LeptF_iface LeptF_weak LeptF_kit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require LeptM_destroy_c0_1_1 LeptM_destroy_c0_1_0 LeptM_destroy_c0_0_1 LeptM_destroy_c0_0_0 LeptM_destroy_c16_1_1 LeptM_destroy_c16_1_0 LeptM_destroy_c16_0_1 LeptM_destroy_c16_0_0.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptM_destroy () := "C69OSSVerify5KrLib2K53B02BLeptM_destroy_defs?pixDestroy_caseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02DLeptM_destroy_c0_1_1BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02DLeptM_destroy_c0_1_0BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02DLeptM_destroy_c0_0_1BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02DLeptM_destroy_c0_0_0BpixDestroy_case_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53B02ELeptM_destroy_c16_1_1BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02ELeptM_destroy_c16_1_0BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02ELeptM_destroy_c16_0_1BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02ELeptM_destroy_c16_0_0BpixDestroy_case_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02BLeptM_destroy_defsDpixDestroy_of_casesFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B029Bi_fkweakCpixDestroy_cps_of_FC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B02=LeptM_destroy>pixDestroy_okFC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Section DESTROY_FINAL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.   (* [comment removed for export] *)
Hypothesis CMD : pixcmapDestroy_cpsF RT.

Theorem pixDestroy_okF : pixDestroy_cpsF RT.
Proof using AF GP FKC CMD.
ltac2:(KReplay.run1 (kr_t_LeptM_destroy ()) ["DESTROY_FINAL"] "p'0h03cnzh13dnzi001bp;4p;5p;1p;3g0000j40Tg001>j5;Tg002Qj53Tg003dj52Tg0057j5:Tg006Jj11Tg006oj19Tg007Mj54Tg008aj55Tg00:5j56Tg00;Ij57Tg00<]j38Tp,2RTR0g00>0R1P1P0g00>PR2f1R3f0R4C0^01P4P1P0P2g00>nR5P4C0P4P0p,2AFR6p,2GPR7p,3FKCR8p,3CMDR9D;P0P6P7P8P9D3n0110000020000X01P1P0P2g00?NR2P4C0P4P0P6P7P8P9D2P0P6P7P8P9D:n0110000020000X01n0110000020000W1P1P0g00?n#1#1#1#1#9R:P3P4C0^01P4P1P0P:P5P4C0P4P0P6P7P8P9D4P0P6P7P8P9D5n0110000020000X01P1P0P:P2P4C0P4P0P6P7P8P9D6P0P6P7P8P9D7n0110000020000X01n0110000020000X1138o"). Qed.

(* [comment removed for export] *)
Theorem pixDestroy_ok : pixDestroy_cps RT.
Proof using AF GP FKC CMD.
ltac2:(KReplay.run1 (kr_t_LeptM_destroy ()) ["DESTROY_FINAL"] "p;2g00@Sj20Tp,2RTg00A\'0o"). Qed.
End DESTROY_FINAL.
