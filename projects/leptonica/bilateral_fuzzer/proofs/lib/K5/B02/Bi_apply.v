(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Km_setelem Km_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_apply_defs Bi_apply0 Bi_apply16.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import BiV_defs BiV_iface2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_apply () := "C69OSSVerify5KrLib2K53B029Bi_apply0@bilateralApply_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Bi_apply16AbilateralApply_16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02=Bi_apply_defsHbilateralApply_of_casesVC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section APPLYTOP.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis PGC : pixaGetCount_cps RT.
Hypothesis TMPL : pixCreateTemplate_cps RT.

Theorem bilateralApply_okV : bilateralApply_cpsV RT.
Proof using AF GP FKC PGC TMPL.
ltac2:(KReplay.run1 (kr_t_Bi_apply ()) ["APPLYTOP"] "p;6p;3g0000j62Tg0016j61Tg002>j30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3PGCR4p,4TMPLR5E2P0P1P2P3P4P5E130o"). Qed.
End APPLYTOP.
