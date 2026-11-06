(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface RT_fk RT_fk_iface Pm_gaps_iface Po_rows Po_iface RT23b_iface Po_sakit Po_msv_defs Po_msv_c0 Po_msv_c16.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_msv () := "C69OSSVerify5KrLib2K53B239Po_msv_c06msv_c0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Po_msv_c167msv_c16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23;Po_msv_defsMmorphSequenceVerify2_of_casesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MSV.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis SGC : sarrayGetCount_cps RT.
Hypothesis SGS : sarrayGetString_cps RT.
Hypothesis SRC : stringRemoveWS_cps RT.
Hypothesis SS : sscanf_dd_icontractF RT.
Hypothesis ACCFMT : forall Σ m, ART RT Σ m -> acc asegs m SSCANF_FMT 6.
Hypothesis ACCILB : forall Σ m, ART RT Σ m -> acc asegs m 0x41400 20.

Theorem morphSequenceVerify2_ok : morphSequenceVerify2_cps RT.
Proof using AF GP FKC SGC SGS SRC SS ACCFMT ACCILB.
ltac2:(KReplay.run1 (kr_t_Po_msv ()) ["MSV"] "p;:p;3g0000l:2Tg000ll:1Tg001jj30Tp,2RTR0P0p,2AFR1p,2GPR2p,3FKCR3p,3SGCR4p,3SGSR5p,3SRCR6p,2SSR7p,6ACCFMTR8p,6ACCILBR9M:2P0P1P2P3P4P5P6P7P8P9M:130o"). Qed.

End MSV.
