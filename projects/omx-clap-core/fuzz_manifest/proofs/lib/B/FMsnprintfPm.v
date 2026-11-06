(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMsnprintfMc71.v, with its module paths and module names changed; 21 of its 50 lines of code are new or changed and 639 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPm.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* ASan's printf_common (fm.asan 0x44d84) for fm's seven snprintf formats: apcommon_realizesU (FMsnprintfI.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE3i YE39 YE3h YE38 YE7d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require YE2t YE35.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMsnprintfI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPmChk FMsnprintfPmK FMsnprintfPmW.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPm1 FMsnprintfPm2 FMsnprintfPm3 FMsnprintfPm4 FMsnprintfPm5 FMsnprintfPm6 FMsnprintfPm7.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem pcommon_realizesU : apcommon_realizesU B A_PCOM.
Proof.
intros ly S U W regs mem md f ps P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hin Hsl Hfr Hlen.
change (cfg_at tfibsegs A_PCOM regs mem md) with (cfg_at tfibsegs PC_ENTRY regs mem md).
change (SRr tfibsegs W (cfg_at tfibsegs PC_ENTRY regs mem md) (pcom_post B ly S U W regs mem md)).
unfold FM_SN_FMTS in Hin. cbn [In] in Hin.
destruct Hin as [Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]]]; injection Hin as <- <-.
- exact (pcm_whole B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_tw B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_tx B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_t1 B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_t2 B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_t3 B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
- exact (pcm_t1x B LAWS TB ly S U W regs mem md P args d n out HPRE Hac Hslo Hpres Hrom G11 G12 HP1 HP2 Hsl Hfr Hlen).
Qed.
End c.
