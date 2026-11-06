(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Malloc top under ARU, any U: the twin of lib/A/AF0w.v (tfib_amalloc_realizes). The primary path (n <= 64512) is
   FSupoisonAllocMm.malloc_primU (miss / hit join over FSupoisonAllocMp2 / Mp3 and the miss arms of FSupoisonAllocMm),
   the secondary path (n >= 64513) is FSupoisonAllocMs.malloc_secU; the unwinder and depot contracts
   (tfib_unwind_spec, tfib_depot_spec B) carry no U and are discharged as AF0w does, by AFl4.tfib_unwind_ok and
   AFem.tfib_depot_ok. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* Modified by Theorem Labs, 2026-10: new file; it proves tfib_amalloc_realizesU, FSupoisonU.amalloc_realizesU for fuzz_state's symbols. *)
(* Modified by Theorem Labs, 2026-10: image-B port (fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d) of lib/A/FSupoisonAllocM.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), the kit is lib/B/FSupoisonAllocR / Rf / Rt, every statement is over B's tfibsegs (lib/B/YB1v.v); the statements are over B's tfibsegs and B's Tfib_code. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFl4 YFem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocMs FSupoisonAllocMm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module Ms := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMs.
Module Mm := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocMm.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* Port-from: lib/B/YF0w.v:29 (amalloc_realizes_of) and lib/B/YF0w.v:45 (tfib_amalloc_realizes). *)
Theorem tfib_amalloc_realizesU : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> FSU.amalloc_realizesU tfibsegs B.
Proof.
intros B TS HD ly S U W regs mem md n ch PRE Hn Hrange Hlive Htr.
pose proof tfib_unwind_ok as U1. pose proof (tfib_depot_ok B TS HD) as D1.
rewrite (ts_code B TS) in Htr |- *. cbn [pc_malloc_ra0 pc_wrap_malloc Tfib_code] in Htr |- *.
destruct (Z_le_gt_dec n 64512) as [Hp|Hs].
- exact (Mm.malloc_primU B TS U1 D1 ly S W regs mem md n ch U PRE Hn ltac:(lia) (tr_admit_call _ _ _ _ _ _ Htr) Hlive).
- exact (Ms.malloc_secU B TS U1 D1 ly S U W regs mem md n ch PRE Hn ltac:(lia) (tr_admit_call _ _ _ _ _ _ Htr) Hlive).
Qed.
End a.
