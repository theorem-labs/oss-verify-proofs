(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfRefillTopreply.v (commit 4d286b2e618d, file sha256 b8e90e21ea94) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* The cf layer's refill contract at reply A in the form CfF1's miss twin consumes (lib/A/YGcfInstEnqMisspreset.v, premise
   HIOK : IOK i -> i = as_inst B), at reply's image CfImgB.CfImg_B:
   - refill_spec_cf_preset_inst / refill_walk_cf_preset_inst: YGcfInstRefillSpecreply's refill_spec_cf_preset /
     refill_walk_cf_preset (instance row IOK i -> i = A_ALLOCATOR, and the class-full arm HCF as a premise, as at cgif)
     under HIOK; reply A's A_ALLOCATOR = TFIB_INST = 0xa8098 (A/YFl1.v, A/YF0m.v) and TfibSyms gives
     as_inst B = TFIB_INST (ts_inst);
   - refill_walk_cf_preset_closed: the same with HCF discharged by the relocated report, RepArmTcf.classfull_cf_of_hyps
     (no premise), for the reply WalkSig closing.
   EVENT-FREE.  rule 24: no function proved (kind: restatement of the relocated refill contract). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFhy YFis YFhz. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFhn. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFhncf YFkocf YFkxcf YFkycf YFkzcf MnRefillB2Rcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFk5cf YFk8cf YFkkcf YFklcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormLoc MnRefillLocpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MnRefillUninitcf MnRefillB3cf MnRefillB3Topcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB YGcfInstRefillSpecpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RepArmTcf.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Lemma iok_alloc : forall (B : asyms) (IOK : Z -> Prop), TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  forall i, IOK i -> i = A_ALLOCATOR.
Proof. intros B IOK TS HIOK i Hi. rewrite (HIOK i Hi), (ts_inst B TS). reflexivity. Qed.

Theorem refill_spec_cf_preset_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_B cp ->
  @refill_spec_cf fx rc CfImg_B cp AImg_cgif AGImg_cgif B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_spec_cf_preset B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_preset_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_B cp ->
  @refill_walk_cf fx rc CfImg_B cp AImg_cgif AGImg_cgif B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_walk_cf_preset B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_preset_closed : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  @refill_walk_cf fx rc CfImg_B cp AImg_cgif AGImg_cgif B IOK.
Proof. intros B IOK TS HIOK. exact (refill_walk_cf_preset_inst B IOK TS HIOK (@RepArmTcf.classfull_cf_of_hyps fx rc cp)). Qed.
End a.
