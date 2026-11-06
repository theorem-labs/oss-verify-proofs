(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfRefillTopreply.v (commit eb934de95d13, blob d602fafda38b) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFhy AFis AFhz YFkpcf YFkrcf YFhmcf YFkscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0qcf YG0scf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import MnRefillSeamcf YGcfRefillCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFhn YFhncf YFkocf YFkxcf YFkycf YFkzcf MnRefillB2Rcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YFk5cf YFk8cf YFkkcf YFklcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormLoc MnRefillLocpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MnRefillUninitcf MnRefillB3cf MnRefillB3Topcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA YGcfInstRefillSpecpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RepArmTcf.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Lemma iok_alloc : forall (B : asyms) (IOK : Z -> Prop), TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  forall i, IOK i -> i = A_ALLOCATOR.
Proof. intros B IOK TS HIOK i Hi. rewrite (HIOK i Hi), (ts_inst B TS). reflexivity. Qed.

Theorem refill_spec_cf_preset_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_A cp ->
  @refill_spec_cf fx rc CfImg_A cp AImg_A AGImg_A B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_spec_cf_preset B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_preset_inst : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) -> @refill_B3_classfull_cf fx rc CfImg_A cp ->
  @refill_walk_cf fx rc CfImg_A cp AImg_A AGImg_A B IOK.
Proof. intros B IOK TS HIOK HCF. exact (refill_walk_cf_preset B IOK TS (iok_alloc B IOK TS HIOK) HCF). Qed.

Theorem refill_walk_cf_preset_closed : forall (B : asyms) (IOK : Z -> Prop),
  TfibSyms B -> (forall i, IOK i -> i = as_inst B) ->
  @refill_walk_cf fx rc CfImg_A cp AImg_A AGImg_A B IOK.
Proof. intros B IOK TS HIOK. exact (refill_walk_cf_preset_inst B IOK TS HIOK (@RepArmTcf.classfull_cf_of_hyps fx rc cp)). Qed.
End a.
