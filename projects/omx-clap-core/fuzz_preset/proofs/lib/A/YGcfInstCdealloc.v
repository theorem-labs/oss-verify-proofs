(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstCdealloc.v (commit 67deba317dfb, blob 9eaf9eb6541e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG DMspec DMiface DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMcdR DMcdF YGcfInstCdReads YGcfInstDrainDq.
Open Scope Z_scope.
#[local] Existing Instance AImgA.AImg_A.
#[local] Existing Instance ADIfaceA.DImg_A.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis TS : AF0m.TfibSyms B.
Hypothesis HIOK : YGcfInstBase.IOK_ok B IOK.
Local Notation ARXr := (ARXr_cf B IOK Hp).
Local Notation AOX := (aowned B).
Local Notation DRq := (DRq_cf B kQuarantineMax).

Lemma de_cdealloc_m_cf : MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.
Proof.
exact (DMcdF.cdealloc_m_of_reads B ARXr AOX DRq RMAXD_cf TS YGcfInstDrainR.rmaxd_ok_cf
  (YGcfInstCdReads.cd_reads_cf B IOK Hp TS HIOK) (YGcfInstDrainDq.drq_cd_cf B)).
Qed.

Lemma de_cdealloc_cf : ErrnoG.de_cdealloc_t B ARXr AOX DRq.
Proof. exact (MnRecycle.de_cdealloc_em_e B ARXr AOX DRq de_cdealloc_m_cf). Qed.

Lemma dr_cdealloc_cf : dr_cdealloc_t B ARXr AOX DRq.
Proof.
intros inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [| exact (de_cdealloc_cf inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HR & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR | exact REST].
Qed.

Lemma di_cdealloc_cf : di_cdealloc_t B ARXr AOX DRq.
Proof.
intros inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [| exact (dr_cdealloc_cf inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | exact REST].
Qed.
End a.
