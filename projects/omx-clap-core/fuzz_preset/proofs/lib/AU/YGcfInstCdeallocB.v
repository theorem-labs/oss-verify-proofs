(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfInstCdeallocB.v (commit ce1a656b52b7, file sha256 10810cbd8ad6) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane: reply B's CDH, the image-B twin of lib/A/YGcfInstCdealloc.v):
   the CacheDealloc callee field of the Deallocate interfaces at reply B's cf instance,
   ARXr := YGcfInstDrainR.ARXr_cf B IOK Hp, DRq := DRq_cf B kQuarantineMax, AOX := aowned B (lib/A's parameters, which
   a prior worker's DIfaceExt instance cites at image A for its field ext_cdealloc).
   rule 24: no function proved here (kind: interface-instance discharge).  The walk is lane B1 slice H3's
   DMcdF.cdealloc_m_of_reads (SizeClassAllocator64LocalCache::Deallocate over an opaque cut relation), and its read
   fields at the cf instance are YGcfInstCdReads.cd_reads_cf; both are carried, not written here.  Reuse search:
   `proof-index de_cdealloc_m_t de_cdealloc_t cdealloc tfib_cdealloc_ok CacheDeallocate` 2026-10-30T18:1xZ: no
   released proof; the unreleased H3 chain only.  The composition is cgif's DMdrainTopC.v:46-48 (the cdealloc
   premise of drain_ok_cd) at reply B, and the weakenings are cgif's YGcfInstDrain.v:121-140 with the DrainSigC
   field replaced by that proof.
   - [de_cdealloc_m_cf]: MnRecycle.de_cdealloc_m_t (raw frame + errno + memnorm), CfF2b's premise CDH of
     YGcfInstDrainTopRh.ds_drain_rh_cf;
   - [de_cdealloc_cf] (drop the memnorm keep), [dr_cdealloc_cf] (drop errno), [di_cdealloc_cf] (drop the raw frame).
   Section hypotheses: TS : TfibSyms B and HIOK : YGcfInstBase.IOK_ok B IOK, the two that YGcfInstCdReads' Section F
   takes; nothing else. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG DMspec DMiface DIfaceR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGif2cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MnRecycle. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMcdR DMcdF YGcfInstCdReads YGcfInstDrainDq.
Open Scope Z_scope.
#[local] Existing Instance AGif2cgif.AImg_cgif.
#[local] Existing Instance DGif0cgif.DImg_cgif.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis TS : YF0m.TfibSyms B.
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
