(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/YGcfInstDrainImgreply.v (commit ce1a656b52b7, file sha256 f05a9936f766) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (CfInstMiss, for lane F2b's drain walk at plugin-hostd/fuzz_reply, reply image B; the B
   twin of lib/A/YGcfInstDrainImgpreset.v, same stems).
   rule 24: no function proved (kind: image-row discharge at reply image B).

   The three image premises of the generic cf layer's drain walk (Section T of YGcfInstDrainTop.v: SBC, IQA, CA), stated
   TOKEN-EQUAL to F2b's Definitions at IM := AImg_cgif (B/AGif2cgif.v): SB_CONST (B/YGcfInstDrainQ.v), IMG_QAPART and
   CONST_APART (B/YGcfInstDrainX.v). None of the three texts reads DImg, CfImg or CfParams, and each binds B itself under
   im_syms B (TfibSyms B at AImg_cgif), so no premise is added. Each is CITED from reply B's image rows, not re-proved
   (the values are reply B's own tables, computed there):
   - SB_CONST_preset_B    = PresetImg_sbconst.SB_CONST_B
   - IMG_QAPART_preset_B  = PresetImg_qapart.IMG_QAPART_B
   - CONST_APART_preset_B = PresetImg_constapart.CONST_APART_B (a prior worker's case split, 195ad575801) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainX YGcfInstDrainQ.
(* reply B's image rows, used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_sbconst PresetImg_qapart PresetImg_constapart.
Local Open Scope Z_scope.

Theorem SB_CONST_preset_B : SB_CONST (IM := AImg_cgif).
Proof. exact PresetImg_sbconst.SB_CONST_B. Qed.

Theorem IMG_QAPART_preset_B : IMG_QAPART (IM := AImg_cgif).
Proof. exact PresetImg_qapart.IMG_QAPART_B. Qed.

Section r. Context {rc : YM05.RunCeil}.
Theorem CONST_APART_preset_B : CONST_APART (IM := AImg_cgif).
Proof. intros B ly c TS LY Hc. exact (PresetImg_constapart.CONST_APART_B B ly c TS LY Hc). Qed.
End r.
