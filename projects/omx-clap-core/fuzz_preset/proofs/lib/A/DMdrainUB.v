(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainUB.v (commit 67deba317dfb, blob 7bfd64ac81d0) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR ErrnoG MemnormT MnEnq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variables (W W2 : world tfibsegs) (ly : alayout) (X S' : astate).
Variables (regs regs' : bvmap 5 word) (mem mem' : word -> option byte) (md md' : Model).
Variable inst : Z.
Let sp0 : Z := spZ regs.

Hypothesis HARX : ARX inst ly S' W2 mem' md'.
Hypothesis HSHR : forall a, AOX ly S' a -> AOX ly X a.
Hypothesis HWLE : wle W W2.

Hypothesis HMD : same_io md md'.
Hypothesis HREG : aregs_preserved regs regs'.
Hypothesis HPRES : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W2) mem' a.

Hypothesis HVIEW : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X a -> ~ AOX ly S' a ->
  ~ ascratch B YFeuC.DSTACK regs a -> aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a.
Hypothesis HRAW : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ AOX ly S' (bv_unsigned x) ->
  ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) -> mem' x = mem x.
Hypothesis HERR : ErrnoG.errno_kept B mem mem'.
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs mem mem'.

Lemma post_recyc : acall_post_x B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly S' W2 regs' mem' md'.
Proof.
unfold acall_post_x. splits.
- exact HARX.
- apply layout_le_refl.
- exact HWLE.
- exact HREG.
- exact HMD.
- intros a A1 A2 A3 A4 _. exact (HVIEW a A1 A2 A3 A4).
- exact HPRES.
Qed.

Lemma raw_recyc : acall_raw_x B AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly S' W2 regs' mem' md'.
Proof. intros x A1 A2 A3 _. exact (HRAW x A1 A2 A3). Qed.

Theorem leaf_recyc : DIfaceR.drain_leaf_g B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md
(tt, S') W2 (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
exists regs', mem', md'. split; [reflexivity|]. split; [exact post_recyc|].
unfold MnEnq.acall_raw_em_x. split; [exact raw_recyc | split; [exact HERR | exact HMN]].
Qed.
End e.
End c.
