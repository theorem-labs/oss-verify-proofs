(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainUB.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 a40e841d8d00) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the drain's LEAF on a recycle arm - DIfaceR.drain_leaf_g with
   MnEnq.acall_raw_em_x (the form MnDrain.de_drain_m_t takes, MnDrain.v:50), at the configuration Recycle's
   epilogue returns to.  The twin of DMdrainT5.leaf_ret, which fixes the final world to the entry's: on a
   recycle arm DoRecycle's callees may give back holes, so the final world [W2] is only above the entry's
   (wle W W2), and the view frame is a premise of its own (DoRecycle's acall_post_x states it across the two
   worlds; the raw frame alone does not give it where a hole was given back).
   rule 24: no function proved (kind: the leaf of segments already walked; the lane's reuse search is
   LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DIfaceR ErrnoG MemnormT MnEnq.
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

(* the invariant at the end (DMiface.di_requar_e after DoRecycle has recycled everything) *)
Hypothesis HARX : ARX inst ly S' W2 mem' md'.
Hypothesis HSHR : forall a, AOX ly S' a -> AOX ly X a.
Hypothesis HWLE : wle W W2.
(* the model and the registers Recycle's epilogue returns *)
Hypothesis HMD : same_io md md'.
Hypothesis HREG : aregs_preserved regs regs'.
Hypothesis HPRES : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W2) mem' a.
(* the composed frames: on the view across the two worlds, and on the raw memory *)
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
