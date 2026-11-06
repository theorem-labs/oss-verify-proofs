(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainUB.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail; file sha256 a40e841d8d00) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainUB.v, with its module paths and module names changed; 14 of its 69 lines of code are new or changed and 9 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b): the lib/B twin of lib/A/DMdrainUBRh.v by path (a working branch 67deba317dfb), with lib.A -> lib.B in the Require lines and image B's names (the rows _reply_B, YGcfInstCdeallocB; CfParams_reply stays lib/A/CfParamsReply's, the one record the B files use). *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b; drain-rh split row (b2)): the drain's LEAF on a recycle arm at the
   re-hide twin - DIfaceRh.drain_leaf_g_rh with MnEnq.acall_raw_em_x, the twin of DMdrainUB.leaf_recyc.  On a
   recycle arm DoRecycle's callees may re-hide a dead secondary's shadow, so the final world [W2] is only above the
   entry's OFF that shadow (wle_in (dead_shadow_new ly X S')), and the view frame excepts it: the primed post
   YGcfRehidePost.acall_post_x_rh states both.  The raw frame and the errno / memnorm keeps are DMdrainUB's.
   A new file: DMdrainUB.v stays byte-unchanged.
   rule 24: no function proved (kind: the leaf of segments already walked, at the primed post). *)
(* DRAFT (reply lib/A, Main's location decision 2026-10-30): imports follow a Theorem Labs lane's DMdrainTFRh.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR ErrnoG MemnormT MnEnq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DIfaceRh.
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
(* the re-hide twin's world order: above the entry's off the dead secondaries' new shadow *)
Hypothesis HWLE : wle_in tfibsegs (YGcfRehidePost.dead_shadow_new ly X S') W W2.
(* the model and the registers Recycle's epilogue returns *)
Hypothesis HMD : same_io md md'.
Hypothesis HREG : aregs_preserved regs regs'.
Hypothesis HPRES : forall a, sp0 - YFeuC.DSTACK <= a < sp0 -> apresent (w_H W2) mem' a.
(* the composed frames: on the view across the two worlds (off the re-hidden shadow), and on the raw memory *)
Hypothesis HVIEW : forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly X a -> ~ AOX ly S' a ->
  ~ ascratch B YFeuC.DSTACK regs a -> ~ YGcfRehidePost.dead_shadow_new ly X S' a ->
  aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W) mem a.
Hypothesis HRAW : forall x : word, ~ AOX ly X (bv_unsigned x) -> ~ AOX ly S' (bv_unsigned x) ->
  ~ ascratch B YFeuC.DSTACK regs (bv_unsigned x) -> mem' x = mem x.
Hypothesis HERR : ErrnoG.errno_kept B mem mem'.
Hypothesis HMN : MemnormT.memnorm_keep tfibsegs mem mem'.

Lemma post_recyc_rh : YGcfRehidePost.acall_post_x_rh B ARX AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False)
  ly S' W2 regs' mem' md'.
Proof.
unfold YGcfRehidePost.acall_post_x_rh. splits.
- exact HARX.
- apply layout_le_refl.
- exact HWLE.
- exact HREG.
- exact HMD.
- intros a A1 A2 A3 A4 _ A6. exact (HVIEW a A1 A2 A3 A4 A6).
- exact HPRES.
Qed.

Lemma raw_recyc_rh : acall_raw_x B AOX inst YFeuC.DSTACK ly X W regs mem md (fun _ => False) ly S' W2 regs' mem' md'.
Proof. intros x A1 A2 A3 _. exact (HRAW x A1 A2 A3). Qed.

Theorem leaf_recyc_rh : DIfaceRh.drain_leaf_g_rh B ARX AOX (MnEnq.acall_raw_em_x B AOX) inst ly X W regs mem md
(tt, S') W2 (cfg_at tfibsegs (raZ regs) regs' mem' md').
Proof.
exists regs', mem', md'. split; [reflexivity|]. split; [exact post_recyc_rh|].
unfold MnEnq.acall_raw_em_x. split; [exact raw_recyc_rh | split; [exact HERR | exact HMN]].
Qed.
End e.
End c.
