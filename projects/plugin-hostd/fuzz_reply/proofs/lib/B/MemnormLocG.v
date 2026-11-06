(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormLocG.v (commit 30a1993588f, c5 + memnorm; file sha256 2c1064554072) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MemnormLocG.v (commit d2dafa219c1, file sha256 3e27aa9de74e) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Theorem Labs, 2026-10 (task MEMNORM, callee add-ons): the image-free part of the location lemmas for the memnorm
   keeps (brief CALLEE-BRIEF.md (sha256 473ea00fb987; internal record)).  rule 24: no function proved (kind: generic lemmas).

   Over any segment list [segs] (an instance takes its own: cgif_file tfibsegs / im_segs, preset its own), no image
   constant:
   - [memnorm_keep_refl] / [memnorm_keep_trans]: keeps chain (a nested callee's `_em` keep between two window keeps);
   - [mn_safe_noseg]: a byte no segment holds, below TASK_SIZE, is MemnormT.mn_safe;
     [mn_safe_wseg]: so is a byte whose segment (if any) is writable;
   - [memnorm_keep_window]: a window frame `mem' x = mem x` outside W, with every byte of W mn_safe, gives the keep
     (MemnormT.memnorm_frame, restated under the name the callee arms use); [memnorm_keep_window2] for a frame with
   The cgif_file location facts (the callee windows YFf4.D / YFf1.D / YFf2.D / YFey.D, zone3 extents) are in
   MemnormLoc.v, which Requires this file and restates memnorm_keep_refl / memnorm_keep_trans under its own name. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Local Open Scope Z_scope.

Lemma memnorm_keep_refl : forall segs (m : word -> option byte), MemnormT.memnorm_keep segs m m.
Proof. intros segs m H. exact H. Qed.

Lemma memnorm_keep_trans : forall segs (m1 m2 m3 : word -> option byte),
  MemnormT.memnorm_keep segs m1 m2 -> MemnormT.memnorm_keep segs m2 m3 -> MemnormT.memnorm_keep segs m1 m3.
Proof. intros segs m1 m2 m3 H1 H2 H. exact (H2 (H1 H)). Qed.

Lemma mn_safe_noseg : forall segs (x : word),
  find_segment segs (bv_unsigned x) 1 = None -> bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe segs x.
Proof. intros segs x F H. split; [unfold YAkMemnorm.ro_addr; rewrite F; reflexivity | exact H]. Qed.

Lemma mn_safe_wseg : forall segs (x : word),
  (forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe segs x.
Proof.
intros segs x HW H. split; [|exact H]. unfold YAkMemnorm.ro_addr.
destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:F; [rewrite (HW seg eq_refl); reflexivity | reflexivity].
Qed.

Lemma memnorm_keep_window : forall segs (W : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, W (bv_unsigned x) -> MemnormT.mn_safe segs x) ->
  (forall x : word, ~ W (bv_unsigned x) -> mem' x = mem x) ->
  MemnormT.memnorm_keep segs mem mem'.
Proof. exact MemnormT.memnorm_frame. Qed.

Lemma memnorm_keep_window2 : forall segs (W1 W2 : Z -> Prop) (mem mem' : word -> option byte),
  (forall x : word, W1 (bv_unsigned x) -> MemnormT.mn_safe segs x) ->
  (forall x : word, W2 (bv_unsigned x) -> MemnormT.mn_safe segs x) ->
  (forall x : word, ~ W1 (bv_unsigned x) -> ~ W2 (bv_unsigned x) -> mem' x = mem x) ->
  MemnormT.memnorm_keep segs mem mem'.
Proof.
intros segs W1 W2 mem mem' H1 H2 F.
apply (MemnormT.memnorm_frame segs (fun a => W1 a \/ W2 a) mem mem').
- intros x [Hx|Hx]; [exact (H1 x Hx) | exact (H2 x Hx)].
- intros x N. apply F; intros X; apply N; [left | right]; exact X.
Qed.
