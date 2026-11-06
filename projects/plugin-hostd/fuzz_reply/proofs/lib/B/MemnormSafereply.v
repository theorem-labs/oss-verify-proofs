(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormSafecgif.v (commit 30a1993588f, c5 + memnorm; file sha256 6db4365d0a7a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MemnormSafereply.v (commit d2dafa219c1, file sha256 7496364a8255) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Theorem Labs, 2026-10: two cgif_file image facts for the memnorm arm twins (task MEMNORM): where a byte may be
   overwritten without breaking YAkMemnorm.memnorm (MemnormT.mn_safe: not read-only, below TASK_SIZE).
   rule 24: no function proved (kind: image lemmas).
   - [mn_safe_rw]: a byte in [0x9d000, TASK_SIZE).  tfibsegs' segments at or above 0x9d000 are writable
     (MemnormHitG.tfib_seg_rw); above them there is no segment.
   - [mn_safe_offimg]: a byte off the image [TFIB_IMG_LO, TFIB_IMG_END) (YF0x.v:24, :36) and below TASK_SIZE: no
     segment holds it (MemnormHitG.tfib_seg_range, from YF0x.v:249 / :257). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormHitG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
Local Open Scope Z_scope.

Lemma mn_safe_rw : forall x : word, 0x9d000 <= bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x [H1 H2]. split; [|exact H2]. unfold YAkMemnorm.ro_addr.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
rewrite (MemnormHitG.tfib_seg_rw (bv_unsigned x) seg H1 F). reflexivity.
Qed.

Lemma mn_safe_offimg : forall x : word, bv_unsigned x < TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned x ->
  bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hoff Hlt. split; [|exact Hlt]. unfold YAkMemnorm.ro_addr.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
exfalso. pose proof (MemnormHitG.tfib_seg_range _ _ F) as R. lia.
Qed.
