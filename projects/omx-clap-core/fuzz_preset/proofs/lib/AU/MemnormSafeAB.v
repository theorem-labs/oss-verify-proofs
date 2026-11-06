(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormSafecgif.v (a working branch 29b7505aa27, file sha256 6db4365d0a7a) onto omx-clap-core/fuzz_preset's asan-ubsan image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53; pin f8f98a95bc52); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin B (pinned fuzz_preset.asan-ubsan f8f98a95bc52, twin 3b5e1a099b53; this file at 74f20580f552) to B' (#102 pin d663f82d7f48, twin c90d4fa54d43) by the relocation route of record, frozen alreloc a5c53bb2bed4ad03 (a Theorem Labs lane's internal file alreloc.py.frozen-a5c53bb2bed4ad03), --assume-source, --resolve resolve-B102.txt (sha256 5cd2316e3413; internal record) (1 line name this file); 1 numeral changed. *)
(* Theorem Labs, 2026-10: two cgif_file image facts for the memnorm arm twins (task MEMNORM): where a byte may be
   overwritten without breaking YAkMemnorm.memnorm (MemnormT.mn_safe: not read-only, below TASK_SIZE).
   rule 24: no function proved (kind: image lemmas).
   - [mn_safe_rw]: a byte in [0xa2000, TASK_SIZE).  tfibsegs' segments at or above 0xa2000 are writable
     (MemnormHitGB.tfib_seg_rw); above them there is no segment.
   - [mn_safe_offimg]: a byte off the image [TFIB_IMG_LO, TFIB_IMG_END) (YF0x.v:24, :36) and below TASK_SIZE: no
     segment holds it (MemnormHitGB.tfib_seg_range, from YF0x.v:249 / :257). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormHitGB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Local Open Scope Z_scope.

Lemma mn_safe_rw : forall x : word, 0xa2000 <= bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x [H1 H2]. split; [|exact H2]. unfold YAkMemnorm.ro_addr.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
rewrite (MemnormHitGB.tfib_seg_rw (bv_unsigned x) seg H1 F). reflexivity.
Qed.

Lemma mn_safe_offimg : forall x : word, bv_unsigned x < TFIB_IMG_LO \/ TFIB_IMG_END <= bv_unsigned x ->
  bv_unsigned x < TASK_SIZE -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hoff Hlt. split; [|exact Hlt]. unfold YAkMemnorm.ro_addr.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
exfalso. pose proof (MemnormHitGB.tfib_seg_range _ _ F) as R. lia.
Qed.
