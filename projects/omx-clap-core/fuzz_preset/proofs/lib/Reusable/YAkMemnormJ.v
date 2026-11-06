(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (h-hpreset-7): the start-up kit's memnorm (YAkMemnorm.v) is
   YAjMemnorm.memnorm (= Lib.Mem.mem_inv /\ MemNorm.task_mem, the walks' aj_memnorm body), by conversion. Only a
   leaf may require this file: it loads lib/Lib/LiaTwx2.v through YAjMemnorm.v (see YAkMemnorm.v's header).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAjMemnorm YAkMemnorm.

Lemma memnorm_kit_j : forall (segs : list Segment) (m : word -> option byte),
  YAkMemnorm.memnorm segs m -> YAjMemnorm.memnorm segs m.
Proof. intros segs m H. exact H. Qed.
