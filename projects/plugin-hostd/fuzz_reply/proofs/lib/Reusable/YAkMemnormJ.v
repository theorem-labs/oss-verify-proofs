(* CARRIED from fuzz_preset cf67bba98b9 proofs/omx-clap-core/fuzz_preset/lib/Reusable/YAkMemnormJ.v, sha256 82f88552384a37dd9d2a3e2122aa53045bdc4621ef34b4290b8e5cb36db027c4.
   Changes: the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib ->
   OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib (2 occurrences), and the two licence lines removed.
   The body is otherwise unchanged. *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (h-hpreset-7): the start-up kit's memnorm (YAkMemnorm.v) is
   YAjMemnorm.memnorm (= Lib.Mem.mem_inv /\ MemNorm.task_mem, the walks' aj_memnorm body), by conversion. Only a
   leaf may require this file: it loads lib/Lib/LiaTwx2.v through YAjMemnorm.v (see YAkMemnorm.v's header).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAjMemnorm YAkMemnorm.

Lemma memnorm_kit_j : forall (segs : list Segment) (m : word -> option byte),
  YAkMemnorm.memnorm segs m -> YAjMemnorm.memnorm segs m.
Proof. intros segs m H. exact H. Qed.
