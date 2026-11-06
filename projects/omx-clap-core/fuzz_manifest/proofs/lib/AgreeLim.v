From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YO0d.
Local Open Scope Z_scope.
Definition LIM_AG : Z := target_alloc_limit.

Lemma LIM_AG_eq : LIM_AG = 2 ^ 39.
Proof. reflexivity. Qed.

Definition limlaw_at {rc : RunCeil} (lim : Z) (B : malloc_syms) (API : AllocAPI B) : Prop :=
  forall L A mem md, aa_MR API L A mem md -> lim <= vm_limit (m_vmmaps md).
