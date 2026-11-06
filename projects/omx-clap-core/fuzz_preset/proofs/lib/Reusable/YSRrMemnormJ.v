(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the YAjMemnorm.memnorm instance of YC80x.v's srr_inv_laws
   (memnorm m := Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m, YAjMemnorm.v:41, the body of the walks' aj_memnorm).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).

   WHY A SEPARATE FILE: YAjMemnorm.v requires lib/Lib/Mem.v, which loads lib/Lib/LiaTwx2.v, and LiaTwx2.v redefines lia
   globally (`Ltac lia ::=`; YAkMemnorm.v header). YSRrMemnorm.v is deliberately override-free, so this instance cannot
   live there: do NOT fold it back. Only a leaf may require this file (h-hpreset-7 11:19Z, h-rw-pre-5's finding).
   YSRrMemnorm.srr_inv_laws_memnorm_k is the same instance over YAkMemnorm.memnorm (the same body); a file that need not
   name YAjMemnorm.memnorm uses that one.

   The msteps fact is YAkMemnorm's: its premise takes YAjMemnorm.memnorm by conversion and YAkMemnormJ.memnorm_kit_j
   gives back YAjMemnorm.memnorm. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC80x YSRrMemnorm YAjMemnorm YAkMemnorm YAkMemnormJ.

Lemma srr_inv_laws_memnorm : forall segs : list Segment, YC80x.srr_inv_laws segs (YAjMemnorm.memnorm segs).
Proof.
intros segs. split.
- exact (YAjMemnorm.memnorm_mrestrict segs).
- intros ms ms' Hms Hm. apply YAkMemnormJ.memnorm_kit_j.
  exact (YAkMemnorm.memnorm_msteps segs ms ms' Hms Hm).
- exact (YAjMemnorm.memnorm_munrestrict segs).
Qed.

Check srr_inv_laws_memnorm.
