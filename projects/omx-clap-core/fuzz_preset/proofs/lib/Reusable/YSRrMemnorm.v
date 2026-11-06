(* Copyright 2026 Anthropic PBC *)
(* WHY THE INVARIANT IS IN THE STATEMENT (a Theorem Labs lane 12:18Z / 12:23Z): an SRr post is OPAQUE once Qed, so a fact about the end state must be in the segment's statement; a generic SRr -> memnorm is NOT provable (SRr is CPS). The three carriers:
   srr_inv_laws carries P across engine steps (runner runs, hand steps), srr_inv_call across a callee's memnorm keep
   implication, srr_inv_mn hands memnorm to a callee that demands it at entry. P is instantiated once at each function's
   top as `fun m => memnorm segs mem0 -> memnorm segs m` (srr_inv_laws_imp / srr_inv_call_imp / srr_inv_mn_imp).
  *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, instances of YC80x.v's memory-invariant laws srr_inv_laws (h-hpreset-7 09:59Z;
   owner h-w6u-pre; engine file of c-omx-alloc-preset-s1b). The runner part that carries an invariant P (srr_inv_laws,
   SRr_msteps_inv, SRr_step_inv and the _inv runner lemmas) is in YC80x.v; the runners paj_run_*_inv and their tactics
   are in YC1fPx.v.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).

   WHAT:
   - srr_inv_laws_memnorm_k, the memnorm instance over YAkMemnorm.memnorm (the body of the walks' aj_memnorm, written
     over LPS only; YAkMemnormJ.memnorm_kit_j converts), from YAkMemnorm's memnorm_mrestrict / memnorm_msteps /
     memnorm_munrestrict. With it a walk keeps aj_memnorm from its entry to a call site without the universal memnorm
     law (refuted). YSRrMemnormJ.v holds the same instance over YAjMemnorm.memnorm.
   - srr_inv_laws_imp: the keep `P mem0 -> P m` is itself an invariant.

   OVERRIDE-FREE: the file is deliberately override-free; the YAj instance lives in YSRrMemnormJ.v. The YAj memnorm
   file loads lib/Lib/Mem.v and through it lib/Lib/LiaTwx2.v, whose `Ltac lia ::=` changes lia in every later proof
   (YAkMemnorm.v header). This file requires YAkMemnorm only (h-hpreset-7 11:19Z, h-rw-pre-5's finding). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.

(* The memnorm instance, from YAkMemnorm.v's own lemmas (YAkMemnorm requires no file that overrides lia). *)
Lemma srr_inv_laws_memnorm_k : forall segs : list Segment, srr_inv_laws segs (YAkMemnorm.memnorm segs).
Proof.
intros segs. split.
- exact (YAkMemnorm.memnorm_mrestrict segs).
- exact (YAkMemnorm.memnorm_msteps segs).
- exact (YAkMemnorm.memnorm_munrestrict segs).
Qed.

(* the laws survive an implication from a fixed memory: the keep `P mem0 -> P m` is itself an invariant
   (h-rw-pre-5's WalkS4, ruled into this file by h-hpreset-7 11:20Z) *)
Lemma srr_inv_laws_imp : forall (segs : list Segment) (P : (word -> option byte) -> Prop) (mem0 : word -> option byte),
  srr_inv_laws segs P -> srr_inv_laws segs (fun m => P mem0 -> P m).
Proof.
intros segs P mem0 [L1 L2 L3]. split.
- intros H m Hm H0. exact (L1 H m (Hm H0)).
- intros ms ms' Hs Hm H0. exact (L2 ms ms' Hs (Hm H0)).
- intros H full m' Hf Hm H0. exact (L3 H full m' (Hf H0) (Hm H0)).
Qed.

(* the CALL variant (h-hpreset-7 12:22Z, h-rw-pre-5's WalkS7a): a callee whose m-form post gives only the memnorm keep
   `memnorm m -> memnorm m'` carries P across the call when P is closed under that keep. A sibling definition, not a field
   of srr_inv_laws (it is true only at memnorm-derived P, e.g. the keep form below). *)
Definition srr_inv_call (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop :=
  forall m m', (YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs m') -> P m -> P m'.

Lemma srr_inv_call_imp : forall (segs : list Segment) (mem0 : word -> option byte),
  srr_inv_call segs (fun m => YAkMemnorm.memnorm segs mem0 -> YAkMemnorm.memnorm segs m).
Proof. intros segs mem0 m m' Hk HP H0. exact (Hk (HP H0)). Qed.

(* the ENTRY variant (h-hpreset-7 12:23Z, h-rw-pre-5's WalkIval2): P hands memnorm to a callee that demands it at entry.
   Spelled over YAkMemnorm.memnorm (this file is override-free); YAjMemnorm.memnorm has the same body (mem_inv /\ task_mem),
   so a YAj-form consumer converts with `exact`. *)
Definition srr_inv_mn (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop :=
  forall m, P m -> YAkMemnorm.memnorm segs m.

Lemma srr_inv_mn_imp : forall (segs : list Segment) (mem0 : word -> option byte),
  YAkMemnorm.memnorm segs mem0 ->
  srr_inv_mn segs (fun m => YAkMemnorm.memnorm segs mem0 -> YAkMemnorm.memnorm segs m).
Proof. intros segs mem0 HMN0 m H. exact (H HMN0). Qed.

Check srr_inv_laws_memnorm_k.
Check srr_inv_laws_imp.
Check srr_inv_call.
Check srr_inv_call_imp.
Check srr_inv_mn.
Check srr_inv_mn_imp.
