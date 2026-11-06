(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the PURE facts of pj_free's image-B walk (lib/B/Prog/pj_free_defs.v), machine-free:
   - the observer: pf_reach composes (pf_reach_trans), lifts past a suffix (pf_reach_app), one step each
     (pf_reach_free1 / pf_reach_null1); pf_safe at the start (pf_safe_here), after a stretch (pf_safe_after), on a
     prefix (pf_safe_prefix);
   - the ordered shape against the text's: pj_foR is pj_fdR with F a permutation of D (pj_foR_fdR), every pj_fdR has its F
     (pj_fdR_foR); its blocks are lblk's (pj_foR_lblk, pf_oitemsR_lblk); it survives a memory and ledger change that
     keeps its footprint (pj_foR_frame, pf_oitemsR_frame);
   - THE ORDER AGAINST THE MODEL: a tree node whose blocks have the writer's sizes (map of the requests of D =
     PresetReqAtNoMiss.tblk t, D in pj_nodeR's order) has an F whose requests are PresetReqAt.fo t, in order
     (pj_free_fo).
   proves no function (kind: pure lemmas). No machine state, no image constant, no address.
   MOVED, statements and proofs unchanged, from h-rw-man-5's image-B lane (h-rw-man-5's YES 2026-10-29, relayed by
   h-rw-pre-5): lib/B/Prog/pj_free_pure.v blob b54814f20036 at origin/cold/h-rw-man-5-b-pjfree-rb ab365ca51d3, lines
   1-338 (Sections reach and shape up to pf_oitemsR_frame), byte-identical except this header paragraph and the one Require line: `lib.B.Prog Require Import
   pj_free_defs` is now `lib.A.Prog Require Import PjFreeCommon`, which holds
   pj_free_defs.v :76-190 unchanged (PjFreeCommon.v blob 58ecccbd017b, origin/cold/h-hpreset-7-walk-S6 c47e66122d3).
   CUT OVER 2026-10-29 (kit-oldpin bd0d3c3a486b, announced 17:42Z): the kit took pj_free_pure.v's whole Section shape
   (lib/A/PRH_PjOrder.v e5917626b82b); this file keeps only Section reach (the observer's lemmas) and cites the kit
   for the rest. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the observer ---- *)
Section reach.
Variable FX : pf_obs.

Lemma pf_reach_trans : forall L1 ly1 S1 L2 ly2 S2 L3 ly3 S3,
  pf_reach FX L1 ly1 S1 L2 ly2 S2 -> pf_reach FX L2 ly2 S2 L3 ly3 S3 -> pf_reach FX L1 ly1 S1 L3 ly3 S3.
Proof.
intros L1 ly1 S1 L2 ly2 S2 L3 ly3 S3 H1 H2. revert H2.
induction H1; intros H2.
- exact H2.
- eapply pfr_null; [eassumption | apply IHpf_reach; exact H2].
- eapply pfr_free; [eassumption | apply IHpf_reach; exact H2].
Qed.

Lemma pf_reach_app : forall L ly S L' ly' S' R,
  pf_reach FX L ly S L' ly' S' -> pf_reach FX (L ++ R) ly S (L' ++ R) ly' S'.
Proof.
intros L ly S L' ly' S' R H.
induction H.
- apply pfr_refl.
- eapply pfr_null; eassumption.
- cbn [app]. eapply pfr_free; eassumption.
Qed.

Lemma pf_reach_free1 : forall b L ly S ly' S', FX ly S ly' S' (Some b) -> pf_reach FX (b :: L) ly S L ly' S'.
Proof. intros b L ly S ly' S' H. eapply pfr_free; [exact H | apply pfr_refl]. Qed.

Lemma pf_reach_null1 : forall L ly S ly' S', FX ly S ly' S' None -> pf_reach FX L ly S L ly' S'.
Proof. intros L ly S ly' S' H. eapply pfr_null; [exact H | apply pfr_refl]. Qed.

Lemma pf_safe_here : forall PB L ly S, pf_safe FX PB L ly S -> PB S.
Proof. intros PB L ly S H. unfold pf_safe in H. exact (H L ly S (pfr_refl FX L ly S)). Qed.

Lemma pf_safe_after : forall PB L ly S L' ly' S',
  pf_safe FX PB L ly S -> pf_reach FX L ly S L' ly' S' -> pf_safe FX PB L' ly' S'.
Proof.
intros PB L ly S L' ly' S' H R. unfold pf_safe in *. intros F'' ly'' S'' R'.
apply (H F'' ly'' S''). eapply pf_reach_trans; [exact R | exact R'].
Qed.

Lemma pf_safe_prefix : forall PB L R ly S, pf_safe FX PB (L ++ R) ly S -> pf_safe FX PB L ly S.
Proof.
intros PB L R ly S H. unfold pf_safe in *. intros F' ly' S' Hr.
apply (H (F' ++ R) ly' S'). apply pf_reach_app. exact Hr.
Qed.
End reach.

(* ---- the ordered shape: the KIT's now (lib/A/PRH_PjOrder.v e5917626b82b Section shape, kit-oldpin bd0d3c3a486b),
   cited, not copied ---- *)
