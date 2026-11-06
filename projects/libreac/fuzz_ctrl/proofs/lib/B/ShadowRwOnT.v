(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ShadowRwOnT.v 6e434d2c487 (the blob this tree had at release c5e779efe8c) (a working branch 9ec78006def: fl_shadow_rw_on moved to lib/B/ShadowRwOnK.v and the unused B.Prog.RcAsanRT Require dropped, as A; first twinned from blob 62335f14b9a at ea8776b2302): character-identical to this tree's A apart from the image prefix (A.AsanRT / A.Img0 / A.ShadowRwOn / A.AsanRTFacts / A.MemNorm / A.MemNormTr / A.Prog.ImgBounds / A.Prog.MemMono -> B.*; lib/A/ -> lib/B/ and "image A" -> "image B" in the comment).  B.Prog.MemMono is lib/B/Prog/MemMono.v, the prefix twin of A's.  The comment's line references are A's text unchanged: B's AsanRTFacts.v:54 and MemNormTr.v:113 / :214 are the same lines, B's Prog/MemMono.v twin of :49 is :50 (its header line); Seg/A1.v:325, F18.v:232, P7.v:136 are image A's stage files. *)
(* lib/B/ShadowRwOnT.v -- route (C): the TRANSPORTS of B.ShadowRwOn.shadow_rw_on across a run's memory relation, one
   twin per shared shadow_rw transport of image B (a Theorem Labs lane 09:24Z, from a Theorem Labs lane's R19F test).  ONE WRITER: a Theorem Labs lane.
   rule 24: no function proved.  Kept out of the leaf ShadowRwOn.v because these Require MemNorm / MemMono / the asan
   FP library; a callee contract that states shadow_rw_on Requires only the leaf.

   Each twin is the original's proof with the region guard P carried through (the originals argue per address):
     shadow_rw_on_kept       <- B.AsanRTFacts.shadow_rw_kept      (AsanRTFacts.v:54; meta_kept + wmono)
     shadow_rw_on_rel        <- the stage-local forward shadow_rw_rel (Seg/A1.v:325, F18.v:232, P7.v:136, ...; mem_rel)
     shadow_rw_on_normalize  <- B.MemNormTr.shadow_rw_normalize   (MemNormTr.v:113; ro_agree)
     shadow_rw_on_of_rel     <- B.MemNormTr.shadow_rw_of_rel      (MemNormTr.v:214; mem_rel, backward)
     shadow_rw_on_mem_mono   <- B.Prog.MemMono.shadow_rw_mono     (MemMono.v:49; wmono + rd_mono)
   fl_shadow_rw_on (<- RcAsanFPLib.fl_shadow_rw) moved to lib/B/ShadowRwOnK.v (12:1xZ; light closure). *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0 B.ShadowRwOn B.AsanRTFacts B.MemNorm B.MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.ImgBounds B.Prog.MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.

Lemma shadow_rw_on_kept : forall P m m', B.ShadowRwOn.shadow_rw_on P m -> B.AsanRTFacts.meta_kept m m' ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H MK WM a Hp Ha. destruct (H a Hp Ha) as [Hw (b & Hb)]. split; [apply WM, Hw|].
  exists b. rewrite MK by exact Ha. exact Hb.
Qed.

Lemma shadow_rw_on_rel : forall P m m0, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m0.
Proof.
  intros P m m0 REL H a Hp Ha. destruct (H a Hp Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr B.Img0.rsegs (lib.Lib.Mem.wa a) = false).
  { apply B.MemNormTr.ro_addr_above_img.
    unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Ha.
    unfold B.Prog.ImgBounds.IMG_HI. lia. }
  split; [rewrite (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite <- (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ REL). exact Hb.
Qed.

Lemma shadow_rw_on_normalize : forall P m, B.MemNorm.ro_agree B.Img0.rsegs m ->
  B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P (B.MemNorm.normalize B.Img0.rsegs m).
Proof.
  intros P m RO H. exact (shadow_rw_on_rel P m _ (B.MemNorm.mem_rel_normalize B.Img0.rsegs m RO) H).
Qed.

Lemma shadow_rw_on_of_rel : forall P m m0, B.MemNorm.mem_rel B.Img0.rsegs m m0 ->
  B.ShadowRwOn.shadow_rw_on P m0 -> B.ShadowRwOn.shadow_rw_on P m.
Proof.
  intros P m m0 REL H a Hp Ha. destruct (H a Hp Ha) as [Hv [b Hb]].
  pose proof (B.MemNorm.ro_false_of_wview B.Img0.rsegs m m0 _ REL Hv) as E.
  split; [rewrite <- (B.MemNorm.wview_rel_rw B.Img0.rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite (B.MemNorm.mrd_rel B.Img0.rsegs m m0 _ REL). exact Hb.
Qed.

Lemma shadow_rw_on_mem_mono : forall P m m', B.ShadowRwOn.shadow_rw_on P m ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> B.Prog.MemMono.rd_mono m m' -> B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H Hw Hr a Hp Ha. destruct (H a Hp Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Print Assumptions shadow_rw_on_normalize.
Print Assumptions shadow_rw_on_of_rel.
Print Assumptions shadow_rw_on_kept.
Print Assumptions shadow_rw_on_mem_mono.
