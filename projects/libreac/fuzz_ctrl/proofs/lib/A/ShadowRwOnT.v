(* lib/A/ShadowRwOnT.v -- route (C): the TRANSPORTS of A.ShadowRwOn.shadow_rw_on across a run's memory relation, one
   twin per shared shadow_rw transport of image A (a Theorem Labs lane 09:24Z, from a Theorem Labs lane's R19F test).  ONE WRITER: a Theorem Labs lane.
   rule 24: no function proved.  Kept out of the leaf ShadowRwOn.v because these Require MemNorm / MemMono / the asan
   FP library; a callee contract that states shadow_rw_on Requires only the leaf.

   Each twin is the original's proof with the region guard P carried through (the originals argue per address):
     shadow_rw_on_kept       <- A.AsanRTFacts.shadow_rw_kept      (AsanRTFacts.v:54; meta_kept + wmono)
     shadow_rw_on_rel        <- the stage-local forward shadow_rw_rel (Seg/A1.v:325, F18.v:232, P7.v:136, ...; mem_rel)
     shadow_rw_on_normalize  <- A.MemNormTr.shadow_rw_normalize   (MemNormTr.v:113; ro_agree)
     shadow_rw_on_of_rel     <- A.MemNormTr.shadow_rw_of_rel      (MemNormTr.v:214; mem_rel, backward)
     shadow_rw_on_mem_mono   <- A.Prog.MemMono.shadow_rw_mono     (MemMono.v:49; wmono + rd_mono)
   fl_shadow_rw_on (<- RcAsanFPLib.fl_shadow_rw) moved to lib/A/ShadowRwOnK.v (12:1xZ; light closure). *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.Img0 A.ShadowRwOn A.AsanRTFacts A.MemNorm A.MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.ImgBounds A.Prog.MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.

Lemma shadow_rw_on_kept : forall P m m', A.ShadowRwOn.shadow_rw_on P m -> A.AsanRTFacts.meta_kept m m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m' -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H MK WM a Hp Ha. destruct (H a Hp Ha) as [Hw (b & Hb)]. split; [apply WM, Hw|].
  exists b. rewrite MK by exact Ha. exact Hb.
Qed.

Lemma shadow_rw_on_rel : forall P m m0, A.MemNorm.mem_rel A.Img0.rsegs m m0 ->
  A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m0.
Proof.
  intros P m m0 REL H a Hp Ha. destruct (H a Hp Ha) as [Hv [b Hb]].
  assert (E : lib.Lib.Mem.ro_addr A.Img0.rsegs (lib.Lib.Mem.wa a) = false).
  { apply A.MemNormTr.ro_addr_above_img.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Ha.
    unfold A.Prog.ImgBounds.IMG_HI. lia. }
  split; [rewrite (A.MemNorm.wview_rel_rw A.Img0.rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite <- (A.MemNorm.mrd_rel A.Img0.rsegs m m0 _ REL). exact Hb.
Qed.

Lemma shadow_rw_on_normalize : forall P m, A.MemNorm.ro_agree A.Img0.rsegs m ->
  A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P (A.MemNorm.normalize A.Img0.rsegs m).
Proof.
  intros P m RO H. exact (shadow_rw_on_rel P m _ (A.MemNorm.mem_rel_normalize A.Img0.rsegs m RO) H).
Qed.

Lemma shadow_rw_on_of_rel : forall P m m0, A.MemNorm.mem_rel A.Img0.rsegs m m0 ->
  A.ShadowRwOn.shadow_rw_on P m0 -> A.ShadowRwOn.shadow_rw_on P m.
Proof.
  intros P m m0 REL H a Hp Ha. destruct (H a Hp Ha) as [Hv [b Hb]].
  pose proof (A.MemNorm.ro_false_of_wview A.Img0.rsegs m m0 _ REL Hv) as E.
  split; [rewrite <- (A.MemNorm.wview_rel_rw A.Img0.rsegs m m0 _ REL E); exact Hv|].
  exists b. rewrite (A.MemNorm.mrd_rel A.Img0.rsegs m m0 _ REL). exact Hb.
Qed.

Lemma shadow_rw_on_mem_mono : forall P m m', A.ShadowRwOn.shadow_rw_on P m ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m' -> A.Prog.MemMono.rd_mono m m' -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H Hw Hr a Hp Ha. destruct (H a Hp Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Print Assumptions shadow_rw_on_normalize.
Print Assumptions shadow_rw_on_of_rel.
Print Assumptions shadow_rw_on_kept.
Print Assumptions shadow_rw_on_mem_mono.
