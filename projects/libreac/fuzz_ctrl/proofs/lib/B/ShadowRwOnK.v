(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ShadowRwOnK.v (an earlier version, blob 7c2643daafc, not in this delivery) (a working branch 88103cea50c / a working branch e60fb7a9ee7: A's header motive corrected, a Theorem Labs lane 12:38Z; first twinned from blob 07ccb82106b, written on a working branch 9ec78006def): character-identical to that earlier A apart from lane names and the image prefix (A.AsanRT / A.Img0 / A.ShadowRwOn / A.Prog.RcAsanRT / A.Prog.RcAsanFPLib -> B.*; lib/A/ -> lib/B/ in the comment).  The comment's closure counts (27 files, ShadowRwOnT's 112) are a Theorem Labs lane's measurement of image A's files, kept as that earlier A's text; RcAsanFPLib.v:40 is the same line in B (lib/B/Prog/RcAsanFPLib.v:40, fl_shadow_rw). *)
(* lib/B/ShadowRwOnK.v -- route (C): the munch transport of B.ShadowRwOn.shadow_rw_on, in a light file so a
   contract-side proof can use it without ShadowRwOnT's MemNormTr closure (a Theorem Labs lane via a Theorem Labs lane, 12:06Z;
   measured by a Theorem Labs lane 12:38Z: this file's closure is 27 files, ShadowRwOnT's 112).  ONE WRITER: a Theorem Labs lane.
   Moved from lib/B/ShadowRwOnT.v: same name, statement and proof.  rule 24: no function proved.
     fl_shadow_rw_on  <- B.Prog.RcAsanFPLib.fl_shadow_rw  (RcAsanFPLib.v:40; munch outside the shadow) *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0 B.ShadowRwOn B.Prog.RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.

Lemma fl_shadow_rw_on : forall P W m m', B.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.munch W m m' ->
  lib.Lib.Frame.wmono B.Img0.rsegs m m' -> (forall x, B.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' H Hm Hw HW a Hp Ha. destruct (H a Hp Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  exists b. pose proof (B.Prog.RcAsanRT.rt_shadow_bound _ Ha) as Hbd.
  unfold lib.Lib.Mem.mrd in *. rewrite Hm; [exact Hb|]. rewrite lib.Lib.Mem.wa_unsigned by lia. apply HW, Ha.
Qed.

Print Assumptions fl_shadow_rw_on.
