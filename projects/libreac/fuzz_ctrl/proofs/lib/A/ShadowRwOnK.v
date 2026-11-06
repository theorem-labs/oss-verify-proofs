(* lib/A/ShadowRwOnK.v -- route (C): the munch transport of A.ShadowRwOn.shadow_rw_on, in a light file so a
   contract-side proof can use it without ShadowRwOnT's MemNormTr -> BzBridge -> Bz closure (a Theorem Labs lane via
   a Theorem Labs lane, 12:06Z).  ONE WRITER: a Theorem Labs lane.  Moved from lib/A/ShadowRwOnT.v: same name, statement and proof.
   rule 24: no function proved.
     fl_shadow_rw_on  <- A.Prog.RcAsanFPLib.fl_shadow_rw  (RcAsanFPLib.v:40; munch outside the shadow) *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AsanRT A.Img0 A.ShadowRwOn A.Prog.RcAsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.

Lemma fl_shadow_rw_on : forall P W m m', A.ShadowRwOn.shadow_rw_on P m -> lib.Lib.Frame.munch W m m' ->
  lib.Lib.Frame.wmono A.Img0.rsegs m m' -> (forall x, A.AsanRT.in_shadow x -> lib.Lib.Frame.outside W x) ->
  A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' H Hm Hw HW a Hp Ha. destruct (H a Hp Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  exists b. pose proof (A.Prog.RcAsanRT.rt_shadow_bound _ Ha) as Hbd.
  unfold lib.Lib.Mem.mrd in *. rewrite Hm; [exact Hb|]. rewrite lib.Lib.Mem.wa_unsigned by lia. apply HW, Ha.
Qed.

Print Assumptions fl_shadow_rw_on.
