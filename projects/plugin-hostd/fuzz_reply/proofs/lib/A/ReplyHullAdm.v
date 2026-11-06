(* The realloc rule's hull admission at reply's instance, from the meter (route R).
   A walk at R states the realloc rule with a generic admission HA and one discharge hypothesis
     HA_ra : forall lyc Sc regsT ch p n, 1 <= n -> mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n
   (the rule's own budget premise gives its mo_ok).  At reply's top HA is the entry form
   (fun _ Sc _ _ _ n => cf_hull_adm Sc n) at CfParams_reply, and this lemma discharges HA_ra once, under the meter's
   three equations (a Theorem Labs lane's / a Theorem Labs lane's MT_ok text, and MT_sec's mo_malloc / mo_free; each holds by reflexivity at
   MT := ReplyKfMeter.MT_sec nsec_cf cf_kmax).
   The step: cf_hull_adm Sc n is nsec_cf Sc + (0 for a primary request, else 1) <= reply_kmax (CfParamsReply.v), the
   meter's budget is nsec_cf Sc + (1 if 64512 < n, else 0) <= cf_kmax, cf_kmax is reply_kmax at CfParams_reply, and a
   request is primary exactly when it is at most 64,512 bytes (ReplyKfMeter.sec_lit, YGcfRoom.is_primary_eq).
   proves no function (kind: model lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG00 YG0f YC5d YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKfMeter.
Open Scope Z_scope.

#[local] Existing Instance CfParams_reply.

Section h.
Variable MT : ameter_ops.
(* the meter's three equations (MT_ok verbatim as a Theorem Labs lane's / a Theorem Labs lane's Sections state it) *)
Hypothesis MT_ok : forall s m, mo_ok MT s m <-> YGcfNames.nsec_cf s + m <= cf_kmax.
Hypothesis MT_malloc : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Hypothesis MT_free : mo_free MT = 0.

(* a request's admission charge is the meter's malloc cost *)
Lemma adm_charge_eq : forall n, (if from_primary n then 0 else 1) = (if 64512 <? n then 1 else 0).
Proof.
intros n. rewrite <- YGcfRoom.is_primary_eq, <- ReplyKfMeter.sec_lit.
destruct (PresetRoom.is_primary n); reflexivity.
Qed.

(* the realloc rule's admission, in the HA_ra shape a walk at R takes *)
Lemma hull_adm_of_mo_reply : forall (lyc : alayout) (Sc : astate) (regsT : bvmap 5 word) (ch : list (Z * Z * Z))
  (p n : Z), 1 <= n -> mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> cf_hull_adm Sc n.
Proof.
intros lyc Sc regsT ch p n _ H. apply MT_ok in H. rewrite MT_malloc, MT_free in H.
cbn [cf_hull_adm cf_kmax CfParams_reply] in H |- *. rewrite adm_charge_eq. lia.
Qed.
End h.
