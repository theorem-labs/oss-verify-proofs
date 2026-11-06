(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg RelSpec SimInv ExitSim CatSim FileSim ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq37Corelib7Numbers7BinNumsh84Npos35stdpp9bitvectorbdefinitionsj82bv03and3h5LinuxProcessSemanticsfLinuxProcessSem5Statelf5eventlf5Model37Corelib4Init9Datatypespd4listpd6option02ex3h5LinuxProcessSemanticsfLinuxProcessSem3Runs97step_topd4Nonepd4Somepd3nil02ors95mkCfgs99sys_inputlfdSyscallEffects95SNextlf8m_halted69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hke8the_scfgpd3apppd4cons03nots96SErrors9h4spurious_refusal_cfg3h5LinuxProcessSemanticsfLinuxProcessSem5Specshs4csyscall_speclf4m_fslf8m_killedlfhamaterialize_model_accesseslfh7syscall_effect_accesses3h5LinuxProcessSemanticsfLinuxProcessSem5Monadikd2Okikd9Unmodeled3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsioedmachine_stateioeems_svc_pendings9h0advance_past_svcs9capply_effects99sstep_cfglf6ExitEvlf6KillEvpd4prodlf9m_vm_lazyikd7outcome03iff69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jkc7node_okpd4boolpd5falses9h3injected_family_offpd4unitpd3natioe8set_gpr0lf7MemCopylf9mkEffectUlfcwith_copyinsjkc8realizesjkc4TSets96configjkc5t_alth81Zpd3sum37Corelib4Init6Specifki63sig5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openkk2dopenat_errnos36Stdlib5Lists4Listko72In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Nodes8WithSegs~~~~~~kq06open_Ilf8alloc_fdlf5m_fdslf9errno_retlf7FdEntrylf9fd_lookupkq07open_nx69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~lib8open_outjkc6t_alt23h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelnb7Segment" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!r5!lr0@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_cfg_svc_inv : ltac2:(zQ "i70!h4!j1!l5!la!od!p5!r5!rc!s5!v5!vf!hg6!hgd!hh3!hh7!hhf!hib!hjb!hk3!ho5!hp1!hp7!hpe!hq3!hqc!hv2!ig2!ig9!ih4!ij2!inb!io1!is5!it6!iu8!ivc!jgb!jh7!ji0>2ms$i0>5model$5>2x8@1$2@1$1#k0>1e@1$6$4>2st$9>0@3$0@1$7@1$2@1$1#k0@1$i1^5@2$b@1$2@1$1#k0^3>0@5$i4?4segs@1$h3?2SC@2$e^6^5^3^2@2$d@2$8$h0\3eff$h0@2$8$5\6model'$5@2$8@1$6$4\3evs@1$6$4@2$3@3$h9@3$f?4segs^a^8^9@4$he$h0^3^2^1@2$d@2$8$5\7model''$5@2$3@3$0@1$7@1$2@1$1#k0@1$h2^3@1$a@1$2@1$1#k0@2$3@3$0@1$6$4^8^2@2$3@1$h6@4$h8@1$h3?2SC@3$f?4segs^b^9^a^4@2$3@3$0@1$7$5@2$hc^3@1$hd^4@2$b$5^1@3$0$9^7@1$h1@2$e@1$i2@2$i3^b^4^1@2$d@2$3@3$0@1$7@1$2@1$1#k0@1$h2^2@1$a@1$2@1$1#k0@2$3@3$0@1$6$4^7@1$c$4@2$3@1$h6@4$h8@1$h3?2SC@3$f?4segs^a^8^9^3@2$3@3$0@1$7$5@2$hc^2@1$hd^3@1$a$5@3$0$9^6$h7@2$d@2$8@1$2@1$1#k0\4code@1$2@1$1#k0@2$3@3$0@1$7@1$2@1$1#k0@1$h2^3@2$b@1$2@1$1#k0^1@2$3@3$0@1$7@1$2@1$1#k0@1$hb^3@1$a@1$2@1$1#k0@2$3@3$0@1$6$4^8@3$h4$4^2@3$h5$4@2$i5^1@1$ha^3@1$c$4@3$0$9^7@1$h1@2$e^b^3@2$8@1$2@1$1#k0\3sig@1$2@1$1#k0@2$3@3$0@1$7@1$2@1$1#k0@1$hb^3@2$b@1$2@1$1#k0^1@2$3@3$0@1$6$4^8@3$h4$4^2@3$h5$4@2$i6^1@1$ha^3@1$c$4@3$0$9^7@1$h1@2$e^b^3@2$3@3$h9@3$f?4segs^7^5^6@1$hf$h0@2$3@3$0@1$6$4^4@1$c$4@3$0$9^3$h7").
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. neexists 3. split; [eassumption|].
    left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. neexists 3. split; [eassumption|].
    right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. neexists 3. split; [eassumption|].
    right. right. left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. neexists 3. split; [eassumption|].
    right. right. right. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_of_spec : ltac2:(zQ "hb1!j1!l5!h4!rc!vf!r5!ji9!hh7!hhf!p5!hib!hk3!ho5!hg6!hgd!hpe!inb!is5!it6!hjb!iu8!ivc!hqc!jgb!hv2!od!jj0&@2$6@1$1@1$0#k0@1$1@1$0#k0>2ms$h1>5model$9>2x8@1$1@1$0#k0>3eff$a>2m'$9>3evs@1$5$h9>0@3$2@1$3@1$1@1$0#k0@1$b^5@1$4@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#k0@1$h2^7@2$d@1$1@1$0#k0^5>0@3$h8@3$8?4segs^8^6^7@4$h0$a^5^4^3>0@1$f@4$h6@1$c?2SC@3$8?4segs^9^7^8^6>0@3$2@1$3@1$1@1$0#k0@1$b^6@1$4@1$1@1$0#k0>0@3$2@1$5~0@1$ha^7@1$e~0@5$h7?4segs@1$c?2SC@2$7^c^b^7@1$h3@2$7@1$h4@2$h5^c^9^8").
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
  apply (sstep_cfg_syscall segs the_scfg ms model x8 eff m' m' evs Hh Hsvc Hc Hns Hh').
  apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma not_spurious_det : ltac2:(zQ "h00!hib!jjc!hhf!p5!r5!h4!jk7!hpe!j1!inb!is5!hqc!hv2!od!ho5!l5>2ms$a>5model$3>2x8@1$f@1$8#k0>4eff0$0>2m0$3>4evs0@1$4$d>0>1o@1$1$0@2$6@3$c@3$2?4segs^7^5^6^1@3$5@1$1$0^1@4$9$0^4^3^2@1$7@4$b@1$e?2SC@3$2?4segs^7^5^6^4").
Proof.
  (intros ms model x8 eff0 m0 evs0 Hchk nd_i1; ndestruct nd_i1 as (_ & Hr & (eff' & m' & evs' & Hspec & Hnr))).
  apply Hchk in Hspec. apply Ok_inj in Hspec as (-> & -> & ->).
  rewrite Hr in Hnr. discriminate Hnr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma node_chk_ev_cfg : ltac2:(zQ "hd1!j1!l5!hib!h4!hhf!r5!p5!hv2!od!rc!hpe!inb!vf!ji9!la!hh7!hqc!hk3!ho5!hg6!hgd!s5!io1!is5!it6!iu8!ivc!jj0!jo7&@2$d@1$1@1$0#k0@1$1@1$0#k0>2ms$h7>5model$6>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$6>3evs>0^3@1$5$8>0@3$3@1$9@1$1@1$0#k0@1$h1^6@1$c@1$1@1$0#k0>0@3$3@1$9@1$1@1$0#k0@1$h8^8@2$h3@1$1@1$0#k0^6>0>1i^6@3$7@3$4?4segs^a^8^9@4$b$2@1^6^1@1^5^1@1^4^1>0>1i^7@1$a@4$h0@1$h2?2SC@3$4?4segs^b^9^a@1^7^1>0>3eff$2>2m'$6>2ev@1$5$8>0@3$7@3$4?4segs^e^c^d@4$b$2^3^2^1>0@1$a@4$h0@1$h2?2SC@3$4?4segs^f^d^e^4@2$h5^d\1i^d@2$e@3$3$2^6@1^d^1@2$e@3$3$6^5@1^c^1@3$3@1$5$8^4@1^b^1>0>3eff$2>2m'$6>2ev@1$5$8>0@3$7@3$4?4segs^f^d^e@4$b$2^3^2^1@3$3@1$9@1$1@1$0#k0@1$h1^3@1$c@1$1@1$0#k0>0@1$a@3$7@3$4?4segs^d^b^c@1$h6$2>0>1i^b@3$3@1$5~0@1$hb@1^a^1@1$h4~0@6$hc?4segs?2SC@2$f^f^e^c^9\1i^c@2$f@1$h9@2$ha^h0@1^c^1@1^b^1").
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnh Hnu Hlazy.
  assert (Hh' : forall i, m_halted (ms' i) = None) by (intros i; exact (Hnh _ _ _ (Hok i))).
  split.
  - intros i. apply (sstep_of_spec ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hs & Hmat & ->)
                                     | [(Hh2 & -> & Hs & Hmat & ->)
                                     | [(code & Hh2 & _ & -> & ->)
                                     | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + exfalso. rewrite (Hnh _ _ _ Hc) in Hh2. discriminate Hh2.
    + exfalso. rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hc)) in Hk. discriminate Hk.
    + exfalso. exact (Hnu Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev : ltac2:(zQ "hd1!j1!l5!h4!hib!r5!hhf!p5!rc!hv2!od!vf!ji9!la!hpe!inb!hh7!hk3!hg6!hgd!s5!io1!is5!it6!iu8!ivc!hqc!jj0!ho5!jo7&@2$b@1$1@1$0#k0@1$1@1$0#k0>2ms$h5>5model$6>2x8@1$1@1$0#k0>1IT>4effs>0^1$3>3ms'>0^2$6>3evs>0^3@1$4$9>0@3$2@1$7@1$1@1$0#k0@1$h0^6@1$a@1$1@1$0#k0>0@3$2@1$7@1$1@1$0#k0@1$h6^8@2$h1@1$1@1$0#k0^6>0>1i^6@3$8@3$5?4segs^a^8^9@4$e$3@1^6^1@1^5^1@1^4^1>0>1i^7@1$d@4$h9@1$hb?2SC@3$5?4segs^b^9^a@1^7^1>0>3eff$3>2m'$6>2ev@1$4$9>0@3$8@3$5?4segs^e^c^d@4$e$3^3^2^1@2$h3^c\1i^c@2$c@3$2$3^5@1^c^1@2$c@3$2$6^4@1^b^1@3$2@1$4$9^3@1^a^1>0@1$d@3$8@3$5?4segs^c^a^b@1$h4$3>0>1i^a@3$2@1$7@1$1@1$0#k0@1$h0@1^9^1@1$a@1$1@1$0#k0>0>1i^b@3$2@1$4~0@1$ha@1^a^1@1$h2~0@6$hc?4segs?2SC@2$f^f^e^c^9\1i^c@2$f@1$h7@2$h8^h0@1^c^1@1^b^1").
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
  apply (node_chk_ev_cfg ms model x8 I effs ms' evs Hh Hsvc Hok Hns).
  - intros eff m' ev Hc _. exact (Hinv _ _ _ Hc).
  - intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). apply Hh'.
  - exact Hnu.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_family : ltac2:(zQ "hd1!j1!l5!hib!h4!jjc!rc!vf!r5!ji9!inb!hh7!hhf!p5!hk3!hg6!hgd!s5!jk7!hpe!is5!it6!iu8!ivc!hqc!hv2!od!jj0!ho5!jo7&@2$8@1$1@1$0#k0@1$1@1$0#k0>2ms$h3>5model$c>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$c>3evs>0^3@1$7$h9>1R>0@1$4$2P>0@3$3@1$5@1$1@1$0#k0@1$d^7@1$6@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#k0@1$h4^9@2$e@1$1@1$0#k0^7>0>1o@1$4$2@2$h1@3$h8@3$b?4segs^b^9^a^1@1^4^1>0>1i^8@1^5@4$9$2@1^8^1@1^7^1@1^6^1>0>1o@1$4$2>0@1^6^1@2$h0^b\1i^b@3$3@1$4$2^3@4$9$2@1^b^1@1^a^1@1^9^1>0>1i^a@1$h2@4$h7@1$hb?2SC@3$b?4segs^e^c^d@1^a^1>0>1i^b@3$3@1$5@1$1@1$0#k0@1$d@1^a^1@1$6@1$1@1$0#k0>0>1i^c@3$3@1$7~0@1$ha@1^b^1@1$f~0@6$hc?4segs?2SC@2$a^h0^f^d^a\1i^d@2$a@1$h5@2$h6^h1@1^d^1@1^c^1").
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hns Hh' Hlazy.
  apply (node_chk_ev ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi).
    apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_family_on : ltac2:(zQ "he1!j1!l5!hib!h4!jjc!rc!vf!r5!ji9!inb!hh7!hhf!p5!hk3!hg6!jp2!jp9!hgd!s5!jk7!is5!it6!iu8!ivc!jq1!hv2!od!jj0!ho5!jo7&@2$8@1$1@1$0#k0@1$1@1$0#k0>2ms$h4>5model$c>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$c>3evs>0^3@1$7$ha>1R>0@1$4$2P>0@3$3@1$5@1$1@1$0#k0@1$d^7@1$6@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#k0@1$h5^9@2$e@1$1@1$0#k0^7>0@3$3$f@2$h8@1$hc?2SC@3$b?4segs^a^8$h0>0>1o@1$4$2@2$h3@3$h9@3$b?4segs^c^a^b^1@1^5^1>0>1i^9@1^6@4$9$2@1^9^1@1^8^1@1^7^1>0>1o@1$4$2>0@1^7^1@2$h2^c\1i^c@3$3@1$4$2^3@4$9$2@1^c^1@1^b^1@1^a^1>0>1i^b@3$3@1$5@1$1@1$0#k0@1$d@1^a^1@1$6@1$1@1$0#k0>0>1i^c@3$3@1$7~0@1$hb@1^b^1@1$h1~0@6$hd?4segs?2SC@2$a^h0^f^d^a\1i^d@2$a@1$h6@2$h7^h1@1^d^1@1^c^1").
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc Hon HR Hin Hout Hh' Hlazy.
  apply (node_family ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout); [|exact Hh'|exact Hlazy].
  intros i. apply spurious_refusal_family_on. exact Hon.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_det : ltac2:(zQ "ha2!j1!l5!h4!hib!rc!jr8!vf!r5!ji9!jjc!hh7!p5!hk3!hg6!hgd!jk7!inb!is5!it6!iu8!ivc!hhf!hv2!od!jj0!jo7&@3$2@1$4@1$1@1$0#k0@1$c^5@1$6@1$1@1$0#k0&@2$8@1$1@1$0#k0@1$1@1$0#k0>2ms$h1>5model$b>2x8@1$1@1$0#k0>4eff0$3>2m0$b>4evs0@1$7$h7>0~0>0@3$2@1$4@1$1@1$0#k0@1$h2^7@2$d@1$1@1$0#k0^5>0>1o@1$9$3@2$f@3$h6@3$h5?4segs^9^7^8^1@3$2@1$9$3^1@4$h0$3^6^5^4>0~0>0@3$2@1$7~1@1$h8^6@1$e~1@6$h9?4segs?2SC@2$a^b^a$5\0$5^7\0$5@2$a@1$h3@2$h4^c^9^8").
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hh0 Hlazy0.
  apply (node_family ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
           (fun o => o = Ok eff0 m0 evs0) Hh Hsvc Hchk).
  - intros []. reflexivity.
  - intros o ->. exists tt. reflexivity.
  - intros []. eapply not_spurious_det. exact Hchk.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only : ltac2:(zQ "hd3!j1!l5!hgd!ji9!h4!r5!rc!jr8!hib!vf!jjc!hh7!p5!hk3!hg6!jrf!jk7!inb!is5!it6!js5!iu8!hhf!hv2!jt1!od!jj0!jtb!jo7&@3$4@1$6@1$1@1$0#k0@1$d^5@1$9@1$1@1$0#k0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>2ms$h2>5model$c>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>2m'$c>3evs@1$5$h9>0~0>0@3$4@1$6@1$1@1$0#k0@1$h3^7@2$e@1$1@1$0#k0^5>0>1o@1$a$8@2$h0@3$h7@3$h6?4segs^9^7^8^1@3$4@1$a$8^1@4$h1$8@6$hb^6@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~2~2@1$2$h8@1$2@2$3@1$1@1$0#k0$f^5^4>0~0>0@3$4@1$5~1@1$ha^6~2@6$hc?4segs?2SC@2$b^b^a$7\0$7^7\0$7@2$b@1$h5@2$h4^c^9^8").
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins : ltac2:(zQ "he2!j1!l5!ji9!hgd!h4!r5!rc!jr8!hib!vf!jrf!jjc!hh7!p5!hk3!hg6!jk7!inb!is5!it6!js5!iu8!hhf!hv2!jt1!od!jj0!jtb!ju7!jo7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>2ms$h2>5model$d>2x8@1$1@1$0#k0>5reads@1$5@2$2@1$1@1$0#k0$a>1r@1$1@1$0#k0>2m'$d>3evs@1$5$h9>0@3$4@1$6@1$1@1$0#k0@1$e^6@1$9@1$1@1$0#k0>0@3$4@1$6@1$1@1$0#k0@1$h3^8@2$f@1$1@1$0#k0^6>0>1o@1$b$8@2$h0@3$h7@3$h6?4segs^a^8^9^1@3$4@1$b$8^1@4$h1$8@2$hc^7@6$hb^6@1$3@2$2@1$1@1$0#k0@1$5@1$1@1$0#8~1~1@1$3$h8@1$3@2$2@1$1@1$0#k0$a^5^4>0@3$4@1$6@1$1@1$0#k0@1$e^5@1$9@1$1@1$0#k0>0@3$4@1$5~0@1$ha^6~1@6$hd?4segs?2SC@2$c^c^b$7\0$7^7\0$7@2$c@1$h5@2$h4^d^9^8").
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent : ltac2:(zQ "hd3!j1!l5!hgd!ji9!h4!rc!hib!vf!r5!jjc!hh7!p5!hk3!jv6!hg6!jrf!jk7!inb!is5!it6!js5!iu8!hhf!hv2!jt1!od!jj0!jtb!kg2&@3$4@1$5@1$1@1$0#k0@1$c^5@1$7@1$1@1$0#k0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>2ms$h2>5model$b>2x8@1$1@1$0#k0>1r@1$1@1$0#k0>2m'$b>1T$hc>0~0>0@3$4@1$5@1$1@1$0#k0@1$h3^7@2$e@1$1@1$0#k0^5>0>1o@1$9$6@2$h0@3$h7@3$h6?4segs^9^7^8^1@3$4@1$9$6^1@4$h1$6@6$hb^6@1$2@2$3@1$1@1$0#k0@1$8@1$1@1$0#8~2~2@1$2$h8@1$2@2$3@1$1@1$0#k0$f^5@1$2$h9>0~0>0@3$4@1$8~1@1$ha^6~2>0@4$d?4segs?2SC@2$a@1$h5@2$h4^b^8^7^6@4$d?4segs?2SC@2$a^c^b^7").
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins_silent : ltac2:(zQ "he2!j1!l5!hgd!ji9!h4!r5!rc!hib!vf!jrf!jjc!hh7!p5!hk3!jv6!hg6!jk7!inb!is5!it6!js5!iu8!hhf!hv2!jt1!od!jj0!jtb!ju7!kg2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$h2>5model$c>2x8@1$1@1$0#k0>5reads@1$5@2$3@1$1@1$0#k0$9>1r@1$1@1$0#k0>2m'$c>1T$hd>0@3$4@1$6@1$1@1$0#k0@1$d^6@1$8@1$1@1$0#k0>0@3$4@1$6@1$1@1$0#k0@1$h3^8@2$f@1$1@1$0#k0^6>0>1o@1$a$7@2$h0@3$h7@3$h6?4segs^a^8^9^1@3$4@1$a$7^1@4$h1$7@2$hc^7@6$hb^6@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~1~1@1$2$h8@1$2@2$3@1$1@1$0#k0$9^5@1$2$h9>0@3$4@1$6@1$1@1$0#k0@1$d^5@1$8@1$1@1$0#k0>0@3$4@1$5~0@1$ha^6~1>0@4$e?4segs?2SC@2$b@1$h5@2$h4^c^8^7^6@4$e?4segs?2SC@2$b^d^c^7").
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_det : ltac2:(zQ "ha2!j1!l5!h4!hib!rc!vf!hgd!ji9!jjc!hh7!p5!hk3!jv6!hg6!r5!jk7!inb!is5!it6!iu8!ivc!hhf!hv2!od!jj0!kg2&@3$2@1$4@1$1@1$0#k0@1$b^5@1$5@1$1@1$0#k0&@2$7@1$1@1$0#k0@1$1@1$0#k0>2ms$h1>5model$a>2x8@1$1@1$0#k0>4eff0$3>2m0$a>1T$h9>0~0>0@3$2@1$4@1$1@1$0#k0@1$h2^7@2$d@1$1@1$0#k0^5>0>1o@1$8$3@2$f@3$h6@3$h5?4segs^9^7^8^1@3$2@1$8$3^1@4$h0$3^6^5@1$6$h7>0~0>0@3$2@1$e~1@1$h8^6@1$6~1>0@4$c?4segs?2SC@2$9@1$h3@2$h4^b^8^7^6@4$c?4segs?2SC@2$9^c^b^7").
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_cases : ltac2:(zQ "70!kga!jv6!hgd!od!kg2!jo7!kh3>1c$0>1IT>2nx>0^1$0>1T>0^2$4>2i0^3>0@6$5?4segs?2SC^5^4\0^4@1$2$3^3>0>1i^5@4$1?4segs?2SC@1^5^1@1^4^1@4$1?4segs?2SC^7@2$6^6^4").
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_I : ltac2:(zQ "10!p5>5model$0T") := ltac2:(zQ "70!khc!ki0!jr8!kjb!p5!kn6!kpa\5model$4@2$1@2$3$0\1e$0@3$6$0^1$5$2").

Definition open_nx : ltac2:(zQ "60!p5!j1!is5!kga!ku1!l5>2ms$2>5model$0>2mk>0@1$5@1$1#k0$0>1i@1$4^2$3") := ltac2:(zQ "h20!khc!kjb!kn6!kpa!ki0!jr8!js5!iu8!kga!hh7!p5!kub!kv6!j1!is5!kve!ku1!l5\2ms$e\5model$a\2mk>0@1$h1@1$d#k0$a\1i@1$h0^2M4\1i@2$4@2$1$0\1e$0@3$3$0^1$2$5$8^1\1s@2$1$0\1e$0@3$3$0^1$2M1\1s@2$1$0\1e$0@3$3$0^1$2$8^1\1e$0\2i0@1\1e$0@3$3$0^1$2^1@2$9@1$7@2$6^7@1$f^2^6\1u$5@2$9@1$7@2$6^5@1$b@1$c^4@1^3@1$b@1$c^4").

Lemma node_open : ltac2:(zQ "i23!j1!l5!h4!ji9!rc!vf!r5!hgd!hhf!lga!p5!kv6!hk3!jj0!ku1!hg6!jp2!jp9!jrf!jk7!jjc!is5!it6!jq1!hh7!hv2!hib!kub!od!lh4!li0!lm5!ho5!jo7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$6~0&@1$7~0>2ms$h5>5model$a>2x8@1$1@1$0#k0>5reads@1$6@2$3@1$1@1$0#k0$h2>2mk>0@1$1@1$0#k0$a>0@3$2@1$4@1$1@1$0#k0@1$c^4@1$5@1$1@1$0#k0>0@3$2~1@1$d^5~2>0@3$2@1$4@1$1@1$0#k0@1$h6^7@2$f@1$1@1$0#k0^5>0@3$2$h0@2$h7@1$i0?2SC@3$8?4segs^8^6$h1>0>1o@1$h4$ha@2$h3@3$h9@3$8?4segs^a^8^9^1@4$hf^7^9^6^1>0>2fd@1$1@1$0#k0@3$2@1$4@1$1@1$0#k0@1$c@1^7^1@1$5@1$1@1$0#k0>0>2fd@1$1@1$0#k0@3$2~1@1$d@1^8^1~2>0@3$2@1$4$9@2$hd@1$b^b@1$hb@1$b^b@1$5$9@6$i1?4segs?2SC@2$h8^d^c@1$e^c\0@1$e^c@1$7$hc@3$he^d^c^9").
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hon Hchk Hmk Hmklazy Hfree.
  pose (effs := fun i : open_I model => match i with
          | inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
          | inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []) end).
  pose (ms' := fun i : open_I model => match i with
          | inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
  assert (Enx : forall i, open_nx ms model mk i
                          = mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
  { intros [[e He] | []]; cbn [open_nx effs ms']; rewrite apply_effect_copyins_no_write; reflexivity. }
  split.
  - intros i. rewrite Enx.
    apply (proj1 (node_family_on ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hon Hchk
                    ltac:(intros [[e He] | []]; [left; exists e; auto | right; auto])
                    ltac:(intros o [(e & He & ->) | (Hlk & ->)];
                            [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[e He] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[e He] | []]; [exact Hlazy | apply Hmklazy])) i).
  - intros e st Hss.
    destruct (proj2 (node_family_on ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hon Hchk
                    ltac:(intros [[er Her] | []]; [left; exists er; auto | right; auto])
                    ltac:(intros o [(er & Her & ->) | (Hlk & ->)];
                            [exists (inl (exist _ er Her)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[er Her] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[er Her] | []]; [exact Hlazy | apply Hmklazy])) e st Hss)
      as (i & -> & ->).
    exists i. rewrite Enx. split; reflexivity.
Qed.

Lemma rz_open : ltac2:(zQ "i73!j1!l5!h4!ji9!rc!kv6!vf!r5!hh7!kub!jv6!hgd!khc!js5!iu8!hhf!lga!p5!hk3!jj0!kg2!hg6!jp2!jp9!jrf!jk7!jjc!is5!it6!jq1!hv2!hib!kve!lh4!kn6!lm5!ho5!ln1!kpa&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$7~0&@1$b~0>2ms$hb>5model$h1>2x8@1$1@1$0#k0>5reads@1$7@2$3@1$1@1$0#k0$h8>2mk>0@1$1@1$0#k0$h1>1A$h4>1B$h4>0@3$2@1$4@1$1@1$0#k0@1$h2^6@1$6@1$1@1$0#k0>0@3$2~1@1$h3^7~2>0@3$2@1$4@1$1@1$0#k0@1$hc^9@2$h5@1$1@1$0#k0^7>0@3$2$h6@2$hd@1$i4?2SC@3$f?4segs^a^8$h7>0>1o@1$ha$hf@2$h9@3$he@3$f?4segs^c^a^b^1@4$i3^9^b^8^1>0>2fd@1$1@1$0#k0@3$2@1$4@1$1@1$0#k0@1$h2@1^9^1@1$6@1$1@1$0#k0>0>2fd@1$1@1$0#k0@3$2~1@1$h3@1^a^1~2>0@3$2@1$4$h0@2$i1@1$5^d@1$9@1$5^d@1$6$h0>0>1e$c>0@3$i6$c^1$i2@4$a?4segs?2SC@2$8@1$e@2$d^h1@1$i0^2^h0^c>0@4$a?4segs?2SC@2$8@1$e@2$d^h0@1$9@1$5^f@1^c@1$9@1$5^f^a@4$a?4segs?2SC@2$8^h1^h0@2$i5^c^b").
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hon Hchk Hmk Hmklazy Hfree HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
(* [comment removed for export] *)
