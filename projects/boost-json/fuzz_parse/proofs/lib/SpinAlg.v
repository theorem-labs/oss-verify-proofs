(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~j44TSetj48realizes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg8WithSegs~~~~~~o19srealizes37Corelib4Init9Datatypest03nil3h5LinuxProcessSemanticsfLinuxProcessSem5Stateue5eventt04list09is_prefix08star_cfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hk08the_scfg0dobs_trace_cfg37Corelib4Init5Logichp23iffhp22ex05SNext09sstep_cfghp23not06SError0h1reaches_error_cfgt04unitj47node_ok37Corelib7Numbers7BinNumshv94Npos35stdpp9bitvectorbdefinitionsiha2bvt06optionhp22eqt04Nonet04Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiladmachine_stateila6ms_gprilaems_svc_pending05mkCfgue5Modelue4m_fsue8m_halted69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ExitSim~~~~~~itfais_exit_noj46t_exitiha7Z_to_bviha6bv_andt04prodhv91Z0h0advance_past_svc0capply_effectue9m_vm_lazy69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~jneemunmap_args_okjneamunmap_effjnecmunmap_modeljnedpage_round_upihabbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekg87Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hi4!kjd@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
(* [comment removed for export] *)
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

(* [comment removed for export] *)
Lemma srealizes_of_realizes : ltac2:(zQ "40!ic!mf!n6!s4>1c$0>1T$1>0@4$2?4segs?2SC^2^1@2$3^3^2").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

(* [comment removed for export] *)
Lemma realizes_of_srealizes : ltac2:(zQ "40!ic!mf!n6!s4>1c$0>1T$1>0@2$3^2^1@4$2?4segs?2SC^3^2").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (rz_node segs c I evs nx T i0 Hnode IH).
  - exact (rz_halt segs c Hh).
  - exact (rz_conseq segs c T T' IH Heq).
Qed.

(* [comment removed for export] *)

Lemma srealizes_nonempty : ltac2:(zQ "50!u8!ic!hhc!mf!s4>1c$1>1T$3>0@2$4^2^1@1^2@1$0$2").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma srealizes_pclosed : ltac2:(zQ "60!hhc!hi4!ic!hib!mf!s4>1c$2>1T$4>0@2$5^2^1>2tr@1$1$0>3tr'@1$1$0>0@1^4^2>0@3$3$0^2^3@1^6^3").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma srealizes_star_only : ltac2:(zQ "70!ic!hi4!hj6!hhc!hn7!mf!s4>1c$0>1T$5>0@2$6^2^1>2tr@1$1$3>2c'$0>0@5$2?4segs@1$4?2SC^5^2^1@1^5^3").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      ndestruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2.
      split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh (star_cfg_sub segs _ _ _ _ Hstar)) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma srealizes_admits : ltac2:(zQ "70!hi4!ic!ho3!hhc!hn7!mf!s4>1c$1>1T$5>0@2$6^2^1>2tr@1$0$3>0@1^3^1@4$2?4segs@1$4?2SC^5^2").
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one'; apply Hcomp | exact Hpre].
    + ndestruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem srealizes_obs_iff : ltac2:(zQ "80!hi4!hq6!ic!ho3!hhc!hn7!mf!s4>1c$2>1T$6>0@2$7^2^1>2tr@1$0$4@2$1@4$3?4segs@1$5?2SC^4^1@1^3^1").
Proof.
  intros c T H tr. split.
  - (intros nd_i1; ndestruct nd_i1 as (tr' & c' & Hstar & Hp)).
    eapply srealizes_pclosed;
      [exact H | eapply srealizes_star_only; eauto | exact Hp].
  - apply srealizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma srealizes_step : ltac2:(zQ "90!mf!ic!s4!hi4!hqd!hr3!hra!hhc!hn7>1c$1>1T$0>1e@1$3$7>2c'$1>0@2$2^4^3>0@5$6?4segs@1$8?2SC^5^3@1$5^2@2$4$0\2T'$0@2$2^4^1").
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    ndestruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma srealizes_no_sserror : ltac2:(zQ "90!hi4!hs5!hsc!ic!hra!hhc!hn7!mf!s4>1c$3>1T$7>1e@1$0$5>0@2$8^3^2@1$1@5$4?4segs@1$6?2SC^4^2$2").
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh
                   | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    ndestruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition srz_path : ltac2:(zQ "10!ic>1c$0P") := ltac2:(zQ "40!mf!hqd!ic!s4\1c$2@2$1$0\1T$0@2$3^2^1").

Theorem srealizes_no_error : ltac2:(zQ "60!hs5!ic!ht4!hn7!mf!s4>1c$1>1T$4>0@2$5^2^1@1$0@3$2?4segs@1$3?2SC^3").
Proof.
  intros c T H.
  apply (inv_no_reaches_error_cfg segs srz_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply srealizes_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply srealizes_no_sserror; eauto.
  - exists T; exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_silent1 : ltac2:(zQ "70!hu8!ic!s4!u8!hhc!mf!huf>1c$1>2c'$1>1T$5>0@6$6?4segs?2SC^3$0\0$0@1$3$4\0$0^3>0@2$2^3^2@2$2^5^3").
Proof.
  intros c c' T Hnode Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma srz_exit : ltac2:(zQ "h20!ih2!ij7!ijd!ik6!ikc!il3!ip1!iq2!iqc!ire!is5!isd!it4!jh9!ji7!s4!jj0!jjb>2ms$6>5model$a>2x8@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#k0@1$c^2@1$4@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#k0@1$8^4@2$5@1$1@1$0#k0^2>0@1$d^3@2$f@2$9^6^5@2$e@3$h1@1$0#k0@2$7^6N0@2$h0@1$0#k0+vf@1$b^5").
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

(* [comment removed for export] *)
Lemma node_munmap : ltac2:(zQ "hb1!ih2!ij7!ik6!hu8!u8!ijd!jk5!iq2!ire!ikc!il3!hi4!jkc!ip1!iqc!jl1!jm4!is5!hhc!it4!jn2!jr8!jsa!jt8!ju8!huf!jv9&@2$6@1$1@1$0#k0@1$1@1$0#k0>2ms$d>5model$h1>2x8@1$1@1$0#k0>0@3$2@1$5@1$1@1$0#k0@1$h3^2@1$9@1$1@1$0#k0>0@3$2@1$b~0@1$h4^3@1$4~0>0@3$2@1$5@1$1@1$0#k0@1$e^5@2$a@1$1@1$0#k0^3>0@3$2$c@2$ha@1$0#k0^4+t7>0@2$h5^7^6@6$h9?4segs?2SC@2$8^8^7$3\0$3@1$4$h2\0$3@2$8@1$f@2$h0^9@1$h6^9@3$h7@2$7^9N0@1$h8@2$7^9N1^8").
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs. split.
  - intros []. apply (sstep_cfg_syscall segs the_scfg ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + apply not_spurious_none. rewrite in_sysno_sys_input, Hno. apply injected_arm_none_215.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
