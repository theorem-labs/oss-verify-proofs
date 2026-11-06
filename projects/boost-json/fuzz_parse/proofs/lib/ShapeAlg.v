(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg RelSpec SimInv ExitSim CatSim MmapSim AllocSim AllocSim2 WallSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list3h5LinuxProcessSemanticsfLinuxProcessSem5Statehe5event79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg4FPX1~~~~~~l44TSet37Corelib4Init5Logicpb3iffl44t_eq03nilpb2eq03apppb3andpb2expb2or3h5LinuxProcessSemanticsfLinuxProcessSem3Runtb9is_prefix37Corelib7Numbers7BinNumshh34Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fshj42Fs35stdpp9bitvectorbdefinitionshm52bv04conshe6ExitEvl46t_emitl45t_nil03nat37Corelib4Init5Peanohqd2le06length37Corelib4Init6Specifhsf3sigl48wr_indexpb4conjhsf5exist46Stdlib5Arith8PeanoNat3Natig67le_refl37Corelib5Lists7ListDefiic3maphe7WriteEvhsf9proj1_sigiic6firstniic5skipnl45t_alttb6configtb5SNexttb9sstep_cfgtb7step_to69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~iq38the_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~iu64TSet79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg8WithSegs~~~~~~ji98realizestb8star_cfgtbdobs_trace_cfg04None06optiontb9cfg_modeltb5sstephe8m_haltedpb3nottb6SErrortbh1reaches_error_cfg04unit02ttiu65t_altiu64t_eqji97node_okiu66t_emit03sum03inl03inriu66t_alt23h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskiedmachine_state04prodtb5mkCfgkie9MachineOkkieemachine_resultkieems_svc_pendingkie4stephe5Modelhe9m_vm_lazy04pairtbfmi_account_step69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ku96msteps04Somekie6ms_gprhe4m_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ExitSim~~~~~~lk3ais_exit_noiu66t_exithm57Z_to_bvhm56bv_and3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelqa7Segment" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet : ltac2:(zQ "00T") := ltac2:(zQ "20!h8!kc>0@1$0$1P").

Definition t_eq : ltac2:(zQ "10!p4>1T$0>2T'$0P") := ltac2:(zQ "40!p4!h8!qf!kc\1T$0\2T'$0>2tr@1$1$3@2$2@1^3^1@1^2^1").

Lemma t_eq_sym : ltac2:(zQ "20!p4!r5>1T$0>2T'$0>0@2$1^2^1@2$1^2^3"). Proof. intros T T' H tr; destruct (H tr); split; auto. Qed.
Lemma t_eq_trans : ltac2:(zQ "20!p4!r5>2T1$0>2T2$0>2T3$0>0@2$1^3^2>0@2$1^3^2@2$1^5^3").
Proof. intros T1 T2 T3 H1 H2 tr; destruct (H1 tr); destruct (H2 tr); split; auto. Qed.

(* [comment removed for export] *)
Definition t_nil : ltac2:(zQ "10!p4$0") := ltac2:(zQ "40!kc!h8!rc!s1\2tr@1$1$0@3$3@1$1$0^1@1$2$0").

(* [comment removed for export] *)
Definition t_emit : ltac2:(zQ "30!p4!h8!kc>3evs@1$1$2>1T$0$0") := ltac2:(zQ "90!kc!h8!s6!sb!s1!t1!t6!hg7!p4\3evs@1$1$0\1T$8\2tr@1$1$0@2$6@3$7$0^1^3@2$5@1$1$0\3tr'@1$1$0@2$3@3$4@1$1$0^2@3$2$0^4^1@1^3^1").

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 : ltac2:(zQ "10!p4>1A$0>1B$0$0") := ltac2:(zQ "40!p4!h8!t6!kc\1A$0\1B$0\2tr@1$1$3@2$2@1^3^1@1^2^1").

(* [comment removed for export] *)
Definition t_exit : ltac2:(zQ "40!hic!hlf!p4!ho2>4code@1$3@1$0#k0>2fs$1$2") := ltac2:(zQ "90!kc!ho8!rc!hic!hlf!hoe!hp7!hq0!ho2\4code@1$8@1$3#k0\2fs$4@2$6@3$1$0@2$5^2^1@1$2$0$7").

(* [comment removed for export] *)
Definition wr_index : ltac2:(zQ "30!h8!hic!ho2>3buf@1$0@1$2@1$1#8T") := ltac2:(zQ "80!hq8!hs1!hic!ho2!hs7!h8!sb!hu4\3buf@1$5@1$3@1$2#8@2$7$0\1n$0@2$6@2$1N1^1@2$1^1@2$4@1$3@1$2#8^2").

Definition wr_full : ltac2:(zQ "60!hic!ho2!hs7!h8!hs1!hub>3buf@1$3@1$1@1$0#8>3Hnb@2$4N1@2$2@1$1@1$0#8^1@1$5^2") := ltac2:(zQ "a0!hic!ho2!hs7!hs1!hq8!h8!sb!hv6!hvd!ii1\3buf@1$5@1$1@1$0#8\3Hnb@2$3N1@2$2@1$1@1$0#8^1@4$8$4\1n$4@2$6@2$3N1^1@2$3^1@2$2@1$1@1$0#8^3@2$2@1$1@1$0#8^2@4$7@2$3N1@2$2@1$1@1$0#8^2@2$3@2$2@1$1@1$0#8^2@2$2@1$1@1$0#8^2^1@1$9@2$2@1$1@1$0#8^2").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_eq : ltac2:(zQ "50!kc!rc!h8!hp7!r5>1T>1x@1$2$0P>0@1^1@1$1$0@2$4@2$3@1$1$0^2^2").
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma t_emit_has_nil : ltac2:(zQ "50!kc!h8!rc!p4!hp7>1e@1$1$0>1T$3@3$4^2^1@1$2$0").
Proof. intros e T. left. apply is_prefix_nil. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt_wall : ltac2:(zQ "h33!hic!ho2!hs1!hq8!kc!hs7!ik3!ika!hp7!sb!il4!hub!h8!rc!im1!imb!p4!in4!r5&@2$9@2$2N1^1@2$2^1@2$5@1$1@1$0#8^6&\1n$3~0&@3$a$3~1^1>2ch@1$1@1$0#k0>4rest@1$c@1$1@1$0#8>1T$h0>0@1^1@1$d$4>0@2$2N1@2$5@1$1@1$0#8^3@2$h2@2$h1@1$b^4\1i@1$b^4@2$8@4$6@1$1@1$0#8$4@1$7^6@3$e@1$1@1$0#8~2^5@2$8@4$6@1$1@1$0#8$4@1$7^6@3$f@1$1@1$0#8~2^5^4@2$8@4$6@1$1@1$0#8$4@1$7^5^4^3").
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.

(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!h8!ltf@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)
Definition node_ok : ltac2:(zQ "30!inc!h8!kc>1c$0>1IT>3evs>0^1@1$1$2>2nx>0^2$0P") := ltac2:(zQ "a0!h8!kc!sb!s1!io5!inc!iod!ip9!ita!t1\1c$5\1IT\3evs>0^1@1$0$1\2nx>0^2$5@2$2>1i^3@5$6?4segs@1$8?2SC^5@1^3^1@1$4@1^2^1>1e@1$0$1>2st$7>0@5$6?4segs@1$8?2SC^6^2^1@2$9^6\1i^6@2$2@3$3@1$0$1^4@1^6^1@3$3$7^3@1$4@1^5^1").

(* [comment removed for export] *)
Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(* [comment removed for export] *)

Lemma realizes_nonempty : ltac2:(zQ "50!rc!inc!kc!ji1!jmd>1c$1>1T$3>0@2$4^2^1@1^2@1$0$2").
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_pclosed : ltac2:(zQ "60!kc!h8!inc!hg7!ji1!jmd>1c$2>1T$4>0@2$5^2^1>2tr@1$1$0>3tr'@1$1$0>0@1^4^2>0@3$3$0^2^3@1^6^3").
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
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

Lemma realizes_star_only : ltac2:(zQ "70!inc!h8!jn9!kc!ita!ji1!jmd>1c$0>1T$5>0@2$6^2^1>2tr@1$1$3>2c'$0>0@5$2?4segs@1$4?2SC^5^2^1@1^5^3").
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      ndestruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_halted_nil segs c tr c' Hh (star_cfg_sub segs _ _ _ _ Hstar)) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma star_cfg_one' : ltac2:(zQ "70!inc!ita!h8!io5!iod!jn9!kc>1c$0>1e@1$2$6>2c'$0>0@5$4?4segs@1$1?2SC^3^2@1$3^1@5$5?4segs@1$1?2SC^4^3^2").
Proof.
  intros c e c' H. rewrite <- (app_nil_r e).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma realizes_admits : ltac2:(zQ "70!h8!inc!jo4!kc!ita!ji1!jmd>1c$1>1T$5>0@2$6^2^1>2tr@1$0$3>0@1^3^1@4$2?4segs@1$4?2SC^5^2").
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one'; apply Hcomp | exact Hpre].
    + ndestruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil].
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem realizes_obs_iff : ltac2:(zQ "80!h8!qf!inc!jo4!kc!ita!ji1!jmd>1c$2>1T$6>0@2$7^2^1>2tr@1$0$4@2$1@4$3?4segs@1$5?2SC^4^1@1^3^1").
Proof.
  intros c T H tr. split.
  - (intros nd_i3; ndestruct nd_i3 as (tr' & c' & Hstar & Hp)).
    eapply realizes_pclosed; [exact H | eapply realizes_star_only; eauto | exact Hp].
  - apply realizes_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma sstep_halted_none : ltac2:(zQ "c0!hic!ho2!jp4!h8!jpa!s1!jq2!inc!jqe!ip9!kc!jr6>1c$7>1e@1$3$a>2st$9>0@4$8?4segs^3^2^1@3$5@1$4@1$1@1$0#k0@1$b@1$6^4@1$2@1$1@1$0#k0").
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma sstep_cfg_halted_none : ltac2:(zQ "d0!hic!ho2!jp4!h8!jpa!s1!jq2!inc!iod!ip9!kc!jr6!ita>1c$7>1e@1$3$a>2st$9>0@5$8?4segs@1$c?2SC^3^2^1@3$5@1$4@1$1@1$0#k0@1$b@1$6^4@1$2@1$1@1$0#k0").
Proof. intros c e st H. eapply sstep_halted_none, sstep_cfg_sub; exact H. Qed.

Lemma realizes_step : ltac2:(zQ "90!ji1!inc!jmd!h8!t1!io5!iod!kc!ita>1c$1>1T$0>1e@1$3$7>2c'$1>0@2$2^4^3>0@5$6?4segs@1$8?2SC^5^3@1$5^2@2$4$0\2T'$0@2$2^4^1").
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    ndestruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_no_sserror : ltac2:(zQ "90!h8!js1!js7!inc!iod!kc!ita!ji1!jmd>1c$3>1T$7>1e@1$0$5>0@2$8^3^2@1$1@5$4?4segs@1$6?2SC^4^2$2").
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    ndestruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition rz_path : ltac2:(zQ "10!inc>1c$0P") := ltac2:(zQ "40!ji1!t1!inc!jmd\1c$2@2$1$0\1T$0@2$3^2^1").

(* [comment removed for export] *)
Lemma star_cfg_inv : ltac2:(zQ "70!inc!h8!kc!ita!io5!iod!jn9>3Inv>0$0P>5Hstep>1c$0>3evs@1$1$2>2c'$0>0@1^4^3>0@5$5?4segs@1$3?2SC^4^3@1$4^2@1^6^3>1c$0>2tr@1$1$2>2c'$0>0@5$6?4segs@1$3?2SC^3^2^1>0@1^6^4@1^7^3").
Proof. intros Inv Hstep. intros c tr c' Hstar. induction Hstar; eauto. Qed.

Lemma inv_no_reaches_error_cfg : ltac2:(zQ "90!inc!ita!h8!js1!iod!kc!js7!io5!jt0>3Inv>0$0P>5Hstep>1c$0>3evs@1$2$5>2c'$0>0@1^4^3>0@5$4?4segs@1$1?2SC^4^3@1$7^2@1^6^3>6Hnoerr>1c$0>3evs@1$2$5>0@1^4^2@1$3@5$4?4segs@1$1?2SC^3^2$6>2c0$0>0@1^4^1@1$3@3$8?4segs@1$1?2SC^2").
Proof. intros Inv Hstep Hnoerr.
  (intros c0 H0 nd_i4; ndestruct nd_i4 as (tr & c & evs & Hstar & Herr)).
  eapply Hnoerr; [| exact Herr].
  eapply star_cfg_inv; eauto.
Qed.

Theorem realizes_no_error : ltac2:(zQ "60!js1!inc!jt0!ita!ji1!jmd>1c$1>1T$4>0@2$5^2^1@1$0@3$2?4segs@1$3?2SC^3").
Proof.
  intros c T H.
  apply (inv_no_reaches_error_cfg rz_path).
  - intros c1 e c2 (T1 & H1) Hss. eapply realizes_step; eauto.
  - intros c1 e (T1 & H1) Hss. eapply realizes_no_sserror; eauto.
  - exists T; exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma t_alt_unit : ltac2:(zQ "50!ju5!jub!ji1!juf!jv8>1f>0$0$2@2$4@2$3$0^1@1^1$1").
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma rz_silent1 : ltac2:(zQ "70!ju5!inc!jmd!rc!kc!ji1!kg0>1c$1>2c'$1>1T$5>0@4$6^3$0\0$0@1$3$4\0$0^3>0@2$2^3^2@2$2^5^3").
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_emit1 : ltac2:(zQ "80!ju5!inc!jmd!h8!kc!ji1!kg0!kgb>1c$1>2c'$1>1e@1$3$4>1T$5>0@4$6^4$0\0$0^3\0$0^4>0@2$2^4^2@2$2^6@2$7^4^3").
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_alt2 : ltac2:(zQ "a0!kh5!jmd!inc!ji1!kha!khf!rc!kc!kg0!ki4>1c$2>2IAT>2IBT>2nx>0@2$0^2^1$2>1A$3>1B$3>2a0^5>2b0^5>0@4$8^8@2$0^7^6\0@2$0^7^6@1$6$7^5>0>1i^8@2$1@1^7@3$4^9^8^1^6>0>1i^8@2$1@1^8@3$5^a^9^1^6@2$1^b@2$9^7^6").
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_nonempty; apply (HB b0)).
  apply (rz_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)

Lemma node_instr : ltac2:(zQ "h41!hic!ho2!s1!km5!ju5!jp4!rc!jpa!kn6!knc!h8!ko4!kp1!kq3!kr5!krd!kc!jr6!ks5!kg0&@2$8@1$1@1$0#k0@1$1@1$0#k0>2ms$3>5model$f>3ms'$3>0@3$2@1$7@1$1@1$0#k0@1$h1^2@1$5@1$1@1$0#k0>0@3$2@1$a~0@1$h2^3@1$6~0>0@3$2@1$7@1$1@1$0#k0@1$d^5@1$5@1$1@1$0#k0>0@3$2@1$c$3@2$e?4segs^6@2$b$3^4@4$h3@2$9^7^6$4\0$4@1$6$h0\0$4@2$9^6^7").
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep. split.
  - intros []. apply (sstep_cfg_instr segs the_scfg ms model ms' model);
      [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros e st Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_instr_inv segs ms model ms' e st Hlazy Hsvc Hstep Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_acct : ltac2:(zQ "h30!km5!krd!hic!ho2!ju5!s1!jp4!jpa!kn6!knc!rc!kt1!ko4!kp1!kq3!kt7!kc!jr6!kg0>2ms$0>5model$1>3ms'$0>6model'$1>0@3$5@1$7@1$3@1$2#k0@1$h1^3@1$6@1$3@1$2#k0>0@3$5@1$7@1$3@1$2#k0@1$e^5@1$6@1$3@1$2#k0>0@3$5@1$d@2$8$0$1@3$f?4segs^6^5@2$c@2$8$0$1@4$b$0$1^4^3@4$h2@2$9^7^6$4\0$4@1$a$h0\0$4@2$9^6^5").
Proof.
  intros ms model ms' model' Hh Hsvc Hstep. split.
  - intros []. apply (sstep_cfg_instr segs the_scfg ms model ms' model'); assumption.
  - intros e st Hss. apply sstep_cfg_sub in Hss.
    inversion Hss; subst; try congruence;
      match goal with H : mi_account_step segs ms model = _ |- _ =>
        rewrite Hstep in H; try discriminate H; injection H as <- <- end.
    exists tt. split; reflexivity.
Qed.

Lemma rz_step : ltac2:(zQ "h31!hic!ho2!s1!km5!jp4!jpa!kn6!knc!jmd!h8!rc!ko4!kp1!kq3!kr5!krd!jr6!ks5!ji1&@2$6@1$1@1$0#k0@1$1@1$0#k0>2ms$3>5model$f>3ms'$3>1T$h2>0@3$2@1$5@1$1@1$0#k0@1$h0^3@1$4@1$1@1$0#k0>0@3$2@1$9~0@1$h1^4@1$a~0>0@3$2@1$5@1$1@1$0#k0@1$d^6@1$4@1$1@1$0#k0>0@3$2@1$c$3@2$e?4segs^7@2$b$3^5>0@2$8@2$7^6^7^5@2$8@2$7^9^8^6").
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma rz_msteps : ltac2:(zQ "h01!hic!ho2!kn6!s1!km5!knc!jmd!jp4!h8!rc!jpa!krd!jr6!ks5!li2!ji1&@2$2@1$1@1$0#k0@1$1@1$0#k0>2ms$4>3ms'$4>5model$b>1T$f>0@3$3@1$a@1$1@1$0#k0@1$c^2@1$7@1$1@1$0#k0>0@3$3@1$8~0@1$d^3@1$9~0>0@3$e?4segs^6^5>0@2$6@2$5^6^5^4@2$6@2$5^8^6^5").
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.


(* [comment removed for export] *)
Lemma rz_exit : ltac2:(zQ "h20!hic!ho2!jpa!s1!jp4!lic!km5!lj2!kq3!knc!krd!ljc!jr6!lnd!jmd!lob!lp5!lq0>2ms$6>5model$a>2x8@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#k0@1$c^2@1$4@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#k0@1$8^4@2$5@1$1@1$0#k0^2>0@1$d^3@2$e@2$9^6^5@2$f@3$h1@1$0#k0@2$7^6N0@2$h0@1$0#k0+vf@1$b^5").
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs the_scfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - apply rz_halt. cbn. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)

End FPX2.
(* [comment removed for export] *)
