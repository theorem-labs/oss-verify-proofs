(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require ITree Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg SimInv ExitSim CatSim ShapeAlg SReach.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state37Corelib4Init5Logick63iff69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~m06msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~q26msteps37Corelib7Numbers7BinNumsu64Npos35stdpp9bitvectorbdefinitionshg62bv37Corelib4Init9Datatypeshi94prodk62eq3h5LinuxProcessSemanticsfLinuxProcessSem3Runhke5mkCfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~ho36sreachhi94Nonehi94listhi93nilhi96optionhke6config3h5LinuxProcessSemanticsfLinuxProcessSem5Statehv15Modelhv18m_haltedhv19m_vm_lazyk63andhke9cfg_modelhke6cfg_msq23evthv15eventk63not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~in34resp3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeir77Segmentin3anode_sound" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hse!iuc@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_msteps_msteps : ltac2:(zQ "40!j7!la!p9!td>2ms$0>3ms'$0@2$1@3$3?4segs^2^1@3$2?4segs^2^1").
Proof.
  intros ms ms'. split.
  - intros H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH].
    + apply mst_refl.
    + eapply mst_step; [exact Hsvc | exact Hstep | exact IH].
  - intros H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH].
    + apply Exec.msteps_refl.
    + eapply Exec.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma cj_msteps_sreach : ltac2:(zQ "h01!vf!hi3!hk1!hk9!j7!hna!hrc!hs6!hse!ht6!htd!hu7!ihf!ii8!ij4!td&@2$2@1$1@1$0#k0@1$1@1$0#k0>2ms$4>3ms'$4>5model$c>1Q>0$bP>0@3$3@1$a@1$1@1$0#k0@1$d^2@1$7@1$1@1$0#k0>0@3$3@1$8~0@1$e^3@1$9~0>0@3$f?4segs^6^5>0@4$6?4segs?2SC^4@2$5^6^5@4$6?4segs?2SC^5@2$5^8^6").
Proof.
  intros ms ms' model Q Hh Hlazy Hms Hc.
  eapply sreach_msteps; [exact Hh | exact Hlazy | apply cj_msteps_msteps; exact Hms | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma cj_evt_sreach : ltac2:(zQ "h31!vf!hi3!hk9!hk1!j7!ihf!hs6!hse!ht6!htd!ik1!ik7!il4!hu7!hna!ii8!ij4!ile!hrc&@2$3@1$1@1$0#k0@1$1@1$0#k0>1P>0$4P>2ms$4>5model$5>0@3$2@1$9@1$1@1$0#k0@1$f^1@1$6@1$1@1$0#k0>0@3$2@1$7~0@1$h0^2@1$8~0>0@3$h1?4segs^5^4@4$h2?4segs?2SC\1c$d@2$a@1^7@1$c^1@3$2$5@1$b^1^5@2$e^5^4").
Proof.
  (intros P ms model Hh Hlazy nd_i1; ndestruct nd_i1 as (ms' & Hms & HP)).
  eapply cj_msteps_sreach; [exact Hh | exact Hlazy | exact Hms |].
  apply sr_done. cbn. split; [exact HP | reflexivity].
Qed.

Lemma cj_evt_sreach_k : ltac2:(zQ "h01!vf!hi3!j7!hk1!hk9!hna!hrc!hs6!hse!ht6!htd!hu7!ihf!ii8!ij4!ile&@2$3@1$1@1$0#k0@1$1@1$0#k0>1P>0$2P>2ms$2>5model$c>1Q>0$bP>0@3$4@1$a@1$1@1$0#k0@1$d^2@1$7@1$1@1$0#k0>0@3$4@1$8~0@1$e^3@1$9~0>0@3$f?4segs^6^5>0>3ms'$2>0@1^8^1@4$6?4segs?2SC^6@2$5^2^7@4$6?4segs?2SC^5@2$5^7^6").
Proof.
  (intros P ms model Q Hh Hlazy nd_i2 K; ndestruct nd_i2 as (ms' & Hms & HP)).
  eapply cj_msteps_sreach; [exact Hh | exact Hlazy | exact Hms | apply K; exact HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tree.
Context {node : Type}.
Variable at_node : ltac2:(zQ "10!j7>0?4node>0$0P").
Variable nstep : ltac2:(zQ "40!ihf!hse!im4!iqf>0?4node>0$0>0$3>0$0>0@1$1$2P").
Variable nexit : ltac2:(zQ "30!ihf!vf!hi3>0?4node>0$0>0@1$2@1$1#k0>0$0P").
Variable minv : ltac2:(zQ "10!ihf>0$0P").
Variable nsafe : ltac2:(zQ "10!ihf>0?4node>0$0P").
Hypothesis NS : ltac2:(zQ "10!iv7@8$0?4node?4segs?2SC?7at_node?5nstep?5nexit?4minv?5nsafe").
Hypothesis minv_lazy : ltac2:(zQ "81!vf!hi3!hk1!hse!ht6!hk9!ihf!ij4&@2$2@1$1@1$0#k0@1$1@1$0#k0>2mo$6>0@1?4minv^1@3$5@1$3~0@1$7^2@1$4~0").

#[local] Notation "'itree'" := (ITree.itree node) (at level 0).
#[local] Notation "'impl'" := (ITree.impl segs at_node) (at level 0).
#[local] Notation "'tsafe'" := (ITree.tsafe nstep nsafe) (at level 0).
#[local] Notation "'tpath'" := (ITree.tpath nstep) (at level 0).

(* [comment removed for export] *)
Fixpoint tsilent {R} (t : itree R) (mo : Model) : Prop :=
  match t with
  | ITree.Ret _ => True
  | ITree.Vis n k =>
      (forall code mo', ~ nexit n mo code mo')
      /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ tsilent (k rsp) mo'
  end.

(* [comment removed for export] *)
Definition silent_node : ltac2:(zQ "00>1n?4nodeP") := ltac2:(zQ "a0!ihf!im4!hse!ht6!ik1!hk9!imd!vf!iqf!hi3\1n?4node@2$4>2mo$0>4code@1$9@1$7#k0>3mo'$0@1$6@4?5nexit^4^3^2^1>2mo$0>3rsp$8>3mo'$0>3evs@1$2$1>0@5?5nstep^5^4^3^2^1@3$5@1$2$1^2@1$3$1").

Fixpoint tforall {R} (P : node -> Prop) (t : itree R) : Prop :=
  match t with
  | ITree.Ret _ => True
  | ITree.Vis n k => P n /\ forall rsp, tforall P (k rsp)
  end.

Lemma tforall_tsilent : forall {R} (t : itree R),
  tforall silent_node t -> forall mo, tsilent t mo.
Proof.
  intros R t. induction t as [r | n k IH]; intros Ht mo; cbn; [exact I|].
  destruct Ht as [[Hne Hns] Hk]. split.
  - intros code mo'. apply Hne.
  - intros rsp mo' evs Hst. split; [eapply Hns; exact Hst | apply IH; apply Hk].
Qed.

Lemma tforall_bind : forall {A B} (P : node -> Prop) (t : itree A) (f : A -> itree B),
  tforall P t -> (forall a, tforall P (f a)) -> tforall P (ITree.bind node t f).
Proof.
  intros A B P t. induction t as [r | n k IH]; intros f Ht Hf; cbn.
  - apply Hf.
  - destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk | exact Hf].
Qed.

Lemma tforall_ebind : forall {A B} (P : node -> Prop) (t : itree (ITree.Exc.exc A))
    (f : A -> itree (ITree.Exc.exc B)),
  tforall P t -> (forall a, tforall P (f a)) -> tforall P (ITree.ebind t f).
Proof.
  intros A B P t f Ht Hf. unfold ITree.ebind. apply tforall_bind; [exact Ht|].
  intros [|a]; cbn; [exact I | apply Hf].
Qed.

(* [comment removed for export] *)
Theorem impl_sreach : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo,
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent t mo ->
  sreach segs
    (fun c => exists r mo', Q r (cfg_ms c) /\ cfg_model c = mo'
                 /\ m_halted mo' = None /\ minv mo' /\ tpath t mo [] r mo')
    (mkCfg ms mo).
Proof.
  intros R t. induction t as [r | n k IH]; intros Q ms mo Himpl Hh Hminv Hsafe Hsil.
  - (* [comment removed for export] *)
    cbn in Himpl.
    eapply sreach_mono; [apply (cj_evt_sreach (Q r) ms mo Hh (minv_lazy mo Hminv) Himpl)|].
    intros [ms1 mo1] [HQ Hmo]; cbn in HQ, Hmo; subst mo1.
    exists r, mo. cbn. repeat split; assumption || reflexivity.
  - (* [comment removed for export] *)
    cbn in Himpl. destruct Hsil as [Hnoexit Hsil]. destruct Hsafe as [Hnsafe Hksafe].
    apply (cj_evt_sreach_k _ ms mo _ Hh (minv_lazy mo Hminv) Himpl).
    intros ms1 [Hat Hk].
    apply sr_step.
    + (* [comment removed for export] *)
      destruct (ITree.ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hminv Hnsafe)
        as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
      * destruct (ITree.ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (_ & _ & Hss).
        destruct (Hsil rsp mo' evs Hst) as [-> _].
        eexists. exact Hss.
      * exfalso. exact (Hnoexit code mo' Hex).
    + (* [comment removed for export] *)
      intros evs X Hss.
      destruct (ITree.ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs X Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & -> & Hst) | (code & mo' & -> & Hex & _)].
      * destruct (Hsil rsp mo' evs Hst) as [-> _]. split; [reflexivity | eexists; reflexivity].
      * exfalso. exact (Hnoexit code mo' Hex).
    + (* [comment removed for export] *)
      intros evs c' Hss.
      destruct (ITree.ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hminv Hnsafe Hss)
        as [(rsp & mo' & E & Hst) | (code & mo' & _ & Hex & _)]; [| exfalso; exact (Hnoexit code mo' Hex)].
      injection E as ->.
      destruct (ITree.ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hminv Hnsafe Hst) as (Hh' & Hminv' & _).
      destruct (Hsil rsp mo' evs Hst) as [-> Hsil'].
      eapply sreach_mono.
      * apply (IH rsp Q (ITree.nret ms1 rsp) mo' (Hk rsp) Hh' Hminv' (Hksafe rsp mo' [] Hst) Hsil').
      * (intros c nd_i3; ndestruct nd_i3 as (r & mo'' & HQ & Hmo & Hh'' & Hminv'' & Hp)).
        exists r, mo''. repeat split; try assumption.
        cbn. nexists rsp, mo', [], []. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Corollary impl_sreach_post : forall {R} (t : itree R) (Q : R -> machine_state -> Prop) ms mo
    (MQ : R -> Model -> Prop),
  impl t Q ms ->
  m_halted mo = None -> minv mo -> tsafe t mo -> tsilent t mo ->
  (forall r mo', tpath t mo [] r mo' -> MQ r mo') ->
  sreach segs
    (fun c => exists r, Q r (cfg_ms c) /\ MQ r (cfg_model c)
                 /\ m_halted (cfg_model c) = None /\ minv (cfg_model c))
    (mkCfg ms mo).
Proof.
  intros R t Q ms mo MQ Himpl Hh Hminv Hsafe Hsil HMQ.
  eapply sreach_mono; [apply (impl_sreach t Q ms mo Himpl Hh Hminv Hsafe Hsil)|].
  (intros c nd_i4; ndestruct nd_i4 as (r & mo' & HQ & <- & Hh' & Hminv' & Hp)).
  exists r. repeat split; try assumption. apply (HMQ _ _ Hp).
Qed.

End Tree.

End WithSegs.
