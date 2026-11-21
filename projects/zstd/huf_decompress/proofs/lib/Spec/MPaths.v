(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (13 recorded proofs replaced by written proofs (tpath_msys_ok, tpath_msys_any, tpath_mbind_ok and 10 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad Sim.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MPaths () := "C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_enodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;tpath_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5texitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;texit_enodeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree;texit_ebindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3Sim3relC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3Sim4fsimC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section Paths.
Context {st : node -> Model -> resp -> Model -> list event -> Prop}.

Lemma tpath_msys_ok {St A} : forall n (dec : resp -> option A) (s s' : St) mo tr a mo',
  tpath st (msys n dec s) mo tr (Ok (a, s')) mo' <-> exists rsp, st n mo rsp mo' tr /\ dec rsp = Some a /\ s' = s.
Proof.
  intros n dec s s' mo tr a mo'. unfold msys. rewrite tpath_enode. split.
  - intros (rsp & Hst & E). exists rsp. destruct (dec rsp) as [a'|]; [|discriminate]. injection E as <- <-. auto.
  - intros (rsp & Hst & Hd & ->). exists rsp. rewrite Hd. auto.
Qed.

Lemma tpath_msys_any {St A} : forall n (dec : resp -> option A) (s : St) mo tr x mo',
  tpath st (msys n dec s) mo tr x mo' -> exists rsp, st n mo rsp mo' tr /\
    x = match dec rsp with Some a => Ok (a, s) | None => Unr end.
Proof.
  intros n dec s mo tr x mo' Hp. unfold msys in Hp. apply tpath_enode in Hp. destruct Hp as (rsp & Hst & E).
  exists rsp. split; [exact Hst|]. destruct (dec rsp); subst; reflexivity.
Qed.

Lemma tpath_mbind_ok {St A B} : forall (m : Monad.M St A) (k : A -> Monad.M St B) s mo tr x mo',
  tpath st (mbind m k s) mo tr (Ok x) mo' <->
  exists tr1 a s1 mo1 tr2, tpath st (m s) mo tr1 (Ok (a, s1)) mo1 /\ tpath st (k a s1) mo1 tr2 (Ok x) mo' /\ tr = tr1 ++ tr2.
Proof.
  intros m k s mo tr x mo'. unfold mbind. rewrite tpath_ebind. split.
  - intros [[_ E]|(tr1 & [a s1] & mo1 & tr2 & H1 & H2 & ->)]; [discriminate|]. exists tr1, a, s1, mo1, tr2. auto.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). right. exists tr1, (a, s1), mo1, tr2. auto.
Qed.

Lemma tpath_mbind_any {St A B} : forall (m : Monad.M St A) (k : A -> Monad.M St B) s mo tr x mo',
  tpath st (mbind m k s) mo tr x mo' ->
  (tpath st (m s) mo tr Unr mo' /\ x = Unr)
  \/ exists tr1 a s1 mo1 tr2, tpath st (m s) mo tr1 (Ok (a, s1)) mo1 /\ tpath st (k a s1) mo1 tr2 x mo' /\ tr = tr1 ++ tr2.
Proof.
  intros m k s mo tr x mo' Hp. unfold mbind in Hp. apply tpath_ebind in Hp.
  destruct Hp as [[Hp E]|(tr1 & [a s1] & mo1 & tr2 & H1 & H2 & ->)]; [left; auto|]. right. exists tr1, a, s1, mo1, tr2. auto.
Qed.

Lemma tpath_mret {St A} : forall (a : A) (s : St) mo tr x mo',
  tpath st (mret a s) mo tr x mo' <-> x = Ok (a, s) /\ mo' = mo /\ tr = [].
Proof. intros. cbn. split; intros (E & -> & ->); auto. Qed.

Lemma tpath_mupd {St} : forall (f : St -> St) s mo tr x mo',
  tpath st (mupd f s) mo tr x mo' <-> x = Ok (tt, f s) /\ mo' = mo /\ tr = [].
Proof. intros. cbn. split; intros (E & -> & ->); auto. Qed.

Lemma tpath_mget {St} : forall (s : St) mo tr x mo',
  tpath st (mget s) mo tr x mo' <-> x = Ok (s, s) /\ mo' = mo /\ tr = [].
Proof. intros. cbn. split; intros (E & -> & ->); auto. Qed.

Lemma tpath_munr {St A} : forall (s : St) mo tr (x : exc (A * St)) mo',
  tpath st (munr (A:=A) s) mo tr x mo' <-> x = Unr /\ mo' = mo /\ tr = [].
Proof. intros. cbn. split; intros (E & -> & ->); auto. Qed.

Lemma texit_msys_nonexit {St A} : forall n (dec : resp -> option A) (s : St) mo tr,
  match n with NExit _ => False | _ => True end -> ~ texit st nexit (msys n dec s) mo tr.
Proof.
  intros n dec s mo tr Hn Hx. unfold msys in Hx. apply texit_enode in Hx. destruct Hx as (code & mo' & Hex & _).
  destruct n; cbn in Hex; try exact Hex. exact Hn.
Qed.

Lemma texit_mbind {St A B} : forall (m : Monad.M St A) (k : A -> Monad.M St B) s mo tr,
  texit st nexit (mbind m k s) mo tr ->
  texit st nexit (m s) mo tr \/ exists tr1 a s1 mo1 tr2, tpath st (m s) mo tr1 (Ok (a, s1)) mo1 /\ texit st nexit (k a s1) mo1 tr2 /\ tr = tr1 ++ tr2.
Proof.
  intros m k s mo tr Hx. unfold mbind in Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & [a s1] & mo1 & tr2 & H1 & H2 & ->)]; [left; exact Hx|].
  right. exists tr1, a, s1, mo1, tr2. auto.
Qed.

Lemma texit_mbind_intro {St A B} : forall (m : Monad.M St A) (k : A -> Monad.M St B) s mo tr,
  (texit st nexit (m s) mo tr \/ exists tr1 a s1 mo1 tr2, tpath st (m s) mo tr1 (Ok (a, s1)) mo1 /\ texit st nexit (k a s1) mo1 tr2 /\ tr = tr1 ++ tr2) ->
  texit st nexit (mbind m k s) mo tr.
Proof.
  intros m k s mo tr H. unfold mbind. apply texit_ebind. destruct H as [H|(tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->)]; [left; exact H|].
  right. exists tr1, (a, s1), mo1, tr2. auto.
Qed.

Lemma texit_mret {St A} : forall (a : A) (s : St) mo tr, ~ texit st nexit (mret a s) mo tr.
Proof. intros a s mo tr H. exact H. Qed.
Lemma texit_mupd {St} : forall (f : St -> St) s mo tr, ~ texit st nexit (mupd f s) mo tr.
Proof. intros f s mo tr H. exact H. Qed.

End Paths.

(* [comment removed for export] *)
Lemma fsim_get_bind {StG StC A B} (debtG : StG -> list event) (debtC : StC -> list event) stepG :
  forall (R : rel StG StC) (fG : StG -> Monad.M StG A) (fC : StC -> Monad.M StC B) Q sG0 sC0,
  fsim debtG debtC stepG (fun sG moG sC moC => sG = sG0 /\ sC = sC0 /\ R sG moG sC moC) (fG sG0) (fC sC0) Q ->
  fsim debtG debtC stepG (fun sG moG sC moC => sG = sG0 /\ sC = sC0 /\ R sG moG sC moC) (x <- mget ;; fG x) (x <- mget ;; fC x) Q.
Proof. intros R fG fC Q sG0 sC0 H sG moG sC moC (-> & -> & HR). unfold mbind, mget. cbn. apply H. auto. Qed.
