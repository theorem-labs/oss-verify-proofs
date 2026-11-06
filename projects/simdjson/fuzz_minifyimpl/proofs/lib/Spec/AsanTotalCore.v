(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed RSim AsanProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Core.
Variable atop : Z.    (* [comment removed for export] *)
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
(* [comment removed for export] *)
Variable aok : aev -> Model -> Prop.
Variable apost : aev -> Model -> Z -> Model -> Prop.

(* [comment removed for export] *)
Definition aev_node (e : aev) : option (node * (resp -> option Z)) :=
  match e with
  | AMmap a l p f => Some (NMmap a l p f, adec_mmap atop l p)
  | AMunmap a l => Some (NMunmap a l, adec_munmap a l)
  | AMprotect a l p => Some (NMprotect a l p, adec_mprotect a l)
  | AMadvise a l => Some (NMadvise a l, adec_madvise a l)      (* [comment removed for export] *)
  | ABrk req => Some (NBrk req, adec_raw)
  | ASetTid _ => Some (NSetTid, adec_raw)
  | AUndef _ => None
  end.

Lemma aev_tree_node : forall e,
  aev_tree atop e = match aev_node e with Some (n, d) => enode n d | None => Ret Unr end.
Proof. destruct e; reflexivity. Qed.

(* [comment removed for export] *)
Definition node_sound : Prop :=
  forall e mo, aok e mo ->
    exists n d, aev_node e = Some (n, d)
    /\ (forall rsp mo' evs, step2 n mo rsp mo' evs -> evs = [] /\ exists z, d rsp = Some z /\ apost e mo z mo')
    /\ (exists rsp mo' evs, step2 n mo rsp mo' evs)
    /\ (forall code mo', ~ nexit n mo code mo').

(* [comment removed for export] *)
Fixpoint atotal {R} (t : AM R) (mo : Model) (Post : R -> Model -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post r mo
  | SVis e k => aok e mo /\ forall z mo', apost e mo z mo' -> atotal (k z) mo' Post
  end.

Lemma atotal_ret : forall {R} (r : R) mo Post, Post r mo -> atotal (SRet r) mo Post.
Proof. intros. exact H. Qed.

Lemma atotal_vis : forall {R} e (k : Z -> AM R) mo Post,
  aok e mo -> (forall z mo', apost e mo z mo' -> atotal (k z) mo' Post) -> atotal (SVis e k) mo Post.
Proof. intros. cbn. auto. Qed.

Lemma atotal_mono : forall {R} (t : AM R) mo (P Q : R -> Model -> Prop),
  (forall r mo', P r mo' -> Q r mo') -> atotal t mo P -> atotal t mo Q.
Proof.
  intros R t. induction t as [r|e k IH]; intros mo P Q HPQ H; cbn in *.
  - auto.
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact HPQ| exact (Hk _ _ Hp)].
Qed.

(* [comment removed for export] *)
Lemma atotal_sbind : forall {A B} (t : AM A) (f : A -> AM B) mo (P : A -> Model -> Prop) (Q : B -> Model -> Prop),
  atotal t mo P -> (forall a mo', P a mo' -> atotal (f a) mo' Q) -> atotal (sbind t f) mo Q.
Proof.
  intros A B t. induction t as [r|e k IH]; intros f mo P Q Ht Hf; cbn in *.
  - exact (Hf _ _ Ht).
  - destruct Ht as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact (Hk _ _ Hp)| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis NS : node_sound.

Local Notation tpath2 := (tpath (node:=node) step2).
Local Notation texit2 := (texit (node:=node) step2 nexit).

Lemma atotal_paths : forall {R} (t : AM R) mo Post tr r mo',
  atotal t mo Post -> tpath2 (aembed atop t) mo tr r mo' ->
  tr = [] /\ exists a, r = Ok a /\ Post a mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr r mo' Ht Hp; cbn in Ht.
  - rewrite aembed_ret in Hp. cbn in Hp. destruct Hp as (<- & <- & ->). split; [reflexivity|]. exists r0; auto.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & _ & _).
    rewrite aembed_vis, aev_tree_node, He in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & z & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. apply tpath_enode in Hp as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z & Hd & _). rewrite Hd in Hr. discriminate.
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (-> & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      cbn [app]. eapply IH; [exact (Hk _ _ Hpost)| exact Hp2].
Qed.

Lemma atotal_noexit : forall {R} (t : AM R) mo Post tr,
  atotal t mo Post -> ~ texit2 (aembed atop t) mo tr.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr Ht Hx; cbn in Ht.
  - rewrite aembed_ret in Hx. exact Hx.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & _ & Hne).
    rewrite aembed_vis, aev_tree_node, He in Hx. apply texit_ebind in Hx.
    destruct Hx as [Hx|(tr1 & z & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + apply texit_enode in Hx as (code & mo' & Hx & _). exact (Hne _ _ Hx).
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      exact (IH _ _ _ _ (Hk _ _ Hpost) Hx2).
Qed.

Lemma atotal_some : forall {R} (t : AM R) mo Post,
  atotal t mo Post -> exists r mo', tpath2 (aembed atop t) mo [] r mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post Ht; cbn in Ht.
  - exists (Ok r0), mo. rewrite aembed_ret. cbn. auto.
  - destruct Ht as [Hok Hk]. destruct (NS e mo Hok) as (n & d & He & Hall & (rsp & mo1 & evs & Hst) & _).
    destruct (Hall _ _ _ Hst) as (-> & z & Hd & Hpost).
    destruct (IH _ _ _ (Hk _ _ Hpost)) as (r & mo' & Hp).
    exists r, mo'. rewrite aembed_vis, aev_tree_node, He. apply tpath_ebind.
    destruct r as [|a].
    + exfalso. destruct (atotal_paths _ _ _ _ _ _ (Hk _ _ Hpost) Hp) as (_ & ? & E & _). discriminate.
    + right. exists [], z, mo1, []. split; [| split; [exact Hp| reflexivity]].
      apply tpath_enode. exists rsp. rewrite Hd. auto.
Qed.

(* [comment removed for export] *)
Theorem atotal_STOT : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
  aps_atop s = atop ->
  atotal t mo Post ->
  STOT (St:=APS) step2 (fun R0 => texit (R:=R0) step2 nexit) (alift t s) mo (fun r s' mo' => s' = s /\ Post r mo').
Proof.
  intros R t s mo Post Hs Ht. unfold alift. rewrite Hs. split; [| split].
  - intros tr r mo' Hp. apply tpath_ebind in Hp. destruct Hp as [[Hp ->]|(tr1 & a & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. destruct (atotal_paths _ _ _ _ _ _ Ht Hp) as (_ & ? & E & _). discriminate.
    + destruct (atotal_paths _ _ _ _ _ _ Ht Hp1) as (-> & a' & E & HP). injection E as <-.
      cbn in Hp2. destruct Hp2 as (<- & -> & ->). split; [reflexivity|]. exists a, s. auto.
  - intros tr Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & a & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + exact (atotal_noexit _ _ _ _ Ht Hx).
    + exact Hx2.
  - destruct (atotal_some _ _ _ Ht) as (r & mo' & Hp).
    destruct r as [|a].
    + exfalso. destruct (atotal_paths _ _ _ _ _ _ Ht Hp) as (_ & ? & E & _). discriminate.
    + exists (Ok (a, s)), mo'. apply tpath_ebind. right. exists [], a, mo', []. cbn. auto.
Qed.

End Core.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glob.
Variable atop : Z.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
Variables aok aokS : aev -> Model -> Prop.
Variable apost : aev -> Model -> Z -> Model -> Prop.
Variable Phi : node -> Model -> Prop.
Hypothesis NS : node_sound atop step2 aok apost.
Hypothesis AOK : forall e mo n d, aev_node atop e = Some (n, d) -> aokS e mo -> Phi n mo -> aok e mo.

Local Notation tpath2 := (tpath (node:=node) step2).
Local Notation texit2 := (texit (node:=node) step2 nexit).
Local Notation tglob2 := (tglob step2 Phi).
Local Notation atotS := (atotal aokS apost).

(* [comment removed for export] *)
Hypothesis AOKN : forall e mo, aokS e mo -> exists n d, aev_node atop e = Some (n, d).

Lemma aok_of_glob : forall e (k : Z -> AM unit) mo,
  aokS e mo -> tglob2 (aembed atop (SVis e k)) mo -> aok e mo.
Proof.
  intros e k mo Hs Hg. destruct (AOKN e mo Hs) as (n & d & He).
  rewrite aembed_vis, aev_tree_node, He in Hg. unfold enode in Hg. cbn [tglob ebind bind] in Hg.
  apply (AOK e mo n d He Hs). exact (proj1 Hg).
Qed.

Lemma glob_node : forall {R} e (k : Z -> AM R) mo,
  aokS e mo -> tglob2 (aembed atop (SVis e k)) mo ->
  exists n d, aev_node atop e = Some (n, d) /\ aok e mo
    /\ forall rsp mo' evs z, step2 n mo rsp mo' evs -> d rsp = Some z -> tglob2 (aembed atop (k z)) mo'.
Proof.
  intros R e k mo Hs Hg. destruct (AOKN e mo Hs) as (n & d & He). exists n, d. split; [exact He|].
  rewrite aembed_vis, aev_tree_node, He in Hg. unfold enode in Hg. cbn [tglob ebind bind] in Hg.
  destruct Hg as [HP HK]. split; [exact (AOK e mo n d He Hs HP)|].
  intros rsp mo' evs z Hst Hd. specialize (HK rsp mo' evs Hst). rewrite Hd in HK. exact HK.
Qed.

Lemma atotal_paths_glob : forall {R} (t : AM R) mo Post tr r mo',
  atotS t mo Post -> tglob2 (aembed atop t) mo -> tpath2 (aembed atop t) mo tr r mo' ->
  tr = [] /\ exists a, r = Ok a /\ Post a mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr r mo' Ht Hg Hp; cbn in Ht.
  - rewrite aembed_ret in Hp. cbn in Hp. destruct Hp as (<- & <- & ->). split; [reflexivity|]. exists r0; auto.
  - destruct Ht as [Hok Hk]. destruct (glob_node e k mo Hok Hg) as (n & d & He & Haok & HG).
    destruct (NS e mo Haok) as (n' & d' & He' & Hall & _ & _). rewrite He in He'. injection He' as <- <-.
    rewrite aembed_vis, aev_tree_node, He in Hp. apply tpath_ebind in Hp.
    destruct Hp as [[Hp ->]|(tr1 & z & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. apply tpath_enode in Hp as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z & Hd & _). rewrite Hd in Hr. discriminate.
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (-> & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      cbn [app]. eapply IH; [exact (Hk _ _ Hpost)| eapply HG; [exact Hst| exact Hd]| exact Hp2].
Qed.

Lemma atotal_noexit_glob : forall {R} (t : AM R) mo Post tr,
  atotS t mo Post -> tglob2 (aembed atop t) mo -> ~ texit2 (aembed atop t) mo tr.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post tr Ht Hg Hx; cbn in Ht.
  - rewrite aembed_ret in Hx. exact Hx.
  - destruct Ht as [Hok Hk]. destruct (glob_node e k mo Hok Hg) as (n & d & He & Haok & HG).
    destruct (NS e mo Haok) as (n' & d' & He' & Hall & _ & Hne). rewrite He in He'. injection He' as <- <-.
    rewrite aembed_vis, aev_tree_node, He in Hx. apply texit_ebind in Hx.
    destruct Hx as [Hx|(tr1 & z & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + apply texit_enode in Hx as (code & mo' & Hx & _). exact (Hne _ _ Hx).
    + apply tpath_enode in Hp1 as (rsp & Hst & Hr).
      destruct (Hall _ _ _ Hst) as (_ & z' & Hd & Hpost). rewrite Hd in Hr. injection Hr as ->.
      exact (IH _ _ _ _ (Hk _ _ Hpost) (HG _ _ _ _ Hst Hd) Hx2).
Qed.

Lemma atotal_some_glob : forall {R} (t : AM R) mo Post,
  atotS t mo Post -> tglob2 (aembed atop t) mo -> exists r mo', tpath2 (aembed atop t) mo [] r mo'.
Proof.
  intros R t. induction t as [r0|e k IH]; intros mo Post Ht Hg; cbn in Ht.
  - exists (Ok r0), mo. rewrite aembed_ret. cbn. auto.
  - destruct Ht as [Hok Hk]. destruct (glob_node e k mo Hok Hg) as (n & d & He & Haok & HG).
    destruct (NS e mo Haok) as (n' & d' & He' & Hall & (rsp & mo1 & evs & Hst) & _). rewrite He in He'. injection He' as <- <-.
    destruct (Hall _ _ _ Hst) as (-> & z & Hd & Hpost).
    destruct (IH _ _ _ (Hk _ _ Hpost) (HG _ _ _ _ Hst Hd)) as (r & mo' & Hp).
    exists r, mo'. rewrite aembed_vis, aev_tree_node, He. apply tpath_ebind.
    destruct r as [|a].
    + exfalso. destruct (atotal_paths_glob _ _ _ _ _ _ (Hk _ _ Hpost) (HG _ _ _ _ Hst Hd) Hp) as (_ & ? & E & _). discriminate.
    + right. exists [], z, mo1, []. split; [| split; [exact Hp| reflexivity]].
      apply tpath_enode. exists rsp. rewrite Hd. auto.
Qed.

(* [comment removed for export] *)
Lemma tglob_alift : forall {R} (t : AM R) (s : APS) mo,
  tglob2 (alift t s) mo -> tglob2 (aembed (aps_atop s) t) mo.
Proof. intros R t s mo H. unfold alift in H. exact (tglob_ebind_l step2 Phi _ _ _ H). Qed.

Theorem atotal_STOT_glob : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
  aps_atop s = atop ->
  atotS t mo Post -> tglob2 (alift t s) mo ->
  STOT (St:=APS) step2 (fun R0 => texit (R:=R0) step2 nexit) (alift t s) mo (fun r s' mo' => s' = s /\ Post r mo').
Proof.
  intros R t s mo Post Hs Ht Hg0. pose proof (tglob_alift t s mo Hg0) as Hg. rewrite Hs in Hg.
  unfold alift. rewrite Hs. split; [| split].
  - intros tr r mo' Hp. apply tpath_ebind in Hp. destruct Hp as [[Hp ->]|(tr1 & a & mo1 & tr2 & Hp1 & Hp2 & ->)].
    + exfalso. destruct (atotal_paths_glob _ _ _ _ _ _ Ht Hg Hp) as (_ & ? & E & _). discriminate.
    + destruct (atotal_paths_glob _ _ _ _ _ _ Ht Hg Hp1) as (-> & a' & E & HP). injection E as <-.
      cbn in Hp2. destruct Hp2 as (<- & -> & ->). split; [reflexivity|]. exists a, s. auto.
  - intros tr Hx. apply texit_ebind in Hx. destruct Hx as [Hx|(tr1 & a & mo1 & tr2 & Hp1 & Hx2 & ->)].
    + exact (atotal_noexit_glob _ _ _ _ Ht Hg Hx).
    + exact Hx2.
  - destruct (atotal_some_glob _ _ _ Ht Hg) as (r & mo' & Hp).
    destruct r as [|a].
    + exfalso. destruct (atotal_paths_glob _ _ _ _ _ _ Ht Hg Hp) as (_ & ? & E & _). discriminate.
    + exists (Ok (a, s)), mo'. apply tpath_ebind. right. exists [], a, mo', []. cbn. auto.
Qed.

(* [comment removed for export] *)
End Glob.
