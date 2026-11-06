(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed RSim AsanProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section Core.
Variable atop : Z.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.
Variable aok : aev -> Model -> Prop.
Variable apost : aev -> Model -> Z -> Model -> Prop.
Definition aev_node (e : aev) : option (node * (resp -> option Z)) :=
match e with
| AMmap a l p f => Some (NMmap a l p f, adec_mmap atop l p)
| AMunmap a l => Some (NMunmap a l, adec_munmap a l)
| AMprotect a l p => Some (NMprotect a l p, adec_mprotect a l)
| ABrk req => Some (NBrk req, adec_raw)
| ASetTid _ => Some (NSetTid, adec_raw)
| AUndef _ => None
end.
#[using="Type"] Lemma aev_tree_node : forall e,
aev_tree atop e = match aev_node e with Some (n, d) => enode n d | None => Ret Unr end.
Proof. destruct e; reflexivity. Qed.
Definition node_sound : Prop :=
forall e mo, aok e mo ->
exists n d, aev_node e = Some (n, d)
/\ (forall rsp mo' evs, step2 n mo rsp mo' evs -> evs = [] /\ exists z, d rsp = Some z /\ apost e mo z mo')
/\ (exists rsp mo' evs, step2 n mo rsp mo' evs)
/\ (forall code mo', ~ nexit n mo code mo').
Fixpoint atotal {R} (t : AM R) (mo : Model) (Post : R -> Model -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post r mo
| SVis e k => aok e mo /\ forall z mo', apost e mo z mo' -> atotal (k z) mo' Post
end.
#[using="Type"] Lemma atotal_ret : forall {R} (r : R) mo Post, Post r mo -> atotal (SRet r) mo Post.
Proof. intros. exact H. Qed.
#[using="Type"] Lemma atotal_vis : forall {R} e (k : Z -> AM R) mo Post,
aok e mo -> (forall z mo', apost e mo z mo' -> atotal (k z) mo' Post) -> atotal (SVis e k) mo Post.
Proof. intros. cbn. auto. Qed.
#[using="Type"] Lemma atotal_mono : forall {R} (t : AM R) mo (P Q : R -> Model -> Prop),
(forall r mo', P r mo' -> Q r mo') -> atotal t mo P -> atotal t mo Q.
Proof.
intros R t. induction t as [r|e k IH]; intros mo P Q HPQ H; cbn in *.
- auto.
- destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact HPQ| exact (Hk _ _ Hp)].
Qed.
Hypothesis NS : node_sound.
Local Notation tpath2 := (tpath (node:=node) step2).
Local Notation texit2 := (texit (node:=node) step2 nexit).
#[using="NS"] Lemma atotal_paths : forall {R} (t : AM R) mo Post tr r mo',
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
#[using="NS"] Lemma atotal_noexit : forall {R} (t : AM R) mo Post tr,
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
#[using="NS"] Lemma atotal_some : forall {R} (t : AM R) mo Post,
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
#[using="NS"] Theorem atotal_STOT : forall {R} (t : AM R) (s : APS) mo (Post : R -> Model -> Prop),
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
