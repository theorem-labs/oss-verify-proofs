(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition E2 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 2)) (to_bytes l).
Lemma E2_app : forall a b, E2 (a ++ b) = E2 a ++ E2 b.
Proof. intros. unfold E2. rewrite to_bytes_app, map_app. reflexivity. Qed.
Lemma E2_nil : E2 [] = [].
Proof. reflexivity. Qed.

Section StderrFacts.
Context {St : Type}.

#[using="Type"] Lemma tpath_mret : forall {A} (a : A) (st : St) mo tr x mo',
tpath nstep (mret a st) mo tr x mo' -> x = Ok (a, st) /\ mo' = mo /\ tr = [].
Proof. intros A a st mo tr x mo' P. cbn in P. destruct P as (<- & -> & ->). auto. Qed.

#[using="Type"] Lemma stderr_pieces_tpath_ok : forall ps buf (st : St) mo tr p mo',
tpath nstep (stderr_pieces buf ps st) mo tr (Ok p) mo' ->
exists buf', p = (buf', st) /\ mo' = mo /\ E2 buf ++ E2 (concat ps) = tr ++ E2 buf'.
Proof.
induction ps as [|q ps IH]; intros buf st mo tr p mo' P; cbn [stderr_pieces] in P.
- apply tpath_mret in P. destruct P as (E & -> & ->). injection E as E. subst p. exists buf. cbn [concat]. rewrite E2_nil, !app_nil_r. auto.
- destruct (INTERNAL_BUFSIZ - zlength buf <? zlength q).
+ unfold mbind in P. apply tpath_ebind in P. destruct P as [[_ E]|(tr1 & [u st1] & mo1 & tr2 & P1 & P2 & ->)]; [discriminate|].
apply stdio_writev_tpath_ok in P1. destruct P1 as (E1 & -> & ->). injection E1 as -> ->. cbn [fst snd] in P2.
destruct (IH [] st mo tr2 p mo' P2) as (buf' & -> & -> & E). exists buf'. split; [reflexivity|]. split; [reflexivity|].
cbn [concat]. rewrite E2_nil in E. cbn [app] in E.
change (map (WriteEv (Z_to_bv 64 2)) (to_bytes (buf ++ q))) with (E2 (buf ++ q)). rewrite !E2_app, E, !app_assoc. reflexivity.
+ destruct (IH (buf ++ q) st mo tr p mo' P) as (buf' & -> & -> & E). exists buf'. split; [reflexivity|]. split; [reflexivity|].
cbn [concat]. rewrite !E2_app in *. rewrite app_assoc, E. reflexivity.
Qed.

#[using="Type"] Theorem stderr_fprintf_tpath_ok : forall ps (st : St) mo tr p mo',
tpath nstep (stderr_fprintf ps st) mo tr (Ok p) mo' ->
p = (tt, st) /\ mo' = mo /\ tr = E2 (concat ps).
Proof.
intros ps st mo tr p mo' P. unfold stderr_fprintf, mbind in P. apply tpath_ebind in P.
destruct P as [[_ E]|(tr1 & [buf st1] & mo1 & tr2 & P1 & P2 & ->)]; [discriminate|].
destruct (stderr_pieces_tpath_ok _ _ _ _ _ _ _ P1) as (buf' & E & -> & Etr). injection E as -> ->. cbn [fst snd] in P2.
apply stdio_writev_tpath_ok in P2. destruct P2 as (-> & -> & ->). rewrite app_nil_r.
split; [reflexivity|]. split; [reflexivity|]. rewrite E2_nil in Etr. cbn [app] in Etr. exact (eq_sym Etr).
Qed.

#[using="Type"] Theorem stderr_fwrite_tpath_ok : forall s (st : St) mo tr p mo',
tpath nstep (stderr_fwrite s st) mo tr (Ok p) mo' -> p = (tt, st) /\ mo' = mo /\ tr = E2 s.
Proof.
intros s st mo tr p mo' P. unfold stderr_fwrite in P. destruct (0 <? zlength s) eqn:T.
- apply stdio_writev_tpath_ok in P. exact P.
- apply tpath_mret in P. destruct P as (E & -> & ->). injection E as E. subst p. apply Z.ltb_ge in T.
destruct s; [auto| unfold zlength in T; cbn in T; lia].
Qed.

#[using="Type"] Lemma stderr_pieces_haspath : forall ps buf (st : St) mo,
zlength buf <= INTERNAL_BUFSIZ -> Forall (fun q => zlength q <= WRITEV_MAX - INTERNAL_BUFSIZ) ps ->
exists buf' tr, zlength buf' <= INTERNAL_BUFSIZ /\ tpath nstep (stderr_pieces buf ps st) mo tr (Ok (buf', st)) mo
/\ E2 buf ++ E2 (concat ps) = tr ++ E2 buf'.
Proof.
induction ps as [|q ps IH]; intros buf st mo Hb Hps; cbn [stderr_pieces].
- exists buf, []. split; [exact Hb|]. split; [cbn; auto|]. cbn [concat app]. rewrite E2_nil, app_nil_r. reflexivity.
- apply Forall_cons_iff in Hps. destruct Hps as [Hq Hps]. pose proof (zlength_nonneg q). pose proof (zlength_nonneg buf).
destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength q)).
+ destruct (IH [] st mo ltac:(unfold zlength, INTERNAL_BUFSIZ; cbn; lia) Hps) as (buf' & tr & Hb' & P & E).
exists buf', (E2 (buf ++ q) ++ tr). split; [exact Hb'|]. split.
* unfold mbind. apply tpath_ebind. right. exists (E2 (buf ++ q)), (tt, st), mo, tr.
split; [apply stdio_writev_haspath; unfold INTERNAL_BUFSIZ in *; lia|]. split; [exact P| reflexivity].
* cbn [concat]. rewrite E2_nil in E. cbn [app] in E. rewrite !E2_app, E, !app_assoc. reflexivity.
+ destruct (IH (buf ++ q) st mo ltac:(rewrite zlength_app; lia) Hps) as (buf' & tr & Hb' & P & E).
exists buf', tr. split; [exact Hb'|]. split; [exact P|]. cbn [concat]. rewrite !E2_app in *. rewrite app_assoc, E. reflexivity.
Qed.

#[using="Type"] Theorem stderr_fprintf_haspath : forall ps (st : St) mo,
Forall (fun q => zlength q <= WRITEV_MAX - INTERNAL_BUFSIZ) ps ->
tpath nstep (stderr_fprintf ps st) mo (E2 (concat ps)) (Ok (tt, st)) mo.
Proof.
intros ps st mo Hps. unfold stderr_fprintf, mbind. apply tpath_ebind. right.
destruct (stderr_pieces_haspath ps [] st mo ltac:(unfold zlength, INTERNAL_BUFSIZ; cbn; lia) Hps) as (buf' & tr & Hb' & P & E).
exists tr, (buf', st), mo, (E2 buf'). split; [exact P|]. cbn [fst snd]. split.
- rewrite <- (app_nil_r buf') at 2. apply stdio_writev_haspath. unfold zlength in *. cbn. unfold INTERNAL_BUFSIZ, WRITEV_MAX in *. lia.
- rewrite E2_nil in E. cbn [app] in E. exact E.
Qed.

#[using="Type"] Lemma stderr_pieces_notexit : forall ps buf (st : St) mo tr, ~ texit nstep nexit (stderr_pieces buf ps st) mo tr.
Proof.
induction ps as [|q ps IH]; intros buf st mo tr X; cbn [stderr_pieces] in X; [exact X|].
destruct (INTERNAL_BUFSIZ - zlength buf <? zlength q); [| exact (IH _ _ _ _ X)].
unfold mbind in X. apply texit_ebind in X. destruct X as [X|(tr1 & [u st1] & mo1 & tr2 & P1 & X & _)].
- exact (stdio_writev_notexit _ _ _ _ _ _ X).
- exact (IH _ _ _ _ X).
Qed.

#[using="Type"] Theorem stderr_fprintf_notexit : forall ps (st : St) mo tr, ~ texit nstep nexit (stderr_fprintf ps st) mo tr.
Proof.
intros ps st mo tr X. unfold stderr_fprintf, mbind in X. apply texit_ebind in X.
destruct X as [X|(tr1 & [buf st1] & mo1 & tr2 & P1 & X & _)]; [exact (stderr_pieces_notexit _ _ _ _ _ X)|].
exact (stdio_writev_notexit _ _ _ _ _ _ X).
Qed.

#[using="Type"] Lemma stderr_pieces_mspec : forall (P : assn St) ps buf,
zlength buf <= INTERNAL_BUFSIZ -> Forall (fun q => zlength q <= WRITEV_MAX - INTERNAL_BUFSIZ) ps ->
mspec P (stderr_pieces buf ps) (fun buf' st mo => P st mo /\ zlength buf' <= INTERNAL_BUFSIZ).
Proof.
intros P ps. revert P. induction ps as [|q ps IH]; intros P buf Hb Hps; cbn [stderr_pieces].
- apply mspec_ret. intros; auto.
- apply Forall_cons_iff in Hps. destruct Hps as [Hq Hps]. pose proof (zlength_nonneg q). pose proof (zlength_nonneg buf).
destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength q)).
+ eapply mspec_seq; [apply stdio_writev_mspec; unfold INTERNAL_BUFSIZ in *; lia|]. intros _. apply IH; [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps].
+ apply IH; [rewrite zlength_app; lia| exact Hps].
Qed.

#[using="Type"] Theorem stderr_fprintf_mspec : forall (P : assn St) ps,
Forall (fun q => zlength q <= WRITEV_MAX - INTERNAL_BUFSIZ) ps ->
mspec P (stderr_fprintf ps) (fun _ => P).
Proof.
intros P ps Hps. unfold stderr_fprintf. eapply mspec_bind; [apply stderr_pieces_mspec; [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps]|].
intros buf. cbv beta. intros st mo [HP Hb].
apply (stdio_writev_mspec P 2 buf [] ltac:(unfold zlength in *; cbn; unfold INTERNAL_BUFSIZ, WRITEV_MAX in *; lia) st mo HP).
Qed.

#[using="Type"] Theorem stderr_fwrite_mspec : forall (P : assn St) s, zlength s <= WRITEV_MAX -> mspec P (stderr_fwrite s) (fun _ => P).
Proof.
intros P s Hs. unfold stderr_fwrite. destruct (0 <? zlength s); [| apply mspec_ret; auto].
apply stdio_writev_mspec. unfold zlength in *. cbn. lia.
Qed.
End StderrFacts.
