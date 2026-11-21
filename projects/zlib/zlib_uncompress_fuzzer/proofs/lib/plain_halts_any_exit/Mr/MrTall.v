(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.MSafe.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Fixpoint uall {R} (phi : R -> Prop) (t : stree ev Z R) : Prop :=
  match t with
  | SRet r => phi r
  | SVis e k => match e with EUndef _ | EPeek _ _ _ => True | _ => forall z, uall phi (k z) end
  end.

Fixpoint tall {R} (Phi : R -> Prop) (t : itree node R) : Prop :=
  match t with
  | Ret r => Phi r
  | Vis _ k => forall rsp, tall Phi (k rsp)
  end.

Lemma tall_mono : forall {R} (P Q : R -> Prop) (t : itree node R), (forall r, P r -> Q r) -> tall P t -> tall Q t.
Proof. intros R P Q t HPQ. induction t as [r | n k IH]; cbn; [apply HPQ | intros H rsp; apply IH, H]. Qed.

Lemma uall_mono : forall {R} (P Q : R -> Prop) (t : stree ev Z R), (forall r, P r -> Q r) -> uall P t -> uall Q t.
Proof. intros R P Q t HPQ. induction t as [r | e k IH]; cbn; [apply HPQ|]. destruct e; try exact (fun H => H); intros H z; apply IH, H. Qed.

Lemma twf_tall : forall {R} node' (nstep' : node' -> Model -> resp -> Model -> list event -> Prop) nsafe'
    (t : itree node' R) mo (P : R -> Model -> Prop) (Phi : R -> Prop),
  B.twf node' nstep' nsafe' t mo P ->
  (fix tl (t : itree node' R) : Prop := match t with Ret r => Phi r | Vis _ k => forall rsp, tl (k rsp) end) t ->
  B.twf node' nstep' nsafe' t mo (fun r mo' => P r mo' /\ Phi r).
Proof.
  intros R node' nstep' nsafe' t. induction t as [r | n k IH]; intros mo P Phi H T; cbn in *; [split; assumption|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst | apply T].
Qed.

Lemma twf_tall' : forall {R} (t : itree node R) mo (P : R -> Model -> Prop) (Phi : R -> Prop),
  B.twf node nstep nsafe t mo P -> tall Phi t -> B.twf node nstep nsafe t mo (fun r mo' => P r mo' /\ Phi r).
Proof.
  intros R t. induction t as [r | n k IH]; intros mo P Phi H T; cbn in *; [split; assumption|].
  destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; [eapply Hk; exact Hst | apply T].
Qed.

Lemma tall_bind : forall {A C} (P : A -> Prop) (Q : C -> Prop) (t : itree node A) (f : A -> itree node C),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ITree.bind node t f).
Proof.
  intros A C P Q t f. induction t as [r | n k IH]; intros Ht Hf; cbn in *; [apply Hf; exact Ht|].
  intros rsp. apply IH; [apply Ht | exact Hf].
Qed.

Section WithRC.
Context {rc : runConstT}.

Definition tallM {A} (phi : A -> PState -> Prop) (m : Monad.M PState A) (s : PState) : Prop :=
  tall (fun r => match r with Unr => True | Ok (a, s') => phi a s' end) (m s).

Lemma tallM_mbind : forall {A C} (phi1 : A -> PState -> Prop) (phi : C -> PState -> Prop)
    (m : Monad.M PState A) (f : A -> Monad.M PState C) s,
  tallM phi1 m s -> (forall a s1, phi1 a s1 -> tallM phi (f a) s1) -> tallM phi (Monad.mbind m f) s.
Proof.
  intros A C phi1 phi m f s H1 H2. unfold tallM, Monad.mbind, ebind in *.
  eapply tall_bind; [exact H1|]. intros [|[a s1]] Ha; [exact I | apply H2; exact Ha].
Qed.

Lemma tallM_msys : forall {A} n (dec : resp -> option A) (s : PState) (phi : A -> PState -> Prop),
  (forall a, phi a s) -> tallM phi (Monad.msys n dec) s.
Proof. intros A n dec s phi H. unfold tallM, Monad.msys. cbn. intros rsp. destruct (dec rsp); [apply H | exact I]. Qed.

Lemma tallM_ret : forall {A} (a : A) (s : PState) (phi : A -> PState -> Prop), phi a s -> tallM phi (Monad.mret a) s.
Proof. intros. exact H. Qed.

Lemma tallM_ev_step : forall atop e s, tallM (fun _ s' => ps_m s' = ps_m s) (ev_step atop e) s.
Proof.
  intros atop e s. destruct e as [req | addr len prot flags | addr len | addr len prot | p c h | why]; cbn [ev_step].
  - destruct (req =? 0)%Z.
    + eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]. intros r s1 E1.
      eapply tallM_mbind with (phi1 := fun _ s' => ps_m s' = ps_m s); [cbn; rewrite <- E1; reflexivity|].
      intros _ s2 E2. exact E2.
    + eapply tallM_mbind with (phi1 := fun a s' => a = s /\ s' = s); [cbn; auto|]. intros s0 s1 [-> ->].
      eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]. intros a s2 E2.
      destruct a.
      * eapply tallM_mbind with (phi1 := fun _ s' => ps_m s' = ps_m s); [cbn; rewrite <- E2; reflexivity|]. intros _ s3 E3. exact E3.
      * exact E2.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)%Z).
    + eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]. intros a s1 E1. exact E1.
    + destruct (prot =? 0)%Z;
        (eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]; intros a s1 E1; exact E1).
  - eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]. intros a s1 E1. exact E1.
  - eapply tallM_mbind; [apply (tallM_msys _ _ _ (fun _ s' => ps_m s' = ps_m s)); reflexivity|]. intros a s1 E1. exact E1.
  - exact I.
  - exact I.
Qed.

Lemma tallM_membed : forall {R} atop (t : stree ev Z R) (phi : R -> Prop) s,
  uall phi t -> tallM (fun r s' => phi r /\ ps_m s' = ps_m s) (membed atop t) s.
Proof.
  intros R atop t phi. induction t as [r | e k IH]; intros s H; cbn [membed].
  - split; [exact H | reflexivity].
  - destruct e as [req | addr len prot flags | addr len | addr len prot | p c h | why];
      try (eapply tallM_mbind; [apply tallM_ev_step|]; intros z s1 E1; cbn in H;
           eapply tall_mono; [| apply (IH z s1 (H z))]; intros [|[r s2]]; [auto|]; intros [H1 H2]; split; [exact H1 | congruence]).
    + exact I.
    + exact I.
Qed.

Theorem tall_raw_malloc : forall n s (phi : mstate -> option cptr -> Prop),
  uall (fun r => phi (fst r) (snd r)) (cmalloc (ps_m s) n) ->
  tallM (fun r s' => phi (ps_m s') (option_map fst r)) (raw_malloc n) s.
Proof.
  intros n s phi H. unfold raw_malloc.
  eapply tallM_mbind with (phi1 := fun a s' => a = s /\ s' = s); [cbn; auto|]. intros s0 s1 [-> ->].
  eapply tallM_mbind; [apply (tallM_membed _ _ _ s H)|]. intros [st' p] s2 [Hphi _]. cbn [fst snd] in Hphi.
  eapply tallM_mbind with (phi1 := fun _ s' => ps_m s' = st'); [cbn; reflexivity|]. intros _ s3 E3.
  cbn. rewrite E3. destruct p; exact Hphi.
Qed.

Theorem tall_raw_free : forall p s (phi : mstate -> Prop),
  uall phi (cfree (ps_m s) (Some (fst p))) ->
  tallM (fun _ s' => phi (ps_m s')) (raw_free p) s.
Proof.
  intros p s phi H. unfold raw_free.
  eapply tallM_mbind with (phi1 := fun a s' => a = s /\ s' = s); [cbn; auto|]. intros s0 s1 [-> ->].
  eapply tallM_mbind; [apply (tallM_membed _ _ _ s H)|]. intros st' s2 [Hphi _].
  cbn. exact Hphi.
Qed.

End WithRC.
