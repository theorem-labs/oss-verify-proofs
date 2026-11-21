(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrTall MrAcc MrAccNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition node_cost (n : node) (dc du : Z) : Prop :=
  match n with
  | NMmap _ len _ _ => 0 <= len <= 2 ^ 30 - 4096 /\ dc = 2 /\ du = len + 4096
  | NMunmap _ _ => dc = 0 /\ du = 0
  | NMprotect _ _ _ => dc = 0 /\ du = 0
  | _ => False
  end.

Fixpoint tacc {R} (t : itree node R) (C U : Z) (Post : R -> Z -> Z -> Prop) : Prop :=
  match t with
  | Ret r => Post r C U
  | Vis n k => exists dc du, node_cost n dc du /\ forall rsp, tacc (k rsp) (C + dc) (U + du) Post
  end.

Lemma tacc_mono : forall {R} (t : itree node R) C U (P Q : R -> Z -> Z -> Prop),
  (forall r c u, P r c u -> Q r c u) -> tacc t C U P -> tacc t C U Q.
Proof.
  intros R t. induction t as [r | n k IH]; intros C U P Q HPQ; cbn; [apply HPQ|].
  intros (dc & du & Hc & H). exists dc, du. split; [exact Hc|]. intros rsp. eapply IH; [exact HPQ | apply H].
Qed.

Theorem tacc_twf : forall {R} (t : itree node R) mo C U (P : R -> Model -> Prop) (Post : R -> Z -> Z -> Prop),
  B.twf node nstep nsafe t mo P -> tacc t C U Post -> acc C U mo ->
  B.twf node nstep nsafe t mo (fun r mo' => P r mo' /\ exists C' U', Post r C' U' /\ acc C' U' mo').
Proof.
  intros R t. induction t as [r | n k IH]; intros mo C U P Post H T A; cbn in *.
  - split; [exact H|]. exists C, U. split; assumption.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst.
    destruct T as (dc & du & Hc & T). apply (IH rsp mo' (C + dc) (U + du)); [eapply Hk; exact Hst | apply T|].
    destruct n; cbn in Hc; try contradiction.
    + destruct Hc as (Hl & -> & ->). replace (U + (len + 4096)) with (U + len + 4096) by lia. eapply acc_mmap; eassumption.
    (* the node is safe (Hs), so the munmap never splits an entry. *)
    + destruct Hc as (-> & ->). rewrite !Z.add_0_r. eapply acc_munmap_safe; eassumption.
    + destruct Hc as (-> & ->). rewrite !Z.add_0_r. eapply acc_mprotect; eassumption.
Qed.

Definition mm_inv (Iv : Model -> Prop) : Prop :=
  forall n mo rsp mo' evs, match n with NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ => True | _ => False end ->
    nstep n mo rsp mo' evs -> Iv mo -> Iv mo'.

Theorem tacc_twf_inv : forall (Iv : Model -> Prop), mm_inv Iv ->
  forall {R} (t : itree node R) mo C U (P : R -> Model -> Prop) (Post : R -> Z -> Z -> Prop),
  B.twf node nstep nsafe t mo P -> tacc t C U Post -> acc C U mo -> Iv mo ->
  B.twf node nstep nsafe t mo (fun r mo' => P r mo' /\ (exists C' U', Post r C' U' /\ acc C' U' mo') /\ Iv mo').
Proof.
  intros Iv HI R t. induction t as [r | n k IH]; intros mo C U P Post H T A HI0; cbn in *.
  - split; [exact H|]. split; [|exact HI0]. exists C, U. split; assumption.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst.
    destruct T as (dc & du & Hc & T). apply (IH rsp mo' (C + dc) (U + du)); [eapply Hk; exact Hst | apply T | |].
    + destruct n; cbn in Hc; try contradiction.
      * destruct Hc as (Hl & -> & ->). replace (U + (len + 4096)) with (U + len + 4096) by lia. eapply acc_mmap; eassumption.
      * destruct Hc as (-> & ->). rewrite !Z.add_0_r. eapply acc_munmap_safe; eassumption.
      * destruct Hc as (-> & ->). rewrite !Z.add_0_r. eapply acc_mprotect; eassumption.
    + eapply HI; [|exact Hst|exact HI0]. destruct n; cbn in Hc; try contradiction; exact I.
Qed.

Lemma tacc_bind : forall {A C0} (t : itree node A) (f : A -> itree node C0) C U (P : A -> Z -> Z -> Prop) (Q : C0 -> Z -> Z -> Prop),
  tacc t C U P -> (forall a c u, P a c u -> tacc (f a) c u Q) -> tacc (ITree.bind node t f) C U Q.
Proof.
  intros A C0 t f. induction t as [r | n k IH]; intros C U P Q Ht Hf; cbn in *; [apply Hf; exact Ht|].
  destruct Ht as (dc & du & Hc & Ht). exists dc, du. split; [exact Hc|]. intros rsp. eapply IH; [apply Ht | exact Hf].
Qed.

Fixpoint ucost {R} (t : stree ev Z R) (C U : Z) (Post : R -> Z -> Z -> Prop) : Prop :=
  match t with
  | SRet r => Post r C U
  | SVis e k =>
      match e with
      | EUndef _ | EPeek _ _ _ => True
      | EMmap _ len _ _ => 0 <= len <= 2 ^ 30 - 4096 /\ forall z, ucost (k z) (C + 2) (U + (len + 4096)) Post
      | EMunmap _ _ | EMprotect _ _ _ => forall z, ucost (k z) C U Post
      | EBrk _ => False
      end
  end.

Section WithRC.
Context {rc : runConstT}.

Definition taccM {A} (m : Monad.M PState A) (s : PState) (C U : Z) (Post : A -> Z -> Z -> Prop) : Prop :=
  tacc (m s) C U (fun r c u => match r with Unr => True | Ok (a, _) => Post a c u end).

Lemma taccM_mbind : forall {A C0} (m : Monad.M PState A) (f : A -> Monad.M PState C0) s C U
    (P : A -> Z -> Z -> Prop) (Q : C0 -> Z -> Z -> Prop),
  taccM m s C U P -> (forall a s1 c u, P a c u -> taccM (f a) s1 c u Q) -> taccM (Monad.mbind m f) s C U Q.
Proof.
  intros A C0 m f s C U P Q H1 H2. unfold taccM, Monad.mbind, ebind in *.
  eapply tacc_bind; [exact H1|]. intros [|[a s1]] c u Ha; [exact I | apply H2; exact Ha].
Qed.

Lemma taccM_msys : forall {A} n (dec : resp -> option A) (s : PState) C U dc du (Post : A -> Z -> Z -> Prop),
  node_cost n dc du -> (forall a, Post a (C + dc) (U + du)) -> taccM (Monad.msys n dec) s C U Post.
Proof.
  intros A n dec s C U dc du Post Hc H. unfold taccM, Monad.msys. cbn. exists dc, du. split; [exact Hc|].
  intros rsp. destruct (dec rsp); [apply H | exact I].
Qed.

Lemma taccM_membed : forall {R} atop (t : stree ev Z R) s C U (Post : R -> Z -> Z -> Prop),
  ucost t C U Post -> taccM (membed atop t) s C U Post.
Proof.
  intros R atop t. induction t as [r | e k IH]; intros s C U Post H; cbn [membed].
  - exact H.
  - destruct e as [req | addr len prot flags | addr len | addr len prot | p c h | why]; cbn [ucost] in H.
    + contradiction.
    + destruct H as [Hl H]. cbn [ev_step].
      destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
        (eapply taccM_mbind with (P := fun _ c u => c = C + 2 /\ u = U + (len + 4096));
         [ eapply taccM_mbind with (P := fun _ c u => c = C + 2 /\ u = U + (len + 4096));
           [ eapply (taccM_msys _ _ _ C U 2 (len + 4096)); [cbn; auto | intros; split; reflexivity]
           | intros a s1 c u [-> ->]; cbn; split; reflexivity ]
         | intros z s1 c u [-> ->]; apply IH; apply H ]).
    + cbn [ev_step].
      eapply taccM_mbind with (P := fun _ c u => c = C /\ u = U);
        [ eapply taccM_mbind with (P := fun _ c u => c = C /\ u = U);
          [ eapply (taccM_msys _ _ _ C U 0 0); [cbn; auto | intros; split; lia]
          | intros a s1 c u [-> ->]; cbn; split; reflexivity ]
        | intros z s1 c u [-> ->]; apply IH; apply H ].
    + cbn [ev_step].
      eapply taccM_mbind with (P := fun _ c u => c = C /\ u = U);
        [ eapply taccM_mbind with (P := fun _ c u => c = C /\ u = U);
          [ eapply (taccM_msys _ _ _ C U 0 0); [cbn; auto | intros; split; lia]
          | intros a s1 c u [-> ->]; cbn; split; reflexivity ]
        | intros z s1 c u [-> ->]; apply IH; apply H ].
    + cbn [ev_step]. eapply taccM_mbind with (P := fun _ _ _ => False); [exact I | intros ? ? ? ? []].
    + cbn [ev_step]. eapply taccM_mbind with (P := fun _ _ _ => False); [exact I | intros ? ? ? ? []].
Qed.

Theorem tacc_raw_malloc : forall n s C U (Post : Z -> Z -> Prop),
  ucost (cmalloc (ps_m s) n) C U (fun _ c u => Post c u) -> taccM (raw_malloc n) s C U (fun _ c u => Post c u).
Proof.
  intros n s C U Post H. unfold raw_malloc.
  eapply taccM_mbind with (P := fun a c u => a = s /\ c = C /\ u = U); [cbn; auto|]. intros s0 s1 c u (-> & -> & ->).
  eapply taccM_mbind; [apply (taccM_membed _ _ s1 C U _ H)|]. intros [st' p] s2 c u HP.
  eapply taccM_mbind with (P := fun _ c' u' => Post c' u'); [cbn; exact HP|]. intros _ s3 c' u' HP'. cbn. exact HP'.
Qed.

Theorem tacc_raw_free : forall p s C U (Post : Z -> Z -> Prop),
  ucost (cfree (ps_m s) (Some (fst p))) C U (fun _ c u => Post c u) -> taccM (raw_free p) s C U (fun _ c u => Post c u).
Proof.
  intros p s C U Post H. unfold raw_free.
  eapply taccM_mbind with (P := fun a c u => a = s /\ c = C /\ u = U); [cbn; auto|]. intros s0 s1 c u (-> & -> & ->).
  eapply taccM_mbind; [apply (taccM_membed _ _ s1 C U _ H)|]. intros st' s2 c u HP. cbn. exact HP.
Qed.

End WithRC.
