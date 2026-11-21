(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrTall MrAcc MrAccNodes MrAccPath MrUcb.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint tgen {R} (t : itree node R) (I : Model -> Prop) (Post : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => forall mo, I mo -> Post r mo
  | Vis n k => forall rsp, tgen (k rsp) (fun mo' => exists mo evs, I mo /\ nstep n mo rsp mo' evs) Post
  end.

Lemma tgen_weak : forall {R} (t : itree node R) (I I' : Model -> Prop) (P Q : R -> Model -> Prop),
  (forall mo, I mo -> I' mo) -> (forall r mo, P r mo -> Q r mo) -> tgen t I' P -> tgen t I Q.
Proof.
  intros R t. induction t as [r | n k IH]; intros I I' P Q HI HPQ H; cbn in *.
  - intros mo Hmo. apply HPQ, H, HI, Hmo.
  - intros rsp. eapply IH; [| exact HPQ | apply H].
    intros mo' (mo & evs & Hmo & Hst). exists mo, evs. split; [apply HI; exact Hmo | exact Hst].
Qed.

Theorem tgen_twf : forall {R} (t : itree node R) mo (I : Model -> Prop) (P Post : R -> Model -> Prop),
  B.twf node nstep nsafe t mo P -> tgen t I Post -> I mo ->
  B.twf node nstep nsafe t mo (fun r mo' => P r mo' /\ Post r mo').
Proof.
  intros R t. induction t as [r | n k IH]; intros mo I P Post H T HI; cbn in *.
  - split; [exact H | apply T; exact HI].
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst.
    eapply IH; [eapply Hk; exact Hst | apply T|]. exists mo, evs. split; assumption.
Qed.

Theorem tgen_tpath : forall {R} (t : itree node R) mo (I : Model -> Prop) (Post : R -> Model -> Prop) tr r mo',
  tgen t I Post -> I mo -> tpath nstep t mo tr r mo' -> Post r mo'.
Proof.
  intros R t. induction t as [r0 | n k IH]; intros mo I Post tr r mo' T HI Hp; cbn in *.
  - destruct Hp as (<- & -> & _). apply T; exact HI.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
    eapply IH; [apply T | | exact Hp]. exists mo, evs. split; assumption.
Qed.

Lemma tgen_bind : forall {A C0} (t : itree node A) (f : A -> itree node C0) (I : Model -> Prop)
    (P : A -> Model -> Prop) (Q : C0 -> Model -> Prop),
  tgen t I P -> (forall a, tgen (f a) (P a) Q) -> tgen (ITree.bind node t f) I Q.
Proof.
  intros A C0 t f. induction t as [r | n k IH]; intros I P Q Ht Hf; cbn in *.
  - eapply tgen_weak; [exact Ht | intros r0 mo H; exact H | apply Hf].
  - intros rsp. eapply IH; [apply Ht | exact Hf].
Qed.

Lemma tgen_pure : forall {R} (t : itree node R) (Pr : Prop) (I : Model -> Prop) (Post : R -> Model -> Prop),
  (Pr -> tgen t I Post) -> tgen t (fun mo => Pr /\ I mo) Post.
Proof.
  intros R t. induction t as [r | n k IH]; intros Pr I Post H; cbn in *.
  - intros mo [HP HI]. apply (H HP). exact HI.
  - intros rsp. eapply tgen_weak with (I' := fun mo' => Pr /\ exists mo evs, I mo /\ nstep n mo rsp mo' evs) (P := Post).
    + intros mo' (mo & evs & [HP HI] & Hst). split; [exact HP|]. exists mo, evs. split; assumption.
    + auto.
    + apply IH. intros HP. apply (H HP).
Qed.

Lemma tgen_false : forall {R} (t : itree node R) (Post : R -> Model -> Prop), tgen t (fun _ => False) Post.
Proof.
  intros R t Post. induction t as [r | n k IH]; cbn; [intros mo []|].
  intros rsp. eapply tgen_weak with (I' := fun _ => False) (P := Post); [intros mo' (mo & evs & [] & _) | auto | apply IH].
Qed.

Section WithRC.
Context {rc : runConstT}.

Definition tgenM {A} (m : Monad.M PState A) (s : PState) (I : Model -> Prop) (Post : A -> PState -> Model -> Prop) : Prop :=
  tgen (m s) I (fun r mo => match r with Unr => True | Ok (a, s') => Post a s' mo end).

Lemma tgenM_weak : forall {A} (m : Monad.M PState A) s (I I' : Model -> Prop) (P Q : A -> PState -> Model -> Prop),
  (forall mo, I mo -> I' mo) -> (forall a s' mo, P a s' mo -> Q a s' mo) -> tgenM m s I' P -> tgenM m s I Q.
Proof.
  intros A m s I I' P Q HI HPQ H. unfold tgenM in *. eapply tgen_weak; [exact HI | | exact H].
  intros [|[a s']] mo; [auto | apply HPQ].
Qed.

Lemma tgenM_mbind : forall {A C0} (m : Monad.M PState A) (f : A -> Monad.M PState C0) s (I : Model -> Prop)
    (P : A -> PState -> Model -> Prop) (Q : C0 -> PState -> Model -> Prop),
  tgenM m s I P -> (forall a s1, tgenM (f a) s1 (P a s1) Q) -> tgenM (Monad.mbind m f) s I Q.
Proof.
  intros A C0 m f s I P Q H1 H2. unfold tgenM, Monad.mbind, ebind in *.
  eapply tgen_bind; [exact H1|]. intros [|[a s1]]; [cbn; auto | apply H2].
Qed.

Lemma tgenM_pure : forall {A} (m : Monad.M PState A) s (Pr : Prop) (I : Model -> Prop) (Post : A -> PState -> Model -> Prop),
  (Pr -> tgenM m s I Post) -> tgenM m s (fun mo => Pr /\ I mo) Post.
Proof. intros A m s Pr I Post H. unfold tgenM in *. apply tgen_pure. exact H. Qed.

Lemma tgenM_ret : forall {A} (a : A) s (I : Model -> Prop) (Post : A -> PState -> Model -> Prop),
  (forall mo, I mo -> Post a s mo) -> tgenM (Monad.mret a) s I Post.
Proof. intros A a s I Post H. unfold tgenM. cbn. exact H. Qed.

Lemma tgenM_msys : forall {A} n (dec : resp -> option A) (s : PState) (I : Model -> Prop) (Post : A -> PState -> Model -> Prop),
  (forall rsp a mo mo' evs, dec rsp = Some a -> I mo -> nstep n mo rsp mo' evs -> Post a s mo') ->
  tgenM (Monad.msys n dec) s I Post.
Proof.
  intros A n dec s I Post H. unfold tgenM, Monad.msys. cbn. intros rsp.
  destruct (dec rsp) as [a|] eqn:E; cbn; [|auto]. intros mo' (mo & evs & HI & Hst). eapply H; eassumption.
Qed.

Definition KB (kb : option Z) (mo : Model) : Prop :=
  match kb with Some b => bv_unsigned (vm_brk (m_vmmaps mo)) = b /\ b < 2 ^ 63 | None => True end.
Definition J (Iv : Model -> Prop) (kb : option Z) (C U : Z) (mo : Model) : Prop := acc C U mo /\ Iv mo /\ KB kb mo.

Section Embed.
Variable Iv : Model -> Prop.
Hypothesis HIv : mm_inv Iv.

Lemma ev_step_J : forall atop e s kb C U,
  ev_ok e kb ->
  tgenM (ev_step atop e) s (J Iv kb C U)
        (fun z _ mo' => ev_ans e kb z /\ J Iv (ev_kb e kb) (C + ev_dc e) (U + ev_du e kb) mo').
Proof.
  intros atop e s kb C U Hok.
  destruct e as [req | addr len prot flags | addr len | addr len prot | p c h | why]; cbn [ev_step ev_ok ev_ans ev_kb ev_dc ev_du] in *.
  -
    destruct (Z.eqb_spec req 0) as [->|Hne].
    +
      eapply tgenM_mbind with (P := fun r _ mo' => (forall b, kb = Some b -> r = b) /\ J Iv kb C U mo').
      * apply tgenM_msys. intros rsp r mo mo' evs Hd (HA & HI & HK) Hst.
        destruct (brk0_query mo rsp mo' evs r Hst Hd) as (Er & Ev & Em & _).
        split; [|split; [eapply acc_brk0; eassumption | split]].
        -- intros b ->. cbn in HK. destruct HK as [HK _]. rewrite Er. exact HK.
        -- eapply HIv; [|exact Hst|exact HI]. exact I.
        -- destruct kb as [b|]; [|exact I]. cbn in *. rewrite Ev. exact HK.
      * intros r s1. eapply tgenM_mbind with (P := fun _ _ mo' => (forall b, kb = Some b -> r = b) /\ J Iv kb C U mo').
        -- unfold Monad.mupd, tgenM. cbn. auto.
        -- intros _ s2. apply tgenM_ret. intros mo [Hr HJ]. rewrite !Z.add_0_r. split; [|exact HJ].
           destruct kb as [b|]; [|exact I]. intros _. apply Hr. reflexivity.
    +
      destruct kb as [b|]; [|contradiction]. destruct Hok as [?|[Hb1 Hb2]]; [contradiction|].
      eapply tgenM_mbind with (P := fun s0 s1 mo' => J Iv (Some b) C U mo'); [unfold Monad.mget, tgenM; cbn; auto|].
      intros s0 s1.
      (* port727 (): the grow backs whole pages: + 4096 (MrUcb.ev_du, acc_brk). *)
      eapply tgenM_mbind with (P := fun _ _ mo' => J Iv None (C + 1) (U + (req - b + 4096)) mo').
      * apply tgenM_msys. intros rsp a mo mo' evs _ (HA & HI & [HK HK2]) Hst.
        split; [|split; [|exact I]].
        -- pose proof (acc_brk req mo rsp mo' evs C U Hst) as K. rewrite HK in K.
           replace (Z.max 0 (req - b)) with (req - b) in K by lia. apply K; try lia; try exact HA.
           pose proof (VmMapsDisjoint.word_range (vm_brk (m_vmmaps mo))). lia.
        -- eapply HIv; [|exact Hst|exact HI]. exact I.
      * intros a s2. destruct a.
        -- eapply tgenM_mbind with (P := fun _ _ mo' => J Iv None (C + 1) (U + (req - b + 4096)) mo'); [unfold Monad.mupd, tgenM; cbn; auto|].
           intros _ s3. apply tgenM_ret. intros mo HJ. split; [intros; contradiction | exact HJ].
        -- apply tgenM_ret. intros mo HJ. split; [intros; contradiction | exact HJ].
  -
    assert (HS : forall {A} (dec : resp -> option A) (f : A -> Z),
               tgenM (Monad.mbind (Monad.msys (NMmap addr len prot flags) dec) (fun a => Monad.mret (f a))) s (J Iv kb C U)
                     (fun _ _ mo' => True /\ J Iv None (C + 2) (U + (len + 4096)) mo')).
    { intros A dec f. eapply tgenM_mbind with (P := fun _ _ mo' => J Iv None (C + 2) (U + (len + 4096)) mo').
      - apply tgenM_msys. intros rsp a mo mo' evs _ (HA & HI & _) Hst. split; [|split; [|exact I]].
        + replace (U + (len + 4096)) with (U + len + 4096) by lia. eapply acc_mmap; eassumption.
        + eapply HIv; [|exact Hst|exact HI]. exact I.
      - intros a s1. apply tgenM_ret. intros mo HJ. split; [exact I | exact HJ]. }
    destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [apply HS|]. destruct (prot =? 0); apply HS.
  -
    (* port727 (): munmap removes a range and can split an entry: C + 2 (MrUcb.ev_dc). *)
    eapply tgenM_mbind with (P := fun _ _ mo' => J Iv None (C + 2) (U + 0) mo').
    + apply tgenM_msys. intros rsp a mo mo' evs _ (HA & HI & _) Hst. rewrite !Z.add_0_r. split; [|split; [|exact I]].
      * eapply acc_munmap; eassumption.
      * eapply HIv; [|exact Hst|exact HI]. exact I.
    + intros a s1. apply tgenM_ret. intros mo HJ. split; [exact I | exact HJ].
  -
    eapply tgenM_mbind with (P := fun _ _ mo' => J Iv None (C + 0) (U + 0) mo').
    + apply tgenM_msys. intros rsp a mo mo' evs _ (HA & HI & _) Hst. rewrite !Z.add_0_r. split; [|split; [|exact I]].
      * eapply acc_mprotect; eassumption.
      * eapply HIv; [|exact Hst|exact HI]. exact I.
    + intros a s1. apply tgenM_ret. intros mo HJ. split; [exact I | exact HJ].
  - unfold Monad.munr, tgenM. cbn. auto.
  - unfold Monad.munr, tgenM. cbn. auto.
Qed.

Lemma tgenM_membed : forall {R} atop (t : stree ev Z R) s kb C U (Post : R -> Z -> Z -> Prop),
  ucb t kb C U Post ->
  tgenM (membed atop t) s (J Iv kb C U) (fun r _ mo' => exists C' U', Post r C' U' /\ acc C' U' mo' /\ Iv mo').
Proof.
  intros R atop t. induction t as [r | e k IH]; intros s kb C U Post H; cbn [membed].
  - apply tgenM_ret. intros mo (HA & HI & _). exists C, U. cbn in H. auto.
  - cbn [ucb] in H.
    assert (HU : match e with EUndef _ | EPeek _ _ _ => True | _ => False end \/
                 (ev_ok e kb /\ forall z, ev_ans e kb z -> ucb (k z) (ev_kb e kb) (C + ev_dc e) (U + ev_du e kb) Post)).
    { destruct e; auto. }
    destruct HU as [HU | [Hok Hk]].
    + eapply tgenM_mbind with (P := fun _ _ _ => False).
      * destruct e; try contradiction; unfold tgenM; cbn; auto.
      * intros a s1. unfold tgenM. apply tgen_false.
    + eapply tgenM_mbind; [apply (ev_step_J atop e s kb C U Hok)|].
      intros z s1. cbv beta. unfold tgenM. apply tgen_pure. intros Hz. apply IH. apply Hk. exact Hz.
Qed.

Theorem tgenM_raw_malloc : forall n s kb C U (Post : mstate * option cptr -> Z -> Z -> Prop),
  ucb (cmalloc (ps_m s) n) kb C U Post ->
  tgenM (raw_malloc n) s (J Iv kb C U)
        (fun r s' mo' => exists p C' U', Post (ps_m s', p) C' U' /\
                           r = match p with Some slot => Some (slot, fresh_off (ps_m s') slot n) | None => None end /\
                           acc C' U' mo' /\ Iv mo').
Proof.
  intros n s kb C U Post H. unfold raw_malloc.
  eapply tgenM_mbind with (P := fun a s1 mo' => (a = s /\ s1 = s) /\ J Iv kb C U mo'); [unfold Monad.mget, tgenM; cbn; auto|].
  intros s0 s1. apply tgenM_pure. intros [-> ->].
  eapply tgenM_mbind; [apply (tgenM_membed _ _ s kb C U Post H)|]. intros [st' p] s2. cbv beta iota.
  eapply tgenM_mbind with (P := fun _ s3 mo' => ps_m s3 = st' /\ exists C' U', Post (st', p) C' U' /\ acc C' U' mo' /\ Iv mo').
  - unfold Monad.mupd, tgenM. cbn. intros mo Hmo. split; [reflexivity | exact Hmo].
  - intros _ s3. apply tgenM_ret. intros mo [E (C' & U' & HP & HA & HI)]. exists p, C', U'. rewrite E. auto.
Qed.

End Embed.
End WithRC.
