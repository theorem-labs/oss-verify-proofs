(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section ImplFLaws.
  Context {node : Type}.
  Variable segs : list Segment.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF := (@ITreeA.implF node segs atn fst_ _).

  Lemma implF_bind_cong : forall {A B} RNG (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> footprint -> machine_state -> Prop) ms,
    (forall r RNG' ms', implF RNG' (k1 r) Q ms' -> implF RNG' (k2 r) Q ms') ->
    implF RNG (ITree.bind node t k1) Q ms -> implF RNG (ITree.bind node t k2) Q ms.
  Proof.
    intros A B RNG t; revert RNG. induction t as [r|n k IH]; intros RNG k1 k2 Q ms HK H; cbn [ITree.bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. eapply IH; [exact HK| apply Hk; exact HF].
  Qed.

  Lemma implF_bind_assoc : forall {A B C} RNG (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    implF RNG (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms -> implF RNG (ITree.bind node (ITree.bind node t g) f) Q ms.
  Proof.
    intros A B C RNG t; revert RNG. induction t as [r|n k IH]; intros RNG g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. apply IH. apply Hk. exact HF.
  Qed.

  Lemma implF_bind_assoc_rev : forall {A B C} RNG (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    implF RNG (ITree.bind node (ITree.bind node t g) f) Q ms -> implF RNG (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms.
  Proof.
    intros A B C RNG t; revert RNG. induction t as [r|n k IH]; intros RNG g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. apply IH. apply Hk. exact HF.
  Qed.

  (* [comment removed for export] *)
  Fixpoint tforall {A} (P : A -> Prop) (t : itree node A) : Prop :=
    match t with
    | ITree.Ret r => P r
    | Vis n k => forall x, tforall P (k x)
    end.
  Lemma tforall_bind : forall {A B} (P : A -> Prop) (P' : B -> Prop) (t : itree node A) (f : A -> itree node B),
    tforall P t -> (forall a, P a -> tforall P' (f a)) -> tforall P' (ITree.bind node t f).
  Proof.
    induction t as [r|n k IH]; intros f H Hf; cbn in *; [apply Hf; exact H|].
    intros x. apply IH; [apply H | exact Hf].
  Qed.
  Lemma tforall_true : forall {A} (t : itree node A), tforall (fun _ => True) t.
  Proof. induction t as [r|n k IH]; cbn; auto. Qed.
  Lemma tforall_mono : forall {A} (P P' : A -> Prop) (t : itree node A), tforall P t -> (forall a, P a -> P' a) -> tforall P' t.
  Proof. induction t as [r|n k IH]; intros HP HI; cbn in *; [apply HI; exact HP| intros x; apply IH; auto]. Qed.

  (* [comment removed for export] *)
  Lemma implF_bind_ext2 : forall {A B C} RNG (P : A -> Prop) (t : itree node A) (f : A -> itree node B) (g : A -> itree node C) Q1 Q2 ms,
    tforall P t ->
    (forall a RNG' ms', P a -> implF RNG' (f a) Q1 ms' -> implF RNG' (g a) Q2 ms') ->
    implF RNG (ITree.bind node t f) Q1 ms -> implF RNG (ITree.bind node t g) Q2 ms.
  Proof.
    intros A B C RNG P t; revert RNG. induction t as [r|n k IH]; intros RNG f g Q1 Q2 ms HP HK H; cbn [ITree.bind tforall] in *.
    - apply HK; [exact HP| exact H].
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. eapply IH; [apply HP| exact HK| apply Hk; exact HF].
  Qed.

  (* [comment removed for export] *)
  Lemma implF_bind_elim : forall {A B} RNG (P : A -> Prop) (t : itree node A) (h : A -> itree node B) Q1 Q2 ms,
    tforall P t ->
    (forall r RNG' ms', P r -> implF RNG' (h r) Q1 ms' -> evtF segs RNG' (Q2 r RNG') ms') ->
    implF RNG (ITree.bind node t h) Q1 ms -> implF RNG t Q2 ms.
  Proof.
    intros A B RNG P t; revert RNG. induction t as [r|n k IH]; intros RNG h Q1 Q2 ms HP Hh H; cbn [ITree.bind tforall] in *.
    - cbn. apply (Hh r); [exact HP | exact H].
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. eapply IH; [apply HP | exact Hh | apply Hk; exact HF].
  Qed.

  Lemma implF_tforall : forall {A} RNG (P : A -> Prop) (t : itree node A) Q ms,
    tforall P t -> implF RNG t Q ms -> implF RNG t (fun a RNG' ms' => Q a RNG' ms' /\ P a) ms.
  Proof.
    intros A RNG P t; revert RNG. induction t as [r|n k IH]; intros RNG Q ms HP H; cbn [tforall] in *.
    - cbn in *. eapply evtF_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
    - cbn in H |- *. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. apply IH; [apply HP| apply Hk; exact HF].
  Qed.
End ImplFLaws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rng0 (RNG : footprint) : Prop := forall b, 0 <= b <= 2^64 -> rng RNG b 0.

Lemma rng0_fp_ok : forall lz AL, rng0 (fp_ok lz AL).
Proof. intros lz AL b Hb. split; [lia|]. split; [lia|]. intros b' j Hb' Hj k Hk. exfalso. lia. Qed.

Lemma rng0_use : forall RNG b, rng0 RNG -> 0 <= b <= 2^64 -> rng RNG b 0.
Proof. intros RNG b H Hb. exact (H b Hb). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implA_implS : forall {R} RNG (t : itree node R) (Q : R -> footprint -> machine_state -> Prop) ms,
  implA bsegs RNG t Q ms -> implS bsegs RNG t Q ms.
Proof.
  intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q ms H; cbn in *; [exact H|].
  eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp RNG' HF. apply IH. apply Hk. exact (fstepS_fstepA _ _ _ _ HF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ImplAM.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.

  (* [comment removed for export] *)
  Definition postF {A} (RNG : footprint) (Q : A -> St -> machine_state -> Prop) : A * St -> footprint -> machine_state -> Prop :=
    fun p RNG' ms' => RNG' = RNG /\ Q (fst p) (snd p) ms'.

  Definition implAM {A} (RNG : footprint) (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
    implS bsegs RNG (c s) (epostF (postF RNG Q)) ms.

  Lemma implAM_fold : forall {A} RNG (c : M A) s Q ms, implS bsegs RNG (c s) (epostF (postF RNG Q)) ms -> implAM RNG c s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implAM_unfold : forall {A} RNG (c : M A) s Q ms, implAM RNG c s Q ms -> implS bsegs RNG (c s) (epostF (postF RNG Q)) ms.
  Proof. intros. exact H. Qed.

  Lemma implAM_ret : forall {A} RNG (a : A) s Q ms, evtF bsegs RNG (Q a s) ms -> implAM RNG (mret a) s Q ms.
  Proof. intros A RNG a s Q ms H. unfold implAM, mret. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  (* [comment removed for export] *)
  Lemma implAM_retF : forall {A} RNG (Q : A -> St -> machine_state -> Prop) (p : A * St) ms,
    evtF bsegs RNG (Q (fst p) (snd p)) ms -> implS bsegs RNG (Ret (Ok p)) (epostF (postF RNG Q)) ms.
  Proof. intros A RNG Q [a s] ms H. apply implF_ret_ok. cbn. eapply evtF_mono; [exact H|]. intros; split; auto. Qed.

  Lemma implAM_unr : forall {A} RNG s (Q : A -> St -> machine_state -> Prop) ms, implAM RNG munr s Q ms.
  Proof. intros. unfold implAM, munr. apply implF_ret_unr. Qed.

  Lemma implAM_bind : forall {A B} RNG (m : M A) (f : A -> M B) s Q1 Q ms,
    implAM RNG m s Q1 ms ->
    (forall a s' ms', Q1 a s' ms' -> implAM RNG (f a) s' Q ms') ->
    implAM RNG (mbind m f) s Q ms.
  Proof.
    intros A B RNG m f s Q1 Q ms Hm Hf. unfold implAM, mbind in *.
    eapply implF_ebind; [exact Hm|]. intros [a s'] RNG' ms' [-> H]. cbn in *. apply Hf. exact H.
  Qed.

  Lemma implAM_mono : forall {A} RNG (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implAM RNG m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implAM RNG m s Q' ms.
  Proof.
    intros A RNG m s Q Q' ms H HQ. unfold implAM in *. eapply implF_epost_mono; [exact H|].
    intros [a s'] RNG' ms' [E H']; split; [exact E| apply HQ; exact H'].
  Qed.

  (* [comment removed for export] *)
  Lemma implAM_sys : forall {A} RNG n (dec : resp -> option A) s Q ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF bsegs RNG (fun ms1 => at_nodeA bsegs n RNG ms1 /\
                            forall rsp a, dec rsp = Some a -> evtF bsegs RNG (Q a s) (nret ms1 rsp)) ms ->
    implAM RNG (msys n dec) s Q ms.
  Proof.
    intros A RNG n dec s Q ms Hn H. unfold implAM, msys. apply implF_enode.
    eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' [a s'] HF E. cbn.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. specialize (Hk rsp).
    destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. eapply evtF_mono; [apply Hk; reflexivity|]. intros; split; auto.
  Qed.

  Lemma implAM_get : forall RNG s Q ms, evtF bsegs RNG (Q s s) ms -> implAM RNG mget s Q ms.
  Proof. intros. unfold implAM, mget. apply implF_ret_ok. eapply evtF_mono; [exact H|]; intros; split; auto. Qed.
  Lemma implAM_put : forall RNG s s' Q ms, evtF bsegs RNG (Q tt s') ms -> implAM RNG (mput s') s Q ms.
  Proof. intros. unfold implAM, mput. apply implF_ret_ok. eapply evtF_mono; [exact H|]; intros; split; auto. Qed.
  Lemma implAM_upd : forall RNG f s Q ms, evtF bsegs RNG (Q tt (f s)) ms -> implAM RNG (mupd f) s Q ms.
  Proof. intros. unfold implAM, mupd. apply implF_ret_ok. eapply evtF_mono; [exact H|]; intros; split; auto. Qed.

  (* [comment removed for export] *)
  Lemma implAM_evt : forall {A} RNG (c : M A) s Q P ms,
    evtF bsegs RNG P ms -> (forall ms', P ms' -> implAM RNG c s Q ms') -> implAM RNG c s Q ms.
  Proof. intros A RNG c s Q P ms H K. unfold implAM in *. eapply implF_evtF; eauto. Qed.

  Lemma implAM_from_evt : forall {A} RNG (c : M A) s Q ms,
    evtF bsegs RNG (fun ms' => implAM RNG c s Q ms') ms -> implAM RNG c s Q ms.
  Proof. intros A RNG c s Q ms H. eapply implAM_evt; [exact H|]. intros ms' H'; exact H'. Qed.

  Lemma implAM_loop_S : forall {X R} RNG fuel (body : X -> M (X + R)) x s Q ms,
    implAM RNG (body x) s (fun r s' ms' => match r with
                                          | inl x' => implAM RNG (mloop fuel body x') s' Q ms'
                                          | inr v => evtF bsegs RNG (Q v s') ms'
                                          end) ms ->
    implAM RNG (mloop (S fuel) body x) s Q ms.
  Proof.
    intros X R RNG fuel body x s Q ms H. cbn [mloop]. eapply implAM_bind; [exact H|].
    intros [x'|v] s' ms' H'; cbn in H'; [exact H'| apply implAM_ret; exact H'].
  Qed.

  Lemma implAM_eq_ms : forall {X} RNG (c : M X) s Q ms ms', ms = ms' -> implAM RNG c s Q ms' -> implAM RNG c s Q ms.
  Proof. intros X RNG c s Q ms ms' -> H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma implAM_bind_assoc : forall {A B C} RNG (m : M A) (g : A -> M B) (f : B -> M C) s Q ms,
    implAM RNG (mbind m (fun a => mbind (g a) f)) s Q ms -> implAM RNG (mbind (mbind m g) f) s Q ms.
  Proof.
    intros A B C RNG m g f s Q ms H. unfold implAM, mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.
  Lemma implAM_assoc : forall {A B C} RNG (a : M A) (b : A -> M B) (k : B -> M C) s Q ms,
    implAM RNG (mbind a (fun x => mbind (b x) k)) s Q ms -> implAM RNG (mbind (mbind a b) k) s Q ms.
  Proof. intros. apply implAM_bind_assoc. exact H. Qed.
  Lemma implAM_assoc_rev : forall {A B C} RNG (a : M A) (b : A -> M B) (k : B -> M C) s Q ms,
    implAM RNG (mbind (mbind a b) k) s Q ms -> implAM RNG (mbind a (fun x => mbind (b x) k)) s Q ms.
  Proof.
    intros A B C RNG a b k s Q ms H. unfold implAM, mbind, ebind in *.
    apply implF_bind_assoc_rev in H. eapply implF_bind_cong; [| exact H].
    intros [|[x s1]] RNG' ms'; cbn [ITree.bind fst snd]; intros Hx; exact Hx.
  Qed.

  Lemma implAM_retb : forall {A B} RNG (a : A) (f : A -> M B) (s : St) Q ms,
    implAM RNG (f a) s Q ms -> implAM RNG (mbind (mret a) f) s Q ms.
  Proof. intros A B RNG a f s Q ms H. exact H. Qed.
  Lemma implAM_ret_l : forall {A B} RNG (v : A) (k : A -> M B) s Q ms,
    implAM RNG (k v) s Q ms -> implAM RNG (mbind (mret v) k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implAM_ret_l_rev : forall {A B} RNG (v : A) (k : A -> M B) s Q ms,
    implAM RNG (mbind (mret v) k) s Q ms -> implAM RNG (k v) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implAM_unr_l : forall {A B} RNG (k : A -> M B) s Q ms, implAM RNG (mbind munr k) s Q ms.
  Proof. intros. apply implAM_unr. Qed.
  Lemma implAM_get_l : forall {B} RNG (k : St -> M B) s Q ms,
    implAM RNG (k s) s Q ms -> implAM RNG (mbind mget k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implAM_put_l : forall {B} RNG (s' : St) (k : unit -> M B) s Q ms,
    implAM RNG (k tt) s' Q ms -> implAM RNG (mbind (mput s') k) s Q ms.
  Proof. intros. exact H. Qed.
  Lemma implAM_upd_l : forall {B} RNG (f : St -> St) (k : unit -> M B) s Q ms,
    implAM RNG (k tt) (f s) Q ms -> implAM RNG (mbind (mupd f) k) s Q ms.
  Proof. intros. exact H. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma implAM_sysk : forall {A B} RNG (n : node) (dec : resp -> option A) (k : A -> M B) (s : St) Q ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF bsegs RNG (fun ms1 => at_nodeA bsegs n RNG ms1 /\
                            (forall rsp a, dec rsp = Some a -> implAM RNG (k a) s Q (nret ms1 rsp))) ms ->
    implAM RNG (mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B RNG n dec k s Q ms Hn H. unfold implAM, mbind, msys, ebind, enode in *. cbn [ITree.bind ITreeA.implF].
    eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF.
    assert (ER : RNG' = RNG).
    { destruct HF as [HF _]. destruct n; try destruct Hn; cbn in HF; exact HF. }
    subst RNG'. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply implF_ret_unr.
  Qed.

  (* [comment removed for export] *)
  Lemma implAM_sys_ret : forall {A} RNG (n : node) (dec : resp -> option A) (s0 : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
    evtF bsegs RNG (fun ms1 : machine_state => at_nodeA bsegs n RNG ms1 /\
                 (forall (rsp : resp) (a : A), dec rsp = Some a -> evtF bsegs RNG (Q tt s0) (nret ms1 rsp))) ms ->
    implAM RNG (mbind (msys n dec) (fun _ => mret tt)) s0 Q ms.
  Proof.
    intros A RNG n dec s0 Q ms Hn H.
    eapply implAM_bind with (Q1 := fun _ s' ms' => s' = s0 /\ evtF bsegs RNG (Q tt s0) ms').
    - apply implAM_sys; [exact Hn|]. eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp a E. apply evtF_done. split; [reflexivity|]. exact (Hk rsp a E).
    - intros a s' ms' [-> H']. apply implAM_ret. exact H'.
  Qed.

  (* [comment removed for export] *)
  Lemma implAM_post_evt : forall {A} RNG (c : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> (forall a s' ms', Q a s' ms' -> evtF bsegs RNG (Q' a s') ms') -> implAM RNG c s Q' ms.
  Proof.
    intros A RNG c s Q Q' ms H HQ. unfold implAM in *. eapply implF_epost_evtF; [exact H|].
    intros [a s'] RNG' ms' [-> H']; cbn. eapply evtF_mono; [apply HQ; exact H'|]. intros; split; auto.
  Qed.
  Lemma implAM_post_evt' : forall {A} RNG (c : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> (forall a s' ms', Q a s' ms' -> evtF bsegs RNG (Q' a s') ms') -> implAM RNG c s Q' ms.
  Proof. intros. eapply implAM_post_evt; eauto. Qed.
  Lemma implAM_post_evt'' : forall {A} RNG (c : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> (forall a s' ms', Q a s' ms' -> evtF bsegs RNG (Q' a s') ms') -> implAM RNG c s Q' ms.
  Proof. intros. eapply implAM_post_evt; eauto. Qed.

  (* [comment removed for export] *)
  Section So.
    Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Lemma implAM_rdso : forall {A} RNG (f : stdout_st -> M A) (s : St) Q ms,
      implAM RNG (f (get_so s)) s Q ms -> implAM RNG (mbind (rd_so get_so) f) s Q ms.
    Proof. intros A RNG f s Q ms H. exact H. Qed.
    Lemma implAM_updso : forall {A} RNG (g : stdout_st -> stdout_st) (f : unit -> M A) (s : St) Q ms,
      implAM RNG (f tt) (set_so (g (get_so s)) s) Q ms -> implAM RNG (mbind (upd_so get_so set_so g) f) s Q ms.
    Proof. intros A RNG g f s Q ms H. exact H. Qed.
    Lemma implAM_updso_last : forall RNG (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
      Q tt (set_so (g (get_so s)) s) ms -> implAM RNG (upd_so get_so set_so g) s Q ms.
    Proof. intros RNG g s Q ms H. apply implAM_upd. apply evtF_done. exact H. Qed.
  End So.
End ImplAM.

End CANSEC1.
Arguments implAM {St A} RNG c s Q ms.
Arguments postF {St A} RNG Q _ _ _ /.

(* [comment removed for export] *)
Ltac ienterF := lazymatch goal with |- implAM _ _ _ _ _ => apply implAM_from_evt | |- ITreeA.implF _ _ _ _ _ _ _ => apply implF_from_evtF | _ => idtac end.
Ltac ileaveF := lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end;
                lazymatch goal with
                | |- ITreeA.implF _ _ _ ?RNG (?c ?s) (epostF (postF ?RNG' ?Q)) ?ms => change (implAM RNG c s Q ms)
                | _ => idtac end.
