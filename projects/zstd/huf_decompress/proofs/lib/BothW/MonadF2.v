(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (teq_refl, teq_sym, teq_trans and 11 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_mlib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto MonadF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MonadF2 () := "I59OSSVerify5KrLib6Common;Printf_mlib3teq00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transK59OSSVerify5KrLib6Common;Printf_mlib3teq01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common;Printf_mlib3teq02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF28teq_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_mlib7teq_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF27teq_symC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2eq01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW7MonadF29teq_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF2=teq_bind_congC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF2>teq_bind_assocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF2:teq_bind_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib6Common;Printf_mlib=impl_bind_extC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF29implF_teqC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4LibA6ITreeA;node_soundA00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF24mteqC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF29mteq_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF28mteq_symC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF2:mteq_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib5BothW7MonadF2:mteq_assocC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF29mteq_congC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF6implAMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7MonadF2:mteq_ret_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6MonadF5postFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~".
Import ListNotations.

Section CANSEC1. Context {rc : runConstT}.
Section Teq.
  Context {node : Type}.

  Lemma teq_refl : forall {A} (t : itree node A), teq t t.
  Proof. induction t; constructor; auto. Qed.

  Lemma teq_sym : forall {A} (t t' : itree node A), teq t t' -> teq t' t.
  Proof. intros A t t' H; induction H; constructor; auto. Qed.

  Lemma teq_trans : forall {A} (t1 t2 t3 : itree node A), teq t1 t2 -> teq t2 t3 -> teq t1 t3.
  Proof.
    intros A t1 t2 t3 H12; revert t3. induction H12 as [r|n k k' Hk IH]; intros t3 H23.
    - exact H23.
    - inversion H23; subst. constructor. intros x. apply IH. auto.
  Qed.

  Lemma teq_bind_cong : forall {A B} (t : itree node A) (f g : A -> itree node B),
    (forall x, teq (f x) (g x)) -> teq (ITree.bind node t f) (ITree.bind node t g).
  Proof. induction t as [r|n k IH]; intros f g H; cbn; [apply H| constructor; intros x; apply IH; exact H]. Qed.

  Lemma teq_bind_assoc : forall {A B C} (t : itree node A) (f : A -> itree node B) (g : B -> itree node C),
    teq (ITree.bind node (ITree.bind node t f) g) (ITree.bind node t (fun x => ITree.bind node (f x) g)).
  Proof. induction t as [r|n k IH]; intros f g; cbn; [apply teq_refl| constructor; intros x; apply IH]. Qed.

  Lemma teq_bind_l : forall {A B} (t t' : itree node A) (f : A -> itree node B),
    teq t t' -> teq (ITree.bind node t f) (ITree.bind node t' f).
  Proof. intros A B t t' f H; induction H; cbn; [apply teq_refl| constructor; auto]. Qed.
End Teq.

Section ImplFTeq.
  Context {node : Type}.
  Variable segs : list Segment.
  Variable atn : node -> footprint -> machine_state -> Prop.
  Variable fst_ : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF := (@ITreeA.implF node segs atn fst_ _).

  Lemma implF_teq : forall {A} RNG (t t' : itree node A) Q ms, teq t t' -> implF RNG t Q ms -> implF RNG t' Q ms.
  Proof.
    intros A RNG t t' Q ms H; revert RNG ms. induction H as [r|n k k' Hk IH]; intros RNG ms Hi; cbn in *.
    - exact Hi.
    - eapply evtF_mono; [exact Hi|]. intros ms1 [Hat HK]. split; [exact Hat|]. intros rsp RNG' HF. apply IH. apply HK. exact HF.
  Qed.
End ImplFTeq.

(* [comment removed for export] *)
Section MTeq.
  Context {St : Type}.
  Local Notation M := (Monad.M St).
  Local Open Scope mspec_scope.

  Definition mteq {A} (c c' : M A) : Prop := forall s, teq (c s) (c' s).

  Lemma mteq_refl : forall {A} (c : M A), mteq c c.
  Proof. intros A c s. apply teq_refl. Qed.
  Lemma mteq_sym : forall {A} (c c' : M A), mteq c c' -> mteq c' c.
  Proof. intros A c c' H s. apply teq_sym. apply H. Qed.
  Lemma mteq_trans : forall {A} (c1 c2 c3 : M A), mteq c1 c2 -> mteq c2 c3 -> mteq c1 c3.
  Proof. intros A c1 c2 c3 H1 H2 s. eapply teq_trans; [apply H1 | apply H2]. Qed.

  Lemma mteq_assoc : forall {A B C} (a : M A) (b : A -> M B) (k : B -> M C),
    mteq (mbind (mbind a b) k) (mbind a (fun x => mbind (b x) k)).
  Proof.
    intros A B C a b k s. unfold mbind, ebind.
    eapply teq_trans; [apply teq_bind_assoc|]. apply teq_bind_cong. intros r; destruct r; cbn; apply teq_refl.
  Qed.

  Lemma mteq_cong : forall {A B} (a : M A) (f g : A -> M B),
    (forall x, mteq (f x) (g x)) -> mteq (mbind a f) (mbind a g).
  Proof.
    intros A B a f g H s. unfold mbind, ebind. apply teq_bind_cong. intros r; destruct r; cbn; first [apply H | apply teq_refl].
  Qed.

  Lemma mteq_ret_l : forall {A B} (v : A) (k : A -> M B), mteq (mbind (mret v) k) (k v).
  Proof. intros A B v k s. apply teq_refl. Qed.

  Lemma implAM_teq : forall {A} RNG (c c' : M A) s Q ms, mteq c c' -> implAM RNG c s Q ms -> implAM RNG c' s Q ms.
  Proof. intros A RNG c c' s Q ms H Hi. unfold implAM in *. eapply implF_teq; [apply H | exact Hi]. Qed.
End MTeq.

(* [comment removed for export] *)
End CANSEC1.
Ltac massocF :=
  repeat lazymatch goal with
  | |- implAM _ (mbind (mbind _ _) _) _ _ _ => apply implAM_assoc
  | |- implAM _ (mbind (mret _) _) _ _ _ => apply implAM_ret_l
  end.
