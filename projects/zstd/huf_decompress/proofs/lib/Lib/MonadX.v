(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (impl_bind_cong, impl_bind_assoc, implM_bind_assoc and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MonadX () := "C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6MonadX>impl_bind_congC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6MonadX?impl_bind_assocC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree<impl_ret_unrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01".
Import ListNotations.
Import ITree.Exc.

Section ImplX.
  Variable segs : list Segment.

  Lemma impl_bind_cong : forall {A B} (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> machine_state -> Prop) ms,
    (forall r ms', impl segs (at_node segs) (k1 r) Q ms' -> impl segs (at_node segs) (k2 r) Q ms') ->
    impl segs (at_node segs) (ITree.bind node t k1) Q ms -> impl segs (at_node segs) (ITree.bind node t k2) Q ms.
  Proof.
    intros A B t. induction t as [r|n k IH]; intros k1 k2 Q ms HK H; cbn [ITree.bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [exact HK| apply Hk].
  Qed.

  Lemma impl_bind_assoc : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl segs (at_node segs) (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms -> impl segs (at_node segs) (ITree.bind node (ITree.bind node t g) f) Q ms.
  Proof.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.

  Context {St : Type}.

  Lemma implM_bind_assoc : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    implM segs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms ->
    implM segs (Monad.mbind (Monad.mbind m g) f) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implM, Monad.mbind, ebind in *.
    apply impl_bind_assoc. eapply impl_bind_cong; [| exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  Lemma implM_retb : forall {A B} (a : A) (f : A -> @M St B) (s : St) Q ms,
    implM segs (f a) s Q ms -> implM segs (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof. intros A B a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma implM_sysk : forall {A B} (n : node) (dec : resp -> option A) (k : A -> @M St B) (s : St) Q ms,
    evt segs (fun ms1 => at_node segs n ms1 /\
                         (forall rsp a, dec rsp = Some a -> implM segs (k a) s Q (nret ms1 rsp))) ms ->
    implM segs (Monad.mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B n dec k s Q ms H. unfold implM, Monad.mbind, msys, ebind, enode in *. cbn [ITree.bind impl].
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply impl_ret_unr.
  Qed.

  (* [comment removed for export] *)
End ImplX.
