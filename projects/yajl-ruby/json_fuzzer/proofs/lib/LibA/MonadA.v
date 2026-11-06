(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Export Monad.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA ITreeA NodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section MonadA.
Context {St : Type}.
Variable segs : list Segment.
Variable P : acc -> Prop.

Local Notation M := (@M St).

Definition implMA {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implA segs (at_nodeA segs) P (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implMA_evtA : forall {A} (c : M A) s Q P0 ms,
  evtA segs P P0 ms -> (forall ms', P0 ms' -> implMA c s Q ms') -> implMA c s Q ms.
Proof. intros A c s Q P0 ms H K. unfold implMA in *. eapply implA_evtA; eauto. Qed.

Lemma implMA_ret : forall {A} (a : A) s Q ms, evtA segs P (Q a s) ms -> implMA (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implMA, mret. apply implA_ret_ok. exact H. Qed.

Lemma implMA_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implMA munr s Q ms.
Proof. intros. unfold implMA, munr. apply implA_ret_unr. Qed.

Lemma implMA_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
  implMA m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implMA (f a) s' Q ms') ->
  implMA (mbind m f) s Q ms.
Proof.
  intros A B m f s Q1 Q ms Hm Hf. unfold implMA, mbind in *.
  eapply implA_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implMA_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implMA m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implMA m s Q' ms.
Proof.
  intros A m s Q Q' ms H HQ. unfold implMA in *. eapply implA_epost_mono; [exact H|].
  intros [a s'] ms'; cbn; auto.
Qed.

Lemma implMA_sys : forall {A} n (dec : resp -> option A) s Q ms,
  evtA segs P (fun ms1 => at_nodeA segs P n ms1 /\
                          forall rsp a, dec rsp = Some a -> evtA segs P (Q a s) (nret ms1 rsp)) ms ->
  implMA (msys n dec) s Q ms.
Proof.
  intros A n dec s Q ms H. unfold implMA, msys. apply implA_enode.
  eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp [a s'] E. cbn. specialize (Hk rsp).
  destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

Lemma implMA_get : forall s Q ms, evtA segs P (Q s s) ms -> implMA mget s Q ms.
Proof. intros. unfold implMA, mget. apply implA_ret_ok. exact H. Qed.
Lemma implMA_put : forall s s' Q ms, evtA segs P (Q tt s') ms -> implMA (mput s') s Q ms.
Proof. intros. unfold implMA, mput. apply implA_ret_ok. exact H. Qed.
Lemma implMA_upd : forall f s Q ms, evtA segs P (Q tt (f s)) ms -> implMA (mupd f) s Q ms.
Proof. intros. unfold implMA, mupd. apply implA_ret_ok. exact H. Qed.

Lemma implMA_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
  implMA (body x) s (fun r s' ms' => match r with
                                    | inl x' => implMA (mloop fuel body x') s' Q ms'
                                    | inr v => evtA segs P (Q v s') ms'
                                    end) ms ->
  implMA (mloop (S fuel) body x) s Q ms.
Proof.
  intros X R fuel body x s Q ms H. cbn [mloop]. eapply implMA_bind; [exact H|].
  intros [x'|v] s' ms' H'; cbn in H'.
  - exact H'.
  - apply implMA_ret. exact H'.
Qed.

End MonadA.

End RC__1.
Arguments implMA {St} segs P {A} c s Q ms.
