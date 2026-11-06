(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import PropExec MState Mem Exec ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.

Section Monad.
Context {St : Type}.

Definition M (A : Type) : Type := St -> itree node (exc (A * St)).

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
  fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : M St := fun s => Ret (Ok (s, s)).
Definition mput (s : St) : M unit := fun _ => Ret (Ok (tt, s)).
Definition mupd (f : St -> St) : M unit := fun s => Ret (Ok (tt, f s)).
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
  fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).
Definition mwhen (b : bool) (m : M unit) : M unit := if b then m else mret tt.
Definition massert (b : bool) : M unit := if b then mret tt else munr.

(* [comment removed for export] *)
Fixpoint mloop {X R} (fuel : nat) (body : X -> M (X + R)) (x : X) : M R :=
  match fuel with
  | O => munr
  | S fuel' => mbind (body x) (fun s => match s with
                                        | inl x' => mloop fuel' body x'
                                        | inr r => mret r
                                        end)
  end.

(* [comment removed for export] *)
Lemma mbind_mret : forall {A B} (a : A) (f : A -> M B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.
Lemma mbind_munr : forall {A B} (f : A -> M B) s, mbind (munr (A:=A)) f s = Ret Unr.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section Machine.
Variable segs : list Segment.

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implM, mret. apply impl_ret_ok. exact H. Qed.

Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof. intros. unfold implM, munr. apply impl_ret_unr. Qed.

Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
  implM m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
  implM (mbind m f) s Q ms.
Proof.
  intros A B m f s Q1 Q ms Hm Hf. unfold implM, mbind in *.
  eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
  intros A m s Q Q' ms H HQ. unfold implM in *. eapply impl_epost_mono; [exact H|].
  intros [a s'] ms'; cbn; auto.
Qed.

Lemma implM_sys : forall {A} n (dec : resp -> option A) s Q ms,
  evt segs (fun ms1 => at_node segs n ms1 /\
                       forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
  implM (msys n dec) s Q ms.
Proof.
  intros A n dec s Q ms H. unfold implM, msys. apply impl_enode.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp [a s'] E. cbn. specialize (Hk rsp).
  destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

Lemma implM_get : forall s Q ms, evt segs (Q s s) ms -> implM mget s Q ms.
Proof. intros. unfold implM, mget. apply impl_ret_ok. exact H. Qed.
Lemma implM_put : forall s s' Q ms, evt segs (Q tt s') ms -> implM (mput s') s Q ms.
Proof. intros. unfold implM, mput. apply impl_ret_ok. exact H. Qed.
Lemma implM_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implM (mupd f) s Q ms.
Proof. intros. unfold implM, mupd. apply impl_ret_ok. exact H. Qed.

(* [comment removed for export] *)
Lemma implM_evt : forall {A} (c : M A) s Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof. intros A c s Q P ms H K. unfold implM in *. eapply impl_evt; eauto. Qed.

Lemma implM_loop_S : forall {X R} fuel (body : X -> M (X + R)) x s Q ms,
  implM (body x) s (fun r s' ms' => match r with
                                   | inl x' => implM (mloop fuel body x') s' Q ms'
                                   | inr v => evt segs (Q v s') ms'
                                   end) ms ->
  implM (mloop (S fuel) body x) s Q ms.
Proof.
  intros X R fuel body x s Q ms H. cbn [mloop]. eapply implM_bind; [exact H|].
  intros [x'|v] s' ms' H'; cbn in H'.
  - exact H'.
  - apply implM_ret. exact H'.
Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
