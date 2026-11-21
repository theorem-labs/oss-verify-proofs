(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import AcctCore ExecF ITreeA NodesA CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import Monad CMonad.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


Lemma rng_le : forall R R' lo len, fp_le R R' -> rng R lo len -> rng R' lo len.
Proof. intros R R' lo len HL H. eapply rng_fp_le; eauto. Qed.

Lemma at_nodeA_mono : forall segs n R R' ms, fp_le R R' -> at_nodeA segs n R ms -> at_nodeA segs n R' ms.
Proof.
  intros segs n R R' ms HL H. destruct n; cbn [at_nodeA] in H |- *.
  all: try (destruct H as [H1 H2]; split; [exact H1|]; cbn [ncov] in H2 |- *; first [exact H2 | eapply rng_le; [exact HL| exact H2]]; fail).
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & iovs & Hi & HF).
  repeat (split; [assumption|]). split; [eapply rng_le; eauto|]. exists iovs. split; [exact Hi|].
  eapply Forall2_impl; [| exact HF]. cbn. intros a b (X1 & X2 & X3 & X4). repeat (split; [assumption|]). eapply rng_le; eauto.
Qed.

Definition fminS (n : node) (rsp : resp) (R : footprint) : footprint :=
  match n with
  | NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ =>
      fun b j => forall R1 R1', fp_le R R1 -> fstepS n rsp R1 R1' -> R1' b j
  | _ => R
  end.

Lemma fminS_ok : forall n rsp R R1 R1', fp_le R R1 -> fstepS n rsp R1 R1' ->
  fstepS n rsp R (fminS n rsp R) /\ fp_le (fminS n rsp R) R1'.
Proof.
  intros n rsp R R1 R1' HLE HF.
  assert (LE0 : forall Ra Ra', fp_le R Ra -> fstepS n rsp Ra Ra' -> fp_le R Ra').
  { intros Ra Ra' L1 F1 b j Hb. eapply fstepS_le; [exact F1|]. apply L1. exact Hb. }
  destruct n; cbn [fminS].
  all: try (split; [| intros b j Hb; eapply fstepS_le; [exact HF| apply HLE; exact Hb]];
         destruct HF as [HA HS]; split; [cbn in HA |- *; reflexivity| exact I]; fail).
  all: (split; [| intros b j Hb; exact (Hb R1 R1' HLE HF)]).
  -
    split; [cbn; intros b j Hb Ra Ra' L1 F1; exact (LE0 Ra Ra' L1 F1 b j Hb)| exact I].
  -
    destruct HF as [[HA1 HA2] [HS1 HS2]]. split; [split|split].
    + intros b j Hb Ra Ra' L1 F1. exact (LE0 Ra Ra' L1 F1 b j Hb).
    + intros Hp Hal. destruct (HA2 Hp Hal) as (A1 & A2 & _). split; [exact A1|]. split; [exact A2|].
      intros b j Hb Hj Ra Ra' L1 [[_ FA2] _]. destruct (FA2 Hp Hal) as (_ & _ & FR). apply FR; assumption.
    + intros Hnr Hp Hal. destruct (HS1 Hnr Hp Hal) as (A1 & A2 & _). split; [exact A1|]. split; [exact A2|].
      intros b j Hb Hj Ra Ra' L1 [_ [FS1 _]]. destruct (FS1 Hnr Hp Hal) as (_ & _ & FR). apply FR; assumption.
    + intros b j Hb Hj Hk Ra Ra' L1 F1. pose proof F1 as [_ [_ BW]]. apply BW; [exact Hb| exact Hj|].
      intros k Hlt. exact (Hk k Hlt Ra Ra' L1 F1).
  -
    split; [cbn; intros b j Hb _ Ra Ra' L1 F1; exact (LE0 Ra Ra' L1 F1 b j Hb)
           | intros b j Hb Ra Ra' L1 F1; exact (LE0 Ra Ra' L1 F1 b j Hb)].
  -
    split; [cbn; intros b j Hb Ra Ra' L1 F1; exact (LE0 Ra Ra' L1 F1 b j Hb)| exact I].
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMAC.
Context {St : Type}.

Definition implMAC {A} (RNG : footprint) (mc : MC St A) (s : St)
    (Q : A -> St -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implFC asegs (at_nodeA asegs) fstepS RNG (mc s) (epostF (fun p => Q (fst p) (snd p))) ms.

Lemma implMAC_lift : forall {A} RNG (m : Monad.M St A) s Q ms,
  implS asegs RNG (m s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMAC RNG (clift m) s Q ms.
Proof. intros A RNG m s Q ms H. unfold implMAC, clift. apply implFC_cinj. exact H. Qed.

Lemma implMAC_ret : forall {A} RNG (a : A) s Q ms, evtF asegs RNG (Q a s RNG) ms -> implMAC RNG (cmret a) s Q ms.
Proof. intros A RNG a s Q ms H. exact H. Qed.

Lemma implMAC_bind : forall {A B} RNG (mc : MC St A) (f : A -> MC St B) s
    (Q1 : A -> St -> footprint -> machine_state -> Prop) (Q : B -> St -> footprint -> machine_state -> Prop) ms,
  implMAC RNG mc s Q1 ms ->
  (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMAC RNG' (f a) s' Q ms') ->
  implMAC RNG (cmbind mc f) s Q ms.
Proof.
  intros A B RNG mc f s Q1 Q ms Hm Hf. unfold implMAC, cmbind, cebind in *.
  eapply implFC_bind; [exact Hm|]. intros [|[a s']] RNG' ms' H; cbn in H |- *.
  - apply evtF_done. exact I.
  - apply Hf. exact H.
Qed.

Lemma implMAC_mono : forall {A} RNG (mc : MC St A) s (Q Q' : A -> St -> footprint -> machine_state -> Prop) ms,
  implMAC RNG mc s Q ms -> (forall a s' RNG' ms', Q a s' RNG' ms' -> Q' a s' RNG' ms') -> implMAC RNG mc s Q' ms.
Proof.
  intros A RNG mc s Q Q' ms H HQ. unfold implMAC in *. eapply implFC_mono; [exact H|]. intros [|[a s']] RNG' ms'; cbn; auto.
Qed.

Lemma implMAC_evtF : forall {A} RNG (mc : MC St A) s Q P ms,
  evtF asegs RNG P ms -> (forall ms', P ms' -> implMAC RNG mc s Q ms') -> implMAC RNG mc s Q ms.
Proof. intros A RNG mc s Q P ms H K. unfold implMAC in *. eapply implFC_evtF; eauto. Qed.

Lemma implMAC_choice_l : forall {A} RNG (a b : MC St A) s Q ms, implMAC RNG a s Q ms -> implMAC RNG (cchoice a b) s Q ms.
Proof. intros A RNG a b s Q ms H. unfold implMAC, cchoice. apply implFC_choice_l. exact H. Qed.
Lemma implMAC_choice_r : forall {A} RNG (a b : MC St A) s Q ms, implMAC RNG b s Q ms -> implMAC RNG (cchoice a b) s Q ms.
Proof. intros A RNG a b s Q ms H. unfold implMAC, cchoice. apply implFC_choice_r. exact H. Qed.

Theorem implMAC_RES : forall {A} RNG (mc : MC St A) s (Q : A -> St -> footprint -> machine_state -> Prop) ms,
  (forall a s' R1 R2 ms', fp_le R1 R2 -> Q a s' R1 ms' -> Q a s' R2 ms') ->
  implMAC RNG mc s Q ms ->
  exists D, implS asegs RNG (RES D [] mc s) (epostF (fun p => Q (fst p) (snd p))) ms.
Proof.
  intros A RNG mc s Q ms Qmono H. unfold implMAC in H.
  apply (implFC_res node asegs (at_nodeA asegs) fstepS fminS fminS_ok (at_nodeA_mono asegs) (mc s) RNG _ ms); [| exact H].
  intros [|[a s']] R1 R2 ms' HLE HQ; cbn in *; [exact I| eapply Qmono; eauto].
Qed.

End ImplMAC.
End CANSEC1.
