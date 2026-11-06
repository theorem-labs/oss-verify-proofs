(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto MonadF AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section Lam.
  Context {St ptr : Type}.
  Variable raw_malloc : Z -> M St (option ptr).
  Variable raw_free : ptr -> M St unit.
  Variable new_handler : M St Empty_set.
  Notation opnew := (HarnessM.opnew raw_malloc new_handler).
  Notation opdelete := (HarnessM.opdelete raw_free).
  Notation odelete := (HarnessM.odelete raw_free).

  (* [comment removed for export] *)
  Definition vctor_model (n : Z) : M St (option ptr) :=
    if n =? 0 then mret None else p <- opnew n ;; mret (Some p).
  (* [comment removed for export] *)
  Definition assign_model (n : Z) (b : option ptr) : M St (option ptr) :=
    if ERRMSG_LEN <=? n then mret b else odelete b ;;; p' <- opnew ERRMSG_LEN ;; mret (Some p').
  (* [comment removed for export] *)
  Definition lam_model (data : list Z) : M St (option ptr) :=
    let n := Z.of_nat (length data) in
    b <- vctor_model n ;;
    if unclosed data then
      t <- opnew ERRSTR_BYTES ;;
      b' <- assign_model n b ;;
      opdelete t ;;;
      mret b'
    else mret b.
End Lam.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Notation MA := (Monad.M APS).

(* [comment removed for export] *)
Lemma implMA_bind_assoc' : forall {X Y W} RNG (ma : MA X) (g : X -> MA Y) (f : Y -> MA W) s Q ms,
  implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms ->
  implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms.
Proof.
  intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
  apply implF_bind_assoc_rev in H. eapply implF_bind_cong; [| exact H].
  intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
Qed.

Lemma implMA_bind_cong : forall {X Y} RNG (ma : MA X) (k1 k2 : X -> MA Y) s Q ms,
  (forall a s' RNG' ms', implMA RNG' (k1 a) s' Q ms' -> implMA RNG' (k2 a) s' Q ms') ->
  implMA RNG (Monad.mbind ma k1) s Q ms -> implMA RNG (Monad.mbind ma k2) s Q ms.
Proof.
  intros X Y RNG ma k1 k2 s Q ms HK H. unfold implMA, Monad.mbind, ebind in *.
  eapply implF_bind_cong; [| exact H]. intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; [exact H'|].
  apply HK. exact H'.
Qed.

(* [comment removed for export] *)
Definition opnewA (n : Z) : MA AsanCtrl.aptr := HarnessM.opnew amalloc_M (new_handlerA AAllocAsan) n.
Definition opdeleteA (p : AsanCtrl.aptr) : MA unit := HarnessM.opdelete afree_M p.
Definition odeleteA (b : option AsanCtrl.aptr) : MA unit := HarnessM.odelete afree_M b.
Definition vctorA (n : Z) : MA (option AsanCtrl.aptr) := vctor_model amalloc_M (new_handlerA AAllocAsan) n.
Definition assignA (n : Z) (b : option AsanCtrl.aptr) : MA (option AsanCtrl.aptr) := assign_model amalloc_M afree_M (new_handlerA AAllocAsan) n b.
Definition lamA (data : list Z) : MA (option AsanCtrl.aptr) := lam_model amalloc_M afree_M (new_handlerA AAllocAsan) data.
Definition minify_callA (data : list Z) : MA unit := HarnessM.minify_call amalloc_M afree_M (new_handlerA AAllocAsan) data.

Lemma odeleteA_none : odeleteA None = mret tt. Proof. reflexivity. Qed.
Lemma odeleteA_some : forall p, odeleteA (Some p) = opdeleteA p. Proof. reflexivity. Qed.
Lemma vctorA_zero : vctorA 0 = mret None. Proof. reflexivity. Qed.
Lemma vctorA_pos : forall n, 0 < n -> vctorA n = (p <- opnewA n ;; mret (Some p)).
Proof. intros n H. unfold vctorA, vctor_model, opnewA. destruct (Z.eqb_spec n 0); [lia| reflexivity]. Qed.
Lemma assignA_inplace : forall n b, ERRMSG_LEN <= n -> assignA n b = mret b.
Proof. intros n b H. unfold assignA, assign_model. destruct (Z.leb_spec ERRMSG_LEN n); [reflexivity| lia]. Qed.
Lemma assignA_realloc : forall n b, n < ERRMSG_LEN -> assignA n b = (odeleteA b ;;; p' <- opnewA ERRMSG_LEN ;; mret (Some p')).
Proof. intros n b H. unfold assignA, assign_model, odeleteA, opnewA. destruct (Z.leb_spec ERRMSG_LEN n); [lia| reflexivity]. Qed.
Lemma lamA_unfold : forall data,
  lamA data = (b <- vctorA (Z.of_nat (length data)) ;;
               if unclosed data then t <- opnewA ERRSTR_BYTES ;; b' <- assignA (Z.of_nat (length data)) b ;; opdeleteA t ;;; mret b'
               else mret b).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma minify_call_of_lam : forall data s Q ms RNG,
  implMA RNG (b' <- lamA data ;; odeleteA b') s Q ms ->
  implMA RNG (minify_callA data) s Q ms.
Proof.
  intros data s Q ms RNG H. unfold minify_callA, HarnessM.minify_call. unfold lamA, lam_model, vctor_model, assign_model, odeleteA in H.
  apply implMA_bind_assoc' in H. eapply implMA_bind_cong; [| exact H]. clear H.
  intros b s' RNG' ms' H. cbv beta in H. destruct (unclosed data).
  - apply implMA_bind_assoc' in H. eapply implMA_bind_cong; [| exact H]. clear H. intros t s2 RNG2 ms2 H. cbv beta in H.
    apply implMA_bind_assoc' in H. eapply implMA_bind_cong; [| exact H]. clear H. intros b' s3 RNG3 ms3 H. cbv beta in H.
    apply implMA_bind_assoc' in H. eapply implMA_bind_cong; [| exact H]. clear H. intros u s4 RNG4 ms4 H. cbv beta in H.
    exact H.
  - exact H.
Qed.

(* [comment removed for export] *)
Lemma fuzz_oneA_unfold : forall payload,
  fuzz_oneA AAllocAsan payload
  = (HarnessM.client_init amalloc_M (new_handlerA AAllocAsan) aps_cl aset_cl ;;; minify_callA payload ;;; mret 0).
Proof. reflexivity. Qed.
End CANSEC1.
