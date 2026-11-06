(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH]; cbn; intros f H HF; [exact I| apply HF; exact H|].
  intros rsp. apply IH; [apply H| exact HF].
Qed.

Lemma impl_tall : forall segs {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t (epost Q) ms -> tall P t ->
  impl segs (at_node segs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
  intros segs R t. induction t as [[|r]|n k IH]; cbn; intros P Q ms H HP.
  - exact H.
  - eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

Section Keeps.
  Context {St B : Type} (f : St -> B).

  Definition keeps {A} (c : M St A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).

  #[using="Type"] Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  #[using="Type"] Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  #[using="Type"] Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  #[using="Type"] Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  #[using="Type"] Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  #[using="Type"] Lemma keeps_bind : forall {A C} (m : M St A) (k : A -> M St C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.

  #[using="Type"] Lemma keeps_getk : forall {C} (k : St -> M St C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  #[using="Type"] Lemma keeps_loop : forall {X R} fuel (body : X -> M St (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
  #[using="Type"] Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M St A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
  #[using="Type"] Lemma keeps_when : forall (b : bool) (m1 : M St unit), keeps m1 -> keeps (mwhen b m1).
  Proof. intros [|] m1 H1; [exact H1| apply keeps_ret]. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if | apply keeps_when
        | apply keeps_upd; [intros; solve [reflexivity | auto | eauto]] ].

Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

Lemma implM_keepsf : forall segs {St B A} (f : St -> B) (c : M St A) s Q ms,
  implM segs c s Q ms -> keeps f c -> implM segs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
  intros segs St B A0 f c s Q ms H K. unfold implM in *.
  eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

Section StdoutKeeps.
  Context {St B : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) (f : St -> B).
  Hypothesis f_set : forall so s, f (set_so so s) = f s.

  #[using="Type"] Lemma stdio_wloop_keeps : forall fuel fd bufs, keeps f (stdio_wloop (St:=St) fuel fd bufs).
  Proof. induction fuel as [|fuel IH]; intros fd bufs; cbn [stdio_wloop]; keeps_tac. Qed.
  #[using="Type"] Lemma stdio_writev_keeps : forall fd buf s, keeps f (stdio_writev (St:=St) fd buf s).
  Proof. intros fd buf s. unfold stdio_writev. apply stdio_wloop_keeps. Qed.
  #[using="f_set"] Lemma stdout_writefn_keeps : forall s, keeps f (stdout_writefn get_so set_so s).
  Proof.
    intros s. unfold stdout_writefn, stdout_stdio_write, rd_so, upd_so. pose proof stdio_writev_keeps. keeps_tac.
  Qed.
  #[using="f_set"] Lemma stdout_fwritex_keeps : forall s, keeps f (stdout_fwritex get_so set_so s).
  Proof.
    intros s. unfold stdout_fwritex, stdout_towrite, rd_so, upd_so. pose proof stdout_writefn_keeps. keeps_tac.
  Qed.
  #[using="f_set"] Lemma out_pieces_keeps : forall ps, keeps f (out_pieces get_so set_so ps).
  Proof. induction ps as [|p ps IH]; cbn [out_pieces]; [apply keeps_ret|]. apply keeps_bind; [apply stdout_fwritex_keeps| intros; exact IH]. Qed.
  #[using="f_set"] Lemma stdout_vprintf_keeps : forall ps, keeps f (stdout_vprintf get_so set_so ps).
  Proof. intros ps. unfold stdout_vprintf, stdout_towrite, upd_so. pose proof out_pieces_keeps. keeps_tac. Qed.
  #[using="f_set"] Lemma stdout_exit_flush_keeps : keeps f (stdout_exit_flush get_so set_so).
  Proof. unfold stdout_exit_flush, rd_so. pose proof stdout_writefn_keeps. keeps_tac. Qed.
End StdoutKeeps.
