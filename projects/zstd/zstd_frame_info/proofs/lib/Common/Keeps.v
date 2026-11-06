(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Driver PState.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma impl_tall : forall segs {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t (epost Q) ms -> tall P t ->
  impl segs (at_node segs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
  intros segs R t. induction t as [[|r]|n k IH]; cbn; intros P Q ms H HP.
  - exact H.
  - eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keeps.
  Context {St B : Type} (f : St -> B).
  Local Notation M := (@Monad.M St).

  Definition keeps {A} (c : M A) : Prop := forall s : St, tall (fun p => f (snd p) = f s) (c s).

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
  #[using="Type"] Lemma keeps_bind : forall {A C} (m : M A) (k : A -> M C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_getk : forall {C} (k : St -> M C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  #[using="Type"] Lemma keeps_loop : forall {X R} fuel (body : X -> M (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
  #[using="Type"] Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
  #[using="Type"] Lemma keeps_when : forall (b : bool) (m1 : M unit), keeps m1 -> keeps (mwhen b m1).
  Proof. intros [|] m1 H1; [exact H1| apply keeps_ret]. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

Ltac keeps_step :=
  first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
        | apply keeps_getk | apply keeps_bind | apply keeps_if | apply keeps_when
        | apply keeps_upd; [intros; reflexivity] ].
(* [comment removed for export] *)
Ltac keeps_tac :=
  repeat (intros; cbn beta;
          first [ solve [auto]
                | keeps_step
                | lazymatch goal with
                  | |- keeps _ (match ?x with _ => _ end) => destruct x
                  end ]).

(* [comment removed for export] *)
Lemma implM_keeps : forall segs {St B A} (f : St -> B) (c : @Monad.M St A) s Q ms,
  implM segs c s Q ms -> keeps f c -> implM segs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
  intros segs St B A f c s Q ms H K. unfold implM in *.
  eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ps_heap (s : PState) : _ := (ps_m s, ps_brk s, ps_fa s).

Section StdoutKeeps.
  Context {B : Type} (f : PState -> B).
  Hypothesis FSO : forall v s, f (set_so_ps v s) = f s.

  #[using="FSO"] Lemma upd_so_k : forall g, keeps f (upd_so ps_so set_so_ps g).
  Proof. intros g. unfold upd_so. apply keeps_upd. intros s. apply FSO. Qed.
  #[using="Type"] Lemma rd_so_k : keeps f (rd_so (St:=PState) ps_so).
  Proof. unfold rd_so. keeps_tac. Qed.
  #[using="Type"] Lemma stdio_write_loop_k : forall fuel fd iov, keeps f (stdio_write_loop (St:=PState) fuel fd iov).
  Proof. induction fuel as [|fuel IH]; intros fd iov; cbn; keeps_tac. Qed.
  #[using="Type"] Lemma stdio_write_k : forall fd buf s, keeps f (stdio_write (St:=PState) fd buf s).
  Proof. intros fd buf s. unfold stdio_write. pose proof stdio_write_loop_k. keeps_tac. Qed.
  #[using="FSO"] Lemma stdout_stdio_write_k : forall s, keeps f (stdout_stdio_write ps_so set_so_ps s).
  Proof. intros s. unfold stdout_stdio_write. pose proof rd_so_k. pose proof upd_so_k. pose proof stdio_write_k. keeps_tac. Qed.
  #[using="FSO"] Lemma stdout_writefn_k : forall s, keeps f (stdout_writefn ps_so set_so_ps s).
  Proof. intros s. unfold stdout_writefn. pose proof rd_so_k. pose proof upd_so_k. pose proof stdout_stdio_write_k. keeps_tac. Qed.
  #[using="FSO"] Lemma stdout_towrite_k : keeps f (stdout_towrite ps_so set_so_ps).
  Proof. unfold stdout_towrite. apply upd_so_k. Qed.
  #[using="FSO"] Lemma stdout_fwritex_k : forall s, keeps f (stdout_fwritex ps_so set_so_ps s).
  Proof. intros s. unfold stdout_fwritex. pose proof rd_so_k. pose proof upd_so_k. pose proof stdout_writefn_k. pose proof stdout_towrite_k. keeps_tac. Qed.
  #[using="FSO"] Lemma out_pieces_k : forall ps, keeps f (out_pieces ps_so set_so_ps ps).
  Proof. induction ps as [|p ps IH]; cbn; [apply keeps_ret|]. pose proof stdout_fwritex_k. keeps_tac. Qed.
  #[using="FSO"] Lemma stdout_vprintf_k : forall ps, keeps f (stdout_vprintf ps_so set_so_ps ps).
  Proof. intros ps. unfold stdout_vprintf. pose proof stdout_towrite_k. pose proof out_pieces_k. keeps_tac. Qed.
  #[using="FSO"] Lemma s_emit_k : forall v, keeps f (s_emit ps_so set_so_ps v).
  Proof. intros v. unfold s_emit. apply stdout_vprintf_k. Qed.
  #[using="FSO"] Lemma stdout_exit_flush_k : keeps f (stdout_exit_flush ps_so set_so_ps).
  Proof. unfold stdout_exit_flush. pose proof rd_so_k. pose proof stdout_writefn_k. keeps_tac. Qed.
End StdoutKeeps.

Lemma s_emit_heap : forall v, keeps ps_heap (s_emit ps_so set_so_ps v).
Proof. intros v. apply s_emit_k. intros; reflexivity. Qed.
