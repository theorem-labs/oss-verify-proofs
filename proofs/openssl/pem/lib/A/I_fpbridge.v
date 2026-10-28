(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes Decode RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad Stdio Canon.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import I_fwrite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma tok_ebind_assoc : forall {X Y Z'} chans (t : itree node (exc X)) (f : X -> itree node (exc Y)) (g : Y -> itree node (exc Z')),
  tok chans (ebind t (fun x => ebind (f x) g)) -> tok chans (ebind (ebind t f) g).
Proof.
  intros X Y Z' chans t f g. induction t as [[|x]|n k IH|v k IH]; cbn [ebind bind tok]; intros H; [exact H| exact H| |exact H].
  destruct n; try exact H.
  - destruct H as (Hfd & H0 & H1). split; [exact Hfd|]. split.
    + intros E. apply IH. exact (H0 E).
    + intros i Hi. apply IH. exact (H1 i Hi).
  - destruct H as (Hfd & H). split; [exact Hfd|]. apply IH. exact H.
Qed.

Section StderrTT.
Context {St : Type}.

Definition stderr_prog (buf : list Z) (ps : list (list Z)) : @M St unit :=
  mbind (stderr_pieces buf ps) (fun b => stdio_writev 2 b []).

Lemma stderr_prog_nil : forall buf (st : St), stderr_prog buf [] st = stdio_writev 2 buf [] st.
Proof. reflexivity. Qed.

Lemma iov_start_total : forall buf s, iov_total (iov_start buf s) = zlength (buf ++ s).
Proof. intros buf s. destruct buf as [|b buf]; unfold iov_total; cbn [iov_start concat]; rewrite ?app_nil_r; reflexivity. Qed.

Lemma iov_start_concat : forall buf s, concat (iov_start buf s) = buf ++ s.
Proof. intros buf s. destruct buf as [|b buf]; cbn [iov_start concat]; rewrite ?app_nil_r; reflexivity. Qed.

Lemma iov_start_len : forall buf s, (1 <= length (iov_start buf s) <= 2)%nat.
Proof. intros buf s. destruct buf; cbn; lia. Qed.

Lemma TT_stdio_writev : forall fd buf s (st : St) (T : unit * St -> TSet),
  zlength (buf ++ s) <= 2^26 -> T (tt, st) [] ->
  t_eq (TT (stdio_writev fd buf s st) T) (t_emit (evw fd (buf ++ s)) (T (tt, st))).
Proof.
  intros fd buf s st T Hl HT. unfold stdio_writev.
  eapply t_eq_trans.
  { apply TT_wv_loop; [apply iov_start_len| | | exact HT]; unfold WV_FUEL; rewrite ?iov_start_total; lia. }
  rewrite iov_start_concat, <- evw_to_bytes. apply t_eq_refl.
Qed.

Lemma tok_stdio_writev : forall fd buf s (st : St), zlength (buf ++ s) <= 2^26 -> tok [fd] (stdio_writev fd buf s st).
Proof.
  intros fd buf s st Hl. unfold stdio_writev.
  apply tok_wv_loop; [left; reflexivity| apply iov_start_len| |]; unfold WV_FUEL; rewrite ?iov_start_total; lia.
Qed.

Theorem TT_stderr_fprintf : forall ps buf (st : St) (T : unit * St -> TSet),
  zlength (buf ++ concat ps) <= 2^26 -> T (tt, st) [] ->
  t_eq (TT (stderr_prog buf ps st) T) (t_emit (evw 2 (buf ++ concat ps)) (T (tt, st))).
Proof.
  induction ps as [|p ps IH]; intros buf st T Hl HT.
  - rewrite stderr_prog_nil. cbn [concat] in *. exact (TT_stdio_writev 2 buf [] st T Hl HT).
  - unfold stderr_prog. cbn [stderr_pieces concat] in *.
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p).
    + unfold mbind at 1. unfold mbind at 1. rewrite (@TT_ebind (list Z * St) (unit * St)), (@TT_ebind (unit * St) (list Z * St)).
      eapply t_eq_trans.
      { apply TT_stdio_writev; [unfold zlength in *; rewrite ?length_app in *; lia|].
        cbn [fst snd]. rewrite <- (@TT_ebind (list Z * St) (unit * St)).
        change (ebind (stderr_pieces [] ps st) (fun x => stdio_writev 2 (fst x) [] (snd x))) with (stderr_prog [] ps st).
        apply (proj2 (IH [] st T ltac:(unfold zlength in *; rewrite ?length_app in *; cbn [length] in *; lia) HT [])). apply t_emit_has_nil. }
      cbn [fst snd]. rewrite <- (@TT_ebind (list Z * St) (unit * St)).
      change (ebind (stderr_pieces [] ps st) (fun x => stdio_writev 2 (fst x) [] (snd x))) with (stderr_prog [] ps st).
      eapply t_eq_trans; [apply t_emit_eq; apply (IH [] st T ltac:(unfold zlength in *; rewrite ?length_app in *; cbn [length] in *; lia) HT)|].
      eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite <- evw_app. cbn [app]. rewrite app_assoc. apply t_eq_refl.
    + change (stderr_prog (buf ++ p) ps st) with (mbind (stderr_pieces (buf ++ p) ps) (fun b => stdio_writev 2 b []) st).
      eapply t_eq_trans; [apply (IH (buf ++ p) st T ltac:(rewrite <- app_assoc; exact Hl) HT)|].
      rewrite <- app_assoc. apply t_eq_refl.
Qed.

Theorem tok_stderr_fprintf : forall ps buf (st : St), zlength (buf ++ concat ps) <= 2^26 -> tok [2] (stderr_prog buf ps st).
Proof.
  induction ps as [|p ps IH]; intros buf st Hl.
  - rewrite stderr_prog_nil. cbn [concat] in *. exact (tok_stdio_writev 2 buf [] st Hl).
  - unfold stderr_prog. cbn [stderr_pieces concat] in *.
    destruct (INTERNAL_BUFSIZ - zlength buf <? zlength p).
    + unfold mbind at 1. unfold mbind at 1. apply tok_ebind_assoc.
      apply tok_ebind; [apply tok_stdio_writev; unfold zlength in *; rewrite ?length_app in *; lia|].
      intros x. apply (IH [] (snd x)). unfold zlength in *; rewrite ?length_app in *; cbn [length] in *; lia.
    + change (tok [2] (stderr_prog (buf ++ p) ps st)). apply IH. rewrite <- app_assoc. exact Hl.
Qed.

End StderrTT.
