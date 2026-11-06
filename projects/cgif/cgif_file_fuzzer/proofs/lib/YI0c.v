(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma raw_addframe_fail_nil : forall ganim sgct rcur img rfattr w h top lf delay slct lct disp ti code bytes,
raw_addframe ganim sgct rcur img rfattr w h top lf delay slct lct disp ti = (code, bytes) -> code <> R_OK -> bytes = [].
Proof.
intros until code. intros bytes H Hc. unfold raw_addframe in H.
destruct (negb (rcur =? R_OK) && negb (rcur =? R_PENDING)); [injection H as _ <-; reflexivity|].
destruct (256 <? slct); [injection H as _ <-; reflexivity|].
cbv zeta in H.
lazymatch type of H with context [lzw_stream ?a ?b ?c] => destruct (lzw_stream a b c) end; [| injection H as _ <-; reflexivity].
injection H as <- _. exfalso. apply Hc. reflexivity.
Qed.
Lemma raw_addframe_code : forall ganim sgct rcur img rfattr w h top lf delay slct lct disp ti code bytes,
raw_addframe ganim sgct rcur img rfattr w h top lf delay slct lct disp ti = (code, bytes) ->
code = rcur \/ code = R_ERROR \/ code = R_EINDEX \/ code = R_OK.
Proof.
intros until code. intros bytes H. unfold raw_addframe in H.
destruct (negb (rcur =? R_OK) && negb (rcur =? R_PENDING)); [injection H as <- _; left; reflexivity|].
destruct (256 <? slct); [injection H as <- _; right; left; reflexivity|].
cbv zeta in H.
lazymatch type of H with context [lzw_stream ?a ?b ?c] => destruct (lzw_stream a b c) end; [| injection H as <- _; right; right; left; reflexivity].
injection H as <- _. right. right. right. reflexivity.
Qed.
Section CL.
Variable g : gcfg.
Lemma flush_frame_fail_nil : forall rcur cur bef code bytes,
flush_frame g rcur cur bef = (code, bytes) -> code <> R_OK -> bytes = [].
Proof.
intros rcur cur bef code bytes H Hc. unfold flush_frame in H. destruct bef as [b|].
- cbv zeta in H.
match type of H with context [match ?d with pair _ _ => _ end] => destruct d as [[[w h] t] l] end.
eapply raw_addframe_fail_nil; [exact H | exact Hc].
- eapply raw_addframe_fail_nil; [exact H | exact Hc].
Qed.
Lemma flush_frame_code : forall rcur cur bef code bytes,
flush_frame g rcur cur bef = (code, bytes) -> code = rcur \/ code = R_ERROR \/ code = R_EINDEX \/ code = R_OK.
Proof.
intros rcur cur bef code bytes H. unfold flush_frame in H. destruct bef as [b|].
- cbv zeta in H.
match type of H with context [match ?d with pair _ _ => _ end] => destruct d as [[[w h] t] l] end.
eapply raw_addframe_code; exact H.
- eapply raw_addframe_code; exact H.
Qed.
Definition cl_bytes (rcur : Z) (q bef : option frame) : list Z :=
match q with Some f => snd (flush_frame g rcur f bef) | None => [] end.
Definition cl_code (rcur : Z) (q bef : option frame) : Z :=
match q with Some f => fst (flush_frame g rcur f bef) | None => C_OK end.
Definition cl_rcur1 (s : gif_st) : Z :=
match s_q1 s with Some f => fst (flush_frame g (s_rcur s) f (s_q0 s)) | None => s_rcur s end.
Lemma cl_bytes_fail : forall rcur q bef, cl_code rcur q bef <> C_OK -> cl_bytes rcur q bef = [].
Proof.
intros rcur [f|] bef Hc; [| reflexivity]. unfold cl_code, cl_bytes in *.
destruct (flush_frame g rcur f bef) as [c b] eqn:E. cbn in Hc |- *. eapply flush_frame_fail_nil; [exact E | exact Hc].
Qed.
Lemma close_gif_dead : forall s, s_cur s <> C_OK -> close_gif g s = s_out s.
Proof.
intros s Hc. unfold close_gif. destruct (Z.eqb_spec (s_cur s) C_OK); [contradiction | reflexivity].
Qed.
Lemma concat_snoc : forall (l : list (list Z)) x, concat (l ++ [x]) = concat l ++ x.
Proof. intros l x. rewrite concat_app. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma close_gif_ok : forall s, s_cur s = C_OK ->
concat (close_gif g s) =
concat (s_out s) ++ cl_bytes (s_rcur s) (s_q1 s) (s_q0 s) ++
(if cl_code (s_rcur s) (s_q1 s) (s_q0 s) =? C_OK then cl_bytes (cl_rcur1 s) (s_q2 s) (s_q1 s) else []).
Proof.
intros s Hc. unfold cl_bytes, cl_code, cl_rcur1, close_gif. rewrite Hc. cbn -[flush_frame].
destruct (s_q1 s) as [f1|] eqn:E1; cbn -[flush_frame]; rewrite ?E1.
- destruct (flush_frame g (s_rcur s) f1 (s_q0 s)) as [c1 b1] eqn:F1. cbn -[flush_frame].
destruct (c1 =? C_OK) eqn:Q1; cbn -[flush_frame].
{ destruct (s_q2 s) as [f2|]; cbn -[flush_frame].
- destruct (flush_frame g c1 f2 (Some f1)) as [c2 b2] eqn:F2. cbn -[flush_frame].
destruct (Z.eqb_spec c2 C_OK) as [E2|Hne2]; cbn [fst s_out].
+ rewrite !concat_snoc, <- app_assoc. reflexivity.
+ rewrite (flush_frame_fail_nil _ _ _ _ _ F2 Hne2), concat_snoc, app_nil_r. reflexivity.
- rewrite concat_snoc, app_nil_r. reflexivity. }
{ apply Z.eqb_neq in Q1. rewrite (flush_frame_fail_nil _ _ _ _ _ F1 Q1). rewrite !app_nil_r. reflexivity. }
- destruct (s_q2 s) as [f2|]; cbn -[flush_frame].
+ destruct (flush_frame g (s_rcur s) f2 None) as [c2 b2] eqn:F2. cbn -[flush_frame].
destruct (Z.eqb_spec c2 C_OK) as [E2|Hne2]; cbn [fst s_out].
* rewrite concat_snoc. reflexivity.
* rewrite (flush_frame_fail_nil _ _ _ _ _ F2 Hne2), app_nil_r. reflexivity.
+ rewrite app_nil_r. reflexivity.
Qed.
End CL.
