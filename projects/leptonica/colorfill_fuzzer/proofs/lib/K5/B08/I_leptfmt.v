(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.G3 Require Import LeptFormats LeptShapes.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import I_pcseg I_pcgen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition kind_dir (k : lkind) (sa : Z * list byte) : pdir :=
  match k with LK_s => PDstr (fst sa) (snd sa) | LK_d => PDint 100 | LK_zu => PDzu end.

Fixpoint fill (sh : pshape) (sargs : list (Z * list byte)) : list pitem :=
  match sh with
  | [] => []
  | (k, nx, t) :: r =>
      match k with
      | LK_s => (kind_dir k (hd (0, []) sargs), nx, t) :: fill r (tl sargs)
      | _ => (kind_dir k (0, []), nx, t) :: fill r sargs
      end
  end.

Lemma ptail_fill : forall sh sargs, ptail (fill sh sargs) = pshape_bytes sh.
Proof.
  induction sh as [|[[k nx] t] r IH]; intros sargs; [reflexivity|].
  destruct k; cbn [fill ptail pshape_bytes kind_dir pdir_bytes lkind_bytes]; rewrite IH; reflexivity.
Qed.

Lemma length_fill : forall sh sargs, length (fill sh sargs) = length sh.
Proof. induction sh as [|[[k nx] t] r IH]; intros sargs; [reflexivity|]. destruct k; cbn [fill length]; rewrite IH; reflexivity. Qed.

Lemma fill_ok : forall sh sargs, pshape_ok sh = true -> Forall pitem_ok (fill sh sargs).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros sargs H; [constructor|].
  cbn [pshape_ok forallb fst snd] in H. apply andb_prop in H. destruct H as [H1 H2].
  destruct k; cbn [fill kind_dir]; (constructor; [split; [exact H1 | first [left; reflexivity | exact I]] | apply IH; exact H2]).
Qed.

Lemma ptxt_ok_range : forall l, ptxt_ok l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  induction l as [|c l IH]; intros H; [constructor|]. cbn [ptxt_ok forallb] in H. apply andb_prop in H. destruct H as [H1 H2].
  apply andb_prop in H1. destruct H1 as [H1 _]. apply andb_prop in H1. destruct H1 as [Ha Hb]. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hb.
  constructor; [lia | exact (IH H2)].
Qed.

Lemma pshape_bytes_range : forall sh, pshape_ok sh = true -> Forall (fun c => 0 <= c < 256) (pshape_bytes sh).
Proof.
  induction sh as [|[[k nx] t] r IH]; intros H; [constructor|].
  cbn [pshape_ok forallb fst snd] in H. apply andb_prop in H. destruct H as [H1 H2].
  cbn [pshape_bytes]. apply Forall_app. split; [destruct k; cbn [lkind_bytes]; repeat constructor; lia|].
  pose proof (ptxt_ok_range _ H1) as R. inversion R as [|x l Rx Rl]; subst x l. constructor; [exact Rx|].
  apply Forall_app. split; [exact Rl | exact (IH H2)].
Qed.

(* [comment removed for export] *)
Lemma lept_fmt_split : forall f ks t0 sh sargs, In (f, ks, (t0, sh)) LEPT_SHAPES ->
  f = t0 ++ ptail (fill sh sargs) ++ [0] /\ txt_ok t0 = true /\ Forall pitem_ok (fill sh sargs)
  /\ (1 <= length (t0 ++ ptail (fill sh sargs)))%nat /\ ks = map (fun it => fst (fst it)) sh /\ pshape_ok sh = true.
Proof.
  intros f ks t0 sh sargs Hin.
  pose proof (proj1 (forallb_forall _ _) LEPT_SHAPES_ok _ Hin) as OK. cbn beta iota in OK.
  apply andb_prop in OK. destruct OK as [OK L1]. apply andb_prop in OK. destruct OK as [OK SOK]. apply andb_prop in OK. destruct OK as [EQ T0].
  destruct (list_eq_dec Z.eq_dec f (t0 ++ pshape_bytes sh ++ [0])) as [E|]; [| discriminate EQ].
  rewrite ptail_fill. split; [exact E|]. split; [exact T0|]. split; [exact (fill_ok sh sargs SOK)|].
  split; [apply Z.leb_le in L1; lia|]. split; [| exact SOK].
  (* [comment removed for export] *)
  unfold LEPT_SHAPES in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <-; reflexivity|]). destruct Hin.
Qed.
