(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog LB_Inv LibProg LibSafe LibOps.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BgState BgInv BgTree BgTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint bg_embed {A} (t : btree bptr A) : lprog A :=
  match t with
  | TRet a => LRet a
  | TUnr => LUnr
  | TMalloc n k => LMalloc n (fun r => bg_embed (k r))
  | TFree p k => LFree p (bg_embed k)
  end.

Definition BG_NBLKZ : Z := 72.
Definition BG_BSZZ : Z := 4096.

Lemma bg_embed_lwf : forall {A} (t : btree bptr A) X (Q : A -> list (bptr * Z) -> Prop),
  gwp t X Q -> lwf (okB BG_NBLKZ BG_BSZZ) (bg_embed t) X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [gwp bg_embed lwf] in *.
  - exact H.
  - exact H.
  - destruct H as ((Hlen & Hn & Hsz) & Hk & H).
    split; [unfold BG_BSZ in Hn; lia|]. split.
    { unfold okB, zlen, BG_NBLKZ, BG_BSZZ, szle. unfold BG_NBLK in Hlen. unfold BG_BSZ in Hn, Hsz. split; [lia|]. split; [exact Hn|exact Hsz]. }
    split; [rewrite Hk; reflexivity|].
    intros q Hq. apply IH. apply H. intros Hin. apply Hq. unfold slotsX.
    apply in_map_iff in Hin. destruct Hin as (xb & E & Hin). apply in_map_iff. exists xb. split; [rewrite E; reflexivity|exact Hin].
  - destruct H as (m & X' & HP & H). exists m, X'. split; [exact HP|]. apply IH. exact H.
Qed.

Lemma leaves_mono : forall {ptr A} (t : btree ptr A) (phi phi' : A -> Prop), leaves t phi -> (forall a, phi a -> phi' a) -> leaves t phi'.
Proof.
  intros ptr A t. induction t as [a| |n k IH|p k IH]; intros phi phi' H Himp; cbn [leaves] in *; auto.
  - intros r. eapply IH; [apply H|exact Himp].
  - eapply IH; [apply H|exact Himp].
Qed.

Lemma bg_embed_lleaves : forall {A} (t : btree bptr A) (phi : A -> Prop), leaves t phi -> lleaves (bg_embed t) phi.
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH]; intros H; cbn [leaves bg_embed lleaves] in *; auto.
Qed.

Definition bg_lib_one (ls : unit) (d : list Z) : lprog (unit * Z) := bg_embed (tbind (bg_one d) (fun rc => TRet (tt, rc))).
Definition bg_linv (ls : unit) (X : list (bptr * Z)) : Prop := X = [].

Theorem bg_H_one : forall ls d X, bg_linv ls X ->
  lwf (okB BG_NBLKZ BG_BSZZ) (bg_lib_one ls d) X (fun r X' => bg_linv (fst r) X').
Proof.
  intros ls d X ->. unfold bg_lib_one. apply bg_embed_lwf. apply gwp_bind.
  eapply gwp_mono; [apply fuzz_one_gwp|]. intros rc X' [-> _]. cbn. reflexivity.
Qed.

Theorem bg_H_rc : forall ls d, lleaves (bg_lib_one ls d) (fun r => snd r = 0).
Proof.
  intros ls d. unfold bg_lib_one. apply bg_embed_lleaves. apply leaves_bind'.
  eapply leaves_mono; [apply fuzz_one_leaves|]. intros rc ->. cbn. reflexivity.
Qed.

