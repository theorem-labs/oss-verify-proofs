(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog LB_Inv LibProg LibSafe LibOps.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint embed {A} (t : btree bptr A) : lprog A :=
  match t with
  | TRet a => LRet a
  | TUnr => LUnr
  | TMalloc n k => LMalloc n (fun r => embed (k r))
  | TFree p k => LFree p (embed k)
  end.

Definition BN_NBLK : Z := 11.
Definition BN_BSZ : Z := 524288.

Lemma embed_lwf : forall {A} (t : btree bptr A) X (Q : A -> list (bptr * Z) -> Prop),
  wp t X Q -> lwf (okB BN_NBLK BN_BSZ) (embed t) X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [wp embed lwf] in *.
  - exact H.
  - exact H.
  - destruct H as ((Hlen & Hn & Hsz) & Hk & H).
    split; [unfold BnTree.BSZ in Hn; lia|]. split.
    { unfold okB, zlen, BN_NBLK, BN_BSZ, szle. unfold NBLK in Hlen. split; [lia|]. split; [exact Hn|exact Hsz]. }
    split; [rewrite Hk; reflexivity|].
    intros q Hq. apply IH. apply H. intros Hin. apply Hq. unfold slotsX.
    apply in_map_iff in Hin. destruct Hin as (xb & E & Hin). apply in_map_iff. exists xb. split; [rewrite E; reflexivity|exact Hin].
  - destruct H as (m & X' & HP & H). exists m, X'. split; [exact HP|]. apply IH. exact H.
Qed.

Lemma embed_lleaves : forall {A} (t : btree bptr A) (phi : A -> Prop), leaves t phi -> lleaves (embed t) phi.
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH]; intros H; cbn [leaves embed lleaves] in *; auto.
Qed.

(* [comment removed for export] *)
Definition bn_lib_one (ls : lstate bptr) (d : list Z) : lprog (lstate bptr * Z) := embed (bn_one ls d).
Definition bn_linv (ls : lstate bptr) (X : list (bptr * Z)) : Prop := ls_inv ls X.

Theorem bn_H_one : forall ls d X, bn_linv ls X ->
  lwf (okB BN_NBLK BN_BSZ) (bn_lib_one ls d) X (fun r X' => bn_linv (fst r) X').
Proof.
  intros ls d X H. unfold bn_lib_one. apply embed_lwf. eapply wp_mono; [apply fuzz_one_wp; exact H|].
  intros r X' [Hinv _]. exact Hinv.
Qed.

Theorem bn_H_rc : forall ls d, lleaves (bn_lib_one ls d) (fun r => snd r = 0).
Proof. intros ls d. unfold bn_lib_one. apply embed_lleaves. apply fuzz_one_rc. Qed.

Theorem bn_linv_init : bn_linv ls_init [].
Proof. apply ls_inv_init. Qed.
