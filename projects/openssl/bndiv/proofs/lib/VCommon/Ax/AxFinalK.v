(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliVerdict CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWShape.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition KDer (T : TSet) (o : list byte) : TSet := fun tr => T (W 2 o ++ tr).

Lemma KDer_nil (T : TSet) : t_eq (KDer T []) T.
Proof. intros tr. unfold KDer. reflexivity. Qed.

Lemma KDer_app (T : TSet) (o bs : list byte) : t_eq (KDer T (o ++ bs)) (KDer (KDer T o) bs).
Proof. intros tr. unfold KDer. rewrite W_app, <- app_assoc. reflexivity. Qed.

Lemma KDer_eq (T T' : TSet) (o : list byte) : t_eq T T' -> t_eq (KDer T o) (KDer T' o).
Proof. intros H tr. unfold KDer. apply H. Qed.

Lemma is_prefix_app_inv {A} : forall (l a : list A), is_prefix (l ++ a) l -> a = [].
Proof.
  induction l as [|x l IH]; intros a H; [apply is_prefix_nil_r; exact H|].
  cbn in H. destruct H as [_ H]. exact (IH a H).
Qed.

(* [comment removed for export] *)
Lemma KDer_emit_same (T : TSet) (o : list byte) : T [] -> t_eq (KDer (t_emit (W 2 o) T) o) T.
Proof.
  intros H0 tr. unfold KDer, t_emit. split.
  - intros [Hp | (tr' & E & HT)].
    + apply is_prefix_app_inv in Hp. subst tr. exact H0.
    + apply app_inv_head in E. subst tr'. exact HT.
  - intros HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

(* [comment removed for export] *)
Lemma KDer_KD (o rest msg : list byte) (fs : Fs.Fs) : msg = o ++ rest -> t_eq (KDer (t_die msg fs) o) (KD msg fs o).
Proof.
  intros ->. unfold t_die, KD. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
  eapply t_eq_trans; [apply KDer_eq; rewrite W_app; apply t_emit_app|].
  apply KDer_emit_same. apply t_emit_has_nil.
Qed.

Lemma W_inj (a b : list byte) : W 2 a = W 2 b -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as -> H. f_equal. exact (IH b H).
Qed.

Lemma W_prefix (a m : list byte) : is_prefix (W 2 a) (W 2 m) -> firstn (length a) m = a.
Proof.
  revert m. induction a as [|x a IH]; intros m H; [reflexivity|].
  destruct m as [|y m]; cbn in H; [contradiction|]. destruct H as [E H]. injection E as ->.
  cbn [length firstn]. f_equal. exact (IH m H).
Qed.

(* [comment removed for export] *)
Lemma W_exit_tail (a m : list byte) (tr' : list event) (code : word) (fs : Fs.Fs) :
  W 2 a = W 2 m ++ tr' -> t_exit code fs tr' -> tr' = [].
Proof.
  intros E HT. destruct tr' as [|ev tr']; [reflexivity|]. exfalso.
  assert (Hin : In ev (W 2 a)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  unfold W in Hin. apply in_map_iff in Hin as (y & Ey & _).
  unfold t_exit, t_emit in HT. destruct HT as [Hp | (tr2 & E2 & _)].
  - cbn in Hp. destruct Hp as [Eev _]. subst ev. discriminate.
  - cbn in E2. injection E2 as Eev _. subst ev. discriminate.
Qed.

(* [comment removed for export] *)
Lemma KDer_die_prefix (msg : list byte) (fs : Fs.Fs) (o : list byte) :
  KDer (t_die msg fs) o [] -> firstn (length o) msg = o.
Proof.
  unfold KDer, t_die, t_emit. rewrite app_nil_r. intros [Hp | (tr' & E & HT)].
  - exact (W_prefix o msg Hp).
  - pose proof (W_exit_tail o msg tr' _ fs E HT) as ->. rewrite app_nil_r in E. apply W_inj in E. subst o. apply firstn_all.
Qed.

Lemma KDer_emit (msg : list byte) (fs : Fs.Fs) (o bs : list byte) :
  KDer (t_die msg fs) (o ++ bs) [] -> t_eq (KDer (t_die msg fs) o) (t_emit (W 2 bs) (KDer (t_die msg fs) (o ++ bs))).
Proof.
  intros H. pose proof (KDer_die_prefix msg fs (o ++ bs) H) as Hp.
  assert (Hp1 : firstn (length o) msg = o).
  { assert (E : firstn (length o) (firstn (length (o ++ bs)) msg) = firstn (length o) msg)
      by (rewrite firstn_firstn; f_equal; rewrite length_app; lia).
    rewrite <- E, Hp, firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. apply app_nil_r. }
  pose proof (KDer_KD o (skipn (length o) msg) msg fs ltac:(rewrite <- Hp1 at 1; symmetry; apply firstn_skipn)) as E1.
  pose proof (KDer_KD (o ++ bs) (skipn (length (o ++ bs)) msg) msg fs ltac:(rewrite <- Hp at 1; symmetry; apply firstn_skipn)) as E2.
  eapply t_eq_trans; [exact E1|]. eapply t_eq_trans; [exact (KD_emit msg fs o bs Hp)|].
  intros tr. unfold t_emit. split; (intros [X | (tr' & -> & HT)]; [left; exact X | right; exists tr'; split; [reflexivity | apply E2; exact HT]]).
Qed.
