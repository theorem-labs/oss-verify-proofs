(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc BnModel BnTree BgState ApBase ApState ApLogic ApErr ApParse ApOwner
  CtSizes CtWire CtTime CtModel CtLogic CtInv CtTac CtSpecs1 CtSpecs2 CtSpecs3 CtSpecs4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Top.
Context {ptr : Type}.
Variables rcrit rcritS rcritI : Z -> Z -> Prop.
Variable spre : sysop -> Prop.
Hypothesis Hgrow : forall na, In na GROWTH -> na <= 21844 -> rcrit (8 * na) (8 * (na * 8 / 5)).
Hypothesis HinI : rcritI SZ_GEN_DATA SZ_GENSTR.

Lemma ct_bytes_nonneg d : Forall (fun x => 0 <= x) (ct_bytes d).
Proof. unfold ct_bytes. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & _). unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma ct_bytes_length d : zlength (ct_bytes d) = zlength d.
Proof. unfold ct_bytes, zlength. rewrite length_map. reflexivity. Qed.

(* [comment removed for export] *)
Definition ct_linv (ls : ap_ls ptr) (X : list (ptr * Z)) : Prop :=
  ap_linv ls X /\ ls_data ls = repeat None ERR_NUM /\ ls_cnf ls = None.

Lemma ct_linv_blocks ls X : ct_linv ls X -> ls_blocks ls = [].
Proof.
  intros (_ & D & C). unfold ls_blocks. rewrite D, C. cbn [ApInv.cnf_blocks]. rewrite app_nil_r.
  clear. induction ERR_NUM; cbn; [reflexivity| assumption].
Qed.
Lemma ct_linv_nil ls X : ct_linv ls X -> X = [].
Proof. intros H. pose proof H as [[_ P] _]. rewrite (ct_linv_blocks ls X H) in P. apply Permutation_nil. apply Permutation_sym. exact P. Qed.
Lemma ct_linv_init : ct_linv ap_ls0 [].
Proof. split; [apply ap_linv_init|]. split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma sinv_st_of_ls_ct (ls : ap_ls ptr) X : ct_linv ls X -> CtInv.sinv (st_of_ls ls) /\ CtInv.st_blocks (st_of_ls ls) = ls_blocks ls.
Proof.
  intros [[[L S] _] [HD HC]]. unfold st_of_ls, CtInv.sinv, CtInv.st_blocks, ls_blocks. cbn -[repeat ERR_NUM CtInv.fm ApInv.fm].
  assert (FR : forall n, CtInv.fm (ptr:=ptr) (repeat None n) = []) by (intros n; induction n; cbn; [reflexivity| assumption]).
  rewrite !FR. cbn [app].
  assert (FM : forall l, CtInv.fm (ptr:=ptr) l = ApInv.fm l) by (intros l; unfold CtInv.fm, ApInv.fm; induction l as [|o l IH]; [reflexivity| cbn; rewrite IH; destruct o; reflexivity]).
  assert (CB : forall c, CtInv.cnf_blocks (ptr:=ptr) c = ApInv.cnf_blocks c) by (intros [[[a b] c]|]; reflexivity).
  rewrite FM, CB. split; [| reflexivity]. rewrite !repeat_length, length_map, L.
  repeat (split; [first [reflexivity| unfold ERR_NUM; lia]|]).
  split; [unfold CtInv.sizes_le; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; exact I|].
  split; [unfold CtInv.sizes_le; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; exact I|].
  split; [exact S|].
  split.
  { intros i. unfold get_data, get_dflags. cbn -[nth map ERR_TXT_MALLOCED]. rewrite nth_map_flag.
    destruct (nth i (ls_data ls) None); [cbn; discriminate| intros C; exfalso; apply C; reflexivity]. }
  split; [| exact HC]. intros i. rewrite HD. apply nth_repeat.
Qed.

Theorem ct_one_awp : forall ls d X, ct_linv ls X -> zlength d <= CT_MAX_INPUT ->
  awp (@okC ptr) rcrit rcritS rcritI spre (ct_one ls d) X (fun r X' => ct_linv (fst r) X').
Proof.
  intros ls d X HL Hlen. pose proof HL as [[Hwf HP] [HD0 HC0]]. unfold ct_one. apply awp_bind.
  destruct (sinv_st_of_ls_ct ls X HL) as [Hs0 Eb0].
  assert (HR0 : rel (st_of_ls ls) [] X) by (split; [exact Hs0| rewrite app_nil_r, Eb0; exact HP]).
  eapply awp_mono.
  { apply (ct_call_spec rcrit rcritS rcritI spre Hgrow HinI (ct_bytes d) (st_of_ls ls) [] X (ct_bytes_nonneg d)); [rewrite ct_bytes_length; exact Hlen| exact HR0| apply RFtop_nil]. }
  intros [rc s1] X1 (HR1 & Erc & Hnone). cbn [fst snd] in *. cbn [awp fst].
  destruct HR1 as [Hs1 HP1]. rewrite app_nil_r in HP1.
  unfold ct_linv, ap_linv, ap_ls_wf, ls_of_st, ls_blocks. cbn [ls_data ls_cnf].
  pose proof Hs1 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & T1 & T2 & S1 & S2 & S3 & FL & DN & CN).
  assert (ER : forall l : list (option (ptr * Z)), length l = ERR_NUM -> (forall j, (j < ERR_NUM)%nat -> nth j l None = None) -> l = repeat None ERR_NUM).
  { intros l Hl Hj. apply nth_ext with (d := None) (d' := None); [rewrite repeat_length; exact Hl|]. intros n Hn. rewrite nth_repeat. apply Hj. rewrite <- Hl. exact Hn. }
  assert (Hf : forall l, length l = ERR_NUM -> (forall j, (j < ERR_NUM)%nat -> nth j l None = None) -> CtInv.fm (ptr:=ptr) l = []).
  { intros l Hl Hj. rewrite (ER l Hl Hj). clear. induction ERR_NUM; cbn; [reflexivity| assumption]. }
  split; [| split; [apply (ER _ L6); intros j _; apply DN| exact CN]].
  split; [split; [exact L6| exact S3]|].
  transitivity (CtInv.st_blocks s1); [exact HP1|]. unfold CtInv.st_blocks.
  rewrite (Hf (as_file s1) L1), (Hf (as_func s1) L2).
  - cbn [app]. assert (FM : forall l, CtInv.fm (ptr:=ptr) l = ApInv.fm l) by (intros l; unfold CtInv.fm, ApInv.fm; induction l as [|o l IH]; [reflexivity| cbn; rewrite IH; destruct o; reflexivity]).
    assert (CB : forall c, CtInv.cnf_blocks (ptr:=ptr) c = ApInv.cnf_blocks c) by (intros [[[a b] c]|]; reflexivity).
    rewrite FM, CB. apply Permutation_refl.
  - intros j Hj. exact (proj2 (Hnone j Hj)).
  - intros j Hj. exact (proj1 (Hnone j Hj)).
Qed.

(* [comment removed for export] *)
Lemma aleaves_all {A} (t : aprog ptr A) (phi : A -> Prop) : (forall a, phi a) -> aleaves t phi.
Proof. intros H. induction t; cbn [aleaves]; auto. Qed.

Theorem ct_one_leaves : forall ls d, aleaves (ct_one (ptr:=ptr) ls d) (fun r => snd r = 0).
Proof.
  intros ls d. unfold ct_one. apply aleaves_bind. unfold ct_call, abind. apply aleaves_bind.
  apply aleaves_all. intros [r s1]. apply aleaves_bind. apply aleaves_all. intros [u s2]. apply aleaves_bind.
  apply aleaves_all. intros [u3 s3]. cbn. reflexivity.
Qed.
End Top.
