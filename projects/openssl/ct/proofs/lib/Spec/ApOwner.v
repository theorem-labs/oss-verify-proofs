(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel BnModel BnTree BgState ApBase ApState ApLogic ApErr ApCnf ApInv
  ApFmt ApParse ApPrim ApObj ApObjTab ApBn ApParse2.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import ApSpecs ApParseSpec ApBnSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Section Top.
Context {ptr : Type}.
Local Notation ST := (ap_st ptr) (only parsing).
Variables rcrit rcritS rcritI : Z -> Z -> Prop.      (* [comment removed for export] *)
Variable spre : sysop -> Prop.
Local Notation awp := (awp (okAp AP_NB AP_TOT) rcrit rcritS rcritI spre) (only parsing).
Hypothesis Hrc_grow : forall m, 0 <= m <= 46 -> rcrit m 1024.
Hypothesis Hrc_shrink : forall n, 1 <= n <= 46 -> rcritS 1024 n.
Hypothesis Hspre : forall o, spre o.
(* [comment removed for export] *)
Lemma obj2txt_num_bwp : forall content X,
  roomy X -> 1 <= zlength content <= 586 ->
  bwp (okAp AP_NB AP_TOT) (tbind (obj2txt_num (tree_ops ptr) content abs0) (fun p => TRet (fst p))) X
      (fun n X' => Permutation X' X /\ -1 <= n <= OBJ_TXT_MAX).
Proof.
  intros content X HR Hlen. eapply bwp_mono; [apply (obj2txt_num_bwp0 content X HR Hlen)|]. intros n X' [HP Hn]. split; [exact HP|]. unfold OBJ_TXT_MAX. lia.
Qed.
(* [comment removed for export] *)
Definition ap_ls_wf (ls : ap_ls ptr) : Prop := length (ls_data ls) = ERR_NUM /\ sizes_le 46 (ls_data ls).
Definition ls_blocks (ls : ap_ls ptr) : list (ptr * Z) := fm (ls_data ls) ++ cnf_blocks (ls_cnf ls).
Definition ap_linv (ls : ap_ls ptr) (X : list (ptr * Z)) : Prop := ap_ls_wf ls /\ Permutation X (ls_blocks ls).

Lemma ap_linv_init : ap_linv ap_ls0 [].
Proof.
  unfold ap_linv, ap_ls_wf, ap_ls0, ls_blocks. cbn. split; [split; [reflexivity|]|apply Permutation_refl].
  unfold sizes_le. repeat constructor.
Qed.

Lemma fm_repeat_none n : fm (ptr:=ptr) (repeat None n) = [].
Proof. induction n; cbn; [reflexivity|assumption]. Qed.

Lemma nth_map_flag (l : list (option (ptr * Z))) i :
  nth i (map (fun d : option (ptr * Z) => match d with Some _ => ERR_TXT_MALLOCED | None => 0 end) l) 0 =
  match nth i l None with Some _ => ERR_TXT_MALLOCED | None => 0 end.
Proof. revert i. induction l as [|x l IH]; intros [|i]; cbn; try reflexivity. all: first [destruct i; reflexivity | destruct x; reflexivity | apply IH]. Qed.

Lemma sinv_st_of_ls ls : ap_ls_wf ls -> sinv (st_of_ls ls) /\ st_blocks (st_of_ls ls) = ls_blocks ls.
Proof.
  intros [L S]. unfold st_of_ls, sinv, st_blocks, ls_blocks. cbn -[repeat ERR_NUM fm]. rewrite !fm_repeat_none. cbn [app].
  split; [|reflexivity]. rewrite !repeat_length, length_map, L.
  repeat (split; [first [reflexivity|unfold ERR_NUM; lia]|]).
  split; [unfold sizes_le; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; exact I|].
  split; [unfold sizes_le; apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x; exact I|].
  split; [exact S|].
  intros i. unfold get_data, get_dflags. cbn -[nth map ERR_TXT_MALLOCED]. rewrite nth_map_flag.
  destruct (nth i (ls_data ls) None); [cbn; discriminate|intros C; exfalso; apply C; reflexivity].
Qed.

Lemma Wp_fuel d : Wp (zlength d) 0 <= Z.of_nat (ap_fuel d).
Proof. unfold Wp, ap_fuel, zlength. rewrite Nat2Z.inj_mul, Nat2Z.inj_add. cbn [Z.of_nat]. lia. Qed.

Theorem ap_one_awp : forall ls d X, ap_linv ls X -> zlength d <= AP_MAX_INPUT ->
  awp (ap_one ls d) X (fun r X' => ap_linv (fst r) X').
Proof.
  intros ls d X [Hwf HP] Hlen. unfold ap_one. apply awp_bind. apply awp_abind.
  destruct (sinv_st_of_ls ls Hwf) as [Hs0 Eb0].
  assert (HR0 : rel (st_of_ls ls) [] X) by (split; [exact Hs0|rewrite app_nil_r, Eb0; exact HP]).
  pose proof (parse_all rcrit rcritS rcritI spre Hrc_grow Hrc_shrink Hspre obj2txt_num_bwp (ap_bytes d) (ap_bytes_nonneg d)) as PA.
  assert (EN : zlength (ap_bytes d) = zlength d) by (unfold ap_bytes, zlength; rewrite length_map; reflexivity).
  assert (HN' : zlength (ap_bytes d) <= AP_MAX_INPUT) by (rewrite EN; exact Hlen).
  destruct (PA HN' (ap_fuel d)) as (Pp & _ & _ & _).
  eapply awp_mono.
  { apply (Pp 0 (zlength d) 0 0 (st_of_ls ls) [] X); try assumption; try lia.
    - apply Wp_fuel.
    - unfold zlength; lia.
    - apply Forall_nil.
    - unfold zlength; cbn; lia.
    - rewrite bsum_nil. lia. }
  intros [[r p'] s1] X1 (HR1 & _). cbn [fst snd] in *.
  eapply awp_mono; [apply (err_clear_error_spec rcrit rcritS rcritI spre); exact HR1|].
  intros [u2 s2] X2 (HR2 & HC2 & Hnone). cbn [fst snd] in *. cbn.
  destruct HR2 as [Hs2 HP2]. rewrite app_nil_r in HP2.
  unfold ap_linv, ap_ls_wf, ls_of_st, ls_blocks. cbn.
  pose proof Hs2 as Hs2'. destruct Hs2' as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & T1 & T2 & S1 & S2 & S3 & FL).
  split; [split; [exact L6|exact S3]|].
  transitivity (st_blocks s2); [exact HP2|]. unfold st_blocks.
  assert (Hf : forall l, length l = ERR_NUM -> (forall j, (j < ERR_NUM)%nat -> nth j l None = None) -> fm (ptr:=ptr) l = []).
  { intros l Hl Hj. assert (E : l = repeat None ERR_NUM).
    { apply nth_ext with (d := None) (d' := None); [rewrite repeat_length; exact Hl|]. intros n Hn. rewrite nth_repeat. apply Hj. rewrite <- Hl. exact Hn. }
    rewrite E. apply fm_repeat_none. }
  rewrite (Hf (as_file s2) L1), (Hf (as_func s2) L2); [cbn [app]; apply Permutation_refl| |].
  - intros j Hj. exact (proj2 (Hnone j Hj)).
  - intros j Hj. exact (proj1 (Hnone j Hj)).
Qed.

Theorem ap_one_leaves : forall ls d, aleaves (ap_one (ptr:=ptr) ls d) (fun r => snd r = 0).
Proof.
  intros ls d. unfold ap_one. apply aleaves_bind. eapply (fun H => H); clear.
  generalize ((parse2 (ap_bytes d) (ap_fuel d) 0 (zlength d) 0 0;;; err_clear_error) (st_of_ls ls)).
  intros t. induction t; cbn; auto.
Qed.
End Top.
