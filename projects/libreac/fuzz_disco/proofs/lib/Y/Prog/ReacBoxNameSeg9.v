(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:137-139 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:56-61 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa0.v:172-173. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg9.v, with its module paths, module names, addresses and numbers changed; 1501 of its 2105 lines of code are new or changed and 1283 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC1h YC4b YC44 YC45 YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YG0t.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Lemma rbn9_dec_len : forall x, bn_ok x = true -> (1 <= length (bn_dec x 1) <= 2)%nat.
Proof.
intros x Hx. apply bn_ok_in in Hx.
assert (A : forallb (fun y => (1 <=? length (bn_dec y 1))%nat && (length (bn_dec y 1) <=? 2)%nat) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A x Hx). apply andb_true_iff in A as [A1 A2].
apply Nat.leb_le in A1. apply Nat.leb_le in A2. lia.
Qed.
Lemma rbn9_tk_len : forall s l, (length (bn_tk s l) <= length l)%nat.
Proof.
intros s l. revert s. induction l as [|c r IH]; intros s; cbn [bn_tk length]; [lia|].
destruct ((c =? 45) && negb s); cbn [length]; [specialize (IH true); lia | specialize (IH s); lia].
Qed.
Lemma rbn9_glob6 : forall q, In (q, 6) tfib_globs ->
  q mod 8 = 0 /\ YImgTop.IMG_LO + 64 <= q /\ q + 6 + 64 <= YImgTop.IMG_TOP.
Proof.
intros q Hq.
assert (A : forallb (fun r => if Z.eqb (snd r) 6 then (fst r mod 8 =? 0) && (YImgTop.IMG_LO + 64 <=? fst r) &&
  (fst r + 6 + 64 <=? YImgTop.IMG_TOP) else true) tfib_globs = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A (q, 6) Hq). cbn [fst snd Z.eqb] in A.
apply andb_true_iff in A as [A A3]. apply andb_true_iff in A as [A1 A2].
apply Z.eqb_eq in A1. apply Z.leb_le in A2. apply Z.leb_le in A3. lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn9_args : forall X : rbn_in, rbm_args X ->
  ri_name X <> 0 /\ ri_token X <> 0 /\ ri_display X <> 0 /\ ri_name_len X <> 0 /\ ri_token_len X <> 0 /\
  ri_display_len X <> 0 /\ bn_ok (ri_i X) = true /\ bn_ok (ri_o X) = true /\
  ((ri_i X =? 0) && (ri_o X =? 0)) = false.
Proof.
intros X H. unfold rbm_args, reac_box_name_c.bn_args_ok in H.
apply andb_true_iff in H as [H H9]. apply andb_true_iff in H as [H H8]. apply andb_true_iff in H as [H H7].
apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply negb_true_iff in H1, H2, H3, H4, H5, H6, H9. apply Z.eqb_neq in H1, H2, H3, H4, H5, H6.
repeat split; assumption.
Qed.
Lemma rbn9_NB_len : forall X : rbn_in, (length (rbm_NB X) <= 23)%nat.
Proof. intros X. unfold rbm_NB. rewrite length_firstn. lia. Qed.
Lemma rbn9_tok0 : forall X : rbn_in, rbm_ovf 23 (bn_TK (rbm_NB X)) = 0.
Proof.
intros X. unfold rbm_ovf, bn_TK.
pose proof (rbn9_tk_len false (rbm_NB X)). pose proof (rbn9_NB_len X).
destruct (23 <? Z.of_nat (length (bn_tk false (rbm_NB X)))) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.
Lemma rbn9_TB_len : forall X : rbn_in, (length (rbm_TB X) <= 23)%nat.
Proof. intros X. unfold rbm_TB. rewrite length_firstn. lia. Qed.
Lemma rbn9_D9_len : forall X : rbn_in, rbm_args X ->
  Z.of_nat (length (rbm_D9 X)) =
    Z.of_nat (length (rbm_NB X)) + 8 + Z.of_nat (length (bn_dec (ri_i X) 1)) + Z.of_nat (length (bn_dec (ri_o X) 1)) /\
  Z.of_nat (length (rbm_D9 X)) <= 35.
Proof.
intros X HA. destruct (rbn9_args X HA) as (_ & _ & _ & _ & _ & _ & Hi & Ho & _).
pose proof (rbn9_dec_len _ Hi). pose proof (rbn9_dec_len _ Ho). pose proof (rbn9_NB_len X).
unfold rbm_D9. rewrite !length_app. cbn [length]. lia.
Qed.
Lemma rbn9_D9_ovf : forall X : rbn_in, rbm_args X ->
  rbm_ovf 47 (rbm_D9 X) = 0 /\ firstn 47 (rbm_D9 X) = rbm_D9 X.
Proof.
intros X HA. destruct (rbn9_D9_len X HA) as [_ H]. unfold rbm_ovf.
split; [destruct (47 <? Z.of_nat (length (rbm_D9 X))) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]|].
apply firstn_all2. lia.
Qed.
Lemma rbn9_ovf01 : forall cap l, rbm_ovf cap l = 0 \/ rbm_ovf cap l = 1.
Proof. intros cap l. unfold rbm_ovf. destruct (cap <? Z.of_nat (length l)); [right | left]; reflexivity. Qed.
Lemma rbn9_acc : forall X : rbn_in, rbm_args X ->
  rbm_acc X = (rbm_ovf 23 (rbm_NM X) =? 0) && (Z.of_nat (length (rbm_NB X)) <? ri_name_len X) &&
    (Z.of_nat (length (rbm_TB X)) <? ri_token_len X) && (Z.of_nat (length (rbm_D9 X)) + 5 <? ri_display_len X).
Proof.
intros X HA. pose proof HA as HA'. destruct (rbn9_args X HA) as (_ & _ & _ & _ & _ & _ & Hi & Ho & Hz).
unfold rbm_acc, reac_box_name_c.bn_accept. unfold rbm_args in HA'. rewrite HA'.
unfold bn_ret. rewrite Hi, Ho, Hz. cbn [andb negb].
unfold rbm_ovf, rbm_TB, rbm_NB, rbm_D9, rbm_NB, rbm_NM.
destruct (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X))) <=? 23) eqn:E.
- apply Z.leb_le in E.
  replace (23 <? Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)))) with false
    by (symmetry; apply Z.ltb_ge; lia).
  rewrite (firstn_all2 (n := 23%nat)) by lia.
  pose proof (rbn9_tk_len false (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X))) as T. unfold bn_TK.
  rewrite (firstn_all2 (n := 23%nat)) by lia.
  unfold bn_DP. rewrite !length_app. cbn [length]. cbn [Z.eqb andb].
  replace (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) + (2 + (length (bn_dec (ri_i X) 1) +
    (6 + (length (bn_dec (ri_o X) 1) + 5)))))) with
    (Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) + (2 + (length (bn_dec (ri_i X) 1) +
    (6 + length (bn_dec (ri_o X) 1))))) + 5) by lia.
  reflexivity.
- apply Z.leb_gt in E.
  replace (23 <? Z.of_nat (length (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)))) with true
    by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma rbn9_acc_parts : forall X : rbn_in, rbm_args X -> rbm_ovf 23 (rbm_NM X) = 0 ->
  rbm_NB X = rbm_NM X /\ rbm_TB X = bn_TK (rbm_NM X) /\
  rbm_D9 X ++ [32; 111; 117; 116; 41] = bn_DP (rbm_NM X) (ri_i X) (ri_o X).
Proof.
intros X HA H0. unfold rbm_ovf in H0.
destruct (23 <? Z.of_nat (length (rbm_NM X))) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
assert (HNB : rbm_NB X = rbm_NM X) by (unfold rbm_NB; apply firstn_all2; lia).
split; [exact HNB|]. split.
- unfold rbm_TB. rewrite HNB. pose proof (rbn9_tk_len false (rbm_NM X)). unfold bn_TK. apply firstn_all2. lia.
- unfold rbm_D9, bn_DP. rewrite HNB. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma rbn9_acc_lens : forall X : rbn_in, rbm_acc X = true ->
  rbm_args X /\ Z.of_nat (length (rbm_NM X)) + 1 <= Z.min (ri_name_len X) 24 /\
  Z.of_nat (length (bn_TK (rbm_NM X))) + 1 <= Z.min (ri_token_len X) 24 /\
  Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) + 1 <= Z.min (ri_display_len X) 48.
Proof.
intros X Hacc.
assert (HA : rbm_args X).
{ unfold rbm_acc, reac_box_name_c.bn_accept in Hacc. unfold rbm_args.
  do 4 (apply andb_true_iff in Hacc as [Hacc _]). exact Hacc. }
pose proof Hacc as Hacc'. rewrite (rbn9_acc X HA) in Hacc'.
apply andb_true_iff in Hacc' as [Hacc' H4]. apply andb_true_iff in Hacc' as [Hacc' H3].
apply andb_true_iff in Hacc' as [H1 H2].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4.
destruct (rbn9_acc_parts X HA H1) as (E1 & E2 & E3).
destruct (rbn9_D9_len X HA) as (_ & HD).
pose proof (rbn9_NB_len X) as HNB.
assert (HL3 : Z.of_nat (length (bn_DP (rbm_NM X) (ri_i X) (ri_o X))) = Z.of_nat (length (rbm_D9 X)) + 5)
  by (rewrite <- E3, length_app; cbn [length]; lia).
rewrite E1 in H2, HNB. rewrite E2 in H3.
pose proof (rbn9_tk_len false (rbm_NM X)) as HT. unfold bn_TK in H3 |- *.
split; [exact HA|]. split; [lia|]. split; [lia|]. lia.
Qed.
Definition rbn9_kept (W : world SEGS) (m m' : word -> option byte) (Wr : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m' a).
Lemma rbn9_kept_of_frame : forall E rs W (m m' : word -> option byte) (Wr : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> Wr a) -> rbn9_kept W m m' Wr.
Proof.
intros E rs W m m' Wr HF HG HW. split.
- intros a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. intros Hi. apply Hn, HW, Hi.
- intros a _ Hp. exact (apresent_grows _ _ _ _ HG Hp).
Qed.
Lemma rbn9_kept_trans : forall W m1 m2 m3 (Wr1 Wr2 : Z -> Prop),
  rbn9_kept W m1 m2 Wr1 -> rbn9_kept W m2 m3 Wr2 -> rbn9_kept W m1 m3 (fun a => Wr1 a \/ Wr2 a).
Proof.
intros W m1 m2 m3 Wr1 Wr2 [K1 P1] [K2 P2]. split.
- intros a Ha Hn. rewrite (K2 a Ha) by tauto. apply K1; tauto.
- intros a Ha Hp. apply P2, P1; assumption.
Qed.
Lemma rbn9_kept_mono : forall W m m' (Wr Wr' : Z -> Prop),
  rbn9_kept W m m' Wr -> (forall a, Wr a -> Wr' a) -> rbn9_kept W m m' Wr'.
Proof. intros W m m' Wr Wr' [K P] H. split; [intros a Ha Hn; apply K; [exact Ha | intros Hw; apply Hn, H, Hw] | exact P]. Qed.
Lemma rbn9_kept_refl : forall W m (Wr : Z -> Prop), rbn9_kept W m m Wr.
Proof. intros W m Wr. split; [reflexivity | intros a _ Hp; exact Hp]. Qed.
Lemma rbn9_kept_val : forall W m m' (Wr : Z -> Prop) a n v,
  rbn9_kept W m m' Wr -> (forall i, 0 <= i < Z.of_nat n -> ~ Wr (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' Wr a n v [K _] Hn H0 H1 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [|exact Hv].
intros i Hi. apply K; [lia | apply Hn; lia].
Qed.
Lemma rbn9_kept_garr : forall W m m' (Wr : Z -> Prop) a l,
  rbn9_kept W m m' Wr -> (forall i, 0 <= i < Z.of_nat (length l) -> ~ Wr (a + i)) -> 0 <= a ->
  a + Z.of_nat (length l) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' Wr a l HK Hn H0 H1 Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (rbn9_kept_val W m m' Wr _ 1 _ HK); [| lia | lia | exact Hv].
intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hn. lia.
Qed.
Lemma rbn9_kept_step : forall E rs W (m1 m2 m3 : word -> option byte) (Wr : Z -> Prop),
  rbn9_kept W m1 m2 Wr -> frame_of E rs (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) ->
  mem_grows (mrestrict (w_H W) m2) (mrestrict (w_H W) m3) -> (forall a, in_wrange E rs a -> Wr a) ->
  rbn9_kept W m1 m3 Wr.
Proof.
intros E rs W m1 m2 m3 Wr K HF HG HW.
apply (rbn9_kept_mono W m1 m3 (fun a => Wr a \/ Wr a)); [|tauto].
exact (rbn9_kept_trans W m1 m2 m3 Wr Wr K (rbn9_kept_of_frame E rs W m2 m3 Wr HF HG HW)).
Qed.
Lemma rbn9_garr8_app : forall (m : word -> option byte) a l1 l2,
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl | Hl].
- rewrite app_nth1 by exact Hl. exact (H1 j Hl).
- rewrite app_nth2 by exact Hl. destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma rbn9_aview_val1 : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
rewrite V0. cbn [option_map]. f_equal.
assert (Hle : YO0f.le_byte v 1 0 = v).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
rewrite Hle, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma rbn9_val1_aview : forall H H' (m m' : word -> option byte) a a' v,
  aview SEGS H' m' a' = aview SEGS H m a -> val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  val_mem SEGS (mrestrict H' m') a' 1 v.
Proof.
intros H H' m m' a a' v E Hv Hr k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
unfold aview in E. rewrite V0 in E. cbn [option_map] in E.
destruct (mbyte SEGS (mrestrict H' m') a') as [b|] eqn:Eb; [|discriminate]. cbn [option_map] in E.
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rbn9_garr8_copy : forall H H' (m m' : word -> option byte) x d l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H' m' (d + j) = aview SEGS H m (x + j)) ->
  garr8 SEGS (mrestrict H m) x l -> garr8 SEGS (mrestrict H' m') d l.
Proof.
intros H H' m m' x d l HE Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
exact (rbn9_val1_aview H H' m m' _ _ _ (HE (Z.of_nat j) ltac:(lia)) Hv Hr).
Qed.
Definition rbn9_same (regs regs2 : bvmap 5 word) (l : list Z) : Prop :=
  forall r, In r l -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition RBN9_ACC : Z := 0x6cc.
Definition RBN9_TAIL : Z := 0x700.
Definition rbn9d_regions : smem :=
  [ YP09.mkRegion (Some 18%nat) 0 64 4 30
      [YP09.mkChunk 4 (CVal 1 (SLit 5)); YP09.mkChunk 5 (CVal 1 (SLit 242)); YP09.mkChunk 6 (CVal 1 (SLit 242));
       YP09.mkChunk 7 (CVal 1 (SLit 242)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0));
       YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 242)); YP09.mkChunk 12 (CVal 1 (SLit 242));
       YP09.mkChunk 13 (CVal 1 (SLit 242)); YP09.mkChunk 14 (CVal 1 (SLit 242)); YP09.mkChunk 15 (CVal 1 (SLit 242));
       YP09.mkChunk 16 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0));
       YP09.mkChunk 19 (CVal 1 (SLit 242)); YP09.mkChunk 20 (CVal 1 (SLit 242)); YP09.mkChunk 21 (CVal 1 (SLit 242));
       YP09.mkChunk 22 (CVal 1 (SLit 242)); YP09.mkChunk 23 (CVal 1 (SLit 242)); YP09.mkChunk 24 (CVal 1 (SLit 0));
       YP09.mkChunk 25 (CVal 1 (SLit 0)); YP09.mkChunk 26 (CVal 1 (SLit 0)); YP09.mkChunk 27 (CVal 1 (SLit 0));
       YP09.mkChunk 28 (CVal 1 (SLit 0)); YP09.mkChunk 29 (CVal 1 (SLit 0))] ].
Definition ss_rbn9d : sstate :=
  mkSS (AF_both3_reac_box_name + RBN9_TAIL) sr_atoms rbn9d_regions None (mkFacts [] [] []).
Definition ERB9d (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Lemma regs_ok_ERB9d : forall regs, regs_ok (ERB9d regs) sr_atoms regs.
Proof.
intros. unfold ERB9d. apply (regs_ok_agree 32 (Ereg regs [])).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9d_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc (SH : Z),
  getr regs 18 = w64 SH -> 0 <= SH -> SH + 64 <= 2 ^ 64 ->
  (forall a, SH + 4 <= a < SH + 30 -> apresent (w_H W) memc a) ->
  (forall j, 4 <= j < 30 -> val_mem SEGS (mrestrict (w_H W) memc) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh true true true true) 0)) ->
  st_ok_pi SEGS VAL (ERB9d regs) ss_rbn9d
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN9_TAIL))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc SH H18 HS0 HS1 HP HSH.
rewrite restrict_mkst_fx.
set (E := ERB9d regs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9d; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold ss_rbn9d, rbn9d_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9d.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 18%nat SH E18) by lia. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
  + repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?j (CVal 1 (SLit ?v))) =>
      apply (chunk_ok_val SEGS E _ SH j 1 (SLit v) v); [reflexivity | lia | zside | exact (HSH j ltac:(lia))] end.
- cbn [pairwise_disjoint]. split; exact I.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn9_byte_lit : forall E m n b lo hi wlo whi cs od v w,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit v))) cs -> byte_of_word (Z_to_bv 64 v) 0 = Z_to_bv 8 (YO0f.le_byte w 1 0) ->
  val_mem SEGS m (b + od) 1 w.
Proof.
intros E m n b lo hi wlo whi cs od v w (_ & _ & _ & Hcs) Hn Hc Hv k Hk.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.r_base base_val YP09.c_off YP09.c_val] in Hb1, Hb2. rewrite Hn in Hb1, Hb2.
destruct k as [|k]; [|lia]. rewrite Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2.
cbn [YP09.cbyte sv_denot] in Hb1. injection Hb1 as <-. f_equal. exact Hv.
Qed.
Lemma rbn9_pc : forall (fq : YK11.FPState) (W : world SEGS) regs mem md Q p q, p = q ->
  SRr SEGS W (cfg_at (fx := fq) SEGS p regs mem md) Q ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 q) mem (seg_rom SEGS)) md) Q.
Proof. intros fq W regs mem md Q p q -> H. exact H. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Ltac r9ewu := cbn [ew ewset extK Nat.eqb];
  lazymatch goal with |- bv_unsigned (ew ?E ?n) = _ => lazymatch goal with Ex : ew E n = Z_to_bv 64 _ |- _ => rewrite Ex end end;
  rewrite unsigned_lit_small by lia; reflexivity.
Ltac r9wr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbv beta;
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    cbn [ew ewset extK Nat.eqb] in Hr;
    repeat match goal with Ex : ew _ _ = Z_to_bv 64 _ |- _ => progress rewrite Ex in Hr end;
    rewrite ?unsigned_lit_small in Hr by lia; lia |]); destruct Hin.
Ltac r9step KP :=
  lazymatch goal with HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ =>
  let K2 := fresh "KP" in
  pose proof (rbn9_kept_step _ _ _ _ _ _ _ KP HFr HG ltac:(r9wr)) as K2;
  clear KP HFr HG; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end); rename K2 into KP end.
Ltac r9same EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- getr _ (Z_to_bv 5 ?z) = _ =>
      let R := fresh "R" in prreg HS (Z_to_bv 5 z) R; rewrite R; apply EE; reflexivity end |]);
  destruct Hr.
Lemma rbn9_tail : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (SH : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 18 = w64 SH -> 0 <= SH -> SH + 64 <= 2 ^ 64 ->
  (forall a, SH + 4 <= a < SH + 30 -> apresent (w_H W) memc a) ->
  (forall a, SH + 4 <= a < SH + 30 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall j, 4 <= j < 30 -> val_mem SEGS (mrestrict (w_H W) memc) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh true true true true) 0)) ->
  (forall regs2 mem2 mdc2,
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k ->
     rbn9_same regs regs2 [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
     rbn9_kept W memc mem2 (fun a => SH + 4 <= a < SH + 30) ->
     (forall j, 4 <= j < 30 ->
        val_mem SEGS (mrestrict (w_H W) mem2) (SH + j) 1 (nth (Z.to_nat j) (rbn_sh false false false false) 0)) ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_P10) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN9_TAIL) regs memc mdc) Q.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs SH Q HJ H18 HS0 HS1 HP HW HSH K.
pose proof (rbn9d_entry fq W regs memc SH H18 HS0 HS1 HP HSH) as HS.
set (E := ERB9d regs) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9d; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9d; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E18 : ew E 18 = Z_to_bv 64 SH) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
clearbody E.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (rbn9_kept_refl W memc (fun a => SH + 4 <= a < SH + 30)) as KP.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_box_name + RBN9_TAIL)) with (Z_to_bv 64 (BASE + AF_both3_reac_box_name + RBN9_TAIL)).
rewrite <- Z.add_assoc.
paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN_P10).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat); [reflexivity | r9ewu |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HW; lia |].
  apply awr_ok_nil. }
r9step KP.
pmkst HS.
lazymatch goal with |- SRr _ ?W (mkCfg (mkst (fx := ?fq) (ms_regs ?msx) _ (ms_mem ?msx) _) ?mdx) ?Q =>
  apply (rbn9_pc fq W (ms_regs msx) (ms_mem msx) mdx Q (BASE + AF_both3_reac_box_name + RBN_P10));
  [unfold AF_both3_reac_box_name, RBN_P10; lia|] end.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
apply K.
- exact HJ.
- r9same EE.
- exact KP.
- intros j Hj. assert (Hjj : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/
    j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 19 \/ j = 20 \/ j = 21 \/ j = 22 \/ j = 23 \/ j = 24 \/ j = 25 \/
    j = 26 \/ j = 27 \/ j = 28 \/ j = 29) by lia.
  repeat (destruct Hjj as [-> | Hjj];
    [eapply (rbn9_byte_lit _ _ _ _ _ _ _ _ _ _ _ _ HR0 ltac:(r9ewu));
     [cbn [In]; repeat (first [left; reflexivity | right]) | apply bv_eq; vm_compute; reflexivity] |]).
  subst j. eapply (rbn9_byte_lit _ _ _ _ _ _ _ _ _ _ _ _ HR0 ltac:(r9ewu));
  [cbn [In]; repeat (first [left; reflexivity | right]) | apply bv_eq; vm_compute; reflexivity].
Qed.
Definition rbn9_cpy (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (m : word -> option byte) (A d x n : Z) : Prop :=
  0 <= n < 2 ^ 32 /\ 0 <= d /\ d + n <= 2 ^ 63 /\
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (A - ESTACK <= a < A)) /\
  amem_range d n /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF d n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) d n) /\
  0 <= x /\ x + n <= 2 ^ 63 /\
  (forall a, x <= a < x + n -> aview SEGS (w_H W) m a <> None /\ ~ (A - ESTACK <= a < A)) /\
  (d + n <= x \/ x + n <= d) /\ amem_range x n /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) m) x n).
Lemma rbn9_amem_sh : forall y p n, amem_range p n -> 0 <= p -> p <= y < p + n ->
  kLowMemEnd <= shadow_of_addr SHADOW_OFF y < kHighMemBeg.
Proof.
intros y p n Ham Hp Hy. unfold shadow_of_addr.
pose proof (Z.div_mod y 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_amem_hull : forall s p n, amem_range p n -> 0 <= p -> 0 < n ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighMemBeg.
Proof.
intros s p n Ham Hp Hn Hs. unfold shadow_addr in Hs.
pose proof (Z.div_mod p 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)) as M4.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_amem_out : forall y p n, amem_range p n -> 0 <= p -> kLowMemEnd <= y < kHighMemBeg -> ~ (p <= y < p + n).
Proof. intros y p n Ham Hp Hy Hc. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. Qed.
Lemma rbn9_cpy_kept2 : forall STK sp0 FP ly S own lyc Sc W m m' A d x n (Wr : Z -> Prop),
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m A d x n -> rbn9_kept W m m' Wr ->
  (forall a, Wr a -> ~ (kLowMemEnd <= a < kHighMemBeg)) -> (forall a, x <= a < x + n -> ~ Wr a) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W m' A d x n.
Proof.
intros STK sp0 FP ly S own lyc Sc W m m' A d x n Wr
  (Hn & Hd0 & Hdn & Hdw & Hdam & Hdra & Hdhv & Hx0 & Hxn & Hxs & Hdx & Hxam & Hxra & Hxhv) [HK _] HWb HWx.
assert (KS : forall y, kLowMemEnd <= y < kHighMemBeg -> aview SEGS (w_H W) m' y = aview SEGS (w_H W) m y).
{ intros y Hy. apply HK; [unfold kLowMemEnd, kHighMemBeg in Hy; lia | intros Hw; exact (HWb y Hw Hy)]. }
split; [exact Hn|]. split; [exact Hd0|]. split; [exact Hdn|]. split; [exact Hdw|]. split; [exact Hdam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hdra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y d n Hdam Hd0 Hy). }
split.
{ intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s d n Hdam Hd0 Hp Hs)). exact (Hdhv Hp s Hs). }
split; [exact Hx0|]. split; [exact Hxn|].
split.
{ intros a Ha. destruct (Hxs a Ha) as [Hv Hw]. split; [|exact Hw]. rewrite HK; [exact Hv | lia | exact (HWx a Ha)]. }
split; [exact Hdx|]. split; [exact Hxam|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) m)); [|exact Hxra].
  intros y Hy. apply KS. exact (rbn9_amem_sh y x n Hxam Hx0 Hy). }
intros Hp s Hs. rewrite (KS s (rbn9_amem_hull s x n Hxam Hx0 Hp Hs)). exact (Hxhv Hp s Hs).
Qed.
Lemma rbn9_kept_call : forall (W : world SEGS) (m1 m2 m3 : word -> option byte) (Wr : Z -> Prop) d n A,
  rbn9_kept W m1 m2 Wr ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
  (forall a, apresent (w_H W) m2 a -> apresent (w_H W) m3 a) ->
  (forall a, d <= a < d + n -> Wr a) -> (forall a, A - ESTACK <= a < A -> Wr a) ->
  rbn9_kept W m1 m3 Wr.
Proof.
intros W m1 m2 m3 Wr d n A [K P] HE HP H1 H2. split.
- intros a Ha Hn. rewrite HE; [apply K; [exact Ha | exact Hn] | exact Ha | |]; intros Hc; apply Hn; auto.
- intros a Ha Hp. apply HP, P; assumption.
Qed.
Lemma rbn9_cp_run : forall (W : world SEGS) (m1 m2 memc : word -> option byte) d x n,
  (forall j, 0 <= j < n -> aview SEGS (w_H W) m1 (d + j) = aview SEGS (w_H W) memc (x + j)) ->
  rbn9_kept W m1 m2 (fun _ => False) -> 0 <= d -> d + n <= 2 ^ 64 ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m2 (d + j) = aview SEGS (w_H W) memc (x + j).
Proof. intros W m1 m2 memc d x n H [K _] Hd Hdn j Hj. rewrite (K (d + j) ltac:(lia) (fun c => c)). apply H, Hj. Qed.
Lemma rbn9_cp_call : forall (W : world SEGS) (m1 m2 memc : word -> option byte) d x n d' n' A,
  (forall j, 0 <= j < n -> aview SEGS (w_H W) m1 (d + j) = aview SEGS (w_H W) memc (x + j)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d' <= a < d' + n') -> ~ (A - ESTACK <= a < A) ->
     aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (d + n <= d' \/ d' + n' <= d) -> (forall j, 0 <= j < n -> ~ (A - ESTACK <= d + j < A)) ->
  0 <= d -> d + n <= 2 ^ 64 ->
  forall j, 0 <= j < n -> aview SEGS (w_H W) m2 (d + j) = aview SEGS (w_H W) memc (x + j).
Proof.
intros W m1 m2 memc d x n d' n' A H HE Hdd Hw Hd Hdn j Hj.
rewrite (HE (d + j) ltac:(lia) ltac:(lia) (Hw j Hj)). apply H, Hj.
Qed.
Lemma rbn9_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_ra_frame : forall W1 (m : word -> option byte) F sh lo hi,
  rbn_shadow_at W1 m (shadow_addr F) sh -> F mod 8 = 0 -> 0 <= lo -> lo <= hi -> hi <= Z.of_nat (length sh) ->
  (forall j, lo <= j < hi -> nth (Z.to_nat j) sh 0 = 0) ->
  range_addressable (aview SEGS (w_H W1) m) SHADOW_OFF (F + 8 * lo) (8 * (hi - lo)).
Proof.
intros W1 m F sh lo hi Hsh HF8 Hlo Hlh Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr F + (x - F) / 8).
{ unfold shadow_of_addr, shadow_addr.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  assert (Q : x / 8 = (x - F) / 8 + F / 8).
  { replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. reflexivity. }
  lia. }
rewrite Ex. assert (Hj : lo <= (x - F) / 8 < hi).
{ split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite (Hsh ((x - F) / 8) ltac:(lia)). rewrite (Hz _ Hj). reflexivity.
Qed.
Lemma rbn9_frame_hull : forall W1 (m : word -> option byte) F sh x n,
  rbn_shadow_at W1 m (shadow_addr F) sh -> length sh = 64%nat -> F mod 8 = 0 -> 0 <= F ->
  F + 64 <= x -> x + n + 64 <= F + 512 -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W1) m) x n.
Proof.
intros W1 m F sh x n Hsh Hl HF8 HF0 Hx Hxn Hn s Hs.
unfold shadow_addr in Hs.
pose proof (Z.div_mod F 8 ltac:(lia)) as D0.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M4.
assert (Hj : 0 <= s - shadow_addr F < Z.of_nat (length sh)) by (rewrite Hl; unfold shadow_addr, SHADOW_OFF in *; lia).
replace s with (shadow_addr F + (s - shadow_addr F)) by lia. rewrite (Hsh _ Hj). discriminate.
Qed.
Lemma rbn9_stack_ra : forall ly S (W : world SEGS) m md a len,
  AR SEGS B ly S W m md -> ly_stk_lo ly <= a -> a + len + 8 <= ly_stk_hi ly -> 0 <= len ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len.
Proof.
intros ly S W m md a len HAR H1 H2 H3 x Hx.
pose proof (al_zshadow _ _ LAWS ly S W m md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  (or_introl eq_refl)) as HZ.
unfold zero_shadow in HZ. cbn [fst snd] in HZ.
destruct (zshadow_range_facts B ly S (aview SEGS (w_H W) m)
  (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (proj1 HAR) (or_introl eq_refl))
  as (Hal8 & _ & _ & _ & _).
cbn [fst snd] in Hal8.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as Dlo. rewrite Hal8, Z.add_0_r in Dlo.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Dh.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Mh.
specialize (HZ (x / 8 - ly_stk_lo ly / 8) ltac:(lia)).
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr in HZ |- *.
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (x / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + x / 8) in HZ by lia.
exact HZ.
Qed.
Lemma rbn9_stack_hull : forall ly S (W : world SEGS) m md a n,
  AR SEGS B ly S W m md -> ly_stk_lo ly + 64 <= a -> a + n + 72 <= ly_stk_hi ly -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) m) a n.
Proof.
intros ly S W m md a n HAR H1 H2 H3 s Hs.
pose proof (al_zshadow _ _ LAWS ly S W m md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  (or_introl eq_refl)) as HZ.
unfold zero_shadow in HZ. cbn [fst snd] in HZ.
destruct (zshadow_range_facts B ly S (aview SEGS (w_H W) m)
  (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (proj1 HAR) (or_introl eq_refl))
  as (Hal8 & _ & _ & _ & _).
cbn [fst snd] in Hal8. unfold shadow_addr in Hs.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)) as Dlo. rewrite Hal8, Z.add_0_r in Dlo.
pose proof (Z.div_mod (ly_stk_hi ly) 8 ltac:(lia)) as Dhi. pose proof (Z.mod_pos_bound (ly_stk_hi ly) 8 ltac:(lia)) as Mhi.
pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Dh. pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as Mh.
pose proof (Z.div_mod a 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as M4.
specialize (HZ (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly)) ltac:(unfold shadow_of_addr, SHADOW_OFF in *; set (q1 := a / 8) in *; set (r1 := a mod 8) in *;
  set (q2 := (a + n - 1) / 8) in *; set (r2 := (a + n - 1) mod 8) in *; set (q3 := (2147450880 + q1) / 8) in *; set (r3 := (2147450880 + q1) mod 8) in *;
  set (q4 := (2147450880 + q2) / 8) in *; set (r4 := (2147450880 + q2) mod 8) in *; set (ql := ly_stk_lo ly / 8) in *; set (qh := ly_stk_hi ly / 8) in *; set (rh := ly_stk_hi ly mod 8) in *; set (qd := (ly_stk_hi ly - ly_stk_lo ly) / 8) in *; set (rd := (ly_stk_hi ly - ly_stk_lo ly) mod 8) in *; clearbody q1 r1 q2 r2 q3 r3 q4 r4 ql qh rh qd rd; lia)).
replace (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) with s in HZ by lia.
rewrite HZ. discriminate.
Qed.
Lemma rbn9_faJ : forall X own lyc' Sc' W' m' md' k', rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own lyc' Sc' W' m' md' k' ->
  forall c p, frame_addr lyc' c p = frame_addr (ri_lyc X) c p.
Proof.
intros X own lyc' Sc' W' m' md' k' HX HJ c p.
destruct HX as ((_ & L0 & _) & _). destruct HJ as (_ & L1 & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn9_stk : forall X own lyc' Sc' W' m' md' k', rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own lyc' Sc' W' m' md' k' ->
  ly_stk_lo lyc' + 8816 <= rbn_SP X /\ rbn_SP X + 16 <= ly_stk_hi lyc'.
Proof.
intros X own lyc' Sc' W' m' md' k' HX HJ.
destruct HX as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & _ & _ & Hslo & Hshi & _) & _).
destruct HJ as (_ & L1 & _). destruct L1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
unfold rbn_SP. rewrite Elo, Ehi. lia.
Qed.
Lemma rbn9_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X mod 16 = 0 /\ ri_sp0 X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity|]. split; [exact Hal | exact Hsp0al].
Qed.
Lemma rbn9_F_facts : forall X pos lyc' Sc' W' m md k', rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc' Sc' W' m md k' ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\ off_img (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W') m a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W') m (rbn_SH X pos + i)).
Proof.
intros X pos lyc' Sc' W' m md k' HX HJm.
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJm 3 pos) as FA.
pose proof HJm as (HAR1 & _ & _ & _ & _ & Hfrs & _).
assert (Hin3 : In (3, pos) (frames Sc')) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & Hspr).
pose proof (frm_off_imgP B _ _ _ _ _ 3 pos HAR1 Hin3) as Hoi.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|]. split; [exact Hoi|].
split.
- intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha.
- intros i Hi. exact (proj1 (Hspr i ltac:(change (512 / 8) with 64; lia))).
Qed.
Lemma rbn9_tsb_pre : forall lyc Sc (W W2 : world SEGS) m m' m2 md sp (E : Z -> Prop),
  AR SEGS B lyc Sc W m md -> rbn9_kept W m m' (fun _ => False) ->
  tsb_ch_kept B lyc Sc W m' W2 m2 sp E -> tsb_ch_kept B lyc Sc W m W2 m2 sp E.
Proof.
intros lyc Sc W W2 m m' m2 md sp E HAR [K P] (T1 & T2 & T3 & T4 & T5 & T6).
pose proof asan_consts as (C1 & _).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw He. rewrite (T1 a Ha Hw He). apply K; [exact Ha | intros []].
- intros b mm i Hb Hi He. rewrite (T2 b mm i Hb Hi He).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hb) as (_ & Hb4 & Hbc & _).
  apply K; [lia | intros []].
- intros a Hi Ho He. rewrite (T3 a Hi Ho He). pose proof (pa_segs_low a Hi). apply K; [unfold kLowMemEnd in *; lia | intros []].
- intros cid pos a Hcp Ha He. rewrite (T4 cid pos a Hcp Ha He).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hcp) as (Hc4 & Hcc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  apply K; [|intros []].
  destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha;
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia));
  assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia);
  assert (frame_addr lyc cid pos / 8 <= frame_addr lyc cid pos) by (apply Z.div_le_upper_bound; lia);
  unfold SHADOW_OFF in *; lia.
- intros a Ha Hw Hp. exact (T5 a Ha Hw (P a Ha Hp)).
- exact T6.
Qed.
Lemma rbn9_tk_val : forall lyc Sc (W W2 : world SEGS) m m2 sp (E : Z -> Prop) a n v,
  tsb_ch_kept B lyc Sc W m W2 m2 sp E ->
  (forall i, 0 <= i < Z.of_nat n -> ~ (sp - TSB_CH_STK <= a + i < sp) /\ ~ E (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W2) m2) a n v.
Proof.
intros lyc Sc W W2 m m2 sp E a n v (T1 & _) Hn H0 H1 Hv.
apply (val_mem_kept SEGS (w_H W) (w_H W2) m m2 a n v); [|exact Hv].
intros i Hi. destruct (Hn i Hi) as [Hw He]. apply T1; [lia | exact Hw | exact He].
Qed.
Lemma rbn9_tk_garr : forall lyc Sc (W W2 : world SEGS) m m2 sp (E : Z -> Prop) a l,
  tsb_ch_kept B lyc Sc W m W2 m2 sp E ->
  (forall i, 0 <= i < Z.of_nat (length l) -> ~ (sp - TSB_CH_STK <= a + i < sp) /\ ~ E (a + i)) -> 0 <= a ->
  a + Z.of_nat (length l) <= 2 ^ 64 ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W2) m2) a l.
Proof.
intros lyc Sc W W2 m m2 sp E a l HT Hn H0 H1 Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (rbn9_tk_val lyc Sc W W2 m m2 sp E _ 1 _ HT); [| lia | lia | exact Hv].
intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hn. lia.
Qed.
Lemma rbn9_sh_kept : forall (W1 : world SEGS) (m m' : word -> option byte) q l (Wr : Z -> Prop),
  rbn_shadow_at W1 m q l -> rbn9_kept W1 m m' Wr -> 0 <= q -> q + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length l) -> ~ Wr (q + j)) -> rbn_shadow_at W1 m' q l.
Proof. intros W1 m m' q l Wr Hs [K _] H0 H1 Hn j Hj. rewrite (K (q + j) ltac:(lia) (Hn j Hj)). exact (Hs j Hj). Qed.
Lemma rbn9_ro_kept : forall (W W' : world SEGS) (m m' : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  (forall a, in_img SEGS a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' Hro HK a Hr Ho He.
assert (Hia : in_img SEGS a)
  by (destruct Hr as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
rewrite (HK a Hia). exact (Hro a Hr Ho He).
Qed.
Lemma rbn9a_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc,
  st_ok_pi SEGS VAL (ERB9d regs) (mkSS (AF_both3_reac_box_name + RBN_P9) sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_P9))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9d.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I|]. split; exact I.
Qed.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis L7F : rbn_L7_fits B.
Lemma rbn9_head : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 Q,
  rbn_cx B X -> rbn_st9 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  (forall lyc2 Sc2 W2 regs3 mem3 mdc3,
     ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
       ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem3 mdc3 (ri_k X) ->
     frames Sc2 = frames Sc1 -> ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 ->
     arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem3) ->
     rbn9_same regs1 regs3 [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27] ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (rbn_A X + 104) 8 (Z.of_nat (length (rbm_D9 X)) + 5) ->
     val_mem SEGS (mrestrict (w_H W2) mem3) (rbn_A X + 112) 4 0 ->
     garr8 SEGS (mrestrict (w_H W2) mem3) (rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X))) rbn_lit7 ->
     tsb_ch_kept B lyc1 Sc1 W1 memc1 W2 mem3 (rbn_A X)
       (fun a => rbn_A X + 88 + 16 <= a < rbn_A X + 88 + 28 \/
          rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X)) <= a <
            rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X)) + Z.of_nat (length rbn_lit7)) ->
     SRr SEGS W2 (rbn_cfg X RBN_L7X regs3 mem3 mdc3) Q) ->
  SRr SEGS W1 (rbn_cfg X RBN_P9 regs1 memc1 mdc1) Q.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 Q HX Hst K.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity. assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct Himg as (t1 & t2 & t3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Lg & Lra & Li) & _ & _ & _ & _ & _ & _ & _ & Hro30).
destruct (rbn9_glob6 _ Hro30) as (P8 & Plo & Phi).
destruct Hst as (HM & (H2 & H3 & H4 & H8 & H9 & H19 & H22 & H23) & H18 & H25 & H26 & H27 & HC & G64 & G128 & G192 & HA).
pose proof HM as (HJ & Hfrs & Hperm & Hro1 & HK1 & Hfr1 & Hfl1 & Hsh1).
pose proof HJ as HJ1. destruct (rbn9_stk X _ _ _ _ _ _ _ HX HJ) as (HSlo & HShi).
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJ) as FA.
destruct (rbn9_D9_ovf X HA) as (Hov47 & Hfirst). destruct (rbn9_D9_len X HA) as (_ & HD9).
unfold rbn_argc, rbn_rw, rbn_rn, rbn_rt, rbn_rd in HC. cbn [rbn_cells app] in HC.
destruct HC as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C184 & C192 & C200 & C208 & C152 & C160 & C168 & C176 &
  C120 & C128 & C136 & C144 & C88 & C96 & C104 & C112 & _).
rewrite Hov47 in C112. rewrite Hfirst in C104, G192.
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 (ri_k X) HX HJ) as (HF4096 & HFceil & HF32 & HFapp & HFoi & _ & _).
set (n0 := Z.of_nat (length (rbm_D9 X))) in *.
set (A := rbn_A X) in *. set (F := rbn_F X pos) in *. set (P := VAL (A_OBJ 30)) in *.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (ESH : rbn_SH X pos = shadow_addr F) by reflexivity.
assert (HSHr : SHADOW_OFF <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighMemBeg).
{ rewrite ESH. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia). lia. }
unfold SHADOW_OFF in HSHr. pose proof (rbn9a_entry (ri_fq X) W1 regs1 memc1) as HS.
set (E := ERB9d regs1) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9d; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB9d; apply ew_Eimg_Ereg_nat; exact Hn).
clearbody E. pose proof (@SRr_run_to_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNTOP.
unfold rbn_cfg, cfg_at. change (w64 (BASE + AF_both3_reac_box_name + RBN_P9)) with (Z_to_bv 64 (BASE + AF_both3_reac_box_name + RBN_P9)).
rewrite <- Z.add_assoc.
paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN_L7).
{ apply awr_ok_nil. }
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) _, HG : mem_grows _ _ |- _ =>
  pose proof (rbn9_kept_of_frame _ _ _ _ _ (fun _ => False) HFr HG ltac:(r9wr)) as FR; clear HFr HG end.
try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end).
assert (SAME0 : rbn9_same regs1 (ms_regs ms) [1; 2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27]) by r9same EE.
pmkst HS.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
rewrite (img_env_atomP E 271 HEI ltac:(unfold A_TEXT, A_LIM; lia)) in Q21.
change 271%nat with (A_OBJ 30) in Q21. fold P in Q21.
pose proof HJ as HJc.
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 (ms_mem ms) _ (ri_k X) HX HJc) as (_ & _ & _ & _ & _ & HFpr2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (R2 : getr (ms_regs ms) 2 = w64 A) by exact (eq_trans (SAME0 2 ltac:(cbn; tauto)) H2).
assert (HspH : spZ (ms_regs ms) = A) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (FRI : forall a, in_img SEGS a -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
{ intros a Hi. pose proof (pa_segs_low a Hi). apply (proj1 FR); [unfold kLowMemEnd in *; lia | intros []]. }
assert (Hsh2 : rbn_shadow_at W1 (ms_mem ms) (shadow_addr F) (rbn_sh true true true true)).
{ rewrite <- ESH. apply (rbn9_sh_kept W1 memc1 (ms_mem ms) _ _ (fun _ => False) Hsh1 FR);
  [lia | change (length (rbn_sh true true true true)) with 64%nat; lia | tauto]. }
assert (HU : ro_unowned B P 6).
{ apply (tfib_ro_unowned_at B _ _ DRO). unfold tfib_ro_ranges. apply in_or_app. left. exact Hro30. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdx) _ =>
  apply (rbn9_pc (ri_fq X) W1 (ms_regs ms) (ms_mem ms) mdx Q (BASE + AF_both3_reac_box_name + RBN_L7));
  [unfold AF_both3_reac_box_name, RBN_L7; lia|];
  pose proof (L7F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 (ms_mem ms) mdx (ri_k X) (ms_regs ms) (F + 192) n0 0 ltac:(lia)) as HL7 end.
unfold rbn_L7_run in HL7. rewrite HspH in HL7.
eapply SRr_bind; [apply HL7; clear HL7|].
- unfold rbn_lcx. rewrite HspH. split; [exact HJc|]. split.
  { apply (rbn9_ro_kept W1 W1 memc1 (ms_mem ms) Hro1 FRI). }
  split; [exact (eq_trans (SAME0 3 ltac:(cbn; tauto)) H3)|]. split; [exact (eq_trans (SAME0 4 ltac:(cbn; tauto)) H4)|].
  split; [rewrite R2; exact (eq_trans (SAME0 9 ltac:(cbn; tauto)) H9)|].
  split; [exact (eq_trans (SAME0 22 ltac:(cbn; tauto)) H22)|].
  split; [pose proof (Z.div_mod A 32 ltac:(lia)); lia|]. split; lia.
- unfold rbn_lrec.
  split; [lia|]. split; [pose proof (Z.div_mod A 32 ltac:(lia)); lia|]. split; [lia|].
  split; [unfold amem_range; right; lia|]. split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; right; lia|].
  split; [left; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply (rbn9_kept_val W1 memc1 (ms_mem ms) (fun _ => False) _ 8 _ FR); [tauto | lia | lia | exact C88]|].
  split; [replace (A + 88 + 8) with (A + 96) by lia;
    apply (rbn9_kept_val W1 memc1 (ms_mem ms) (fun _ => False) _ 8 _ FR); [tauto | lia | lia | exact C96]|].
  split; [replace (A + 88 + 16) with (A + 104) by lia;
    apply (rbn9_kept_val W1 memc1 (ms_mem ms) (fun _ => False) _ 8 _ FR); [tauto | lia | lia | exact C104]|].
  split; [replace (A + 88 + 24) with (A + 112) by lia;
    apply (rbn9_kept_val W1 memc1 (ms_mem ms) (fun _ => False) _ 4 _ FR); [tauto | lia | lia | exact C112]|].
  split; [apply (rbn9_stack_ra lyc1 Sc1 W1 (ms_mem ms) _ _ _ (proj1 HJc)); lia|].
  split; [apply (rbn9_stack_hull lyc1 Sc1 W1 (ms_mem ms) _ _ _ (proj1 HJc)); lia|].
  intros a Ha. split; [left; lia | apply HJpres; lia].
- unfold rbn_lbuf.
  split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ HFapp); lia|].
  split; [unfold in_app, amem_range, kLowShadowBeg in *; lia|].
  split; [unfold off_img in *; lia|]. split; [right; lia|]. split; [left; lia|].
  split.
  { replace (F + 192) with (F + 8 * 24) by lia. replace 48 with (8 * (30 - 24)) by lia.
    apply (rbn9_ra_frame W1 (ms_mem ms) F (rbn_sh true true true true) 24 30 Hsh2 HF8); [lia | lia | cbn; lia |].
    intros j Hj. assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as Hjj by lia.
    repeat (destruct Hjj as [-> | Hjj]; [reflexivity|]). subst j. reflexivity. }
  split; [apply (rbn9_frame_hull W1 (ms_mem ms) F (rbn_sh true true true true) _ _ Hsh2 eq_refl HF8); lia|].
  intros a Ha. split; [|exact (proj1 (HFpr2 a ltac:(lia)))].
  right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with F.
  change (fs_frame_bytes 3) with 512. lia.
- unfold rbn_lsrc, rbn_lit7. cbn [length app]. change (Z.of_nat 6) with 6.
  split.
  { apply (rbn9_garr8_copy (w_H (ri_W X)) (w_H W1) (ri_memc X) (ms_mem ms) P P); [|exact Lg].
    intros j Hj. cbn [length app] in Hj. change (Z.of_nat 6) with 6 in Hj.
    rewrite (FRI (P + j) ltac:(apply Li; simpl; lia)).
    destruct (HU (P + j) ltac:(lia)) as [U1 U2].
    exact (proj1 (proj2 (proj2 HK1)) (P + j) ltac:(apply Li; simpl; lia) U1 U2). }
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Plo, Phi.
  split; [lia|]. split; [lia|]. split; [lia|].
  destruct (ro_read_ok_glob SEGS B tfib_globs lyc1 Sc1 W1 (ms_mem ms) _ P 6 P 6 GM Hro30 HV
    (proj1 HJc) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold YImgTop.IMG_LO; lia) ltac:(unfold YImgTop.IMG_TOP; lia)) as [R _].
  exact R.
- exact P8.
- unfold rbn_lsep. unfold off_img in HFoi. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Plo, Phi, HFoi.
  split; [|split; [left; lia | right; lia]].
  destruct HFoi as [Hlo | Hhi]; [right; lia | left; lia].
- lia.
- left; reflexivity.
- rewrite Q20. reflexivity.
- rewrite Q21. reflexivity.
- rewrite Q24. reflexivity.
- intros W' c' _ (lyc2 & Sc2 & regs3 & mem3 & md3 & -> & HJ3 & Hfr3 & Hbl3 & Hro3 & HKR & M104 & M112 & G7 & TK).
  apply (K lyc2 Sc2 W' regs3 mem3 md3 HJ3 Hfr3 Hbl3 Hro3).
  + intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [rewrite HKR; [apply SAME0; cbn; tauto | lia | unfold rbn_cl5, rbn_clc; cbn; lia] |]). destruct Hr.
  + replace (A + 104) with (A + 88 + 16) by lia. exact M104.
  + replace (A + 112) with (A + 88 + 24) by lia. exact M112.
  + exact G7.
  + rewrite HspH in TK. exact (rbn9_tsb_pre lyc1 Sc1 W1 W' memc1 (ms_mem ms) mem3 mdc1 A _ (proj1 HJ1) FR TK).
Qed.
Lemma rbn9_not_val : forall x c, 0 <= x < 2 ^ 64 -> c mod 2 ^ 64 = 2 ^ 64 - 1 ->
  bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 c)) = 2 ^ 64 - 1 - x.
Proof.
intros x c Hx Hc. rewrite YP0m.zalu64_sound. unfold YP0m.zalu64. cbn [YP0m.zalu_raw].
rewrite (YP0m.zcanon_small x) by lia.
replace (YP0m.zcanon c) with (2 ^ 64 - 1) by (unfold YP0m.zcanon, YP0m.M64; rewrite Hc; reflexivity).
rewrite YI08.lxor_allones by lia. rewrite YP0m.zcanon_small by lia. apply unsigned_lit_small. lia.
Qed.
Definition rbn9b_r0 (ov : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 212 0 0
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
     YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 104 (CVal 8 (SOff 35 0));
     YP09.mkChunk 112 (CVal 4 (SLit 0)); YP09.mkChunk 136 (CVal 8 (SOff 36 0));
     YP09.mkChunk 144 (CVal 4 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SOff 37 0));
     YP09.mkChunk 176 (CVal 4 (SLit ov)); YP09.mkChunk 208 (CVal 4 (SLit 0))].
Definition rbn9b_regions (ov : Z) : smem := [rbn9b_r0 ov; YP09.mkRegion (Some 38%nat) 0 1 0 1 []].
Definition rbn9b_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (38%nat, mkAF 4096 (2 ^ 47 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 26 0) (SOff 35 0), SOff 38 0)].
Definition ss_rbn9b (ov : Z) : sstate :=
  mkSS (AF_both3_reac_box_name + RBN_L7X) sr_atoms (rbn9b_regions ov) None rbn9b_facts.
Definition rbn9b_extra (tkl dl nml nD ltb lnb t : Z) : list word := map (Z_to_bv 64) [tkl; dl; nml; nD; ltb; lnb; t].
Definition ERB9b (regs : bvmap 5 word) (tkl dl nml nD ltb lnb t : Z) : env :=
  Eimg (Ereg regs (rbn9b_extra tkl dl nml nD ltb lnb t)).
Lemma regs_ok_ERB9b : forall regs tkl dl nml nD ltb lnb t, regs_ok (ERB9b regs tkl dl nml nD ltb lnb t) sr_atoms regs.
Proof.
intros. unfold ERB9b. apply (regs_ok_agree 32 (Ereg regs (rbn9b_extra tkl dl nml nD ltb lnb t))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9b_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc (A F nD tkl dl nml ltb lnb ov : Z),
  getr regs 9 = w64 A -> getr regs 26 = w64 (F + 192) ->
  A mod 32 = 0 -> 2 ^ 46 <= A -> A + 212 <= 2 ^ 47 -> F + 512 <= A ->
  4096 <= F -> F + 512 <= 2 ^ 47 - 1 -> 0 <= nD < 48 -> (ov = 0 \/ ov = 1) ->
  0 <= tkl < 2 ^ 64 -> 0 <= dl < 2 ^ 64 -> 0 <= nml < 2 ^ 64 -> 0 <= ltb < 2 ^ 64 -> 0 <= lnb < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 tkl -> val_mem SEGS (mrestrict (w_H W) memc) (A + 32) 8 dl ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 56) 8 nml -> val_mem SEGS (mrestrict (w_H W) memc) (A + 104) 8 nD ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 112) 4 0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 ltb ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 168) 8 lnb ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 176) 4 ov -> val_mem SEGS (mrestrict (w_H W) memc) (A + 208) 4 0 ->
  apresent (w_H W) memc (F + 192 + nD) ->
  st_ok_pi SEGS VAL (ERB9b regs tkl dl nml nD ltb lnb (F + 192 + nD)) (ss_rbn9b ov)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L7X))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc A F nD tkl dl nml ltb lnb ov H9 H26 HA32 HAlo HAhi HFA HF0 HF1 HnD Hov
  Rtkl Rdl Rnml Rltb Rlnb M24 M32 M56 M104 M112 M136 M144 M168 M176 M208 HPT.
rewrite restrict_mkst_fx.
set (E := ERB9b regs tkl dl nml nD ltb lnb (F + 192 + nD)).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rbn9b_extra tkl dl nml nD ltb lnb (F + 192 + nD))) m)
  by (intros m Hm; subst E; unfold ERB9b; apply Eimg_low; exact Hm).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (rbn9b_extra tkl dl nml nD ltb lnb (F + 192 + nD)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. cbn [Nat.add nth rbn9b_extra map] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 (F + 192)) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (CH : forall off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + off) 8 v -> YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) A (YP09.mkChunk off (CVal 8 e))).
{ intros off e v He Hv Hm. apply (chunk_ok_val SEGS E _ A off 8 e v He); [zside | zside | exact Hm]. }
unfold ss_rbn9b, rbn9b_regions, rbn9b_r0. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9b.
- destruct Hov as [-> | ->]; vm_compute; reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat A E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CH 24 _ tkl); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M24].
    * apply (CH 32 _ dl); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M32].
    * apply (CH 56 _ nml); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M56].
    * apply (CH 104 _ nD); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M104].
    * apply (chunk_ok_val SEGS E _ A 112 4 (SLit 0) 0); [reflexivity | lia | zside | exact M112].
    * apply (CH 136 _ ltb); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M136].
    * apply (chunk_ok_val SEGS E _ A 144 4 (SLit 0) 0); [reflexivity | lia | zside | exact M144].
    * apply (CH 168 _ lnb); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact M168].
    * apply (chunk_ok_val SEGS E _ A 176 4 (SLit ov) ov); [reflexivity | cbn; lia | zside | exact M176].
    * apply (chunk_ok_val SEGS E _ A 208 4 (SLit 0) 0); [reflexivity | lia | zside | exact M208].
  + rewrite (VB 38%nat (F + 192 + nD) E38) by lia. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (F + 192 + nD + o) with (F + 192 + nD) by lia. apply (apresent_writable SEGS). exact HPT.
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat A E9) by lia. rewrite (VB 38%nat (F + 192 + nD) E38) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
- unfold rbn9b_facts. split; [|split].
  + cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E9, E38, !unsigned_lit_small by lia.
    split; [split; [lia|]; split; [change (2 ^ 5) with 32; exact HA32 | lia]|].
    split; [split; [lia|]; split; [apply Z.mod_1_r | lia]|]. exact I.
  + exact I.
  + cbn [f_alias alias_ok sv_denot]. split; [|exact I].
    rewrite E26, E35, E38. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned. rewrite alu_add_small by (unfold YP0m.M64; lia). reflexivity.
Qed.
Definition rbn9_jc (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc k (regs : bvmap 5 word)
  (F nD : Z) (regs2 : bvmap 5 word) mem2 mdc2 : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k /\
  rbn9_same regs regs2 [1; 2; 3; 4; 8; 9; 18; 19; 23; 24; 25; 26; 27] /\
  rbn9_kept W memc mem2 (fun a => a = F + 192 + nD) /\
  val_mem SEGS (mrestrict (w_H W) mem2) (F + 192 + nD) 1 0.
Ltac r9hc :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
  cbn [branch_taken sv_denot ew ewset extK Nat.eqb] in Hc; unfold bv_ltu in Hc;
  repeat match goal with Ex : ew ?E ?n = Z_to_bv 64 _ |- _ => progress rewrite Ex in Hc end;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc; rewrite ?unsigned_lit_small in Hc by lia end.
Ltac r9no := lazymatch goal with Hc : _ = _ |- _ =>
  first [ apply Z.ltb_lt in Hc; lia | apply Z.ltb_ge in Hc; lia
        | apply negb_true_iff, Z.ltb_ge in Hc; lia | apply negb_false_iff, Z.ltb_lt in Hc; lia
        | rewrite rbn9_not_val in Hc by (lia || reflexivity); first [apply Z.ltb_lt in Hc; lia | apply negb_true_iff, Z.ltb_ge in Hc; lia]
        | vm_compute in Hc; discriminate Hc ] end.
Ltac r9awrb HWT :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 38%nat); [reflexivity | r9ewu |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; lazymatch type of HWT with awr_byte _ _ _ _ _ _ _ ?t => replace a with t by lia end; exact HWT |];
  apply awr_ok_nil.
Ltac r9go HS off :=
  pmkst HS;
  lazymatch goal with |- SRr _ ?W (mkCfg (mkst (fx := ?fq) (ms_regs ?msx) _ (ms_mem ?msx) _) ?mdx) ?Q =>
  apply (rbn9_pc fq W (ms_regs msx) (ms_mem msx) mdx Q (BASE + AF_both3_reac_box_name + off));
  [unfold AF_both3_reac_box_name, RBN9_TAIL, RBN9_ACC; lia|] end.
Ltac r9jc HS HJ KP EE :=
  split; [exact HJ|]; split; [r9same EE|]; split; [exact KP|];
  let HR1 := fresh "HR1" in let V := fresh "V" in
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
  pose proof (field_of_region _ _ _ _ _ _ _ _ _ 0 1 (SLit 0) 0 HR1 ltac:(r9ewu) ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as V;
  rewrite Z.add_0_r in V; exact V.
Ltac r9finR HS HJ KP K EE :=
  r9go HS RBN9_TAIL;
  apply K; [ r9jc HS HJ KP EE
           | let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R; unfold w64; apply bv_eq;
             rewrite !Z_to_bv_unsigned; reflexivity
           | ].
Lemma rbn9_checks : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A F nD tkl dl nml ltb lnb ovn : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> getr regs 26 = w64 (F + 192) ->
  A mod 32 = 0 -> 2 ^ 46 <= A -> A + 212 <= 2 ^ 47 -> F + 512 <= A ->
  4096 <= F -> F + 512 <= 2 ^ 47 - 1 -> 0 <= nD <= 47 -> (ovn = 0 \/ ovn = 1) ->
  0 <= tkl < 2 ^ 64 -> 0 <= dl < 2 ^ 64 -> 0 <= nml < 2 ^ 64 -> 0 <= ltb < 2 ^ 64 -> 0 <= lnb < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 24) 8 tkl -> val_mem SEGS (mrestrict (w_H W) memc) (A + 32) 8 dl ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 56) 8 nml -> val_mem SEGS (mrestrict (w_H W) memc) (A + 104) 8 nD ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 112) 4 0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 136) 8 ltb ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 144) 4 0 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 168) 8 lnb ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 176) 4 ovn -> val_mem SEGS (mrestrict (w_H W) memc) (A + 208) 4 0 ->
  apresent (w_H W) memc (F + 192 + nD) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (F + 192 + nD) ->
  (forall regs2 mem2 mdc2, rbn9_jc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs F nD regs2 mem2 mdc2 ->
     getr regs2 20 = w64 (-1) -> ~ (ovn = 0 /\ lnb < nml /\ nD < dl /\ ltb < tkl) ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN9_TAIL) regs2 mem2 mdc2) Q) ->
  (forall regs2 mem2 mdc2, rbn9_jc fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs F nD regs2 mem2 mdc2 ->
     getr regs2 12 = w64 lnb -> getr regs2 21 = w64 nD -> getr regs2 22 = w64 ltb ->
     ovn = 0 /\ lnb < nml /\ nD < dl /\ ltb < tkl ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN9_ACC) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L7X) regs memc mdc) Q.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A F nD tkl dl nml ltb lnb ovn Q HJ
  H9 H26 HA32 HAlo HAhi HFA HF0 HF1 HnD Hovn Rtkl Rdl Rnml Rltb Rlnb
  M24 M32 M56 M104 M112 M136 M144 M168 M176 M208 HPT HWT KREF KACC.
pose proof (rbn9b_entry fq W regs memc A F nD tkl dl nml ltb lnb ovn H9 H26 HA32 HAlo HAhi HFA HF0 HF1 ltac:(lia) Hovn
  Rtkl Rdl Rnml Rltb Rlnb M24 M32 M56 M104 M112 M136 M144 M168 M176 M208 HPT) as HS.
set (E := ERB9b regs tkl dl nml nD ltb lnb (F + 192 + nD)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9b; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9b; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (rbn9b_extra tkl dl nml nD ltb lnb (F + 192 + nD)) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9b; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. cbn [Nat.add nth rbn9b_extra map] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 (F + 192)) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
clearbody E.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (L := lib_both3_0_listing) (PI := PI)) as BR.
pose proof (rbn9_kept_refl W memc (fun a => a = F + 192 + nD)) as KP.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_box_name + RBN_L7X)) with (Z_to_bv 64 (BASE + AF_both3_reac_box_name + RBN_L7X)).
rewrite <- Z.add_assoc.
destruct Hovn as [-> | ->].
- paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc; [r9no|]. clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc; [r9no|]. clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc.
  + apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
    r9step KP. r9finR HS HJ KP KREF EE. lia.
  + apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc1.
    paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
    r9step KP.
    psrr_branch_pi RUNP BR HS; r9hc.
    * apply negb_true_iff, Z.ltb_ge in Hc.
      paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
      r9step KP. r9finR HS HJ KP KREF EE. lia.
    * apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc2.
      paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
      r9step KP.
      psrr_branch_pi RUNP BR HS; r9hc.
      -- apply negb_true_iff, Z.ltb_ge in Hc.
         paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
         r9step KP. r9finR HS HJ KP KREF EE. lia.
      -- apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hc3.
         paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_ACC). { r9awrb HWT. }
         r9step KP. r9go HS RBN9_ACC.
         apply KACC.
         ++ r9jc HS HJ KP EE.
         ++ let R := fresh "R" in prreg HS (12%bv : bv 5) R; rewrite R; rewrite ?E37; reflexivity.
         ++ let R := fresh "R" in prreg HS (21%bv : bv 5) R; rewrite R; rewrite ?E35; reflexivity.
         ++ let R := fresh "R" in prreg HS (22%bv : bv 5) R; rewrite R; rewrite ?E36; reflexivity.
         ++ lia.
- paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc; [r9no|]. clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP.
  psrr_branch_pi RUNP BR HS; r9hc; [r9no|]. clear Hc.
  paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN9_TAIL). { r9awrb HWT. }
  r9step KP. r9finR HS HJ KP KREF EE. lia.
Qed.
Definition rbn9c_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 24 0 0
      [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
       YP09.mkChunk 16 (CVal 8 (SOff 34 0))] ].
Definition ss_rbn9c : sstate := mkSS (AF_both3_reac_box_name + RBN9_ACC) sr_atoms rbn9c_regions None (mkFacts [] [] []).
Definition ERB9c (regs : bvmap 5 word) (d3 d1 d2 : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [d3; d1; d2])).
Lemma regs_ok_ERB9c : forall regs d3 d1 d2, regs_ok (ERB9c regs d3 d1 d2) sr_atoms regs.
Proof.
intros. unfold ERB9c. apply (regs_ok_agree 32 (Ereg regs (map (Z_to_bv 64) [d3; d1; d2]))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn9c_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc (A d1 d2 d3 : Z),
  getr regs 9 = w64 A -> 0 <= A -> A + 24 <= 2 ^ 64 ->
  0 <= d1 < 2 ^ 64 -> 0 <= d2 < 2 ^ 64 -> 0 <= d3 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 0) 8 d3 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 d2 ->
  st_ok_pi SEGS VAL (ERB9c regs d3 d1 d2) ss_rbn9c
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN9_ACC))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc A d1 d2 d3 H9 HA0 HA1 R1 R2 R3 M0 M8 M16.
rewrite restrict_mkst_fx.
set (E := ERB9c regs d3 d1 d2).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9c; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [d3; d1; d2]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9c; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth map] in E32, E33, E34. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
unfold ss_rbn9c, rbn9c_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB9c.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ A 0 8 _ d3); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M0].
  + apply (chunk_ok_val SEGS E _ A 8 8 _ d1); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
  + apply (chunk_ok_val SEGS E _ A 16 8 _ d2); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M16].
- cbn [pairwise_disjoint]. split; exact I.
- split; [exact I|]. split; exact I.
Qed.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Ltac r9norm H :=
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val sv_denot ew ewset havoc extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in H;
  repeat (match goal with Ex : ew ?E ?n = Z_to_bv 64 _ |- _ => progress rewrite Ex in H end);
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H; rewrite ?unsigned_lit_small in H by lia.
Ltac r9rk Hfrc XF :=
  cbn [ms_mem restrict mkst]; apply Forall_cons; [|apply Forall_nil];
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; r9norm Ha;
    apply (mbyte_of_aview SEGS); apply Hfrc; [lia | | lia];
    let Hd := fresh "Hd" in intros Hd; apply (proj2 (XF a ltac:(lia))); lia
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; r9norm Ha; exfalso; lia ].
Ltac r9after HS HP2 Hfrc XF kk :=
  lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
  lazymatch type of Hfrc with forall a, _ -> _ -> _ -> aview _ (w_H ?Wx) ?mem2 a = _ =>
  let HS2 := fresh "HS2" in
  jafter_call_keep_pi HS kk regs2 (mrestrict (w_H Wx) mem2) HP2 [0]%nat HS2;
  let HRK := fresh "HRK" in
  match type of HS2 with ?tq -> _ => assert (HRK : tq) by (r9rk Hfrc XF) end;
  specialize (HS2 HRK); clear HRK;
  clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
  let HEI2 := fresh "HEI" in
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?k0 ?ws) _ _ =>
    lazymatch goal with HEIo : img_env _ _ Eo |- _ =>
      assert (HEI2 : img_env VAL A_LIM (havoc Eo k0 ws)) by (apply img_env_havoc; [exact HEIo | cbv; lia]) end end
  end end.
Ltac r9run3 KP FR :=
  lazymatch goal with HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ =>
  pose proof (rbn9_kept_of_frame _ _ _ _ _ (fun _ => False) HFr HG ltac:(r9wr)) as FR;
  clear HFr HG; try (lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end);
  let K2 := fresh "KP" in
  pose proof (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ KP FR) ltac:(intros a [Ha | []]; exact Ha)) as K2;
  clear KP; rename K2 into KP end.
Ltac r9ro := lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Lemma rbn9_copies : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A F d1 d2 d3 lnb ltb nD : Z) Q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 2 = w64 A -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 9 = w64 A -> getr regs 12 = w64 lnb -> getr regs 21 = w64 nD -> getr regs 22 = w64 ltb ->
  getr regs 25 = w64 (F + 128) -> getr regs 26 = w64 (F + 192) -> getr regs 27 = w64 (F + 64) ->
  0 <= A -> A + 24 <= 2 ^ 64 -> 0 <= F -> F + 512 <= 2 ^ 63 ->
  0 <= d1 < 2 ^ 64 -> 0 <= d2 < 2 ^ 64 -> 0 <= d3 < 2 ^ 64 -> 0 <= lnb < 64 -> 0 <= ltb < 64 -> 0 <= nD < 64 ->
  (A - sp0) mod 16 = 0 -> A <= sp0 -> ESTACK - (A - sp0) <= STK -> kHighMemBeg <= A - ESTACK ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 0) 8 d3 -> val_mem SEGS (mrestrict (w_H W) memc) (A + 8) 8 d1 ->
  val_mem SEGS (mrestrict (w_H W) memc) (A + 16) 8 d2 ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d1 (F + 64) (lnb + 1) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d2 (F + 128) (ltb + 1) ->
  rbn9_cpy STK sp0 FP ly S own lyc Sc W memc A d3 (F + 192) (nD + 1) ->
  (d1 + lnb + 1 <= d2 \/ d2 + ltb + 1 <= d1) -> (d1 + lnb + 1 <= d3 \/ d3 + nD + 1 <= d1) ->
  (d2 + ltb + 1 <= d3 \/ d3 + nD + 1 <= d2) ->
  (forall a, (d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nD + 1) ->
     ~ (F <= a < F + 512) /\ ~ (A <= a < A + 24)) ->
  (forall regs2 mem2 mdc2,
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 mdc2 k ->
     rbn9_same regs regs2 [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> getr regs2 20 = w64 0 ->
     rbn9_kept W memc mem2
       (fun a => d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nD + 1 \/ A - ESTACK <= a < A) ->
     (forall i, 0 <= i < lnb + 1 -> aview SEGS (w_H W) mem2 (d1 + i) = aview SEGS (w_H W) memc (F + 64 + i)) ->
     (forall i, 0 <= i < ltb + 1 -> aview SEGS (w_H W) mem2 (d2 + i) = aview SEGS (w_H W) memc (F + 128 + i)) ->
     (forall i, 0 <= i < nD + 1 -> aview SEGS (w_H W) mem2 (d3 + i) = aview SEGS (w_H W) memc (F + 192 + i)) ->
     SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN9_TAIL) regs2 mem2 mdc2) Q) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN9_ACC) regs memc mdc) Q.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A F d1 d2 d3 lnb ltb nD Q HJ
  H2 H3 H4 H9 H12 H21 H22 H25 H26 H27 HA0 HA1 HF0 HF1 R1 R2 R3 Rl1 Rl2 Rl3 Ho16 Hosp Hostk HAhi
  M0 M8 M16 C1 C2 C3 D12 D13 D23 XF K.
pose proof (rbn9c_entry fq W regs memc A d1 d2 d3 H9 HA0 HA1 R1 R2 R3 M0 M8 M16) as HS.
set (E := ERB9c regs d3 d1 d2) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB9c; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB9c; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) [d3; d1; d2]) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold ERB9c; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth map] in E32, E33, E34. clear EX.
assert (E2 : ew E 2 = Z_to_bv 64 A) by (rewrite (EE 2%nat 2%bv eq_refl); exact H2).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E12 : ew E 12 = Z_to_bv 64 lnb) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E21 : ew E 21 = Z_to_bv 64 nD) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 ltb) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E25 : ew E 25 = Z_to_bv 64 (F + 128)) by (rewrite (EE 25%nat 25%bv eq_refl); exact H25).
assert (E26 : ew E 26 = Z_to_bv 64 (F + 192)) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = Z_to_bv 64 (F + 64)) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
clearbody E.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hes : ESTACK = 4096) by reflexivity.
set (Wr3 := fun a => d1 <= a < d1 + lnb + 1 \/ d2 <= a < d2 + ltb + 1 \/ d3 <= a < d3 + nD + 1 \/ A - ESTACK <= a < A).
pose proof C1 as (_ & Hd10 & Hd1n & Hd1w & Hd1am & _ & _ & _ & _ & Hs1w & _).
pose proof C2 as (_ & Hd20 & Hd2n & Hd2w & Hd2am & _ & _ & _ & _ & Hs2w & _).
pose proof C3 as (_ & Hd30 & Hd3n & Hd3w & Hd3am & _ & _ & _ & _ & Hs3w & _).
assert (HWb : forall a, Wr3 a -> ~ (kLowMemEnd <= a < kHighMemBeg)).
{ intros a Ha Hb. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - exact (rbn9_amem_out a d1 (lnb + 1) Hd1am Hd10 Hb ltac:(lia)).
  - exact (rbn9_amem_out a d2 (ltb + 1) Hd2am Hd20 Hb ltac:(lia)).
  - exact (rbn9_amem_out a d3 (nD + 1) Hd3am Hd30 Hb ltac:(lia)).
  - unfold kHighMemBeg in *. lia. }
assert (HWF : forall a, F <= a < F + 512 -> ~ (A - ESTACK <= a < A) -> ~ Wr3 a).
{ intros a Ha Hw Hc. destruct Hc as [Hc | [Hc | [Hc | Hc]]];
  [apply (proj1 (XF a ltac:(tauto))) | apply (proj1 (XF a ltac:(tauto))) | apply (proj1 (XF a ltac:(tauto))) | apply Hw];
  first [exact Ha | exact Hc]. }
assert (HWx1 : forall a, F + 64 <= a < F + 64 + (lnb + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs1w a Ha))]).
assert (HWx2 : forall a, F + 128 <= a < F + 128 + (ltb + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs2w a Ha))]).
assert (HWx3 : forall a, F + 192 <= a < F + 192 + (nD + 1) -> ~ Wr3 a)
  by (intros a Ha; apply HWF; [lia | exact (proj2 (Hs3w a Ha))]).
pose proof (rbn9_kept_refl W memc Wr3) as KP.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_box_name + RBN9_ACC)) with (Z_to_bv 64 (BASE + AF_both3_reac_box_name + RBN9_ACC)).
rewrite <- Z.add_assoc.
paj_run_shc RUNP RUNC HS HJ.
{ r9ro. }
r9step KP.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 KP HWb HWx1) as C1'.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
r9norm Ra0. r9norm Ra1. r9norm Ra2. r9norm Rsp. r9norm Rgp. r9norm Rtp.
rewrite (EE 3%nat 3%bv eq_refl) in Rgp. rewrite (EE 4%nat 4%bv eq_refl) in Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by lia; lia) end.
destruct C1' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d1 (F + 64) (lnb + 1) (A - sp0) _ HJ) end;
  [ rewrite Ra0; reflexivity | rewrite Ra1; reflexivity | rewrite Ra2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT | exact Ho16 | lia | exact Hostk | rewrite Rgp; exact H3 | rewrite Rtp; exact H4 | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfrc & Hpres2).
replace (sp0 + (A - sp0)) with A in Hfrc by lia.
assert (CP1 : forall j, 0 <= j < lnb + 1 -> aview SEGS (w_H W) mem2 (d1 + j) = aview SEGS (w_H W) memc (F + 64 + j)).
{ intros j Hj. rewrite (Heff j Hj). apply (proj1 KP); [lia | apply HWx1; lia]. }
pose proof (rbn9_kept_call W memc _ mem2 Wr3 d1 (lnb + 1) A KP Hfrc Hpres2
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP2 Hfrc XF 40%nat.
paj_run_shc RUNP RUNC HS HJ2.
{ r9ro. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1 FR. rename CP1b into CP1.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C2 KP HWb HWx2) as C2'.
pmkst HS.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2.
prreg HS (1%bv : bv 5) Rrb. prreg HS (2%bv : bv 5) Rspb. prreg HS (3%bv : bv 5) Rgpb. prreg HS (4%bv : bv 5) Rtpb.
r9norm Rb0. r9norm Rb1. r9norm Rb2. r9norm Rspb. r9norm Rgpb. r9norm Rtpb.
rewrite (EE 3%nat 3%bv eq_refl) in Rgpb. rewrite (EE 4%nat 4%bv eq_refl) in Rtpb.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT2 : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rspb; rewrite unsigned_lit_small by lia; lia) end.
destruct C2' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d2 (F + 128) (ltb + 1) (A - sp0) _ HJ2) end;
  [ rewrite Rb0; reflexivity | rewrite Rb1; reflexivity | rewrite Rb2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT2 | exact Ho16 | lia | exact Hostk | rewrite Rgpb; exact H3 | rewrite Rtpb; exact H4 | exact Rrb
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT2; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hb0' & Heff2 & Hfrc2 & Hpres3).
replace (sp0 + (A - sp0)) with A in Hfrc2 by lia.
assert (CP2 : forall j, 0 <= j < ltb + 1 -> aview SEGS (w_H W) mem3 (d2 + j) = aview SEGS (w_H W) memc (F + 128 + j)).
{ intros j Hj. rewrite (Heff2 j Hj). apply (proj1 KP); [lia | apply HWx2; lia]. }
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP1 Hfrc2 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd1w (d1 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_kept_call W memc _ mem3 Wr3 d2 (ltb + 1) A KP Hfrc2 Hpres3
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP3 Hfrc2 XF 60%nat.
paj_run_shc RUNP RUNC HS HJ3.
{ r9ro. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP2 FR ltac:(lia) ltac:(lia)) as CP2b. clear CP2 FR. rename CP2b into CP2.
pose proof (rbn9_cpy_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C3 KP HWb HWx3) as C3'.
pmkst HS.
prreg HS (10%bv : bv 5) Rc0. prreg HS (11%bv : bv 5) Rc1. prreg HS (12%bv : bv 5) Rc2.
prreg HS (1%bv : bv 5) Rrc. prreg HS (2%bv : bv 5) Rspc. prreg HS (3%bv : bv 5) Rgpc. prreg HS (4%bv : bv 5) Rtpc.
r9norm Rc0. r9norm Rc1. r9norm Rc2. r9norm Rspc. r9norm Rgpc. r9norm Rtpc.
rewrite (EE 3%nat 3%bv eq_refl) in Rgpc. rewrite (EE 4%nat 4%bv eq_refl) in Rtpc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  assert (HspT3 : spZ rT = sp0 + (A - sp0)) by (unfold spZ; rewrite Rspc; rewrite unsigned_lit_small by lia; lia) end.
destruct C3' as (Cn & Cd0 & Cdn & Cdw & Cdam & Cdra & Cdhv & Cx0 & Cxn & Cxs & Cdx & Cxam & Cxra & Cxhv).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W rT mT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc dT k d3 (F + 192) (nD + 1) (A - sp0) _ HJ3) end;
  [ rewrite Rc0; reflexivity | rewrite Rc1; reflexivity | rewrite Rc2; reflexivity | exact Cn | exact Cd0 | exact Cdn
  | exact HspT3 | exact Ho16 | lia | exact Hostk | rewrite Rgpc; exact H3 | rewrite Rtpc; exact H4 | exact Rrc
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; replace (sp0 + (A - sp0)) with A by lia; exact (Cdw a Ha)
  | exact Cdam | exact Cdra | exact Cdhv
  | split; [exact Cx0|]; split; [exact Cxn|]; split;
    [intros a Ha; rewrite HspT3; replace (sp0 + (A - sp0)) with A by lia; exact (Cxs a Ha)|];
    split; [exact Cdx|]; split; [exact Cxam|]; split; [exact Cxra | exact Cxhv] ]. }
clear Cn Cd0 Cdn Cdw Cdam Cdra Cdhv Cx0 Cxn Cxs Cdx Cxam Cxra Cxhv.
intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hc0' & Heff3 & Hfrc3 & Hpres4).
replace (sp0 + (A - sp0)) with A in Hfrc3 by lia.
assert (CP3 : forall j, 0 <= j < nD + 1 -> aview SEGS (w_H W) mem4 (d3 + j) = aview SEGS (w_H W) memc (F + 192 + j)).
{ intros j Hj. rewrite (Heff3 j Hj). apply (proj1 KP); [lia | apply HWx3; lia]. }
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP1 Hfrc3 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd1w (d1 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_call _ _ _ _ _ _ _ _ _ _ CP2 Hfrc3 ltac:(lia) ltac:(intros j Hj; exact (proj2 (Hd2w (d2 + j) ltac:(lia))))
  ltac:(lia) ltac:(lia)) as CP2b. clear CP2. rename CP2b into CP2.
pose proof (rbn9_kept_call W memc _ mem4 Wr3 d3 (nD + 1) A KP Hfrc3 Hpres4
  ltac:(intros a Ha; unfold Wr3; lia) ltac:(intros a Ha; unfold Wr3; lia)) as KP2. clear KP. rename KP2 into KP.
r9after HS HP4 Hfrc3 XF 80%nat.
paj_run_to_sh RUNTOP HS HJ4 (AF_both3_reac_box_name + RBN9_TAIL).
{ r9ro. }
r9run3 KP FR.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP1 FR ltac:(lia) ltac:(lia)) as CP1b. clear CP1. rename CP1b into CP1.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP2 FR ltac:(lia) ltac:(lia)) as CP2b. clear CP2. rename CP2b into CP2.
pose proof (rbn9_cp_run _ _ _ _ _ _ _ CP3 FR ltac:(lia) ltac:(lia)) as CP3b. clear CP3 FR. rename CP3b into CP3.
r9go HS RBN9_TAIL.
apply K.
- assumption.
- r9same EE.
- let R := fresh "R" in prreg HS (20%bv : bv 5) R; rewrite R; reflexivity.
- exact KP.
- intros j Hj. apply CP1. lia.
- intros j Hj. apply CP2. lia.
- intros j Hj. apply CP3. lia.
Qed.
Lemma rbn9_val1_of : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v E Hr k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. rewrite E.
assert (Hle : YO0f.le_byte v 1 0 = v).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
rewrite Hle, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. lia.
Qed.
Lemma rbn9_pres_view : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma rbn9_sep : forall (P : Z -> Prop) lo1 n1 lo2 n2, 0 < n1 -> 0 < n2 ->
  (forall x, lo1 <= x < lo1 + n1 -> ~ P x) -> (forall x, lo2 <= x < lo2 + n2 -> P x) ->
  lo1 + n1 <= lo2 \/ lo2 + n2 <= lo1.
Proof.
intros P lo1 n1 lo2 n2 H1 H2 HN HP.
destruct (Z_le_gt_dec (lo1 + n1) lo2) as [L | L]; [left; exact L|].
destruct (Z_le_gt_dec (lo2 + n2) lo1) as [R | R]; [right; exact R|].
exfalso. apply (HN (Z.max lo1 lo2)); [lia|]. apply HP. lia.
Qed.
Lemma rbn9_awr_lift : forall STK sp0 FP bl0 blc blc' ly ly' (own : list (Z * Z)) (e : Z * Z) a,
  awr_byte STK sp0 FP bl0 blc ly own a -> Permutation blc' blc ->
  (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
  awr_byte STK sp0 FP bl0 blc' ly' (e :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own e a [H | [(HF & b & n & Hb & Hr) | [(b & n & Hb & Hn & Hr) | (cid & p & Hcp & Hr)]]] HP FA.
- left; exact H.
- right; left. split; [exact HF|]. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hb) | exact Hr].
- right; right; left. exists b, n. split; [exact (Permutation_in _ (Permutation_sym HP) Hb)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, p. split; [right; exact Hcp|]. rewrite !FA. exact Hr.
Qed.
Lemma rbn9_stk_byte : forall lyc Sc (W : world SEGS) mem md x,
  AR SEGS B lyc Sc W mem md -> ly_stk_lo lyc <= x < ly_stk_hi lyc ->
  aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x) = Some 0 /\
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 -> aview SEGS (w_H W) mem s <> None).
Proof.
intros lyc Sc W mem md x HAR Hx.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
assert (Hz : forall y, ly_stk_lo lyc <= y < ly_stk_hi lyc -> aview SEGS (w_H W) mem (shadow_addr y) = Some 0).
{ intros y Hy.
  pose proof (HZ (y / 8 - ly_stk_lo lyc / 8) ltac:(lia)) as E.
  unfold shadow_of_addr in E. unfold shadow_addr.
  replace (SHADOW_OFF + y / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (y / 8 - ly_stk_lo lyc / 8)) by lia.
  exact E. }
split; [exact (Hz x Hx)|].
intros s Hs.
assert (Hy : shadow_addr (8 * (s - SHADOW_OFF)) = s) by (unfold shadow_addr; lia).
rewrite <- Hy. rewrite Hz; [discriminate|]. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_shband : forall G nb s, 4096 <= G -> 0 <= nb -> G + nb <= alloc_ceiling ->
  in_zr s (shadow_addr G, nb / 8) -> SHADOW_OFF + 512 <= s < kHighMemBeg.
Proof.
intros G nb s H1 H2 H3 Hs. pose proof Hs as Hs0. unfold in_zr in Hs. cbn [fst snd] in Hs.
assert (HL : SHADOW_OFF + 512 <= shadow_addr G) by (unfold shadow_addr; pose proof (Z.div_le_mono 4096 G 8 ltac:(lia) H1); lia).
split; [lia|].
replace s with (shadow_addr G + (s - shadow_addr G)) by lia.
apply (rbn9_sh_band G nb); lia.
Qed.
Lemma rbn9_ubuf_now : forall X own' lyc' Sc' (W' : world SEGS) m' md' k' b n,
  rbn_cx B X ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    own' lyc' Sc' W' m' md' k' ->
  Permutation (ablocks B lyc' Sc') (ablocks B (ri_lyc X) (ri_Sc X)) ->
  (forall cid p s, In (cid, p) (frames (ri_Sc X)) ->
     in_zr s (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8) ->
     aview SEGS (w_H W') m' s = aview SEGS (w_H (ri_W X)) (ri_memc X) s) ->
  rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X)
    (rbn_SP X) b n ->
  forall n', 0 <= n' <= n ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF b n' /\ (0 < n' -> shadow_hull_vis (aview SEGS (w_H W') m') b n').
Proof.
intros X own' lyc' Sc' W' m' md' k' b n HX HJc HPerm HFK (Hb0 & Hbn & Ham & Hsp & Hra0 & Hhv0 & Hw) n' Hn'.
pose proof HX as (HJ0 & _).
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Hslo & Hshi & _) & _).
pose proof HJc as (HARc & LYc & _).
destruct LYc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (BYTE : forall x, b <= x < b + n ->
  (exists s, aview SEGS (w_H W') m' (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s) /\
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr x / 8 * 8 + 8 -> aview SEGS (w_H W') m' s <> None)).
{ intros x Hx.
  destruct (proj1 (Hw x Hx)) as [Hst | [(_ & bb & mm & Hbb & Hr) | [(bb & mm & Hbb & _ & Hr) | (cid & p & Hcp & Hr)]]].
  - destruct (rbn9_stk_byte lyc' Sc' W' m' md' x HARc ltac:(rewrite Elo, Ehi; lia)) as [Z1 Z2].
    split; [exists 0; split; [exact Z1 | left; reflexivity] | exact Z2].
  - assert (Hbb' : In (bb, mm) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPerm) Hbb).
    split.
    + destruct (range_addressable_of_block SEGS B LAWS lyc' Sc' W' m' md' bb mm x 1 HARc Hbb' ltac:(lia) ltac:(lia) x ltac:(lia))
        as (s & Hs1 & Hs2). exists s. split; assumption.
    + intros s Hs. apply (shadow_hull_vis_of_block SEGS B LAWS lyc' Sc' W' m' md' bb mm x 1 HARc Hbb' ltac:(lia) ltac:(lia) ltac:(lia)).
      replace (x + 1 - 1) with x by lia. exact Hs.
  - assert (Hbb' : In (bb, mm) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPerm) Hbb).
    split.
    + destruct (range_addressable_of_block SEGS B LAWS lyc' Sc' W' m' md' bb mm x 1 HARc Hbb' ltac:(lia) ltac:(lia) x ltac:(lia))
        as (s & Hs1 & Hs2). exists s. split; assumption.
    + intros s Hs. apply (shadow_hull_vis_of_block SEGS B LAWS lyc' Sc' W' m' md' bb mm x 1 HARc Hbb' ltac:(lia) ltac:(lia) ltac:(lia)).
      replace (x + 1 - 1) with x by lia. exact Hs.
  - assert (Hcp0 : In (cid, p) (frames (ri_Sc X))) by (rewrite Hfrs0; apply in_or_app; left; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR0 Hcp0) as (Hc4 & Hcc & _).
    destruct (frame_facts B _ _ _ cid p (proj1 HAR0) Hcp0) as (_ & _ & _ & _ & HPF & _ & _ & H64 & Hb64 & Hbm64 & _).
    unfold page_aligned in HPF.
    assert (HG64 : frame_addr (ri_lyc X) cid p mod 64 = 0) by (unfold frame_addr; lia).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    set (G := frame_addr (ri_lyc X) cid p) in *.
    destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
    2: { exfalso. pose proof (rbn9_shband G (fs_frame_bytes cid) x Hc4 Hnn Hcc ltac:(unfold in_zr; cbn [fst snd]; lia)) as Hb.
         unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
    split.
    + destruct (Hra0 x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
      rewrite (HFK cid p _ Hcp0); [exact Hs1|]. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia.
    + intros s Hs. rewrite (HFK cid p s Hcp0).
      * assert (M1 : shadow_addr b / 8 * 8 <= shadow_addr x / 8 * 8) by (apply R8; apply shadow_mono; lia).
        assert (M2 : shadow_addr x / 8 * 8 <= shadow_addr (b + n - 1) / 8 * 8) by (apply R8; apply shadow_mono; lia).
        apply (Hhv0 s). lia.
      * unfold in_zr, shadow_addr, SHADOW_OFF in *. cbn [fst snd]. lia. }
split.
- intros x Hx. exact (proj1 (BYTE x ltac:(lia))).
- intros Hn s Hs.
  destruct (Z_lt_le_dec (64 * ((s - SHADOW_OFF) / 8)) b) as [Hlt | Hge].
  + apply (proj2 (BYTE b ltac:(lia)) s). unfold shadow_addr, SHADOW_OFF in *. lia.
  + apply (proj2 (BYTE (64 * ((s - SHADOW_OFF) / 8)) ltac:(unfold shadow_addr, SHADOW_OFF in *; lia)) s).
    unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.
Definition rbn9_W (X : rbn_in) (pos a : Z) : Prop :=
  (rbn_F X pos + 192 <= a < rbn_F X pos + 240) \/ (rbn_A X - ESTACK <= a < rbn_A X) \/
  (rbn_SH X pos + 4 <= a < rbn_SH X pos + 30) \/
  rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
    (ri_display X) (ri_display_len X) a.
Lemma rbn9_buf_byte : forall X pos lyc1 Sc1 W1 memc1 mdc1 sh b n a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X)
    (rbn_SP X) b n -> b <= a < b + n ->
  ~ in_img SEGS a /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512) /\ ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\
  (a < kLowMemEnd \/ kHighMemBeg <= a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 sh b n a HX HM (Hb0 & Hbn & Ham & Hsp & _ & _ & Hw) Ha.
pose proof HM as (HJ1 & Hfrs1 & Hperm & _).
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJ1) as FA.
destruct (rbn9_A_rng X HX) as (AR1 & _).
pose proof HX as (HJ0 & _).
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil0 & Hslo0 & _) & _).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hband : a < kLowMemEnd \/ kHighMemBeg <= a) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Hwin : ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X)) by (unfold rbn_SP in *; lia).
assert (HFN : forall b' m', In (b', m') (ablocks B (ri_lyc X) (ri_Sc X)) -> b' <= a < b' + req_size m' ->
  ~ in_img SEGS a /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)).
{ intros b' m' Hb' Hab. split.
  - exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_introl (ex_intro _ b' (ex_intro _ m' (conj Hb' Hab)))))).
  - assert (Hb1 : In (b', m') (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb').
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b' m' 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd. lia. }
destruct (proj1 (Hw a Ha)) as [Hs | [(_ & b' & m' & Hb' & Hab) | [(b' & m' & Hb' & _ & Hab) | (cid & p & Hcp & Hr)]]].
- assert (Hni : ~ in_img SEGS a) by (intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & HFc & _). rewrite FA3 in HFc.
  change (fs_frame_bytes 3) with 512 in HFc. split; [exact Hni|]. split; [lia|]. split; [exact Hwin | exact Hband].
- destruct (HFN b' m' Hb' Hab) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. split; [exact Hwin | exact Hband].
- destruct (HFN b' m' Hb' Hab) as [H1 H2]. split; [exact H1|]. split; [exact H2|]. split; [exact Hwin | exact Hband].
- assert (Hcp0 : In (cid, p) (frames (ri_Sc X))) by (rewrite Hfrs0; apply in_or_app; left; exact Hcp).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR0 Hcp0) as (Hc4 & Hcc & _).
  destruct Hr as [Hr | Hr].
  + unfold in_zr in Hr. cbn [fst snd] in Hr.
    split.
    * exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR0 (or_intror (or_introl (ex_intro _ cid (ex_intro _ p (conj Hcp0 Hr))))))).
    * split; [|split; [exact Hwin | exact Hband]].
      destruct (in_split _ _ Hcp0) as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
        ltac:(rewrite Hfrs1, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, (FA cid p) in Hd.
      change (fs_frame_bytes 3) with 512 in Hd. lia.
  + exfalso. pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (rbn9_shband _ _ a Hc4 Hnn Hcc Hr) as Hsb.
    unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn9_wr_buf : forall X a, rbn_cx B X ->
  rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
    (ri_display X) (ri_display_len X) a ->
  exists b n, rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X)
    (ri_W X) (ri_memc X) (rbn_SP X) b n /\ b <= a < b + n.
Proof.
intros X a HX [Hacc Ha].
change (rbm_acc X = true) in Hacc.
destruct (rbn9_acc_lens X Hacc) as (HA & L1 & L2 & L3).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hargs).
destruct (Hargs HA) as (_ & B1 & B2 & B3 & _).
change (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) with (rbm_NM X) in Ha.
destruct Ha as [Ha | [Ha | Ha]].
- exists (ri_name X), (Z.min (ri_name_len X) 24). split; [exact B1 | lia].
- exists (ri_token X), (Z.min (ri_token_len X) 24). split; [exact B2 | lia].
- exists (ri_display X), (Z.min (ri_display_len X) 48). split; [exact B3 | lia].
Qed.
Lemma rbn9_sh_same : forall k, (k < 4 \/ 30 <= k < 64)%nat ->
  nth k (rbn_sh true true true true) 0 = nth k (rbn_sh false false false false) 0.
Proof. intros k Hk. do 64 (destruct k as [|k]; [first [reflexivity | lia] |]). lia. Qed.
Lemma rbn9_close : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem3 regs6 mem6 mdc6,
  rbn_cx B X -> rbn_st9 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem6 mdc6 (ri_k X) ->
  frames Sc2 = frames Sc1 -> ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem3) ->
  tsb_ch_kept B lyc1 Sc1 W1 memc1 W2 mem3 (rbn_A X)
    (fun a => rbn_A X + 88 + 16 <= a < rbn_A X + 88 + 28 \/
       rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X)) <= a <
         rbn_F X pos + 192 + Z.of_nat (length (rbm_D9 X)) + Z.of_nat (length rbn_lit7)) ->
  rbn9_kept W2 mem3 mem6 (rbn9_W X pos) ->
  (forall j, 4 <= j < 30 ->
     val_mem SEGS (mrestrict (w_H W2) mem6) (rbn_SH X pos + j) 1 (nth (Z.to_nat j) (rbn_sh false false false false) 0)) ->
  rbn9_same regs1 regs6 [2; 3; 4; 8; 9; 18; 19; 23] ->
  getr regs6 20 = w64 (if rbm_acc X then 0 else -1) ->
  (rbm_acc X = true ->
     garr8 SEGS (mrestrict (w_H W2) mem6) (ri_name X) (rbm_NM X ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W2) mem6) (ri_token X) (bn_TK (rbm_NM X) ++ [0]) /\
     garr8 SEGS (mrestrict (w_H W2) mem6) (ri_display X) (bn_DP (rbm_NM X) (ri_i X) (ri_o X) ++ [0])) ->
  rbn_st10 B X pos regs6 lyc2 Sc2 W2 mem6 mdc6.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem3 regs6 mem6 mdc6 HX Hst HJ6 Hfr3 Hbl3 Hro3 TK K9 HSH6 SAME H20 HG.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity. assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof Hst as (HM & _).
destruct Hst as (_ & (H2 & H3 & H4 & H8 & H9 & H19 & H22 & H23) & H18 & _ & _ & _ & _ & _ & _ & _ & HA).
destruct (rbn9_D9_len X HA) as (_ & HD9).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh).
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJ1) as FA.
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 (ri_k X) HX HJ1) as (HF4096 & HFceil & HF32 & HFapp & HFoi & HFpr & HSpr).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
set (A := rbn_A X) in *. set (F := rbn_F X pos) in *. set (SP := rbn_SP X) in *.
set (n0 := Z.of_nat (length (rbm_D9 X))) in *.
assert (ESH : rbn_SH X pos = SHADOW_OFF + F / 8) by reflexivity.
assert (HF8 : F / 8 * 8 = F).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  pose proof (Z.div_mod F 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M2. lia. }
rs_hide_all. assert (HSHb : SHADOW_OFF + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighMemBeg).
{ rewrite ESH. unfold SHADOW_OFF, kHighMemBeg. lia. }
assert (HE7 : forall a, (A + 88 + 16 <= a < A + 88 + 28 \/ F + 192 + n0 <= a < F + 192 + n0 + Z.of_nat (length rbn_lit7)) ->
  (A + 104 <= a < A + 116) \/ (F + 192 <= a < F + 240))
  by (intros a [Ha | Ha]; [left; lia | right; unfold rbn_lit7 in Ha; cbn [length] in Ha; lia]).
assert (WRF : forall a, rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X)
  (ri_token_len X) (ri_display X) (ri_display_len X) a ->
  ~ in_img SEGS a /\ ~ (F <= a < F + 512) /\ ~ (SP - REAC_BOX_NAME_STK <= a < SP) /\ (a < kLowMemEnd \/ kHighMemBeg <= a)).
{ intros a Hw. destruct (rbn9_wr_buf X a HX Hw) as (b & n & Hb & Hab).
  exact (rbn9_buf_byte X pos lyc1 Sc1 W1 memc1 mdc1 _ b n a HX HM Hb Hab). }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ rbn9_W X pos a -> aview SEGS (w_H W2) mem6 a = aview SEGS (w_H W2) mem3 a)
  by exact (proj1 K9).
assert (Himg : forall a, in_img SEGS a -> ~ rbn9_W X pos a).
{ intros a Hi Hw. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  destruct Hw as [Hw | [Hw | [Hw | Hw]]].
  - exact (proj2 (HFpr a ltac:(fold F; lia)) Hi).
  - unfold A in *. lia.
  - unfold SHADOW_OFF in HSHb. lia.
  - exact (proj1 (WRF a Hw) Hi). }
pose proof TK as (T1 & T2 & T3 & T4 & T5 & T6).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
assert (Hshv : forall cid p a, In (cid, p) (frames (ri_Sc X)) ->
  (in_zr a (frame_rng (ri_lyc X) (cid, p)) \/ in_zr a (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  ~ rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
      (ri_display X) (ri_display_len X) a ->
  aview SEGS (w_H W2) mem6 a = aview SEGS (w_H (ri_W X)) (ri_memc X) a).
{ intros cid p a Hcp Ha He.
  assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & _).
  rewrite FA in Hc4096, Hcceil.
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  destruct (in_split _ _ Hcp) as (l2 & l3 & El).
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
    ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, (FA cid p) in Hd.
  change (fs_frame_bytes 3) with 512 in Hd.
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hcal & Hcapp & _).
  rewrite FA in Hcal, Hcapp.
  set (G := frame_addr (ri_lyc X) cid p) in *.
  assert (HG8 : G / 8 * 8 = G).
  { pose proof (Z.div_mod G 32 ltac:(lia)) as D1. rewrite Hcal, Z.add_0_r in D1.
    pose proof (Z.div_mod G 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound G 8 ltac:(lia)) as M2. lia. }
  destruct (frame_facts B _ _ _ cid p (proj1 HAR1) Hcp1) as (_ & _ & _ & _ & _ & _ & _ & _ & H64 & Hb64 & _).
  assert (Hcb8 : fs_frame_bytes cid / 8 * 8 = fs_frame_bytes cid).
  { pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D1. rewrite Hb64, Z.add_0_r in D1.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
    lia. }
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS.
  assert (Hband : (G <= a < G + fs_frame_bytes cid) \/ (SHADOW_OFF + 512 <= a < kHighMemBeg)).
  { destruct Ha as [Ha | Ha]; [left; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; exact Ha|].
    right. exact (rbn9_shband G (fs_frame_bytes cid) a Hc4096 Hcnn Hcceil Ha). }
  rewrite (KV a).
  2: { destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold G in Ha;
       unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
  2: { intros [Hw | [Hw | [Hw | Hw]]]; [| unfold A in *; destruct Hband as [Hb | Hb]; unfold kLowShadowBeg, kHighMemBeg in *; lia | | exact (He Hw)].
       - fold F in Hw. destruct Hband as [Hb | Hb]; [lia|].
         unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia.
       - rewrite ESH in Hw. destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha; fold G in Ha;
         unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
  rewrite (T4 cid p a Hcp1).
  - exact (K4 cid p a Hcp Ha (fun c => c)).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite (FA cid p). fold G. exact Ha.
  - intros Hc. destruct (HE7 a Hc) as [Hc' | Hc'].
    + destruct Hband as [Hb | Hb]; unfold A, kLowShadowBeg, kHighMemBeg in *; lia.
    + destruct Hband as [Hb | Hb]; [lia|]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia. }
split.
{ split; [exact HJ6|]. split; [rewrite Hfr3; exact Hfrs|]. split; [rewrite Hbl3; exact Hperm|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (KV a ltac:(lia) (Himg a Hia)). exact (Hro3 a Hro0 Ho He). }
  split.
  { split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hn He. rewrite (KV a ltac:(lia)).
      + rewrite (T1 a ltac:(lia) ltac:(unfold A, SP in *; lia) ltac:(intros Hc; destruct (HE7 a Hc); unfold A, SP in *; lia)).
        exact (K1 a Ha Hn (fun c => c)).
      + intros [Hw | [Hw | [Hw | Hw]]]; [fold F in Hw; lia | unfold A, SP in *; lia | lia | exact (He Hw)].
    - intros b m j Hb Hj He.
      assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & Hbapp & _).
      pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
      rewrite FA3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd.
      pose proof (in_app_addr _ _ (b + j) Hbapp ltac:(lia)) as Hap.
      rewrite (KV (b + j)).
      + rewrite (T2 b m j Hb1 Hj ltac:(intros Hc; destruct (HE7 _ Hc); unfold A in *; lia)).
        exact (K2 b m j Hb Hj (fun c => c)).
      + lia.
      + intros [Hw | [Hw | [Hw | Hw]]]; [fold F in Hw; lia | unfold A in *; lia | | exact (He Hw)].
        unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
    - intros a Hia Ho He. rewrite (KV a ltac:(pose proof (pa_segs_low a Hia); unfold kLowMemEnd in *; lia) (Himg a Hia)).
      rewrite (T3 a Hia Ho He). exact (K3 a Hia Ho He).
    - exact Hshv.
    - intros a Ha Hn Hp. apply (proj2 K9 a Ha). apply (T5 a ltac:(lia) ltac:(unfold A, SP in *; lia)). exact (K5 a Ha Hn Hp).
    - intros a Ha. apply Hpres6. unfold SP, rbn_SP in *. lia. }
  split.
  { unfold rbn_frame. intros j r Hj.
    assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length rbn_saved_regs) with 13%nat in Hj13.
    apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem3 mem6).
    - intros kk Hkk. apply KV; [unfold SP, rbn_SP in *; lia|].
      intros [Hw | [Hw | [Hw | Hw]]]; [fold F in Hw; unfold SP in *; lia | unfold A, SP in *; lia | unfold SP in *; lia |].
      destruct (WRF _ Hw) as (_ & _ & Hn & _). apply Hn. unfold SP in *. lia.
    - apply (rbn9_tk_val lyc1 Sc1 W1 W2 memc1 mem3 A _ _ _ _ TK); [| unfold SP in *; lia | unfold SP in *; lia | exact (Hfr j r Hj)].
      intros i Hi. split; [unfold A, SP in *; lia|]. intros Hc. destruct (HE7 _ Hc); unfold A, SP in *; lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem3 mem6).
    - intros kk Hkk. apply KV; [lia|].
      intros [Hw | [Hw | [Hw | Hw]]];
      [fold F in Hw; lia | unfold A in *; lia | unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia |].
      destruct (WRF _ Hw) as (_ & Hn & _). apply Hn. fold F. lia.
    - apply (rbn9_tk_val lyc1 Sc1 W1 W2 memc1 mem3 A _ _ _ _ TK); [| lia | lia | exact Hfl].
      intros i Hi. split; [unfold A in *; lia|]. intros Hc. destruct (HE7 _ Hc); unfold A in *; lia. }
  intros j Hj. change (length (rbn_sh false false false false)) with 64%nat in Hj.
  assert (Hout : forall jj, 0 <= jj < 64 -> (jj < 4 \/ 30 <= jj) ->
    aview SEGS (w_H W2) mem6 (rbn_SH X pos + jj) = Some (nth (Z.to_nat jj) (rbn_sh false false false false) 0)).
  { intros jj Hjj Hjo.
    rewrite (KV (rbn_SH X pos + jj)).
    - rewrite (T4 3 pos (rbn_SH X pos + jj) Hin3).
      + rewrite (Hsh jj ltac:(change (length (rbn_sh true true true true)) with 64%nat; lia)).
        rewrite rbn9_sh_same by lia. reflexivity.
      + right. unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes 3 / 8) with 64.
        unfold rbn_SH. fold F. lia.
      + intros Hc. destruct (HE7 _ Hc) as [Hc' | Hc']; [unfold A, SHADOW_OFF in *; lia|].
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia.
    - unfold SHADOW_OFF in *; lia.
    - intros [Hw | [Hw | [Hw | Hw]]].
      + fold F in Hw. unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF, kHighMemBeg in *; lia.
      + unfold A in *. unfold SHADOW_OFF in *. lia.
      + lia.
      + destruct (WRF _ Hw) as (_ & _ & _ & Hb). unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
  destruct (Z_lt_ge_dec j 4) as [Hj4 | Hj4]; [|destruct (Z_lt_ge_dec j 30) as [Hj30 | Hj30]].
  - apply Hout; lia.
  - apply rbn9_aview_val1; [exact (HSH6 j ltac:(lia))|].
    assert (Hk : (Z.to_nat j < 64)%nat) by lia.
    clear - Hk. generalize (Z.to_nat j) Hk. intros k Hk'. do 64 (destruct k as [|k]; [cbn; lia|]). lia.
  - apply Hout; lia. }
split.
{ split; [exact (eq_trans (SAME 2 ltac:(cbn; tauto)) H2)|]. split; [exact (eq_trans (SAME 3 ltac:(cbn; tauto)) H3)|].
  split; [exact (eq_trans (SAME 4 ltac:(cbn; tauto)) H4)|]. split; [exact (eq_trans (SAME 8 ltac:(cbn; tauto)) H8)|].
  split; [exact (eq_trans (SAME 9 ltac:(cbn; tauto)) H9)|]. split; [exact (eq_trans (SAME 19 ltac:(cbn; tauto)) H19)|].
  exact (eq_trans (SAME 23 ltac:(cbn; tauto)) H23). }
split; [exact (eq_trans (SAME 18 ltac:(cbn; tauto)) H18)|].
split; [exact H20|]. exact HG.
Qed.
Theorem rbn_seg9 : rbn_seg9_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 HX Hst.
apply (rbn9_head X pos regs1 lyc1 Sc1 W1 memc1 mdc1 _ HX Hst).
intros lyc2 Sc2 W2 regs3 mem3 mdc3 HJ3 Hfr3 Hbl3 Hro3 SAME3 M104 M112 G7 TK.
pose proof Hst as Hst0.
destruct (rbn9_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
destruct Hst0 as (HM & (H2 & H3 & H4 & H8 & H9 & H19 & H22 & H23) & H18 & H25 & H26 & H27 & HC & G64 & G128 & G192 & HA).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro1 & HK1 & Hfr1 & Hfl1 & Hsh1).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Rnm & _ & Rnml & _ & Rtk & _ & Rtkl & _ & Rd & _ & Rdl & _ & Hargs).
destruct (rbn9_D9_ovf X HA) as (Hov47 & Hfirst). destruct (rbn9_D9_len X HA) as (_ & HD9).
pose proof (rbn9_tok0 X) as Htok0. pose proof (rbn9_NB_len X) as HNB. pose proof (rbn9_TB_len X) as HTB.
pose proof (rbn9_ovf01 23 (rbm_NM X)) as Hov01.
unfold rbn_argc, rbn_rw, rbn_rn, rbn_rt, rbn_rd in HC. cbn [rbn_cells app] in HC.
destruct HC as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C184 & C192 & C200 & C208 & C152 & C160 & C168 & C176 &
  C120 & C128 & C136 & C144 & C88 & C96 & C104 & C112 & _).
rewrite Htok0 in C144. rewrite Hfirst in G192.
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJ1) as FA1.
pose proof (rbn9_faJ X _ _ _ _ _ _ _ HX HJ3) as FA2.
destruct (rbn9_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 (ri_k X) HX HJ1) as (HF4096 & HFceil & HF32 & HFapp & HFoi & HFpr & HSpr).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA1; reflexivity).
assert (HPerm2 : Permutation (ablocks B lyc2 Sc2) (ablocks B (ri_lyc X) (ri_Sc X))) by (rewrite Hbl3; exact Hperm).
set (n0 := Z.of_nat (length (rbm_D9 X))) in *.
set (A := rbn_A X) in *. set (F := rbn_F X pos) in *.
set (lnb := Z.of_nat (length (rbm_NB X))) in *. set (ltb := Z.of_nat (length (rbm_TB X))) in *.
set (ovn := rbm_ovf 23 (rbm_NM X)) in *.
assert (ESH : rbn_SH X pos = shadow_addr F) by reflexivity.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D1. rewrite HF32, Z.add_0_r in D1.
  rewrite D1. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (HSHb : 2147450880 + 512 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighMemBeg).
{ rewrite ESH. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia). lia. }
assert (HFin : F + 512 <= kLowShadowBeg \/ kHighMemBeg <= F) by (unfold in_app in HFapp; lia).
rs_hide_all.
assert (E7 : forall a, (A + 88 + 16 <= a < A + 88 + 28 \/ F + 192 + n0 <= a < F + 192 + n0 + Z.of_nat (length rbn_lit7)) ->
  (A + 104 <= a < A + 116) \/ (F + 192 + n0 <= a < F + 192 + n0 + 5))
  by (intros a [Ha | Ha]; [left; lia | right; unfold rbn_lit7 in Ha; cbn [length] in Ha; lia]).
assert (TV : forall a (nn : nat) v, A <= a -> (a + Z.of_nat nn <= A + 104 \/ (A + 116 <= a /\ a + Z.of_nat nn <= A + 320)) ->
  val_mem SEGS (mrestrict (w_H W1) memc1) a nn v -> val_mem SEGS (mrestrict (w_H W2) mem3) a nn v).
{ intros a nn v Ha1 Ha2 Hv. apply (rbn9_tk_val lyc1 Sc1 W1 W2 memc1 mem3 A _ a nn v TK); [|lia|lia|exact Hv].
  intros i Hi. split; [lia|]. intros Hc. destruct (E7 _ Hc); lia. }
assert (TG : forall a l, F <= a -> (a + Z.of_nat (length l) <= F + 192 + n0 \/ F + 192 + n0 + 5 <= a) ->
  a + Z.of_nat (length l) <= F + 512 ->
  garr8 SEGS (mrestrict (w_H W1) memc1) a l -> garr8 SEGS (mrestrict (w_H W2) mem3) a l).
{ intros a l Hg1 Hg2 Hg3 Hg. apply (rbn9_tk_garr lyc1 Sc1 W1 W2 memc1 mem3 A _ a l TK); [|lia|lia|exact Hg].
  intros i Hi. split; [lia|]. intros Hc. destruct (E7 _ Hc); lia. }
assert (G64' : garr8 SEGS (mrestrict (w_H W2) mem3) (F + 64) (rbm_NB X ++ [0]))
  by (apply TG; [lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact G64]).
assert (G128' : garr8 SEGS (mrestrict (w_H W2) mem3) (F + 128) (rbm_TB X ++ [0]))
  by (apply TG; [lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact G128]).
assert (G192' : garr8 SEGS (mrestrict (w_H W2) mem3) (F + 192) (rbm_D9 X)) by (apply TG; [lia | left; lia | lia | exact G192]).
assert (GD : garr8 SEGS (mrestrict (w_H W2) mem3) (F + 192) (rbm_D9 X ++ rbn_lit7)) by (apply rbn9_garr8_app; [exact G192' | exact G7]).
assert (SHK : forall j, 0 <= j < 64 ->
  aview SEGS (w_H W2) mem3 (rbn_SH X pos + j) = Some (nth (Z.to_nat j) (rbn_sh true true true true) 0)).
{ intros j Hj. rewrite (proj1 (proj2 (proj2 (proj2 TK))) 3 pos (rbn_SH X pos + j) Hin3).
  - apply Hsh1. change (length (rbn_sh true true true true)) with 64%nat. lia.
  - right. unfold in_zr. cbn [fst snd]. rewrite FA3. change (fs_frame_bytes 3 / 8) with 64. rewrite ESH. lia.
  - intros Hc. destruct (E7 _ Hc) as [Hc' | Hc']; [unfold A in *; lia|].
    destruct HFin; unfold kLowShadowBeg, kHighMemBeg in *; lia. }
pose proof C0 as M0. apply TV in M0; [| lia | lia].
pose proof C8 as M8. apply TV in M8; [| lia | lia].
pose proof C16 as M16. apply TV in M16; [| lia | lia].
pose proof C24 as M24. apply TV in M24; [| lia | lia].
pose proof C32 as M32. apply TV in M32; [| lia | lia].
pose proof C56 as M56. apply TV in M56; [| lia | lia].
pose proof C136 as M136. apply TV in M136; [| lia | lia].
pose proof C144 as M144. apply TV in M144; [| lia | lia].
pose proof C168 as M168. apply TV in M168; [| lia | lia].
pose proof C176 as M176. apply TV in M176; [| lia | lia].
pose proof C208 as M208. apply TV in M208; [| lia | lia].
destruct (rbn9_F_facts X pos lyc2 Sc2 W2 mem3 mdc3 (ri_k X) HX HJ3) as (_ & _ & _ & _ & _ & HFpr3 & _).
assert (HAWR : forall a, F <= a < F + 512 ->
  awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc2 Sc2) lyc2 ((3, pos) :: ri_own X) a).
{ intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite FA2. change (frame_addr (ri_lyc X) 3 pos) with F. change (fs_frame_bytes 3) with 512. lia. }
assert (HAWRS : forall a, rbn_SH X pos <= a < rbn_SH X pos + 64 ->
  awr_byte (ri_STK X) (ri_sp0 X) (ri_FP X) (ablocks B (ri_ly X) (ri_S X)) (ablocks B lyc2 Sc2) lyc2 ((3, pos) :: ri_own X) a).
{ intros a Ha. right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite FA2. change (frame_addr (ri_lyc X) 3 pos) with F. change (fs_frame_bytes 3 / 8) with 64.
  rewrite ESH in Ha. exact Ha. }
assert (R3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact SAME3.
unfold rbn_cfg.
apply (rbn9_checks (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem3 mdc3 (ri_k X) regs3 A F (n0 + 5) (ri_token_len X) (ri_display_len X)
  (ri_name_len X) ltb lnb ovn _ HJ3).
- exact (eq_trans (R3 9 ltac:(cbn; tauto)) H9).
- exact (eq_trans (R3 26 ltac:(cbn; tauto)) H26).
- exact AR7.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact Hov01.
- lia.
- lia.
- lia.
- lia.
- lia.
- exact M24.
- exact M32.
- exact M56.
- exact M104.
- exact M112.
- exact M136.
- exact M144.
- exact M168.
- exact M176.
- exact M208.
- destruct (HFpr3 (F + 192 + (n0 + 5)) ltac:(lia)) as [Hp9 _]. exact Hp9.
- apply HAWR. lia.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & KP4 & NUL4) R20 Hnc.
  assert (Hacc : rbm_acc X = false).
  { rewrite (rbn9_acc X HA). fold lnb ltb ovn n0.
    destruct (Z.eqb_spec ovn 0), (Z.ltb_spec lnb (ri_name_len X)), (Z.ltb_spec ltb (ri_token_len X)),
      (Z.ltb_spec (n0 + 5) (ri_display_len X)); cbn [andb]; try reflexivity. exfalso. apply Hnc. lia. }
  destruct (rbn9_F_facts X pos lyc2 Sc2 W2 mem4 mdc4 (ri_k X) HX HJ4) as (_ & _ & _ & _ & _ & _ & HSpr4).
  apply (rbn9_tail (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem4 mdc4 (ri_k X) regs4 (rbn_SH X pos) _ HJ4).
  + exact (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (R3 18 ltac:(cbn; tauto)) H18)).
  + lia.
  + lia.
  + intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by lia. apply HSpr4. lia.
  + intros a Ha. apply HAWRS. lia.
  + intros j Hj. apply rbn9_val1_of.
    * rewrite (proj1 KP4 (rbn_SH X pos + j) ltac:(lia) ltac:(destruct HFin; unfold kLowShadowBeg, kHighMemBeg in *; lia)).
      apply SHK. lia.
    * assert (Hk : (Z.to_nat j < 64)%nat) by lia.
      clear - Hk. generalize (Z.to_nat j) Hk. intros k Hk'. do 64 (destruct k as [|k]; [cbn; lia|]). lia.
  + intros regs6 mem6 mdc6 HJ6 SAME6 KP6 HSH6.
    apply SRr_ret. exists pos, regs6, lyc2, Sc2, mem6, mdc6. split; [reflexivity|].
    apply (rbn9_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem3 regs6 mem6 mdc6 HX Hst HJ6 Hfr3 Hbl3 Hro3 TK).
    * apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ KP4 KP6)).
      intros a [Ha | Ha]; unfold rbn9_W; [left; fold F; lia | right; right; left; exact Ha].
    * exact HSH6.
    * intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [etransitivity; [apply SAME6; cbn; tauto
         | etransitivity; [apply SAME4; cbn; tauto | apply R3; cbn; tauto]] |]).
      destruct Hr.
    * rewrite Hacc. exact (eq_trans (SAME6 20 ltac:(cbn; tauto)) R20).
    * intros Ht. rewrite Hacc in Ht. discriminate.
- intros regs4 mem4 mdc4 (HJ4 & SAME4 & KP4 & NUL4) R12 R21 R22 Hcond.
  destruct Hcond as (Hc1 & Hc2 & Hc3 & Hc4).
  assert (Hacc : rbm_acc X = true).
  { rewrite (rbn9_acc X HA). fold lnb ltb ovn n0.
    rewrite (proj2 (Z.eqb_eq _ _) Hc1), (proj2 (Z.ltb_lt _ _) Hc2), (proj2 (Z.ltb_lt _ _) Hc4), (proj2 (Z.ltb_lt _ _) Hc3).
    reflexivity. }
  destruct (rbn9_acc_parts X HA Hc1) as (E1 & E2 & E3).
  destruct (Hargs HA) as (_ & Bn & Bt & Bd & D12 & D13 & D23).
  destruct (rbn9_F_facts X pos lyc2 Sc2 W2 mem4 mdc4 (ri_k X) HX HJ4) as (_ & _ & _ & _ & _ & HFpr4 & HSpr4).
  assert (SHK4 : forall j, 0 <= j < 64 ->
    aview SEGS (w_H W2) mem4 (rbn_SH X pos + j) = Some (nth (Z.to_nat j) (rbn_sh true true true true) 0)).
  { intros j Hj. rewrite (proj1 KP4 (rbn_SH X pos + j) ltac:(lia) ltac:(destruct HFin; unfold kLowShadowBeg, kHighMemBeg in *; lia)). apply SHK. lia. }
  assert (Hsh4 : rbn_shadow_at W2 mem4 (shadow_addr F) (rbn_sh true true true true)).
  { intros j Hj. rewrite <- ESH. apply SHK4. change (length (rbn_sh true true true true)) with 64%nat in Hj. lia. }
  assert (HFK4 : forall cid p s, In (cid, p) (frames (ri_Sc X)) ->
    in_zr s (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8) ->
    aview SEGS (w_H W2) mem4 s = aview SEGS (w_H (ri_W X)) (ri_memc X) s).
  { intros cid p s Hcp Hs.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p (proj1 HJ1) Hcp1) as (Hc4096 & Hcceil & _).
    rewrite FA1 in Hc4096, Hcceil. pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    pose proof (rbn9_shband _ _ s Hc4096 Hcnn Hcceil Hs) as Hsb.
    rewrite (proj1 KP4 s ltac:(unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)
      ltac:(destruct HFin; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)).
    rewrite (proj1 (proj2 (proj2 (proj2 TK))) cid p s Hcp1).
    - exact (proj1 (proj2 (proj2 (proj2 HK1))) cid p s Hcp (or_intror Hs) (fun c => c)).
    - right. rewrite FA1. exact Hs.
    - intros Hc. destruct (E7 _ Hc) as [Hc' | Hc']; [unfold A, kHighMemBeg, SHADOW_OFF in *; lia|].
      destruct HFin; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
  assert (MV : forall a v, A <= a -> a <= A + 24 -> val_mem SEGS (mrestrict (w_H W2) mem3) a 8 v ->
    val_mem SEGS (mrestrict (w_H W2) mem4) a 8 v).
  { intros a v Ha1 Ha2 Hv. apply (rbn9_kept_val W2 mem3 mem4 _ a 8%nat v KP4); [intros i Hi; lia | lia | lia | exact Hv]. }
  pose proof (rbn9_acc_lens X Hacc) as (_ & L1 & L2 & L3).
  rewrite <- E1 in L1. rewrite <- E2 in L2. fold lnb in L1. fold ltb in L2.
  rewrite <- E3, length_app in L3. cbn [length] in L3. rewrite Nat2Z.inj_add in L3. fold n0 in L3.
  rs_hide_all.
  assert (BB : forall b n a, rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X) (ri_Sc X)
      (ri_W X) (ri_memc X) (spZ (ri_regs X)) b n -> b <= a < b + n ->
    ~ in_img SEGS a /\ ~ (F <= a < F + 512) /\ ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ (a < kLowMemEnd \/ kHighMemBeg <= a))
    by (intros b n a Hb Ha; exact (rbn9_buf_byte X pos lyc1 Sc1 W1 memc1 mdc1 _ b n a HX HM Hb Ha)).
  assert (CPY : forall b nb x nx lo hi, rbn_buf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_own X) (ri_lyc X)
      (ri_Sc X) (ri_W X) (ri_memc X) (spZ (ri_regs X)) b nb -> 0 < nx <= nb -> nx <= 48 ->
    x = F + 8 * lo -> nx <= 8 * (hi - lo) -> 8 <= lo -> lo <= hi -> hi <= 30 ->
    (forall j, lo <= j < hi -> nth (Z.to_nat j) (rbn_sh true true true true) 0 = 0) ->
    rbn9_cpy (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem4 A b x nx).
  { intros b nb x nx lo hi Hb Hnx Hnx24 -> Hnxh Hlo Hlh Hhi Hz.
    pose proof Hb as (Hb0 & Hbn & Ham & Hsp & _ & _ & Hw).
    rs_hide_all.
    destruct (rbn9_ubuf_now X _ lyc2 Sc2 W2 mem4 mdc4 (ri_k X) b nb HX HJ4 HPerm2 HFK4 Hb nx ltac:(lia)) as [Ura Uhv].
    unfold rbn9_cpy. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { intros a Ha. split.
      - apply (rbn9_awr_lift _ _ _ _ (ablocks B (ri_lyc X) (ri_Sc X)) _ (ri_lyc X) _ _ _ a (proj1 (Hw a ltac:(lia))) HPerm2 FA2).
      - destruct (BB b nb a Hb ltac:(lia)) as (_ & _ & Hn & _). clear - Hn AR2 AR3 Hes WS. unfold rbn_SP in *. lia. }
    split; [clear - Ham Hnx; unfold amem_range in *; lia|]. split; [exact Ura|]. split; [exact Uhv|].
    split; [lia|]. split; [lia|].
    split.
    { intros a Ha. split; [apply rbn9_pres_view; exact (proj1 (HFpr4 a ltac:(lia)))|]. lia. }
    split.
    { apply (rbn9_sep (fun y => F <= y < F + 512) b nx (F + 8 * lo) nx); [lia | lia | | intros y Hy; lia].
      intros y Hy. exact (proj1 (proj2 (BB b nb y Hb ltac:(lia)))). }
    split; [destruct HFin; unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
    split.
    { apply (range_addressable_sub (aview SEGS (w_H W2) mem4) SHADOW_OFF (F + 8 * lo) (8 * (hi - lo))); [| lia | lia].
      apply (rbn9_ra_frame W2 mem4 F (rbn_sh true true true true) lo hi Hsh4 HF8); [lia | lia | cbn; lia | exact Hz]. }
    intros _. apply (rbn9_frame_hull W2 mem4 F (rbn_sh true true true true) _ _ Hsh4 eq_refl HF8); lia. }
  apply (rbn9_copies (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem4 mdc4 (ri_k X) regs4 A F (ri_name X) (ri_token X) (ri_display X)
    lnb ltb (n0 + 5) _ HJ4).
  + exact (eq_trans (SAME4 2 ltac:(cbn; tauto)) (eq_trans (R3 2 ltac:(cbn; tauto)) H2)).
  + exact (eq_trans (SAME4 3 ltac:(cbn; tauto)) (eq_trans (R3 3 ltac:(cbn; tauto)) H3)).
  + exact (eq_trans (SAME4 4 ltac:(cbn; tauto)) (eq_trans (R3 4 ltac:(cbn; tauto)) H4)).
  + exact (eq_trans (SAME4 9 ltac:(cbn; tauto)) (eq_trans (R3 9 ltac:(cbn; tauto)) H9)).
  + exact R12.
  + exact R21.
  + exact R22.
  + exact (eq_trans (SAME4 25 ltac:(cbn; tauto)) (eq_trans (R3 25 ltac:(cbn; tauto)) H25)).
  + exact (eq_trans (SAME4 26 ltac:(cbn; tauto)) (eq_trans (R3 26 ltac:(cbn; tauto)) H26)).
  + exact (eq_trans (SAME4 27 ltac:(cbn; tauto)) (eq_trans (R3 27 ltac:(cbn; tauto)) H27)).
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + pose proof (Z.div_mod A 32 ltac:(lia)) as Q1. pose proof (Z.div_mod (ri_sp0 X) 16 ltac:(lia)) as Q2. clear - AR7 AR9 Q1 Q2. unfold rs_hold in AR7, AR9. lia.
  + lia.
  + lia.
  + lia.
  + apply MV; [lia | lia | exact M0].
  + apply MV; [lia | lia | exact M8].
  + apply MV; [lia | lia | exact M16].
  + apply (CPY _ _ _ _ 8 11 Bn); [lia | lia | lia | lia | lia | lia | lia |].
    intros j Hj. assert (j = 8 \/ j = 9 \/ j = 10) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
  + apply (CPY _ _ _ _ 16 19 Bt); [lia | lia | lia | lia | lia | lia | lia |].
    intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as Hjj by lia. destruct Hjj as [-> | [-> | ->]]; reflexivity.
  + apply (CPY _ _ _ _ 24 30 Bd); [lia | lia | lia | lia | lia | lia | lia |].
    intros j Hj. assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as Hjj by lia.
    repeat (destruct Hjj as [-> | Hjj]; [reflexivity|]). subst j. reflexivity.
  + clear - D12 L1 L2. unfold rs_hold in D12. lia.
  + clear - D13 L1 L3. unfold rs_hold in D13. lia.
  + clear - D23 L2 L3. unfold rs_hold in D23. lia.
  + intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    * destruct (BB _ _ a Bn ltac:(lia)) as (_ & HF & Hs & _). split; [exact HF | clear - Hs AR2 AR3 WS; unfold rbn_SP in *; lia].
    * destruct (BB _ _ a Bt ltac:(lia)) as (_ & HF & Hs & _). split; [exact HF | clear - Hs AR2 AR3 WS; unfold rbn_SP in *; lia].
    * destruct (BB _ _ a Bd ltac:(lia)) as (_ & HF & Hs & _). split; [exact HF | clear - Hs AR2 AR3 WS; unfold rbn_SP in *; lia].
  + intros regs5 mem5 mdc5 HJ5 SAME5 R20 KP5 CP1 CP2 CP3.
    destruct (rbn9_F_facts X pos lyc2 Sc2 W2 mem5 mdc5 (ri_k X) HX HJ5) as (_ & _ & _ & _ & _ & _ & HSpr5).
    assert (DSH : forall a, rbn_SH X pos <= a < rbn_SH X pos + 64 ->
      ~ (ri_name X <= a < ri_name X + lnb + 1 \/ ri_token X <= a < ri_token X + ltb + 1 \/
         ri_display X <= a < ri_display X + (n0 + 5) + 1 \/ A - ESTACK <= a < A)).
    { intros a Ha [Hd | [Hd | [Hd | Hd]]].
      - destruct (BB _ _ a Bn ltac:(lia)) as (_ & _ & _ & Hb). clear - Ha Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
      - destruct (BB _ _ a Bt ltac:(lia)) as (_ & _ & _ & Hb). clear - Ha Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
      - destruct (BB _ _ a Bd ltac:(lia)) as (_ & _ & _ & Hb). clear - Ha Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
      - unfold A, kHighMemBeg in *. lia. }
    apply (rbn9_tail (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
      ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem5 mdc5 (ri_k X) regs5 (rbn_SH X pos) _ HJ5).
    * exact (eq_trans (SAME5 18 ltac:(cbn; tauto)) (eq_trans (SAME4 18 ltac:(cbn; tauto)) (eq_trans (R3 18 ltac:(cbn; tauto)) H18))).
    * lia.
    * lia.
    * intros a Ha. replace a with (rbn_SH X pos + (a - rbn_SH X pos)) by lia. apply HSpr5. lia.
    * intros a Ha. apply HAWRS. lia.
    * intros j Hj. apply rbn9_val1_of.
      -- rewrite (proj1 KP5 (rbn_SH X pos + j) ltac:(lia) (DSH (rbn_SH X pos + j) ltac:(lia))). apply SHK4. lia.
      -- assert (Hk : (Z.to_nat j < 64)%nat) by lia.
         clear - Hk. generalize (Z.to_nat j) Hk. intros k Hk'. do 64 (destruct k as [|k]; [cbn; lia|]). lia.
    * intros regs6 mem6 mdc6 HJ6 SAME6 KP6 HSH6.
      apply SRr_ret. exists pos, regs6, lyc2, Sc2, mem6, mdc6. split; [reflexivity|].
      assert (WRN : forall a, ri_name X <= a < ri_name X + lnb + 1 ->
        rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
          (ri_display X) (ri_display_len X) a).
      { intros a Ha. split; [exact Hacc|]. left. change (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) with (rbm_NM X).
        rewrite <- E1. fold lnb. lia. }
      assert (WRT : forall a, ri_token X <= a < ri_token X + ltb + 1 ->
        rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
          (ri_display X) (ri_display_len X) a).
      { intros a Ha. split; [exact Hacc|]. right; left. change (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) with (rbm_NM X).
        rewrite <- E2. fold ltb. lia. }
      assert (WRD : forall a, ri_display X <= a < ri_display X + (n0 + 5) + 1 ->
        rbn_wr (ri_f X) (ri_sd X) (ri_i X) (ri_o X) (ri_name X) (ri_name_len X) (ri_token X) (ri_token_len X)
          (ri_display X) (ri_display_len X) a).
      { intros a Ha. split; [exact Hacc|]. right; right. change (bn_NM (ri_f X) (ri_sd X) (ri_i X) (ri_o X)) with (rbm_NM X).
        rewrite <- E3, length_app. cbn [length]. fold n0. lia. }
      assert (K9 : rbn9_kept W2 mem3 mem6 (rbn9_W X pos)).
      { apply (rbn9_kept_mono _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ (rbn9_kept_trans _ _ _ _ _ _ KP4 KP5) KP6)).
        intros a [[Ha | [Ha | [Ha | [Ha | Ha]]]] | Ha]; unfold rbn9_W.
        - left. fold F. lia.
        - right; right; right. exact (WRN a Ha).
        - right; right; right. exact (WRT a Ha).
        - right; right; right. exact (WRD a Ha).
        - right; left. exact Ha.
        - right; right; left. exact Ha. }
      assert (K6 : forall a, ~ (rbn_SH X pos + 4 <= a < rbn_SH X pos + 30) -> 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W2) mem6 a = aview SEGS (w_H W2) mem5 a) by (intros a Ha H0; exact (proj1 KP6 a H0 Ha)).
      apply (rbn9_close X pos regs1 lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem3 regs6 mem6 mdc6 HX Hst HJ6 Hfr3 Hbl3 Hro3 TK K9 HSH6).
      -- intros r Hr. cbn [In] in Hr.
         repeat (destruct Hr as [<- | Hr];
           [etransitivity; [apply SAME6; cbn; tauto
            | etransitivity; [apply SAME5; cbn; tauto
              | etransitivity; [apply SAME4; cbn; tauto | apply R3; cbn; tauto]]] |]).
         destruct Hr.
      -- rewrite Hacc. exact (eq_trans (SAME6 20 ltac:(cbn; tauto)) R20).
      -- intros _. pose proof Bn as (Bn0 & Bn1 & _). pose proof Bt as (Bt0 & Bt1 & _).
         pose proof Bd as (Bd0 & Bd1 & _). split; [|split].
         ++ rewrite <- E1. apply (rbn9_garr8_copy (w_H W2) (w_H W2) mem4 mem6 (F + 64) (ri_name X)).
            ** intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. fold lnb in Hj.
               rewrite (K6 (ri_name X + j)).
               --- apply CP1. lia.
               --- intros Hs. destruct (BB _ _ (ri_name X + j) Bn ltac:(lia)) as (_ & _ & _ & Hb). clear - Hs Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
               --- lia.
            ** apply (rbn9_kept_garr W2 mem3 mem4 _ _ _ KP4);
               [rewrite length_app; cbn [length]; intros i Hi; lia | lia
                | rewrite length_app; cbn [length]; lia | exact G64'].
         ++ rewrite <- E2. apply (rbn9_garr8_copy (w_H W2) (w_H W2) mem4 mem6 (F + 128) (ri_token X)).
            ** intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. fold ltb in Hj.
               rewrite (K6 (ri_token X + j)).
               --- apply CP2. lia.
               --- intros Hs. destruct (BB _ _ (ri_token X + j) Bt ltac:(lia)) as (_ & _ & _ & Hb). clear - Hs Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
               --- lia.
            ** apply (rbn9_kept_garr W2 mem3 mem4 _ _ _ KP4);
               [rewrite length_app; cbn [length]; intros i Hi; lia | lia
                | rewrite length_app; cbn [length]; lia | exact G128'].
         ++ rewrite <- E3. change [32; 111; 117; 116; 41] with rbn_lit7.
            apply (rbn9_garr8_copy (w_H W2) (w_H W2) mem4 mem6 (F + 192) (ri_display X)).
            ** intros j Hj. rewrite !length_app in Hj. unfold rbn_lit7 in Hj. cbn [length] in Hj. fold n0 in Hj.
               rewrite (K6 (ri_display X + j)).
               --- apply CP3. lia.
               --- intros Hs. destruct (BB _ _ (ri_display X + j) Bd ltac:(lia)) as (_ & _ & _ & Hb). clear - Hs Hb HSHb. unfold kLowMemEnd, kHighMemBeg in *. lia.
               --- lia.
            ** apply rbn9_garr8_app.
               --- apply (rbn9_kept_garr W2 mem3 mem4 _ _ _ KP4);
                   [rewrite length_app; unfold rbn_lit7; cbn [length]; intros i Hi; lia | lia
                    | rewrite length_app; unfold rbn_lit7; cbn [length]; lia | exact GD].
               --- assert (Lz : Z.of_nat (length (rbm_D9 X ++ rbn_lit7)) = n0 + 5)
                     by (rewrite length_app, Nat2Z.inj_add; fold n0; unfold rbn_lit7; cbn [length]; lia).
                   rewrite Lz. intros jj Hjj. cbn [length] in Hjj. destruct jj as [|jj]; [|lia]. split; [|cbn; lia].
                   cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact NUL4.
Qed.
End h.
End f.
End d.
