(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayHuff4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayLP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayBlock.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRows.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayFacts.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayRuns.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import OverlayDamage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition WL (b : oblock) : Z := lsum (fL b) (zrange 0 286).
Definition WD (b : oblock) : Z := vP b + Z.of_nat (length (ob_forced b)).
Definition rho_of (LL : Z) : Z * Z := if LL <=? 9 then (3, 8) else (1, 1).
Definition Kbl_of (LL : Z) : Z := if LL <=? 9 then 13 else 19.

Definition n1_of (b : oblock) : Z := countZ (fun c => usedLb b c && (ob_lenL b c =? 1)) (zrange 0 286).
Definition d1_of (b : oblock) : Z :=
  fold_right (fun c m => if fL b c =? 1 then Z.min (ob_lenL b c) m else m) (ob_lenL b 256) (zrange 0 286).

Record prm_ok (prm : oprm) (lbs : Z) (b : oblock) : Prop := {
  po_lbs : p_lbs prm = lbs;
  po_LL : 1 <= p_LL prm <= 15 /\ lbs + 1 < fib (p_LL prm + 3);
  po_blc : p_blc prm = (if p_LL prm <=? 14 then 18 else 19);
  po_d1 : p_d1 prm = d1_of b;
  po_n1 : p_n1 prm = n1_of b;
  po_rho : (p_rnum prm, p_rden prm) = rho_of (p_LL prm);
  po_dmg : dmg_cert (Kbl_of (p_LL prm)) (fst (rho_of (p_LL prm))) (snd (rho_of (p_LL prm))) = true
}.


Fixpoint gsum {A} (f : A -> Z) (L : list A) : Z := match L with [] => 0 | i :: r => f i + gsum f r end.

Lemma gsum_lsum f L : gsum f L = lsum f L.
Proof. induction L; cbn; [reflexivity|]. rewrite IHL. reflexivity. Qed.


Lemma gsum_pick (f : Z -> Z) (L : list Z) (v : Z) : NoDup L -> In v L ->
  gsum (fun l => if l =? v then f l else 0) L = f v.
Proof.
  intros ND I. rewrite gsum_lsum.
  rewrite (lsum_ext _ (fun l => if l =? v then f v else 0)) by (intros l _; destruct (Z.eqb_spec l v); [subst; reflexivity|reflexivity]).
  destruct (lsum_in_split L v I ND) as (l1 & l2 & E & N1 & N2). rewrite E, lsum_app. cbn. rewrite Z.eqb_refl.
  rewrite (lsum_ext _ (fun _ => 0) l1) by (intros l Hl; destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]).
  rewrite (lsum_ext _ (fun _ => 0) l2) by (intros l Hl; destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]).
  rewrite !lsum_zero. lia.
Qed.
Lemma gsum_miss (f : Z -> Z) (L : list Z) (v : Z) : ~ In v L -> gsum (fun l => if l =? v then f l else 0) L = 0.
Proof. intros N. rewrite gsum_lsum. rewrite (lsum_ext _ (fun _ => 0)); [apply lsum_zero|]. intros l Hl. destruct (Z.eqb_spec l v); [subst; tauto|reflexivity]. Qed.

Lemma zrange_in lo n x : In x (zrange lo n) <-> lo <= x < lo + Z.of_nat n.
Proof.
  unfold zrange. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma zrange_nodup lo n : NoDup (zrange lo n).
Proof. unfold zrange. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia. Qed.




Lemma scount_nonneg (P : osym -> bool) l : 0 <= scount P l.
Proof. unfold scount. induction l; cbn; [lia|]. destruct (P a); lia. Qed.
Lemma scount_le_len (P : osym -> bool) l : scount P l <= Z.of_nat (length l).
Proof. unfold scount. induction l; cbn; [lia|]. destruct (P a); lia. Qed.
Lemma ssum_ext f g l : (forall s, In s l -> f s = g s) -> ssum f l = ssum g l.
Proof. induction l; cbn; intros; [reflexivity|]. rewrite H, IHl; auto. Qed.
Lemma ssum_add f g l : ssum (fun s => f s + g s) l = ssum f l + ssum g l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. lia. Qed.
Lemma ssum_le f g l : (forall s, In s l -> f s <= g s) -> ssum f l <= ssum g l.
Proof. induction l; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHl ltac:(intros; apply H; auto)). lia. Qed.

Lemma lsum_scount (key : osym -> Z) (w : Z -> Z) (S : list Z) (l : list osym) : NoDup S ->
  lsum (fun c => w c * scount (fun s => key s =? c) l) S = ssum (fun s => if existsb (Z.eqb (key s)) S then w (key s) else 0) l.
Proof.
  intros ND. induction l as [|s r IH]; cbn.
  - unfold scount; cbn. induction S; cbn; [reflexivity|]. inversion ND; subst. rewrite IHS; [lia|assumption].
  - unfold scount in *. cbn.
    rewrite (lsum_ext (fun c => w c * ((if key s =? c then 1 else 0) + ssum (fun s0 => if key s0 =? c then 1 else 0) r))
                      (fun c => (if c =? key s then w c else 0) + w c * ssum (fun s0 => if key s0 =? c then 1 else 0) r))
      by (intros c _; rewrite (Z.eqb_sym (key s) c); destruct (c =? key s); lia).
    rewrite lsum_add, IH. rewrite <- gsum_lsum.
    destruct (in_dec Z.eq_dec (key s) S) as [I|NI].
    + rewrite (gsum_pick w S (key s) ND I). replace (existsb (Z.eqb (key s)) S) with true; [lia|].
      symmetry. apply existsb_exists. exists (key s). rewrite Z.eqb_refl. auto.
    + rewrite (gsum_miss w S (key s) NI). replace (existsb (Z.eqb (key s)) S) with false; [lia|].
      symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists. intros (x & Ix & Ex). apply Z.eqb_eq in Ex. subst. tauto.
Qed.

Definition keyL (s : osym) : Z := match s with OLit c => c | OPair lc _ => lc end.
Definition keyD (s : osym) : Z := match s with OLit _ => -1 | OPair _ dc => dc end.


Section Sound.
Variable b : oblock.
Variable lbs : Z.
Hypothesis OK : oblock_ok b lbs.
Notation lenL := (ob_lenL b).
Notation lenD := (ob_lenD b).
Notation BC := (ob_BC b).
Notation BD := (ob_BD b).
Notation syms := (ob_syms b).

Lemma sym_ok_in s : In s syms -> sym_ok s.
Proof. intros I. pose proof (ok_syms b lbs OK) as F. rewrite Forall_forall in F. apply F. exact I. Qed.

Lemma fL_eq c : fL b c = scount (fun s => keyL s =? c) syms + (if c =? 256 then 1 else 0).
Proof.
  unfold fL. f_equal. unfold scount. apply ssum_ext. intros s I. destruct s; reflexivity.
Qed.
Lemma gD_eq d : 0 <= d -> gD b d = scount (fun s => keyD s =? d) syms.
Proof.
  intros Hd. unfold gD, scount. apply ssum_ext. intros s I. destruct s as [c|lc dc]; [|reflexivity]. cbn [keyD].
  replace (-1 =? d) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma gD_nonneg d : 0 <= gD b d.
Proof. unfold gD. apply scount_nonneg. Qed.

Lemma keyL_range s : In s syms -> (0 <= keyL s < 256 /\ exists c, s = OLit c) \/ (257 <= keyL s <= 285 /\ exists lc dc, s = OPair lc dc /\ 0 <= dc <= 29).
Proof. intros I. pose proof (sym_ok_in s I). destruct s; cbn in *; [left; split; [lia|eexists; reflexivity] | right; split; [lia|do 2 eexists; split; [reflexivity|lia]]]. Qed.

Lemma lsum_fL_w (w : Z -> Z) (lo : Z) (n : nat) :
  lsum (fun c => w c * fL b c) (zrange lo n) =
  ssum (fun s => if existsb (Z.eqb (keyL s)) (zrange lo n) then w (keyL s) else 0) syms
  + (if existsb (Z.eqb 256) (zrange lo n) then w 256 else 0).
Proof.
  rewrite (lsum_ext _ (fun c => w c * scount (fun s => keyL s =? c) syms + (if c =? 256 then w c else 0))) by (intros c _; rewrite fL_eq; destruct (c =? 256); lia).
  rewrite lsum_add, (lsum_scount keyL w) by apply zrange_nodup. f_equal.
  rewrite <- gsum_lsum. destruct (in_dec Z.eq_dec 256 (zrange lo n)) as [I|NI].
  - rewrite (gsum_pick w _ 256 (zrange_nodup lo n) I). replace (existsb (Z.eqb 256) (zrange lo n)) with true; [reflexivity|].
    symmetry. apply existsb_exists. exists 256. split; [exact I|reflexivity].
  - rewrite (gsum_miss w _ 256 NI). replace (existsb (Z.eqb 256) (zrange lo n)) with false; [reflexivity|].
    symmetry. apply Bool.not_true_iff_false. rewrite existsb_exists. intros (x & Ix & Ex). apply Z.eqb_eq in Ex. subst. tauto.
Qed.
Lemma existsb_zrange x lo n : existsb (Z.eqb x) (zrange lo n) = ((lo <=? x) && (x <? lo + Z.of_nat n)).
Proof.
  destruct (existsb (Z.eqb x) (zrange lo n)) eqn:E.
  - apply existsb_exists in E. destruct E as (y & Iy & Ey). apply Z.eqb_eq in Ey. subst. apply zrange_in in Iy. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
  - symmetry. apply Bool.not_true_iff_false. intros H. apply Bool.not_true_iff_false in E. apply E. apply existsb_exists. exists x. rewrite Z.eqb_refl. split; [|reflexivity].
    apply zrange_in. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma lsum_gD_w (w : Z -> Z) : lsum (fun d => w d * gD b d) (zrange 0 30) = ssum (fun s => match s with OPair _ dc => w dc | _ => 0 end) syms.
Proof.
  rewrite (lsum_ext _ (fun d => w d * scount (fun s => keyD s =? d) syms)) by (intros d Id; apply zrange_in in Id; rewrite gD_eq by lia; reflexivity).
  rewrite (lsum_scount keyD w) by apply zrange_nodup. apply ssum_ext. intros s I.
  rewrite existsb_zrange. destruct (keyL_range s I) as [(R & c & ->)|(R & lc & dc & -> & Rd)]; cbn [keyD keyL] in *.
  - reflexivity.
  - replace ((0 <=? dc) && (dc <? 0 + Z.of_nat 30)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma vP_eq : vP b = ssum (fun s => match s with OPair _ _ => 1 | _ => 0 end) syms.
Proof. unfold vP, scount. apply ssum_ext. intros s _. destruct s; reflexivity. Qed.


Lemma WL_eq : WL b = NSYM b + 1.
Proof.
  unfold WL.
  rewrite (lsum_ext (fL b) (fun c => 1 * scount (fun s => keyL s =? c) syms + (if c =? 256 then 1 else 0)) (zrange 0 286)) by (intros; rewrite fL_eq; lia).
  rewrite lsum_add. rewrite (lsum_scount keyL (fun _ => 1)) by apply zrange_nodup.
  rewrite <- gsum_lsum, (gsum_pick (fun _ => 1) _ 256 (zrange_nodup 0 286)) by (apply zrange_in; lia).
  unfold NSYM. enough (ssum (fun s => if existsb (Z.eqb (keyL s)) (zrange 0 286) then 1 else 0) syms = Z.of_nat (length syms)) by lia.
  rewrite (ssum_ext _ (fun _ => 1)); [generalize (ob_syms b); intros l; induction l; [reflexivity|cbn [ssum length]; rewrite Nat2Z.inj_succ; lia]|].
  intros s I. pose proof (sym_ok_in s I).
  replace (existsb (Z.eqb (keyL s)) (zrange 0 286)) with true; [reflexivity|]. symmetry. apply existsb_exists.
  exists (keyL s). rewrite Z.eqb_refl. split; [|reflexivity]. apply zrange_in. destruct s; cbn in *; lia.
Qed.
Lemma zrange_rangeZ lo n : zrange lo n = rangeZ lo n.
Proof.
  unfold zrange. revert lo. induction n as [|n IH]; intros lo; [reflexivity|].
  cbn [seq map rangeZ]. f_equal; [lia|]. rewrite <- seq_shift, map_map. rewrite <- (IH (lo + 1)). apply map_ext. intros; lia.
Qed.
Lemma lsum_zrange f lo n : lsum f (zrange lo n) = zsum f lo n.
Proof. rewrite zrange_rangeZ. apply lsum_zsum. Qed.
Lemma countZ_zsum (P : Z -> bool) lo n : countZ P (zrange lo n) = zsum (fun c => if P c then 1 else 0) lo n.
Proof. unfold countZ. apply lsum_zrange. Qed.
Lemma ffreq_nil F c : ffreq F [] c = F c. Proof. reflexivity. Qed.
Lemma TL_W zL : tree_facts zL 286 15 (fL b) [] -> g_W (zt_g zL) = NSYM b + 1.
Proof.
  intros TF. rewrite <- (sumW zL 286 15 (fL b) [] TF). change (Z.to_nat 286) with 286%nat.
  rewrite <- lsum_zrange. rewrite <- WL_eq. unfold WL. apply lsum_ext. intros; reflexivity.
Qed.
Lemma lenL_used c : 0 <= c < 286 -> 0 < fL b c -> 1 <= lenL c <= 15.
Proof.
  intros Hc U. destruct (ok_TL b lbs OK) as (zL & TF & _ & EL). rewrite EL by lia.
  apply (tlen_used zL 286 15 (fL b) [] TF c Hc). rewrite ffreq_nil. lia.
Qed.

Lemma forced_facts : NoDup (ob_forced b) /\ (length (ob_forced b) <= 2)%nat /\ (forall d, In d (ob_forced b) -> 0 <= d <= 2 /\ gD b d = 0).
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & _). destruct (tFl zD 30 15 (gD b) (ob_forced b) TF) as (A & B & C).
  split; [exact B|]. split; [exact A|]. intros d Hd. destruct (C d Hd) as (X & Y & W). lia.
Qed.
Lemma forcedD_spec d : forcedD b d = true <-> In d (ob_forced b).
Proof. unfold forcedD. apply existsb_In. Qed.
Lemma ffreqD d : ffreq (gD b) (ob_forced b) d = (if forcedD b d then 1 else gD b d).
Proof. reflexivity. Qed.

Lemma sum_gD : lsum (gD b) (zrange 0 30) = vP b.
Proof.
  rewrite vP_eq, <- (lsum_gD_w (fun _ => 1)). apply lsum_ext. intros; lia.
Qed.
Lemma TD_W zD : tree_facts zD 30 15 (gD b) (ob_forced b) -> g_W (zt_g zD) = WD b.
Proof.
  intros TF. rewrite <- (sumW zD 30 15 (gD b) (ob_forced b) TF). rewrite (sumW_F zD 30 15 (gD b) (ob_forced b) TF).
  change (Z.to_nat 30) with 30%nat. rewrite <- lsum_zrange, sum_gD. reflexivity.
Qed.
Lemma WD_le : WD b <= lbs + 1.
Proof.
  unfold WD. destruct forced_facts as (_ & LF & _). unfold vP.
  pose proof (scount_le_len (fun s => match s with OLit _ => false | OPair _ _ => true end) syms). pose proof (ok_N b _ OK). unfold NSYM in *. lia.
Qed.

Lemma D2 : 2 <= vV b.
Proof.
  destruct (ok_TD b lbs OK) as (zD & TF & _ & EL). pose proof (tused_two zD 30 15 (gD b) (ob_forced b) TF) as T.
  change (Z.to_nat 30) with 30%nat in T. unfold vV. destruct forced_facts as (ND & _ & FF).
  rewrite countZ_zsum.
  rewrite (zsum_ext _ (fun d => (if 0 <? gD b d then 1 else 0) + (if existsb (Z.eqb d) (ob_forced b) then 1 else 0))) in T.
  2:{ intros d Hd. rewrite ffreqD. unfold forcedD. pose proof (gD_nonneg d).
      destruct (existsb (Z.eqb d) (ob_forced b)) eqn:X.
      - apply existsb_In in X. destruct (FF d X). replace (0 <? gD b d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      - destruct (Z.ltb_spec 0 (gD b d)); destruct (Z.eqb_spec (gD b d) 0); lia. }
  rewrite zsum_add in T. rewrite <- (lsum_zrange (fun d => if existsb (Z.eqb d) (ob_forced b) then 1 else 0)) in T.
  rewrite (lsum_support (fun _ => 1) (zrange 0 30) (ob_forced b) (zrange_nodup 0 30) ND) in T.
  2:{ intros x Hx. apply zrange_in. destruct (FF x Hx). lia. }
  replace (lsum (fun _ => 1) (ob_forced b)) with (Z.of_nat (length (ob_forced b))) in T; [lia|].
  generalize (ob_forced b). intros l. induction l; [reflexivity|]. cbn [lsum length]. lia.
Qed.
Lemma bforced_facts : NoDup (ob_bforced b) /\ (length (ob_bforced b) <= 2)%nat /\ (forall x, In x (ob_bforced b) -> 0 <= x < 19 /\ BC x = 0).
Proof.
  destruct (ok_TB b lbs OK) as (zB & TF & _ & _). destruct (tFl zB 19 7 BC (ob_bforced b) TF) as (A & B & C).
  split; [exact B|]. split; [exact A|]. intros x Hx. destruct (C x Hx) as (X & Y & W). lia.
Qed.
Lemma BC'_eq x : BC' b x = BC x + (if existsb (Z.eqb x) (ob_bforced b) then 1 else 0).
Proof.
  unfold BC', ffreq. destruct (existsb (Z.eqb x) (ob_bforced b)) eqn:X; [|lia].
  apply existsb_In in X. destruct bforced_facts as (_ & _ & C). destruct (C x X). lia.
Qed.
Lemma BC_nonneg x : 0 <= x < 19 -> 0 <= BC x.
Proof.
  intros Hx. destruct (ok_TB b lbs OK) as (zB & TF & _ & _).
  pose proof (W_nonneg zB 19 7 BC (ob_bforced b) TF x Hx) as P. fold (BC' b) in P. rewrite BC'_eq in P.
  destruct (existsb (Z.eqb x) (ob_bforced b)) eqn:X; [|lia].
  apply existsb_In in X. destruct bforced_facts as (_ & _ & C). destruct (C x X). lia.
Qed.

Lemma BD_range x : 0 <= x < 19 -> 0 <= BD x <= 7.
Proof.
  intros Hx. destruct (ok_TB b lbs OK) as (zB & TF & _ & EB). rewrite EB by lia.
  destruct (Z.eq_dec (BC' b x) 0) as [Z0|NZ].
  - rewrite (tlen_unused zB 19 7 BC (ob_bforced b) TF x Hx Z0). lia.
  - pose proof (tlen_used zB 19 7 BC (ob_bforced b) TF x Hx NZ). lia.
Qed.

Variable prm : oprm.
Hypothesis PRM : prm_ok prm lbs b.
Local Notation LL := (p_LL prm).
Local Notation Ls := (lens prm).





Definition cntL (k : nat) (l : Z) : Z := countZ (fun c => usedLb b c && (lenL c =? l)) (lc_codes (lcl k)).
Definition wgtL (k : nat) (l : Z) : Z := lsum (fun c => if usedLb b c && (lenL c =? l) then fL b c else 0) (lc_codes (lcl k)).
Definition cntD (k : nat) (m : Z) : Z := countZ (fun d => usedDb b d && (lenD d =? m)) (dc_codes (dcl k)).
Definition wgtD (k : nat) (m : Z) : Z := lsum (fun d => if (0 <? gD b d) && (lenD d =? m) then gD b d else 0) (dc_codes (dcl k)).



















Lemma ssum_nonneg f l : (forall s, In s l -> 0 <= f s) -> 0 <= ssum f l.
Proof. induction l; cbn; intros; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IHl ltac:(intros; apply H; auto)). lia. Qed.

Lemma ssum_ge_member f l x : (forall s, In s l -> 0 <= f s) -> In x l -> f x <= ssum f l.
Proof.
  induction l as [|y r IH]; cbn; intros P I; [destruct I|]. destruct I as [->|I].
  - pose proof (ssum_nonneg f r ltac:(intros; apply P; auto)). lia.
  - pose proof (P y (or_introl eq_refl)). specialize (IH ltac:(intros; apply P; auto) I). lia.
Qed.
Lemma in_syms_fL s : In s syms -> 1 <= fL b (keyL s).
Proof.
  intros I. rewrite fL_eq. pose proof (ssum_ge_member (fun s' => if keyL s' =? keyL s then 1 else 0) syms s ltac:(intros s0 _; cbv beta; destruct (keyL s0 =? keyL s); lia) I) as X.
  cbv beta in X. rewrite Z.eqb_refl in X. unfold scount. destruct (keyL s =? 256); lia.
Qed.














End Sound.
