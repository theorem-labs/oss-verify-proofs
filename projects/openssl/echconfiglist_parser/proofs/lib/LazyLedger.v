(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => (if P lo then 1 else 0) + zcount P (lo + 1) n'
  end.

(* [comment removed for export] *)
Definition zmeasure (P : Z -> bool) (lo hi : Z) : Z := zcount P lo (Z.to_nat (hi - lo)).

Lemma zcount_bounds : forall P lo n, 0 <= zcount P lo n <= Z.of_nat n.
Proof.
  intros P lo n. revert lo. induction n as [|n IH]; intros lo; cbn [zcount]; [lia|].
  specialize (IH (lo + 1)). destruct (P lo); lia.
Qed.

Lemma zcount_split : forall P lo n1 n2,
  zcount P lo (n1 + n2) = zcount P lo n1 + zcount P (lo + Z.of_nat n1) n2.
Proof.
  intros P lo n1 n2. revert lo. induction n1 as [|n1 IH]; intros lo.
  - cbn [zcount Nat.add]. rewrite Z.add_0_r. lia.
  - cbn [zcount Nat.add]. rewrite IH.
    replace (lo + 1 + Z.of_nat n1) with (lo + Z.of_nat (S n1)) by lia. lia.
Qed.

Lemma zcount_ext : forall P Q lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = Q x) ->
  zcount P lo n = zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n as [|n IH]; intros lo H; cbn [zcount]; [reflexivity|].
  rewrite (H lo) by lia. rewrite (IH (lo + 1)) by (intros x Hx; apply H; lia). reflexivity.
Qed.

Lemma zcount_mono : forall P Q lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = true -> Q x = true) ->
  zcount P lo n <= zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n as [|n IH]; intros lo H; cbn [zcount]; [lia|].
  specialize (IH (lo + 1) ltac:(intros x Hx; apply H; lia)).
  destruct (P lo) eqn:EP.
  - rewrite (H lo) by (lia || exact EP). lia.
  - destruct (Q lo); lia.
Qed.

Lemma zcount_all : forall P lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = true) -> zcount P lo n = Z.of_nat n.
Proof.
  intros P lo n. revert lo. induction n as [|n IH]; intros lo H; cbn [zcount]; [reflexivity|].
  rewrite (H lo) by lia. rewrite (IH (lo + 1)) by (intros x Hx; apply H; lia). lia.
Qed.

Lemma zcount_none : forall P lo n,
  (forall x, lo <= x < lo + Z.of_nat n -> P x = false) -> zcount P lo n = 0.
Proof.
  intros P lo n. revert lo. induction n as [|n IH]; intros lo H; cbn [zcount]; [reflexivity|].
  rewrite (H lo) by lia. rewrite (IH (lo + 1)) by (intros x Hx; apply H; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma zcount_or_le : forall P Q lo n,
  zcount (fun x => P x || Q x) lo n <= zcount P lo n + zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n as [|n IH]; intros lo; cbn [zcount]; [lia|].
  specialize (IH (lo + 1)). destruct (P lo), (Q lo); cbn [orb]; lia.
Qed.

(* [comment removed for export] *)
Lemma zmeasure_empty : forall P lo hi, hi <= lo -> zmeasure P lo hi = 0.
Proof.
  intros P lo hi H. unfold zmeasure. replace (Z.to_nat (hi - lo)) with 0%nat by lia. reflexivity.
Qed.

Lemma zmeasure_bounds : forall P lo hi, 0 <= zmeasure P lo hi <= Z.max 0 (hi - lo).
Proof.
  intros P lo hi. unfold zmeasure. pose proof (zcount_bounds P lo (Z.to_nat (hi - lo))). lia.
Qed.

Lemma zmeasure_split : forall P lo mid hi,
  lo <= mid <= hi ->
  zmeasure P lo hi = zmeasure P lo mid + zmeasure P mid hi.
Proof.
  intros P lo mid hi H. unfold zmeasure.
  replace (Z.to_nat (hi - lo)) with (Z.to_nat (mid - lo) + Z.to_nat (hi - mid))%nat by lia.
  rewrite zcount_split. f_equal. f_equal. lia.
Qed.

Lemma zmeasure_ext : forall P Q lo hi,
  (forall x, lo <= x < hi -> P x = Q x) -> zmeasure P lo hi = zmeasure Q lo hi.
Proof.
  intros P Q lo hi H. unfold zmeasure. apply zcount_ext. intros x Hx. apply H. lia.
Qed.

Lemma zmeasure_mono : forall P Q lo hi,
  (forall x, lo <= x < hi -> P x = true -> Q x = true) -> zmeasure P lo hi <= zmeasure Q lo hi.
Proof.
  intros P Q lo hi H. unfold zmeasure. apply zcount_mono. intros x Hx. apply H. lia.
Qed.

Lemma zmeasure_all : forall P lo hi,
  lo <= hi -> (forall x, lo <= x < hi -> P x = true) -> zmeasure P lo hi = hi - lo.
Proof.
  intros P lo hi Hle H. unfold zmeasure. rewrite zcount_all; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma zmeasure_none : forall P lo hi,
  (forall x, lo <= x < hi -> P x = false) -> zmeasure P lo hi = 0.
Proof.
  intros P lo hi H. unfold zmeasure. apply zcount_none. intros x Hx. apply H. lia.
Qed.

Lemma zmeasure_or_le : forall P Q lo hi,
  zmeasure (fun x => P x || Q x) lo hi <= zmeasure P lo hi + zmeasure Q lo hi.
Proof. intros. unfold zmeasure. apply zcount_or_le. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lo (r : word * word) : Z := bv_unsigned (fst r).
Definition hi (r : word * word) : Z := bv_unsigned (fst r) + bv_unsigned (snd r).

Lemma lo_hi : forall r, lo r <= hi r.
Proof. intros [a n]. unfold lo, hi. cbn. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma lo_nonneg : forall r, 0 <= lo r.
Proof. intros [a n]. unfold lo. cbn. pose proof (bv_unsigned_in_range 64 a). lia. Qed.

Lemma hi_minus_lo : forall r, hi r - lo r = bv_unsigned (snd r).
Proof. intros [a n]. unfold lo, hi. cbn. lia. Qed.

(* [comment removed for export] *)
Definition zcovb (C : list (word * word)) (x : Z) : bool := existsb (zin_rangeb x) C.

Lemma zin_rangeb_iff : forall x r, zin_rangeb x r = true <-> lo r <= x < hi r.
Proof.
  intros x [a n]. unfold zin_rangeb, lo, hi. cbn [fst snd].
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma zcovb_true : forall C x, zcovb C x = true <-> exists r, In r C /\ lo r <= x < hi r.
Proof.
  intros C x. unfold zcovb. rewrite existsb_exists. split.
  - intros (r & Hin & Hr). exists r. split; [exact Hin | apply zin_rangeb_iff; exact Hr].
  - intros (r & Hin & Hr). exists r. split; [exact Hin | apply zin_rangeb_iff; exact Hr].
Qed.

Lemma zcovb_false : forall C x, zcovb C x = false <-> forall r, In r C -> ~ (lo r <= x < hi r).
Proof.
  intros C x. split.
  - intros H r Hin Hr. assert (zcovb C x = true) by (apply zcovb_true; eauto). congruence.
  - intros H. destruct (zcovb C x) eqn:E; [|reflexivity].
    apply zcovb_true in E. destruct E as (r & Hin & Hr). exfalso. exact (H r Hin Hr).
Qed.

Lemma zcovb_cons : forall c C x, zcovb (c :: C) x = zin_rangeb x c || zcovb C x.
Proof. reflexivity. Qed.

Lemma zcovb_app : forall C1 C2 x, zcovb (C1 ++ C2) x = zcovb C1 x || zcovb C2 x.
Proof. intros. unfold zcovb. apply existsb_app. Qed.

Lemma in_rangesb_zcovb : forall (a : word) C, in_rangesb a C = zcovb C (bv_unsigned a).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rem (e : word * word) (C : list (word * word)) : Z :=
  zmeasure (fun x => negb (zcovb C x)) (lo e) (hi e).

Fixpoint eagerZ (X C : list (word * word)) : Z :=
  match X with
  | [] => 0
  | e :: X' => rem e C + eagerZ X' C
  end.

Lemma eagerZ_app : forall X1 X2 C, eagerZ (X1 ++ X2) C = eagerZ X1 C + eagerZ X2 C.
Proof. induction X1 as [|e X1 IH]; intros; cbn [eagerZ app]; [lia | rewrite IH; lia]. Qed.

Lemma rem_bounds : forall e C, 0 <= rem e C <= bv_unsigned (snd e).
Proof.
  intros e C. unfold rem. pose proof (zmeasure_bounds (fun x => negb (zcovb C x)) (lo e) (hi e)).
  pose proof (lo_hi e). rewrite <- hi_minus_lo. lia.
Qed.

Lemma eagerZ_nonneg : forall X C, 0 <= eagerZ X C.
Proof. induction X as [|e X IH]; intros C; cbn [eagerZ]; [lia|]. pose proof (rem_bounds e C). specialize (IH C). lia. Qed.

(* [comment removed for export] *)
Lemma rem_covered : forall e C c,
  In c C -> lo c <= lo e -> hi e <= hi c -> rem e C = 0.
Proof.
  intros e C c Hin H1 H2. unfold rem. apply zmeasure_none. intros x Hx.
  apply negb_false_iff. apply zcovb_true. exists c. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma rem_free : forall e C,
  (forall c, In c C -> hi c <= lo e \/ hi e <= lo c) -> rem e C = bv_unsigned (snd e).
Proof.
  intros e C H. unfold rem. rewrite <- hi_minus_lo. apply zmeasure_all; [apply lo_hi|].
  intros x Hx. apply negb_true_iff. apply zcovb_false. intros r Hin Hr.
  destruct (H r Hin); lia.
Qed.

Lemma rem_nil : forall e, rem e [] = bv_unsigned (snd e).
Proof. intros e. apply rem_free. intros c []. Qed.

(* [comment removed for export] *)
Lemma rem_mono_cuts : forall e C C',
  (forall x, lo e <= x < hi e -> zcovb C x = true -> zcovb C' x = true) ->
  rem e C' <= rem e C.
Proof.
  intros e C C' H. unfold rem. apply zmeasure_mono. intros x Hx HC'.
  apply negb_true_iff in HC'. apply negb_true_iff.
  destruct (zcovb C x) eqn:E; [|reflexivity]. rewrite (H x Hx E) in HC'. discriminate.
Qed.

Lemma eagerZ_mono_cuts : forall X C C',
  (forall x, zcovb C x = true -> zcovb C' x = true) ->
  eagerZ X C' <= eagerZ X C.
Proof.
  intros X C C' H. induction X as [|e X IH]; cbn [eagerZ]; [lia|].
  pose proof (rem_mono_cuts e C C' ltac:(intros x _ Hc; exact (H x Hc))). lia.
Qed.

Lemma eagerZ_cuts_ext : forall X C C',
  (forall x, zcovb C x = zcovb C' x) -> eagerZ X C' = eagerZ X C.
Proof.
  intros X C C' H.
  pose proof (eagerZ_mono_cuts X C C' ltac:(intros x Hx; rewrite <- H; exact Hx)).
  pose proof (eagerZ_mono_cuts X C' C ltac:(intros x Hx; rewrite H; exact Hx)). lia.
Qed.

Lemma eagerZ_le_live : forall X C, eagerZ X C <= live_bytes X.
Proof.
  induction X as [|[a n] X IH]; intros C; cbn [eagerZ live_bytes]; [lia|].
  pose proof (rem_bounds (a, n) C). cbn [snd] in H. specialize (IH C). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition entry_nowrap (e : word * word) : Prop := hi e <= 2 ^ 64.
Definition entries_nowrap (X : list (word * word)) : Prop := forall e, In e X -> entry_nowrap e.

Lemma entries_nowrap_cons : forall e X,
  entries_nowrap (e :: X) <-> entry_nowrap e /\ entries_nowrap X.
Proof.
  intros e X. unfold entries_nowrap. split.
  - intros H. split; [apply H; left; reflexivity | intros e' He'; apply H; right; exact He'].
  - intros [He HX] e' [<-|He']; [exact He | exact (HX e' He')].
Qed.

Lemma entries_nowrap_app : forall X1 X2,
  entries_nowrap (X1 ++ X2) <-> entries_nowrap X1 /\ entries_nowrap X2.
Proof.
  intros X1 X2. unfold entries_nowrap. split.
  - intros H. split; intros e He; apply H; apply in_app_iff; auto.
  - intros [H1 H2] e He. apply in_app_iff in He. destruct He; auto.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_pieces : forall (a sz : word) (clo chi : Z) (F : word * word -> Z),
  entry_nowrap (a, sz) -> 0 <= clo -> clo <= chi ->
  (forall p, In p (iv_subtract a sz clo chi) ->
     (lo p = lo (a, sz) /\ hi p = Z.min (hi (a, sz)) clo /\ lo (a, sz) < clo)
     \/ (lo p = Z.max (lo (a, sz)) chi /\ hi p = hi (a, sz) /\ chi < hi (a, sz))) /\
  fold_right (fun p acc => F p + acc) 0 (iv_subtract a sz clo chi)
  = (if lo (a, sz) <? clo
     then F (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (clo - bv_unsigned a))) else 0)
    + (if chi <? hi (a, sz)
       then F (Z_to_bv 64 (Z.max (bv_unsigned a) chi),
               Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) chi))
       else 0).
Proof.
  intros a sz clo chi F Hnw Hclo Hcc. unfold entry_nowrap, lo, hi in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hsz.
  change (bv_modulus 64) with (2 ^ 64) in Ha, Hsz.
  unfold iv_subtract. cbn [fst snd].
  split.
  - intros p Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + destruct (bv_unsigned a <? clo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
      destruct Hin as [<- | []]. left. cbn [fst snd].
      rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    + destruct (chi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
      destruct Hin as [<- | []]. right. cbn [fst snd].
      rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (bv_unsigned a <? clo), (chi <? bv_unsigned a + bv_unsigned sz); cbn; lia.
Qed.

Lemma fold_right_add_app : forall (A : Type) (F : A -> Z) l1 l2,
  fold_right (fun p acc => F p + acc) 0 (l1 ++ l2)
  = fold_right (fun p acc => F p + acc) 0 l1 + fold_right (fun p acc => F p + acc) 0 l2.
Proof. intros A F l1 l2. induction l1 as [|x l1 IH]; cbn; [lia | rewrite IH; lia]. Qed.

Lemma eagerZ_fold : forall X C, eagerZ X C = fold_right (fun p acc => rem p C + acc) 0 X.
Proof. induction X as [|e X IH]; intros C; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma rem_left_piece : forall (a sz : word) (cl : Z) C,
  bv_unsigned a < cl ->
  rem (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (cl - bv_unsigned a))) C
  = zmeasure (fun x => negb (zcovb C x)) (bv_unsigned a) (Z.min (bv_unsigned a + bv_unsigned sz) cl).
Proof.
  intros a sz cl C Hlt. unfold rem, lo, hi. cbn [fst snd].
  pose proof (bv_unsigned_in_range 64 sz) as Hsz. change (bv_modulus 64) with (2 ^ 64) in Hsz.
  rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  f_equal. lia.
Qed.

Lemma rem_right_piece : forall (a sz : word) (ch : Z) C,
  0 <= ch -> ch < bv_unsigned a + bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2 ^ 64 ->
  rem (Z_to_bv 64 (Z.max (bv_unsigned a) ch),
       Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) ch)) C
  = zmeasure (fun x => negb (zcovb C x)) (Z.max (bv_unsigned a) ch) (bv_unsigned a + bv_unsigned sz).
Proof.
  intros a sz ch C Hch Hlt Hnw. unfold rem, lo, hi. cbn [fst snd].
  pose proof (bv_unsigned_in_range 64 sz) as Hsz. change (bv_modulus 64) with (2 ^ 64) in Hsz.
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2 ^ 64) in Ha.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma rem_cons_cut : forall (a sz : word) (c : word * word) C,
  entry_nowrap (a, sz) ->
  rem (a, sz) (c :: C)
  = fold_right (fun p acc => rem p C + acc) 0 (iv_subtract a sz (lo c) (hi c)).
Proof.
  intros a sz c C Hnw. unfold entry_nowrap, hi in Hnw. cbn [fst snd] in Hnw.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hsz.
  change (bv_modulus 64) with (2 ^ 64) in Ha, Hsz.
  pose proof (lo_hi c) as Hc. pose proof (lo_nonneg c) as Hc0.
  unfold iv_subtract. rewrite fold_right_add_app.
  unfold rem at 1. unfold lo at 1. unfold hi at 1. cbn [fst snd].
  set (P := fun x => negb (zcovb (c :: C) x)).
  set (Q := fun x => negb (zcovb C x)).
  set (ea := bv_unsigned a) in *. set (esz := bv_unsigned sz) in *.
  set (cl := lo c) in *. set (ch := hi c) in *.
  set (m1 := Z.min (ea + esz) (Z.max ea cl)).
  set (m2 := Z.min (ea + esz) (Z.max ea ch)).
  rewrite (zmeasure_split P ea m1 (ea + esz)) by lia.
  rewrite (zmeasure_split P m1 m2 (ea + esz)) by lia.
  rewrite (zmeasure_none P m1 m2).
  2:{ intros x Hx. unfold P. rewrite zcovb_cons. apply negb_false_iff. apply orb_true_iff. left.
      apply zin_rangeb_iff. fold cl ch. lia. }
  assert (HPQ : forall x, x < cl \/ ch <= x -> P x = Q x).
  { intros x Hx. unfold P, Q. rewrite zcovb_cons.
    destruct (zin_rangeb x c) eqn:E; [|reflexivity].
    apply zin_rangeb_iff in E. fold cl ch in E. lia. }
  rewrite (zmeasure_ext P Q ea m1) by (intros x Hx; apply HPQ; lia).
  rewrite (zmeasure_ext P Q m2 (ea + esz)) by (intros x Hx; apply HPQ; lia).
  f_equal; [|rewrite Z.add_0_l].
  - destruct (ea <? cl) eqn:E; cbn [fold_right].
    + apply Z.ltb_lt in E. rewrite Z.add_0_r. unfold ea, esz. rewrite (rem_left_piece a sz cl C) by lia.
      fold ea esz Q. f_equal. lia.
    + apply Z.ltb_ge in E. apply zmeasure_empty. lia.
  - destruct (ch <? ea + esz) eqn:E; cbn [fold_right].
    + apply Z.ltb_lt in E. rewrite Z.add_0_r. unfold ea, esz. rewrite (rem_right_piece a sz ch C) by lia.
      fold ea esz Q. f_equal. lia.
    + apply Z.ltb_ge in E. apply zmeasure_empty. lia.
Qed.

Lemma maps_subtract_app : forall X1 X2 clo chi,
  maps_subtract (X1 ++ X2) clo chi = maps_subtract X1 clo chi ++ maps_subtract X2 clo chi.
Proof.
  induction X1 as [|[a sz] X1 IH]; intros; cbn [maps_subtract app]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma maps_subtract_nowrap : forall X clo chi,
  entries_nowrap X -> 0 <= clo -> clo <= chi -> entries_nowrap (maps_subtract X clo chi).
Proof.
  induction X as [|[a sz] X IH]; intros clo chi HX Hclo Hcc; cbn [maps_subtract].
  - intros e [].
  - apply entries_nowrap_cons in HX. destruct HX as [He HX].
    apply entries_nowrap_app. split; [|exact (IH clo chi HX Hclo Hcc)].
    intros p Hp.
    destruct (iv_subtract_pieces a sz clo chi (fun _ => 0) He Hclo Hcc) as [Hpieces _].
    unfold entry_nowrap in *. destruct (Hpieces p Hp) as [(H1 & H2 & H3) | (H1 & H2 & H3)]; lia.
Qed.

Lemma eagerZ_cons_cut : forall X c C,
  entries_nowrap X ->
  eagerZ X (c :: C) = eagerZ (maps_subtract X (lo c) (hi c)) C.
Proof.
  induction X as [|[a sz] X IH]; intros c C HX; cbn [eagerZ maps_subtract]; [reflexivity|].
  apply entries_nowrap_cons in HX. destruct HX as [He HX].
  rewrite eagerZ_app, (IH c C HX), (rem_cons_cut a sz c C He), <- eagerZ_fold. reflexivity.
Qed.

Theorem live_bytes_msa : forall C X,
  entries_nowrap X ->
  live_bytes (maps_subtract_all X C) = eagerZ X C.
Proof.
  induction C as [|[ca cn] C IH]; intros X HX.
  - cbn [maps_subtract_all]. induction X as [|[a n] X IHX]; cbn [live_bytes eagerZ]; [reflexivity|].
    apply entries_nowrap_cons in HX. destruct HX as [_ HX].
    rewrite (IHX HX), rem_nil. reflexivity.
  - cbn [maps_subtract_all]. rewrite (eagerZ_cons_cut X (ca, cn) C HX).
    apply IH. apply maps_subtract_nowrap; [exact HX | apply lo_nonneg | apply lo_hi].
Qed.

Lemma maps_subtract_all_app : forall X C1 C2,
  maps_subtract_all X (C1 ++ C2) = maps_subtract_all (maps_subtract_all X C1) C2.
Proof.
  intros X C1; revert X; induction C1 as [|[a n] C1 IH]; intros X C2; cbn [maps_subtract_all app];
    [reflexivity | apply IH].
Qed.

(* [comment removed for export] *)
Theorem eager_used_eq : forall m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  eager_used m = eagerZ (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m).
Proof.
  intros m HX. unfold eager_used, vm_backed_maps.
  rewrite <- maps_subtract_all_app. apply live_bytes_msa. exact HX.
Qed.

Corollary eager_used_le_live_bytes : forall m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  eager_used m <= live_bytes (vm_maps (m_vmmaps m)).
Proof. intros m HX. rewrite (eager_used_eq m HX). apply eagerZ_le_live. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zinb (l h x : Z) : bool := (l <=? x) && (x <? h).

Lemma zinb_true : forall l h x, zinb l h x = true <-> l <= x < h.
Proof. intros. unfold zinb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma zinb_false : forall l h x, zinb l h x = false <-> ~ (l <= x < h).
Proof.
  intros l h x. destruct (zinb l h x) eqn:E.
  - apply zinb_true in E. split; [discriminate | tauto].
  - split; [|reflexivity]. intros _ Hx. apply zinb_true in Hx. congruence.
Qed.

(* [comment removed for export] *)
Lemma zcovb_iv_subtract : forall (a sz : word) l h x,
  entry_nowrap (a, sz) -> 0 <= l -> l <= h ->
  zcovb (iv_subtract a sz l h) x = zin_rangeb x (a, sz) && negb (zinb l h x).
Proof.
  intros a sz l h x Hnw Hl Hlh.
  destruct (iv_subtract_pieces a sz l h (fun _ => 0) Hnw Hl Hlh) as [Hp _].
  unfold entry_nowrap, lo, hi in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hsz.
  change (bv_modulus 64) with (2 ^ 64) in Ha, Hsz.
  apply Bool.eq_true_iff_eq. rewrite andb_true_iff, negb_true_iff, zinb_false, zin_rangeb_iff, zcovb_true.
  unfold lo, hi. cbn [fst snd]. split.
  - intros (p & Hin & Hx). destruct (Hp p Hin) as [(H1 & H2 & H3) | (H1 & H2 & H3)];
      unfold lo, hi in H1, H2, H3; cbn [fst snd] in H1, H2, H3; lia.
  - intros [Hx Hout]. unfold iv_subtract. cbn [fst snd].
    destruct (Z.lt_ge_cases x l) as [Hxl | Hxl].
    + exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (l - bv_unsigned a))). split.
      * apply in_app_iff. left. destruct (bv_unsigned a <? l) eqn:E; [left; reflexivity|].
        apply Z.ltb_ge in E. lia.
      * cbn [fst snd]. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
    + assert (Hxh : h <= x) by lia.
      exists (Z_to_bv 64 (Z.max (bv_unsigned a) h), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) h)). split.
      * apply in_app_iff. right. destruct (h <? bv_unsigned a + bv_unsigned sz) eqn:E; [left; reflexivity|].
        apply Z.ltb_ge in E. lia.
      * cbn [fst snd]. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma zcovb_maps_subtract : forall C l h x,
  entries_nowrap C -> 0 <= l -> l <= h ->
  zcovb (maps_subtract C l h) x = zcovb C x && negb (zinb l h x).
Proof.
  induction C as [|[a sz] C IH]; intros l h x HC Hl Hlh; cbn [maps_subtract]; [reflexivity|].
  apply entries_nowrap_cons in HC. destruct HC as [He HC].
  rewrite zcovb_app, zcovb_cons, (IH l h x HC Hl Hlh), (zcovb_iv_subtract a sz l h x He Hl Hlh).
  destruct (zin_rangeb x (a, sz)), (zcovb C x), (zinb l h x); reflexivity.
Qed.

Lemma maps_subtract_In : forall C l h p,
  entries_nowrap C -> 0 <= l -> l <= h ->
  In p (maps_subtract C l h) ->
  exists c, In c C /\ lo c <= lo p /\ hi p <= hi c /\ (hi p <= l \/ h <= lo p).
Proof.
  induction C as [|[a sz] C IH]; intros l h p HC Hl Hlh Hin; cbn [maps_subtract] in Hin; [destruct Hin|].
  apply entries_nowrap_cons in HC. destruct HC as [He HC].
  apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - destruct (iv_subtract_pieces a sz l h (fun _ => 0) He Hl Hlh) as [Hp _].
    exists (a, sz). split; [left; reflexivity|].
    pose proof (lo_hi (a, sz)).
    destruct (Hp p Hin) as [(H1 & H2 & H3) | (H1 & H2 & H3)]; lia.
  - destruct (IH l h p HC Hl Hlh Hin) as (c & Hc & H1). exists c. split; [right; exact Hc | exact H1].
Qed.

(* [comment removed for export] *)
Lemma map_remove_In : forall X (a : word) p, In p (map_remove X a) -> In p X /\ fst p <> a.
Proof.
  intros X a p H. unfold map_remove in H. apply filter_In in H. destruct H as [Hin Hb].
  split; [exact Hin|]. intros E. subst. unfold bv_eqb in Hb. rewrite Z.eqb_refl in Hb. discriminate.
Qed.

Lemma entries_nowrap_map_remove : forall X a, entries_nowrap X -> entries_nowrap (map_remove X a).
Proof. intros X a H p Hp. apply H. exact (proj1 (map_remove_In X a p Hp)). Qed.

Lemma lazy_interior_sub : forall (a n : word) p,
  entry_nowrap (a, n) ->
  In p (lazy_interior a n) -> lo (a, n) <= lo p /\ hi p <= hi (a, n).
Proof.
  intros a n p Hnw Hin. unfold entry_nowrap, hi in Hnw. cbn [fst snd] in Hnw. unfold lazy_interior in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 n) as Hn.
  change (bv_modulus 64) with (2 ^ 64) in Ha, Hn.
  set (l := bv_unsigned a) in *. set (sz := bv_unsigned n) in *.
  assert (Hps : 0 < page_size) by (unfold page_size; lia).
  pose proof (Z.div_mod (l + page_size - 1) page_size ltac:(lia)).
  pose proof (Z.mod_pos_bound (l + page_size - 1) page_size ltac:(lia)).
  pose proof (Z.div_mod (l + sz) page_size ltac:(lia)).
  pose proof (Z.mod_pos_bound (l + sz) page_size ltac:(lia)).
  set (lo' := (l + page_size - 1) / page_size * page_size) in *.
  set (hi' := (l + sz) / page_size * page_size) in *.
  destruct (lo' <? hi') eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
  destruct Hin as [<- | []]. unfold lo, hi. cbn [fst snd]. fold l sz.
  assert (Hhi' : hi' <= l + sz) by lia.
  assert (Hlo' : l <= lo') by lia.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma entries_nowrap_lazy_interior : forall (a n : word),
  entry_nowrap (a, n) -> entries_nowrap (lazy_interior a n).
Proof.
  intros a n H p Hp. pose proof (lazy_interior_sub a n p H Hp). unfold entry_nowrap in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint nooverlap (X : list (word * word)) : Prop :=
  match X with
  | [] => True
  | e :: X' => (forall e', In e' X' -> hi e <= lo e' \/ hi e' <= lo e) /\ nooverlap X'
  end.

Lemma nooverlap_cons_intro : forall e X,
  (forall e', In e' X -> hi e <= lo e' \/ hi e' <= lo e) -> nooverlap X -> nooverlap (e :: X).
Proof. intros; cbn; auto. Qed.

(* [comment removed for export] *)
Lemma region_free_disjoint : forall X (a n : word) e,
  region_free X a n = true -> In e X -> 0 < bv_unsigned n -> 0 < bv_unsigned (snd e) ->
  hi (a, n) <= lo e \/ hi e <= lo (a, n).
Proof.
  intros X a n [b s] Hrf Hin Hn Hs.
  pose proof (region_free_In X a n b s Hrf Hin) as Hov.
  unfold iv_overlap in Hov. unfold lo, hi. cbn [fst snd] in *.
  apply andb_false_iff in Hov. destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma region_free_disjoint' : forall X (a n : word) e,
  region_free X a n = true -> In e X ->
  hi (a, n) <= lo e \/ hi e <= lo (a, n) \/ bv_unsigned n = 0 \/ bv_unsigned (snd e) = 0.
Proof.
  intros X a n e Hrf Hin.
  pose proof (bv_unsigned_in_range 64 n). pose proof (bv_unsigned_in_range 64 (snd e)).
  destruct (Z.eq_dec (bv_unsigned n) 0); [tauto|].
  destruct (Z.eq_dec (bv_unsigned (snd e)) 0); [tauto|].
  pose proof (region_free_disjoint X a n e Hrf Hin ltac:(lia) ltac:(lia)). tauto.
Qed.

Lemma filter_sublist_nooverlap : forall f X, nooverlap X -> nooverlap (List.filter f X).
Proof.
  induction X as [|e X IH]; cbn; intros H; [exact I|].
  destruct H as [He HX]. destruct (f e); cbn.
  - split; [|exact (IH HX)]. intros e' Hin. apply filter_In in Hin. apply He. tauto.
  - exact (IH HX).
Qed.

Lemma nooverlap_map_remove : forall X a, nooverlap X -> nooverlap (map_remove X a).
Proof. intros X a. unfold map_remove. apply filter_sublist_nooverlap. Qed.

(* [comment removed for export] *)
Lemma eagerZ_mono_cuts_on : forall X C C',
  (forall e x, In e X -> lo e <= x < hi e -> zcovb C x = true -> zcovb C' x = true) ->
  eagerZ X C' <= eagerZ X C.
Proof.
  intros X C C' H. induction X as [|e X IH]; cbn [eagerZ]; [lia|].
  pose proof (rem_mono_cuts e C C' ltac:(intros x Hx Hc; exact (H e x (or_introl eq_refl) Hx Hc))).
  specialize (IH ltac:(intros e' x Hin; apply H; right; exact Hin)). lia.
Qed.

Lemma eagerZ_cuts_ext_on : forall X C C',
  (forall e x, In e X -> lo e <= x < hi e -> zcovb C x = zcovb C' x) ->
  eagerZ X C' = eagerZ X C.
Proof.
  intros X C C' H.
  pose proof (eagerZ_mono_cuts_on X C C' ltac:(intros e x He Hx Hc; rewrite <- (H e x He Hx); exact Hc)).
  pose proof (eagerZ_mono_cuts_on X C' C ltac:(intros e x He Hx Hc; rewrite (H e x He Hx); exact Hc)). lia.
Qed.

(* [comment removed for export] *)
Lemma rem_uncover_le : forall e C C' l h,
  l <= h ->
  (forall x, lo e <= x < hi e -> ~ (l <= x < h) -> zcovb C x = true -> zcovb C' x = true) ->
  rem e C' <= rem e C + zmeasure (zinb l h) (lo e) (hi e).
Proof.
  intros e C C' l h Hlh H. unfold rem.
  etransitivity; [|apply (zmeasure_or_le (fun x => negb (zcovb C x)) (zinb l h))].
  apply zmeasure_mono. intros x Hx HC'. apply orb_true_iff.
  destruct (zinb l h x) eqn:E; [right; reflexivity | left].
  apply zinb_false in E. apply negb_true_iff. apply negb_true_iff in HC'.
  destruct (zcovb C x) eqn:EC; [|reflexivity]. rewrite (H x Hx E EC) in HC'. discriminate.
Qed.

Lemma zmeasure_zinb_disjoint : forall l h a b,
  (h <= a \/ b <= l) -> zmeasure (zinb l h) a b = 0.
Proof.
  intros l h a b H. apply zmeasure_none. intros x Hx. apply zinb_false. lia.
Qed.

Lemma zmeasure_zinb_le : forall l h a b, l <= h -> zmeasure (zinb l h) a b <= h - l.
Proof.
  intros l h a b Hlh.
  destruct (Z.le_gt_cases b a) as [Hba | Hab].
  { rewrite zmeasure_empty by lia. lia. }
  (* [comment removed for export] *)
  set (m1 := Z.min b (Z.max a l)). set (m2 := Z.min b (Z.max a h)).
  rewrite (zmeasure_split _ a m1 b) by lia.
  rewrite (zmeasure_split _ m1 m2 b) by lia.
  rewrite (zmeasure_none _ a m1) by (intros x Hx; apply zinb_false; lia).
  rewrite (zmeasure_none _ m2 b) by (intros x Hx; apply zinb_false; lia).
  pose proof (zmeasure_bounds (zinb l h) m1 m2). lia.
Qed.

(* [comment removed for export] *)
Theorem eagerZ_uncover_le : forall X C C' e0 l h,
  nooverlap X -> In e0 X -> lo e0 <= l -> l <= h -> h <= hi e0 ->
  (forall x, ~ (l <= x < h) -> zcovb C x = true -> zcovb C' x = true) ->
  eagerZ X C' <= eagerZ X C + (h - l).
Proof.
  induction X as [|e X IH]; intros C C' e0 l h HX Hin H1 H2 H3 Hcov; [destruct Hin|].
  cbn [eagerZ]. destruct HX as [He HX].
  destruct Hin as [Ee | Hin].
  - subst e.
    pose proof (rem_uncover_le e0 C C' l h H2 ltac:(intros x _ Hn Hc; exact (Hcov x Hn Hc))) as HA.
    pose proof (zmeasure_zinb_le l h (lo e0) (hi e0) H2) as HB.
    assert (eagerZ X C' <= eagerZ X C); [|lia].
    apply eagerZ_mono_cuts_on. intros e' x Hin' Hx Hc. apply Hcov; [|exact Hc].
    destruct (He e' Hin'); lia.
  - pose proof (IH C C' e0 l h HX Hin H1 H2 H3 Hcov) as HA.
    assert (rem e C' <= rem e C); [|lia].
    pose proof (rem_uncover_le e C C' l h H2 ltac:(intros x _ Hn Hc; exact (Hcov x Hn Hc))) as HB.
    rewrite (zmeasure_zinb_disjoint l h (lo e) (hi e)) in HB; [lia|].
    destruct (He e0 Hin); lia.
Qed.

(* [comment removed for export] *)
Lemma eagerZ_map_remove_le : forall X a C, eagerZ (map_remove X a) C <= eagerZ X C.
Proof.
  intros X a C. unfold map_remove. induction X as [|e X IH]; cbn; [lia|].
  pose proof (rem_bounds e C). destruct (negb (bv_eqb (fst e) a)); cbn [eagerZ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ModelOps.

(* [comment removed for export] *)
Definition cuts (m : Model) : list (word * word) := vm_noaccess (m_vmmaps m) ++ m_vm_lazy m.

Lemma eager_used_cuts : forall m,
  entries_nowrap (vm_maps (m_vmmaps m)) -> eager_used m = eagerZ (vm_maps (m_vmmaps m)) (cuts m).
Proof. intros m H. apply eager_used_eq. exact H. Qed.

(* [comment removed for export] *)
Lemma with_mmap_backing_lazy : forall flags a n m,
  m_vm_lazy (with_mmap_backing flags a n m)
  = (if mmap_noreserve_b flags then lazy_interior a n else []) ++ m_vm_lazy m.
Proof.
  intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [|reflexivity].
  apply m_vm_lazy_vm_add_lazy.
Qed.

Lemma with_mmap_backing_materialized : forall flags a n m,
  m_vm_materialized (with_mmap_backing flags a n m) = m_vm_materialized m.
Proof.
  intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [apply m_vm_materialized_vm_add_lazy | reflexivity].
Qed.

Lemma with_mmap_backing_vmmaps : forall flags a n m,
  m_vmmaps (with_mmap_backing flags a n m) = m_vmmaps m.
Proof.
  intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [apply m_vmmaps_vm_add_lazy | reflexivity].
Qed.

Lemma with_mmap_backing_nonvm : forall flags a n m,
  m_fd (with_mmap_backing flags a n m) = m_fd m
  /\ m_io (with_mmap_backing flags a n m) = m_io m
  /\ m_fsys (with_mmap_backing flags a n m) = m_fsys m
  /\ m_proc (with_mmap_backing flags a n m) = m_proc m
  /\ m_lim (with_mmap_backing flags a n m) = m_lim m
  /\ m_time (with_mmap_backing flags a n m) = m_time m.
Proof.
  intros flags a n [fd [maps lazy mat] io fs proc lim tm]. unfold with_mmap_backing, vm_add_lazy.
  destruct (mmap_noreserve_b flags); cbn; repeat split; reflexivity.
Qed.

Lemma vm_forget_range_nonvm : forall l h m,
  m_fd (vm_forget_range l h m) = m_fd m
  /\ m_io (vm_forget_range l h m) = m_io m
  /\ m_fsys (vm_forget_range l h m) = m_fsys m
  /\ m_proc (vm_forget_range l h m) = m_proc m
  /\ m_lim (vm_forget_range l h m) = m_lim m
  /\ m_time (vm_forget_range l h m) = m_time m.
Proof. intros l h [fd [maps lazy mat] io fs proc lim tm]. cbn. repeat split; reflexivity. Qed.

Lemma with_vmmaps_nonvm : forall h' m,
  m_fd (with_vmmaps h' m) = m_fd m
  /\ m_io (with_vmmaps h' m) = m_io m
  /\ m_fsys (with_vmmaps h' m) = m_fsys m
  /\ m_proc (with_vmmaps h' m) = m_proc m
  /\ m_lim (with_vmmaps h' m) = m_lim m
  /\ m_time (with_vmmaps h' m) = m_time m.
Proof. intros h' [fd [maps lazy mat] io fs proc lim tm]. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)

Definition grant_vmmaps (h : VmMaps) (a n : word) (na : bool) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
    (if na then (a, n) :: vm_noaccess h else vm_noaccess h)
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition grant_model (flags a n : word) (na : bool) (m : Model) : Model :=
  with_mmap_backing flags a n (with_vmmaps (grant_vmmaps (m_vmmaps m) a n na) m).

Lemma grant_model_vmmaps : forall flags a n na m,
  m_vmmaps (grant_model flags a n na m) = grant_vmmaps (m_vmmaps m) a n na.
Proof. intros. unfold grant_model. rewrite with_mmap_backing_vmmaps. apply m_vmmaps_with_vmmaps. Qed.

Lemma grant_model_lazy : forall flags a n na m,
  m_vm_lazy (grant_model flags a n na m)
  = (if mmap_noreserve_b flags then lazy_interior a n else []) ++ m_vm_lazy m.
Proof. intros. unfold grant_model. rewrite with_mmap_backing_lazy, m_vm_lazy_with_vmmaps. reflexivity. Qed.

Lemma grant_model_materialized : forall flags a n na m,
  m_vm_materialized (grant_model flags a n na m) = m_vm_materialized m.
Proof. intros. unfold grant_model. rewrite with_mmap_backing_materialized. apply m_vm_materialized_with_vmmaps. Qed.

(* [comment removed for export] *)
Lemma eager_used_grant : forall flags a n na m,
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap (a, n) ->
  eager_used (grant_model flags a n na m)
  = rem (a, n) (cuts (grant_model flags a n na m))
    + eagerZ (vm_maps (m_vmmaps m)) (cuts (grant_model flags a n na m)).
Proof.
  intros flags a n na m HX He.
  rewrite eager_used_cuts by (rewrite grant_model_vmmaps; cbn; apply entries_nowrap_cons; auto).
  rewrite grant_model_vmmaps. reflexivity.
Qed.

Lemma cuts_grant : forall flags a n na m x,
  zcovb (cuts (grant_model flags a n na m)) x
  = (if na then zin_rangeb x (a, n) else false)
    || zcovb (if mmap_noreserve_b flags then lazy_interior a n else []) x
    || zcovb (cuts m) x.
Proof.
  intros flags a n na m x. unfold cuts. rewrite grant_model_vmmaps, grant_model_lazy.
  destruct na; cbn [vm_noaccess grant_vmmaps app]; rewrite ?zcovb_cons; repeat rewrite zcovb_app;
  destruct (zin_rangeb x (a, n)), (zcovb (vm_noaccess (m_vmmaps m)) x),
    (zcovb (if mmap_noreserve_b flags then lazy_interior a n else []) x), (zcovb (m_vm_lazy m) x); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eager_used_grant_rw_le : forall flags a n m,
  mmap_noreserve_b flags = false ->
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap (a, n) ->
  eager_used (grant_model flags a n false m) <= eager_used m + bv_unsigned n.
Proof.
  intros flags a n m Hnr HX He. rewrite (eager_used_grant flags a n false m HX He), (eager_used_cuts m HX).
  pose proof (rem_bounds (a, n) (cuts (grant_model flags a n false m))) as Hr. cbn [snd] in Hr.
  rewrite (eagerZ_cuts_ext (vm_maps (m_vmmaps m)) (cuts m) (cuts (grant_model flags a n false m))); [lia|].
  intros x. rewrite cuts_grant, Hnr. reflexivity.
Qed.

Lemma eager_used_grant_rw_eq : forall flags a n m,
  mmap_noreserve_b flags = false ->
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap (a, n) ->
  (forall c, In c (cuts m) -> hi c <= lo (a, n) \/ hi (a, n) <= lo c) ->
  eager_used (grant_model flags a n false m) = eager_used m + bv_unsigned n.
Proof.
  intros flags a n m Hnr HX He Hfree. rewrite (eager_used_grant flags a n false m HX He), (eager_used_cuts m HX).
  assert (Hc : forall x, zcovb (cuts m) x = zcovb (cuts (grant_model flags a n false m)) x)
    by (intros x; rewrite cuts_grant, Hnr; reflexivity).
  rewrite (eagerZ_cuts_ext _ _ _ Hc).
  rewrite (rem_free (a, n)); [cbn [snd]; lia|].
  intros c Hin. apply Hfree. unfold cuts in Hin |- *.
  rewrite grant_model_vmmaps, grant_model_lazy, Hnr in Hin. cbn in Hin. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma eager_used_grant_covered_le : forall flags a n na m,
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap (a, n) ->
  (na = true \/ (mmap_noreserve_b flags = true /\ lazy_interior a n = [(a, n)])) ->
  eager_used (grant_model flags a n na m) <= eager_used m.
Proof.
  intros flags a n na m HX He Hcov. rewrite (eager_used_grant flags a n na m HX He), (eager_used_cuts m HX).
  rewrite (rem_covered (a, n) (cuts (grant_model flags a n na m)) (a, n)); [| |lia|lia].
  - pose proof (eagerZ_mono_cuts (vm_maps (m_vmmaps m)) (cuts m) (cuts (grant_model flags a n na m))
                  ltac:(intros x Hx; rewrite cuts_grant, Hx, !orb_true_r; reflexivity)). lia.
  - unfold cuts. rewrite grant_model_vmmaps, grant_model_lazy. apply in_app_iff.
    destruct Hcov as [-> | [-> ->]]; [left; left; reflexivity | right; left; reflexivity].
Qed.

Lemma eager_used_grant_covered_eq : forall flags a n na m,
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap (a, n) ->
  (na = true \/ (mmap_noreserve_b flags = true /\ lazy_interior a n = [(a, n)])) ->
  (forall e, In e (vm_maps (m_vmmaps m)) -> hi e <= lo (a, n) \/ hi (a, n) <= lo e) ->
  eager_used (grant_model flags a n na m) = eager_used m.
Proof.
  intros flags a n na m HX He Hcov Hfree. rewrite (eager_used_grant flags a n na m HX He), (eager_used_cuts m HX).
  rewrite (rem_covered (a, n) (cuts (grant_model flags a n na m)) (a, n)); [| |lia|lia].
  - rewrite (eagerZ_cuts_ext_on (vm_maps (m_vmmaps m)) (cuts m) (cuts (grant_model flags a n na m))); [lia|].
    intros e x Hin Hx. rewrite cuts_grant.
    assert (Hna : zin_rangeb x (a, n) = false).
    { apply Bool.not_true_is_false. intros H. apply zin_rangeb_iff in H. destruct (Hfree e Hin); lia. }
    assert (Hli : zcovb (lazy_interior a n) x = false).
    { apply zcovb_false. intros r Hr. pose proof (lazy_interior_sub a n r He Hr). destruct (Hfree e Hin); lia. }
    destruct na; rewrite ?Hna; destruct (mmap_noreserve_b flags); rewrite ?Hli; reflexivity.
  - unfold cuts. rewrite grant_model_vmmaps, grant_model_lazy. apply in_app_iff.
    destruct Hcov as [-> | [-> ->]]; [left; left; reflexivity | right; left; reflexivity].
Qed.

(* [comment removed for export] *)

Definition commit_vmmaps (h : VmMaps) (addr n : word) (na : bool) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
    ((if na then [(addr, n)] else [])
       ++ maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition commit_model (flags addr n : word) (na : bool) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (commit_vmmaps (m_vmmaps m) addr n na) m).

(* [comment removed for export] *)
Lemma mmap_fixed_rw_commit_model : forall flags addr n m,
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)
  = commit_model flags addr n false m.
Proof. reflexivity. Qed.

Lemma mmap_fixed_na_commit_model : forall flags addr n m,
  with_mmap_replacement flags addr n
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
       ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
       (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m)
  = commit_model flags addr n true m.
Proof. reflexivity. Qed.

Lemma commit_model_vmmaps : forall flags addr n na m,
  m_vmmaps (commit_model flags addr n na m) = commit_vmmaps (m_vmmaps m) addr n na.
Proof.
  intros. unfold commit_model, with_mmap_replacement.
  rewrite with_mmap_backing_vmmaps, m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps.
Qed.

Lemma commit_model_lazy : forall flags addr n na m,
  m_vm_lazy (commit_model flags addr n na m)
  = (if mmap_noreserve_b flags then lazy_interior addr n else [])
    ++ maps_subtract (m_vm_lazy m) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof.
  intros. unfold commit_model, with_mmap_replacement.
  rewrite with_mmap_backing_lazy, m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity.
Qed.

Lemma commit_model_materialized : forall flags addr n na m,
  m_vm_materialized (commit_model flags addr n na m)
  = List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized m).
Proof.
  intros. unfold commit_model, with_mmap_replacement.
  rewrite with_mmap_backing_materialized, m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps. reflexivity.
Qed.

Lemma commit_model_nonvm : forall flags addr n na m,
  m_fd (commit_model flags addr n na m) = m_fd m
  /\ m_io (commit_model flags addr n na m) = m_io m
  /\ m_fsys (commit_model flags addr n na m) = m_fsys m
  /\ m_proc (commit_model flags addr n na m) = m_proc m
  /\ m_lim (commit_model flags addr n na m) = m_lim m
  /\ m_time (commit_model flags addr n na m) = m_time m.
Proof.
  intros flags addr n na [fd [maps lazy mat] io fs proc lim tm].
  unfold commit_model, with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
  destruct (mmap_noreserve_b flags); cbn; repeat split; reflexivity.
Qed.

Lemma cuts_commit : forall flags addr n na m x,
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  zcovb (cuts (commit_model flags addr n na m)) x
  = (if na then zin_rangeb x (addr, n) else false)
    || zcovb (if mmap_noreserve_b flags then lazy_interior addr n else []) x
    || (zcovb (cuts m) x && negb (zinb (lo (addr, n)) (hi (addr, n)) x)).
Proof.
  intros flags addr n na m x HNA HL. unfold cuts. rewrite commit_model_vmmaps, commit_model_lazy. cbn [vm_noaccess commit_vmmaps].
  pose proof (lo_nonneg (addr, n)) as H0. pose proof (lo_hi (addr, n)) as H1.
  unfold lo, hi in H0, H1 |- *. cbn [fst snd] in *.
  rewrite !zcovb_app, !zcovb_maps_subtract by assumption.
  destruct na; cbn [zcovb existsb app];
  destruct (zin_rangeb x (addr, n)), (zcovb (vm_noaccess (m_vmmaps m)) x),
    (zcovb (if mmap_noreserve_b flags then lazy_interior addr n else []) x), (zcovb (m_vm_lazy m) x),
    (zinb _ _ x); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eager_used_commit_rw_le : forall flags addr n m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  nooverlap (vm_maps (m_vmmaps m)) ->
  (exists e0, In e0 (vm_maps (m_vmmaps m)) /\ lo e0 <= lo (addr, n) /\ hi (addr, n) <= hi e0) ->
  eager_used (commit_model flags addr n false m) <= eager_used m + bv_unsigned n.
Proof.
  intros flags addr n m HX HNA HL Hdisj (e0 & Hin & H1 & H2).
  rewrite (eager_used_cuts (commit_model flags addr n false m)) by (rewrite commit_model_vmmaps; exact HX).
  rewrite (eager_used_cuts m HX), commit_model_vmmaps. cbn [vm_maps commit_vmmaps].
  replace (bv_unsigned n) with (hi (addr, n) - lo (addr, n)) by (exact (hi_minus_lo (addr, n))).
  apply (eagerZ_uncover_le _ _ _ e0 (lo (addr, n)) (hi (addr, n)) Hdisj Hin H1 (lo_hi _) H2).
  intros x Hout Hc. rewrite (cuts_commit flags addr n false m x HNA HL), Hc. cbn [andb orb].
  replace (zinb (lo (addr, n)) (hi (addr, n)) x) with false by (symmetry; apply zinb_false; exact Hout).
  cbn. apply orb_true_r.
Qed.

(* [comment removed for export] *)
Lemma eager_used_commit_covered_le : forall flags addr n na m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  (na = true \/ (mmap_noreserve_b flags = true /\ lazy_interior addr n = [(addr, n)])) ->
  eager_used (commit_model flags addr n na m) <= eager_used m.
Proof.
  intros flags addr n na m HX HNA HL Hcov.
  rewrite (eager_used_cuts (commit_model flags addr n na m)) by (rewrite commit_model_vmmaps; exact HX).
  rewrite (eager_used_cuts m HX), commit_model_vmmaps. cbn [vm_maps commit_vmmaps].
  apply eagerZ_mono_cuts. intros x Hc. rewrite (cuts_commit flags addr n na m x HNA HL), Hc. cbn [andb].
  destruct (zinb (lo (addr, n)) (hi (addr, n)) x) eqn:E.
  - apply zinb_true in E. assert (Hx : zin_rangeb x (addr, n) = true) by (apply zin_rangeb_iff; exact E).
    destruct Hcov as [-> | [-> ->]]; rewrite ?Hx; [reflexivity|]. cbn [zcovb existsb]. rewrite Hx.
    destruct na; reflexivity.
  - cbn [negb]. rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)

Definition munmap_vmmaps (h : VmMaps) (a n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition munmap_modelL (a n : word) (m : Model) : Model :=
  with_mmap_destroyed a n (munmap_vmmaps (m_vmmaps m) a n) m.

Lemma munmap_modelL_vmmaps : forall a n m, m_vmmaps (munmap_modelL a n m) = munmap_vmmaps (m_vmmaps m) a n.
Proof. intros. unfold munmap_modelL, with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.

Lemma munmap_modelL_lazy : forall a n m,
  m_vm_lazy (munmap_modelL a n m) = maps_subtract (m_vm_lazy m) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. intros. unfold munmap_modelL, with_mmap_destroyed. rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity. Qed.

Lemma munmap_modelL_materialized : forall a n m,
  m_vm_materialized (munmap_modelL a n m)
  = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m).
Proof. intros. unfold munmap_modelL, with_mmap_destroyed. rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps. reflexivity. Qed.

Lemma munmap_modelL_nonvm : forall a n m,
  m_fd (munmap_modelL a n m) = m_fd m
  /\ m_io (munmap_modelL a n m) = m_io m
  /\ m_fsys (munmap_modelL a n m) = m_fsys m
  /\ m_proc (munmap_modelL a n m) = m_proc m
  /\ m_lim (munmap_modelL a n m) = m_lim m
  /\ m_time (munmap_modelL a n m) = m_time m.
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma eager_used_munmap_le : forall a n m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  nooverlap (vm_maps (m_vmmaps m)) -> In (a, n) (vm_maps (m_vmmaps m)) ->
  eager_used (munmap_modelL a n m) + rem (a, n) (cuts m) <= eager_used m.
Proof.
  intros a n m HX HNA HL Hdisj Hin.
  rewrite (eager_used_cuts (munmap_modelL a n m))
    by (rewrite munmap_modelL_vmmaps; cbn; apply entries_nowrap_map_remove; exact HX).
  rewrite (eager_used_cuts m HX), munmap_modelL_vmmaps. cbn [vm_maps munmap_vmmaps].
  (* [comment removed for export] *)
  rewrite (eagerZ_cuts_ext_on (map_remove (vm_maps (m_vmmaps m)) a) (cuts m) (cuts (munmap_modelL a n m))).
  2:{ intros e x He Hx. apply map_remove_In in He. destruct He as [He Hne].
      unfold cuts. rewrite munmap_modelL_vmmaps, munmap_modelL_lazy. cbn [vm_noaccess munmap_vmmaps].
      pose proof (lo_nonneg (a, n)) as H0. pose proof (lo_hi (a, n)) as H1. unfold lo, hi in H0, H1. cbn [fst snd] in H0, H1.
      rewrite !zcovb_app, !zcovb_maps_subtract by assumption.
      replace (zinb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x) with false.
      2:{ symmetry. apply zinb_false. intros Hxr.
          (* [comment removed for export] *)
          assert (Hd : hi e <= lo (a, n) \/ hi (a, n) <= lo e \/ e = (a, n)).
          { clear - Hdisj He Hin. induction (vm_maps (m_vmmaps m)) as [|e1 X IH]; [destruct He|].
            destruct Hdisj as [H1 H2]. destruct He as [<- | He], Hin as [E | Hin].
            - right; right; exact E.
            - pose proof (H1 _ Hin); lia.
            - subst e1. pose proof (H1 _ He); lia.
            - exact (IH H2 Hin He). }
          assert (Hxr' : lo (a, n) <= x < hi (a, n)) by exact Hxr.
          destruct Hd as [Hd | [Hd | Hd]]; [lia | lia | subst e; cbn in Hne; exact (Hne eq_refl)]. }
      rewrite !andb_true_r. reflexivity. }
  (* [comment removed for export] *)
  unfold map_remove. clear - Hin. induction (vm_maps (m_vmmaps m)) as [|e X IH]; [destruct Hin|].
  cbn [List.filter eagerZ]. destruct Hin as [-> | Hin].
  - cbn [fst]. replace (bv_eqb a a) with true by (unfold bv_eqb; symmetry; apply Z.eqb_refl). cbn [negb].
    pose proof (eagerZ_map_remove_le X a (cuts m)) as Hle. unfold map_remove in Hle. lia.
  - specialize (IH Hin). pose proof (rem_bounds e (cuts m)).
    destruct (negb (bv_eqb (fst e) a)); cbn [eagerZ]; lia.
Qed.

(* [comment removed for export] *)
Lemma mprotect_model_next_commit : forall m addr n,
  mprotect_model_next m addr n = with_vmmaps (commit_vmmaps (m_vmmaps m) addr n false) m.
Proof. reflexivity. Qed.

Lemma eager_used_mprotect_le : forall addr n m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  entries_nowrap (vm_noaccess (m_vmmaps m)) -> entries_nowrap (m_vm_lazy m) ->
  nooverlap (vm_maps (m_vmmaps m)) ->
  (exists e0, In e0 (vm_maps (m_vmmaps m)) /\ lo e0 <= lo (addr, n) /\ hi (addr, n) <= hi e0) ->
  eager_used (mprotect_model_next m addr n) <= eager_used m + bv_unsigned n.
Proof.
  intros addr n m HX HNA HL Hdisj He0.
  rewrite mprotect_model_next_commit.
  destruct He0 as (e0 & Hin & H1 & H2).
  rewrite (eager_used_cuts (with_vmmaps _ m)) by (rewrite m_vmmaps_with_vmmaps; exact HX).
  rewrite (eager_used_cuts m HX), m_vmmaps_with_vmmaps. cbn [vm_maps commit_vmmaps].
  replace (bv_unsigned n) with (hi (addr, n) - lo (addr, n)) by (exact (hi_minus_lo (addr, n))).
  apply (eagerZ_uncover_le _ _ _ e0 (lo (addr, n)) (hi (addr, n)) Hdisj Hin H1 (lo_hi _) H2).
  intros x Hout Hc. unfold cuts in Hc |- *. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps.
  cbn [vm_noaccess commit_vmmaps app].
  pose proof (lo_nonneg (addr, n)) as H0. pose proof (lo_hi (addr, n)) as H3.
  unfold lo, hi in H0, H3, Hout |- *. cbn [fst snd] in *.
  rewrite !zcovb_app, zcovb_maps_subtract by assumption. rewrite zcovb_app in Hc.
  replace (zinb (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) x) with false
    by (symmetry; apply zinb_false; exact Hout).
  rewrite andb_true_r. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma eager_used_with_vmmaps_cons_le : forall m e h',
  entries_nowrap (vm_maps (m_vmmaps m)) -> entry_nowrap e ->
  vm_maps h' = e :: vm_maps (m_vmmaps m) -> vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
  eager_used (with_vmmaps h' m) <= eager_used m + bv_unsigned (snd e).
Proof.
  intros m e h' HX He Hm Hna.
  rewrite (eager_used_cuts (with_vmmaps h' m)) by (rewrite m_vmmaps_with_vmmaps, Hm; apply entries_nowrap_cons; auto).
  rewrite (eager_used_cuts m HX). unfold cuts. rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hm, Hna.
  cbn [eagerZ]. pose proof (rem_bounds e (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m)). lia.
Qed.

(* [comment removed for export] *)
Lemma eager_used_with_vmmaps_same : forall m h',
  vm_maps h' = vm_maps (m_vmmaps m) -> vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
  eager_used (with_vmmaps h' m) = eager_used m.
Proof.
  intros m h' Hm Hna. unfold eager_used, vm_backed_maps.
  rewrite m_vmmaps_with_vmmaps, m_vm_lazy_with_vmmaps, Hm, Hna. reflexivity.
Qed.

End ModelOps.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma maps_subtract_pos : forall C l h p,
  entries_nowrap C -> 0 <= l -> l <= h ->
  (forall c, In c C -> lo c < hi c) ->
  In p (maps_subtract C l h) -> lo p < hi p.
Proof.
  induction C as [|[a sz] C IH]; intros l h p HC Hl Hlh Hpos Hin; cbn [maps_subtract] in Hin; [destruct Hin|].
  apply entries_nowrap_cons in HC. destruct HC as [He HC].
  apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - destruct (iv_subtract_pieces a sz l h (fun _ => 0) He Hl Hlh) as [Hp _].
    pose proof (Hpos (a, sz) (or_introl eq_refl)).
    destruct (Hp p Hin) as [(H1 & H2 & H3) | (H1 & H2 & H3)]; lia.
  - apply (IH l h p HC Hl Hlh); [|exact Hin]. intros c Hc. apply Hpos. right. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint_id : forall (a sz : word) l h,
  lo (a, sz) < hi (a, sz) -> (hi (a, sz) <= l \/ h <= lo (a, sz)) -> l <= h ->
  iv_subtract a sz l h = [(a, sz)].
Proof.
  intros a sz l h Hpos Hd Hlh. unfold lo, hi in Hpos, Hd. cbn [fst snd] in Hpos, Hd.
  unfold iv_subtract. cbn [fst snd].
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    f_equal. f_equal. rewrite Z.min_l by lia. apply Z_to_bv_bv_unsigned.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) l)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. f_equal. f_equal; [apply Z_to_bv_bv_unsigned|].
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    apply Z_to_bv_bv_unsigned.
Qed.

Lemma maps_subtract_disjoint_id : forall C l h,
  l <= h ->
  (forall c, In c C -> lo c < hi c /\ (hi c <= l \/ h <= lo c)) ->
  maps_subtract C l h = C.
Proof.
  induction C as [|[a sz] C IH]; intros l h Hlh HC; cbn [maps_subtract]; [reflexivity|].
  destruct (HC (a, sz) (or_introl eq_refl)) as [Hpos Hd].
  rewrite (iv_subtract_disjoint_id a sz l h Hpos Hd Hlh). cbn [app]. f_equal.
  apply IH; [exact Hlh|]. intros c Hc. apply HC. right. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_containing : forall (a sz : word) l h,
  entry_nowrap (a, sz) -> lo (a, sz) <= l -> l <= h -> h <= hi (a, sz) ->
  iv_subtract a sz l h
  = (if lo (a, sz) <? l then [(a, Z_to_bv 64 (l - lo (a, sz)))] else [])
    ++ (if h <? hi (a, sz) then [(Z_to_bv 64 h, Z_to_bv 64 (hi (a, sz) - h))] else []).
Proof.
  intros a sz l h Hnw H1 H2 H3. unfold entry_nowrap, lo, hi in *. cbn [fst snd] in *.
  unfold iv_subtract. cbn [fst snd].
  destruct (bv_unsigned a <? l) eqn:E1.
  - apply Z.ltb_lt in E1. rewrite Z.min_r by lia.
    destruct (h <? bv_unsigned a + bv_unsigned sz) eqn:E2; [|reflexivity].
    apply Z.ltb_lt in E2. rewrite Z.max_r by lia. reflexivity.
  - destruct (h <? bv_unsigned a + bv_unsigned sz) eqn:E2; [|reflexivity].
    apply Z.ltb_lt in E2. rewrite Z.max_r by lia. reflexivity.
Qed.
