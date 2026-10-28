(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BazyRestrict.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Open Scope Z_scope.

Fixpoint zcount (P : Z -> bool) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => (if P lo then 1 else 0) + zcount P (lo + 1) n'
  end.

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

Lemma zcount_or_le : forall P Q lo n,
  zcount (fun x => P x || Q x) lo n <= zcount P lo n + zcount Q lo n.
Proof.
  intros P Q lo n. revert lo. induction n as [|n IH]; intros lo; cbn [zcount]; [lia|].
  specialize (IH (lo + 1)). destruct (P lo), (Q lo); cbn [orb]; lia.
Qed.

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

Definition lo (r : word * word) : Z := bv_unsigned (fst r).
Definition hi (r : word * word) : Z := bv_unsigned (fst r) + bv_unsigned (snd r).

Lemma lo_hi : forall r, lo r <= hi r.
Proof. intros [a n]. unfold lo, hi. cbn. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma lo_nonneg : forall r, 0 <= lo r.
Proof. intros [a n]. unfold lo. cbn. pose proof (bv_unsigned_in_range 64 a). lia. Qed.

Lemma hi_minus_lo : forall r, hi r - lo r = bv_unsigned (snd r).
Proof. intros [a n]. unfold lo, hi. cbn. lia. Qed.

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

Lemma rem_covered : forall e C c,
  In c C -> lo c <= lo e -> hi e <= hi c -> rem e C = 0.
Proof.
  intros e C c Hin H1 H2. unfold rem. apply zmeasure_none. intros x Hx.
  apply negb_false_iff. apply zcovb_true. exists c. split; [exact Hin | lia].
Qed.

Lemma rem_free : forall e C,
  (forall c, In c C -> hi c <= lo e \/ hi e <= lo c) -> rem e C = bv_unsigned (snd e).
Proof.
  intros e C H. unfold rem. rewrite <- hi_minus_lo. apply zmeasure_all; [apply lo_hi|].
  intros x Hx. apply negb_true_iff. apply zcovb_false. intros r Hin Hr.
  destruct (H r Hin); lia.
Qed.

Lemma rem_nil : forall e, rem e [] = bv_unsigned (snd e).
Proof. intros e. apply rem_free. intros c []. Qed.

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

Theorem eager_used_eq : forall m,
  entries_nowrap (vm_maps (m_vmmaps m)) ->
  eager_used m = eagerZ (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m).
Proof.
  intros m HX. unfold eager_used, vm_backed_maps.
  rewrite <- maps_subtract_all_app. apply live_bytes_msa. exact HX.
Qed.

Definition zinb (l h x : Z) : bool := (l <=? x) && (x <? h).

Lemma zinb_true : forall l h x, zinb l h x = true <-> l <= x < h.
Proof. intros. unfold zinb. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma zinb_false : forall l h x, zinb l h x = false <-> ~ (l <= x < h).
Proof.
  intros l h x. destruct (zinb l h x) eqn:E.
  - apply zinb_true in E. split; [discriminate | tauto].
  - split; [|reflexivity]. intros _ Hx. apply zinb_true in Hx. congruence.
Qed.

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

Lemma map_remove_In : forall X (a : word) p, In p (map_remove X a) -> In p X /\ fst p <> a.
Proof.
  intros X a p H. unfold map_remove in H. apply filter_In in H. destruct H as [Hin Hb].
  split; [exact Hin|]. intros E. subst. unfold bv_eqb in Hb. rewrite Z.eqb_refl in Hb. discriminate.
Qed.

Lemma entries_nowrap_map_remove : forall X a, entries_nowrap X -> entries_nowrap (map_remove X a).
Proof. intros X a H p Hp. apply H. exact (proj1 (map_remove_In X a p Hp)). Qed.

Fixpoint nooverlap (X : list (word * word)) : Prop :=
  match X with
  | [] => True
  | e :: X' => (forall e', In e' X' -> hi e <= lo e' \/ hi e' <= lo e) /\ nooverlap X'
  end.

Lemma nooverlap_cons_intro : forall e X,
  (forall e', In e' X -> hi e <= lo e' \/ hi e' <= lo e) -> nooverlap X -> nooverlap (e :: X).
Proof. intros; cbn; auto. Qed.

Lemma filter_sublist_nooverlap : forall f X, nooverlap X -> nooverlap (List.filter f X).
Proof.
  induction X as [|e X IH]; cbn; intros H; [exact I|].
  destruct H as [He HX]. destruct (f e); cbn.
  - split; [|exact (IH HX)]. intros e' Hin. apply filter_In in Hin. apply He. tauto.
  - exact (IH HX).
Qed.

Lemma nooverlap_map_remove : forall X a, nooverlap X -> nooverlap (map_remove X a).
Proof. intros X a. unfold map_remove. apply filter_sublist_nooverlap. Qed.

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

  set (m1 := Z.min b (Z.max a l)). set (m2 := Z.min b (Z.max a h)).
  rewrite (zmeasure_split _ a m1 b) by lia.
  rewrite (zmeasure_split _ m1 m2 b) by lia.
  rewrite (zmeasure_none _ a m1) by (intros x Hx; apply zinb_false; lia).
  rewrite (zmeasure_none _ m2 b) by (intros x Hx; apply zinb_false; lia).
  pose proof (zmeasure_bounds (zinb l h) m1 m2). lia.
Qed.

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

Lemma eagerZ_map_remove_le : forall X a C, eagerZ (map_remove X a) C <= eagerZ X C.
Proof.
  intros X a C. unfold map_remove. induction X as [|e X IH]; cbn; [lia|].
  pose proof (rem_bounds e C). destruct (negb (bv_eqb (fst e) a)); cbn [eagerZ]; lia.
Qed.

Section ModelOps.

Definition cuts (m : Model) : list (word * word) := vm_noaccess (m_vmmaps m) ++ m_vm_lazy m.

Lemma eager_used_cuts : forall m,
  entries_nowrap (vm_maps (m_vmmaps m)) -> eager_used m = eagerZ (vm_maps (m_vmmaps m)) (cuts m).
Proof. intros m H. apply eager_used_eq. exact H. Qed.

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

Definition commit_vmmaps (h : VmMaps) (addr n : word) (na : bool) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
    ((if na then [(addr, n)] else [])
       ++ maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition commit_model (flags addr n : word) (na : bool) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (commit_vmmaps (m_vmmaps m) addr n na) m).

Lemma mmap_fixed_rw_commit_model : forall flags addr n m,
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m)
  = commit_model flags addr n false m.
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

  rewrite (eagerZ_cuts_ext_on (map_remove (vm_maps (m_vmmaps m)) a) (cuts m) (cuts (munmap_modelL a n m))).
  2:{ intros e x He Hx. apply map_remove_In in He. destruct He as [He Hne].
      unfold cuts. rewrite munmap_modelL_vmmaps, munmap_modelL_lazy. cbn [vm_noaccess munmap_vmmaps].
      pose proof (lo_nonneg (a, n)) as H0. pose proof (lo_hi (a, n)) as H1. unfold lo, hi in H0, H1. cbn [fst snd] in H0, H1.
      rewrite !zcovb_app, !zcovb_maps_subtract by assumption.
      replace (zinb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x) with false.
      2:{ symmetry. apply zinb_false. intros Hxr.

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

  unfold map_remove. clear - Hin. induction (vm_maps (m_vmmaps m)) as [|e X IH]; [destruct Hin|].
  cbn [List.filter eagerZ]. destruct Hin as [-> | Hin].
  - cbn [fst]. replace (bv_eqb a a) with true by (unfold bv_eqb; symmetry; apply Z.eqb_refl). cbn [negb].
    pose proof (eagerZ_map_remove_le X a (cuts m)) as Hle. unfold map_remove in Hle. lia.
  - specialize (IH Hin). pose proof (rem_bounds e (cuts m)).
    destruct (negb (bv_eqb (fst e) a)); cbn [eagerZ]; lia.
Qed.

End ModelOps.

