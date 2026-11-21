(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl AsanCtrlProps AsanInv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma pick_seq : forall (f : Z -> Z) c0 n a,
  fold_right (fun c acc => (if c0 =? c then f c else 0) + acc) 0 (map Z.of_nat (seq a n))
  = if (Z.of_nat a <=? c0) && (c0 <? Z.of_nat a + Z.of_nat n) then f c0 else 0.
Proof.
  intros f c0. induction n as [|n IH]; intros a.
  - cbn [seq map fold_right]. destruct (Z.leb_spec (Z.of_nat a) c0), (Z.ltb_spec c0 (Z.of_nat a + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - cbn [seq map fold_right]. rewrite IH.
    destruct (Z.eqb_spec c0 (Z.of_nat a)) as [E|E];
      destruct (Z.leb_spec (Z.of_nat (S a)) c0), (Z.ltb_spec c0 (Z.of_nat (S a) + Z.of_nat n)),
               (Z.leb_spec (Z.of_nat a) c0), (Z.ltb_spec c0 (Z.of_nat a + Z.of_nat (S n))); cbn [andb]; try lia; subst; lia.
Qed.

Lemma pick_CLASSES : forall (f : Z -> Z) c0, 1 <= c0 <= 31 ->
  fold_right (fun c acc => (if c0 =? c then f c else 0) + acc) 0 CLASSES = f c0.
Proof.
  intros f c0 Hc. unfold CLASSES. rewrite pick_seq.
  destruct (Z.leb_spec (Z.of_nat 1) c0), (Z.ltb_spec c0 (Z.of_nat 1 + Z.of_nat 31)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma fold_add : forall (f g : Z -> Z) l,
  fold_right (fun c acc => (f c + g c) + acc) 0 l = fold_right (fun c acc => f c + acc) 0 l + fold_right (fun c acc => g c + acc) 0 l.
Proof. induction l as [|c l IH]; cbn [fold_right]; [reflexivity| rewrite IH; lia]. Qed.
Lemma fold_ext : forall (f g : Z -> Z) l, (forall c, In c l -> f c = g c) ->
  fold_right (fun c acc => f c + acc) 0 l = fold_right (fun c acc => g c + acc) 0 l.
Proof. induction l as [|c l IH]; intros H; cbn [fold_right]; [reflexivity|]. rewrite (H c (or_introl eq_refl)), IH; [reflexivity|]. intros; apply H; right; assumption. Qed.
Lemma fold_le : forall (f g : Z -> Z) l, (forall c, In c l -> f c <= g c) ->
  fold_right (fun c acc => f c + acc) 0 l <= fold_right (fun c acc => g c + acc) 0 l.
Proof. induction l as [|c l IH]; intros H; cbn [fold_right]; [lia|]. pose proof (H c (or_introl eq_refl)). specialize (IH ltac:(intros; apply H; right; assumption)). lia. Qed.
Lemma fold_const : forall (k : Z) (l : list Z), fold_right (fun _ acc => k + acc) 0 l = k * zlen l.
Proof. induction l as [|c l IH]; cbn [fold_right]; [unfold zlen; cbn [length]; lia| rewrite IH, zlen_cons; lia]. Qed.

Fixpoint pvol (l : list achunk) : Z :=
  match l with [] => 0 | CPrim c _ :: l' => size_of_class c + pvol l' | CSec _ _ _ :: l' => pvol l' end.

Definition cls_ok1 (ch : achunk) : Prop := match ch with CPrim c _ => 1 <= c <= 31 | CSec _ _ _ => True end.

Lemma csum_cntP : forall l, Forall cls_ok1 l ->
  fold_right (fun c acc => size_of_class c * cntP c l + acc) 0 CLASSES = pvol l.
Proof.
  induction l as [|ch l IH]; intros HF.
  - cbn [pvol]. rewrite (fold_ext (fun c => size_of_class c * cntP c []) (fun _ => 0)) by (intros; rewrite cntP_nil; lia). rewrite fold_const. lia.
  - apply Forall_cons_iff in HF as [H1 HF]. specialize (IH HF).
    rewrite (fold_ext (fun c => size_of_class c * cntP c (ch :: l))
                      (fun c => (if is_prim_of c ch then size_of_class c else 0) + size_of_class c * cntP c l)).
    2:{ intros c _. rewrite cntP_cons. destruct (is_prim_of c ch); lia. }
    rewrite (fold_add (fun c => if is_prim_of c ch then size_of_class c else 0) (fun c => size_of_class c * cntP c l)), IH.
    destruct ch as [c0 n|mb ms n]; cbn [is_prim_of pvol cls_ok1] in *.
    + rewrite (pick_CLASSES size_of_class c0 H1). reflexivity.
    + rewrite (fold_const 0). lia.
Qed.

Lemma vol_chunks : forall ATOP l, Forall (chunk_wf ATOP) l ->
  Forall cls_ok1 l /\ pvol l + zsum2 (secs l) <= 2 * zsumc l + 128 * zlen l.
Proof.
  intros ATOP. induction l as [|ch l IH]; intros HF.
  - split; [constructor|]. unfold zlen. cbn. lia.
  - apply Forall_cons_iff in HF as [H1 HF]. destruct (IH HF) as [IH1 IH2]. rewrite zlen_cons, secs_cons.
    destruct ch as [c n|mb ms n]; cbn [chunk_wf] in H1; cbn [pvol zsumc chunk_size sec_of app].
    + destruct H1 as [Hn ->]. destruct (class_size_bound n Hn) as (Hp & Hsz & _).
      pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & _).
      split; [constructor; [cbn [cls_ok1]; lia| exact IH1]|]. lia.
    + destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
      split; [constructor; [exact I| exact IH1]|]. cbn [zsum2 snd]. lia.
Qed.

Lemma zsum2_secs_nonneg : forall ATOP l, Forall (chunk_wf ATOP) l -> 0 <= zsum2 (secs l).
Proof.
  intros ATOP. induction l as [|ch l IH]; intros HF; [cbn; lia|]. apply Forall_cons_iff in HF as [H1 HF]. specialize (IH HF). rewrite secs_cons.
  destruct ch as [c n|mb ms n]; cbn [sec_of app]; [exact IH|]. cbn [chunk_wf] in H1. destruct H1 as (Hn & -> & _).
  pose proof (sec_map_size_bounds n ltac:(lia)). cbn [zsum2 snd]. lia.
Qed.

Definition CLS_SLACK : Z := UNUSED_MAX + 2 * K_USER_MAP + K_FREEARR_MAP.

Lemma cls_vol : forall pc pb st c, cls_inv pc pb st c ->
  cls_mapped_bytes' (get_cls st c) <= size_of_class c * cntP c (all_chunks pc pb st) + size_of_class c * nbatch c (qbatches pb st) + CLS_SLACK.
Proof.
  intros pc pb st c H. unfold cls_inv in H. cbv zeta in H. destruct H as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  unfold cls_mapped_bytes', CLS_SLACK.
  replace (size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count (get_cls st c) + c_num_freed (get_cls st c)))
    with (size_of_class c * cntP c (all_chunks pc pb st) + size_of_class c * nbatch c (qbatches pb st)
          + size_of_class c * (c_count (get_cls st c) + c_num_freed (get_cls st c))) in C10 by ring.
  lia.
Qed.

Lemma nbatch_sum : forall bs, fold_right (fun c acc => size_of_class c * nbatch c bs + acc) 0 CLASSES = Q_BATCH_BYTES * zlen bs.
Proof.
  intros bs. rewrite (fold_ext (fun c => size_of_class c * nbatch c bs) (fun c => if K_BATCH_CLASS =? c then size_of_class c * zlen bs else 0)).
  2:{ intros c _. unfold nbatch. rewrite (Z.eqb_sym c K_BATCH_CLASS). destruct (K_BATCH_CLASS =? c); lia. }
  rewrite (pick_CLASSES (fun c => size_of_class c * zlen bs) K_BATCH_CLASS ltac:(unfold K_BATCH_CLASS; lia)). reflexivity.
Qed.

Definition VOL_CONST : Z := 31 * CLS_SLACK + 8 * K_CHUNKS_BLOCK.

Theorem VOL : forall ATOP pc pb st, AINV ATOP pc pb st ->
  commit_bytes st + zsum2 (CH pc pb st)
  <= 2 * zsumc (all_chunks pc pb st) + 128 * zlen (all_chunks pc pb st) + Q_BATCH_BYTES * zlen (qbatches pb st) + VOL_CONST.
Proof.
  intros ATOP pc pb st H. pose proof H as (HC & HW & _ & _ & _ & _ & Hres & _).
  destruct (vol_chunks ATOP _ HW) as [HK HV].
  unfold commit_bytes, csum, CH, VOL_CONST.
  pose proof (fold_le (fun c => cls_mapped_bytes' (get_cls st c))
                (fun c => (size_of_class c * cntP c (all_chunks pc pb st) + size_of_class c * nbatch c (qbatches pb st)) + CLS_SLACK) CLASSES) as B.
  specialize (B ltac:(intros c Hc; apply In_CLASSES in Hc; pose proof (cls_vol pc pb st c (HC c Hc)); cbv beta; lia)).
  rewrite (fold_add (fun c => size_of_class c * cntP c (all_chunks pc pb st) + size_of_class c * nbatch c (qbatches pb st)) (fun _ => CLS_SLACK)) in B.
  rewrite (fold_add (fun c => size_of_class c * cntP c (all_chunks pc pb st)) (fun c => size_of_class c * nbatch c (qbatches pb st))) in B.
  rewrite (csum_cntP _ HK), nbatch_sum, (fold_const CLS_SLACK) in B. change (zlen CLASSES) with 31 in B.
  unfold K_CHUNKS_BLOCK in *. destruct Hres as [E | E]; rewrite E; lia.
Qed.

Definition W (pc : list achunk) (pb : list abatch) (st : astate) : Z :=
  2 * zsumc (all_chunks pc pb st) + 128 * zlen (all_chunks pc pb st) + Q_BATCH_BYTES * zlen (qbatches pb st).
Definition WCAP : Z := 2^33.
Definition vroomL (pc : list achunk) (pb : list abatch) (st : astate) : Prop := W pc pb st <= WCAP.
Definition WPCAP : Z := 2^30 - 2^22.
Definition vroom (pc : list achunk) (pb : list abatch) (st : astate) : Prop := W pc pb st <= WPCAP.
Lemma vroom_L : forall pc pb st, vroom pc pb st -> vroomL pc pb st.
Proof. intros pc pb st H. unfold vroom, vroomL, WPCAP, WCAP in *. change (2 ^ 30) with 1073741824 in H. change (2 ^ 22) with 4194304 in H. change (2 ^ 33) with 8589934592. lia. Qed.

Lemma VOL_W : forall ATOP pc pb st, AINV ATOP pc pb st -> commit_bytes st + zsum2 (CH pc pb st) <= W pc pb st + VOL_CONST.
Proof. intros. unfold W. apply (VOL ATOP). assumption. Qed.

Lemma W_same : forall pc pb st st', all_chunks pc pb st' = all_chunks pc pb st -> qbatches pb st' = qbatches pb st -> W pc pb st' = W pc pb st.
Proof. intros pc pb st st' E1 E2. unfold W. rewrite E1, E2. reflexivity. Qed.
Lemma vroom_put : forall pc pb c r st, vroom pc pb st -> vroom pc pb (put_cls c r st).
Proof. intros. unfold vroom in *. rewrite (W_same pc pb st); [assumption| reflexivity| reflexivity]. Qed.
Lemma vroom_init_cache : forall pc pb st, vroom pc pb st -> vroom pc pb (init_cache st).
Proof. intros. unfold vroom in *. rewrite (W_same pc pb st); [assumption| apply all_chunks_init_cache| apply qbatches_init_cache]. Qed.
Lemma W_cons : forall ch pc pb st, W (ch :: pc) pb st = W pc pb st + 2 * chunk_size ch + 128.
Proof. intros. unfold W. change (all_chunks (ch :: pc) pb st) with (ch :: all_chunks pc pb st). cbn [zsumc]. rewrite zlen_cons. lia. Qed.

Lemma fold_ge_term : forall (f : Z -> Z) l c, (forall x, In x l -> 0 <= f x) -> In c l -> f c <= fold_right (fun x acc => f x + acc) 0 l.
Proof.
  induction l as [|x l IH]; intros c H0 Hin; [destruct Hin|]. cbn [fold_right].
  assert (G : 0 <= fold_right (fun x acc => f x + acc) 0 l).
  { clear - H0. induction l as [|y l IH]; cbn [fold_right]; [lia|]. pose proof (H0 y (or_intror (or_introl eq_refl))).
    specialize (IH ltac:(intros z Hz; apply H0; destruct Hz as [->|Hz]; [left; reflexivity| right; right; exact Hz])). lia. }
  destruct Hin as [->|Hin]; [lia|]. pose proof (H0 x (or_introl eq_refl)). specialize (IH c ltac:(intros z Hz; apply H0; right; exact Hz) Hin). lia.
Qed.

Lemma size_of_class_pos : forall c, 1 <= c <= 31 -> 0 < size_of_class c.
Proof.
  intros c Hc. assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct H as [->|H]; [reflexivity|]). subst c. reflexivity.
Qed.

Lemma cls_user_W : forall ATOP pc pb st c, AINV ATOP pc pb st -> 1 <= c <= 31 ->
  c_mapped_user (get_cls st c) <= W pc pb st + CLS_SLACK.
Proof.
  intros ATOP pc pb st c H Hc. pose proof H as (HC & HW & _). destruct (vol_chunks ATOP _ HW) as [HK HV].
  pose proof (cls_vol pc pb st c (HC c Hc)) as CV. unfold cls_mapped_bytes' in CV.
  destruct (HC c Hc) as (_ & _ & _ & _ & _ & F6 & _).
  pose proof (size_of_class_pos c Hc) as SP.
  assert (T1 : size_of_class c * cntP c (all_chunks pc pb st) <= pvol (all_chunks pc pb st)).
  { rewrite <- (csum_cntP _ HK). apply (fold_ge_term (fun x => size_of_class x * cntP x (all_chunks pc pb st))); [| apply In_CLASSES; exact Hc].
    intros x Hx. apply In_CLASSES in Hx. pose proof (size_of_class_pos x Hx). pose proof (cntP_nonneg x (all_chunks pc pb st)). apply Z.mul_nonneg_nonneg; lia. }
  assert (T2 : size_of_class c * nbatch c (qbatches pb st) <= Q_BATCH_BYTES * zlen (qbatches pb st)).
  { rewrite <- (nbatch_sum (qbatches pb st)). apply (fold_ge_term (fun x => size_of_class x * nbatch x (qbatches pb st))); [| apply In_CLASSES; exact Hc].
    intros x Hx. apply In_CLASSES in Hx. pose proof (size_of_class_pos x Hx). unfold nbatch. destruct (x =? K_BATCH_CLASS); [pose proof (zlen_nonneg (qbatches pb st))|]; nia. }
  pose proof (zsum2_secs_nonneg ATOP _ HW) as S0.
  unfold W. lia.
Qed.

Lemma VOL_CONST_val : VOL_CONST = 48889856. Proof. reflexivity. Qed.
