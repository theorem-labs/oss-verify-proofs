(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflRoom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import FillWinModel BitsModel SendModel CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma put_byte_fp : forall s c,
  ds_pending (put_byte s c) = ds_pending s + 1
  /\ arr_len (ds_pending_buf (put_byte s c)) = arr_len (ds_pending_buf s)
  /\ (forall i, i <> ds_pending s -> arr_get (ds_pending_buf (put_byte s c)) i = arr_get (ds_pending_buf s) i)
  /\ (0 <= ds_pending s < arr_len (ds_pending_buf s) -> arr_get (ds_pending_buf (put_byte s c)) (ds_pending s) = wrap8 c)
  /\ ds_lit_bufsize (put_byte s c) = ds_lit_bufsize s /\ ds_sym_next (put_byte s c) = ds_sym_next s
  /\ ds_bi_valid (put_byte s c) = ds_bi_valid s.
Proof.
  intros s c. unfold put_byte. dsred. rewrite arr_len_set.
  repeat split; try reflexivity.
  - intros i Hi. apply arr_get_set_other. lia.
  - intros H. apply arr_get_set_same. exact H.
Qed.

Lemma send_bits_fp : forall s v l,
  let s' := send_bits s v l in
  (ds_pending s' = ds_pending s \/ ds_pending s' = ds_pending s + 2)
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s)
  /\ (forall i, (i < ds_pending s \/ ds_pending s' <= i) -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s.
Proof.
  intros s v l. cbv zeta. unfold send_bits, put_short, Buf_size.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)).
  - set (s1 := set_bi_buf s _).
    pose proof (put_byte_fp s1 (Z.land (ds_bi_buf s1) 255)) as (P1 & L1 & O1 & _ & LB1 & SN1 & _).
    set (s2 := put_byte s1 _) in *.
    pose proof (put_byte_fp s2 (Z.shiftr (wrap16 (ds_bi_buf s1)) 8)) as (P2 & L2 & O2 & _ & LB2 & SN2 & _).
    set (s3 := put_byte s2 _) in *.
    assert (E1 : ds_pending s1 = ds_pending s /\ ds_pending_buf s1 = ds_pending_buf s /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_sym_next s1 = ds_sym_next s)
      by (subst s1; dsred; repeat split; reflexivity).
    destruct E1 as (E1 & E2 & E3 & E4).
    dsred. split; [lia|]. split; [rewrite L2, L1, E2; reflexivity|].
    split; [| rewrite LB2, LB1, SN2, SN1; auto].
    intros i Hi. rewrite O2 by lia. rewrite O1 by lia. rewrite E2. reflexivity.
  - dsred. repeat split; auto.
Qed.

Lemma send_bits_bi_valid : forall s v l, 0 <= ds_bi_valid s <= 16 -> 0 <= l <= 16 ->
  0 <= ds_bi_valid (send_bits s v l) <= 16.
Proof.
  intros s v l H Hl. unfold send_bits, put_short, put_byte, Buf_size.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)); dsred; lia.
Qed.

Lemma sbs_fp : forall cs s, lens_ok cs -> 0 <= ds_bi_valid s <= 16 ->
  let s' := sbs_run s cs in
  ds_pending s <= ds_pending s'
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s)
  /\ (forall i, (i < ds_pending s \/ ds_pending s' <= i) -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s
  /\ 0 <= ds_bi_valid s' <= 16
  /\ vsize s' = vsize s + sumlen cs.
Proof.
  induction cs as [|[v l] cs IH]; intros s LO BV; cbv zeta.
  - cbn. repeat split; auto; try lia.
  - inversion LO; subst. cbn in H1.
    pose proof (send_bits_fp s v l) as (P1 & L1 & O1 & LB1 & SN1). cbv zeta in *.
    pose proof (send_bits_bi_valid s v l BV H1) as BV1.
    specialize (IH (send_bits s v l) H2 BV1). cbv zeta in IH. destruct IH as (P2 & L2 & O2 & LB2 & SN2 & BV2 & VS2).
    cbn [sbs_run sumlen]. split; [lia|]. split; [rewrite L2, L1; reflexivity|].
    split. { intros i Hi. rewrite O2 by lia. apply O1. lia. }
    split; [rewrite LB2, LB1; reflexivity|]. split; [rewrite SN2, SN1; reflexivity|].
    split; [exact BV2|]. rewrite VS2, send_bits_size. lia.
Qed.

Lemma pending_le_vsize : forall s, 0 <= ds_bi_valid s -> 8 * ds_pending s <= vsize s.
Proof. intros s H. unfold vsize. lia. Qed.

Lemma put_byte_PBB : forall s c, PBB s -> PBB (put_byte s c).
Proof.
  intros s c HP i Hi. pose proof (put_byte_fp s c) as (_ & L1 & O1 & S1 & _).
  rewrite L1 in Hi. destruct (Z.eq_dec i (ds_pending s)).
  - subst i. rewrite S1 by lia. pose proof (wrap8_range c) as W. lia.
  - rewrite O1 by lia. apply HP. lia.
Qed.

Lemma send_bits_PBB : forall s v l, PBB s -> PBB (send_bits s v l).
Proof.
  intros s v l HP. unfold send_bits, put_short, Buf_size.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)).
  - intros i Hi. dsred in Hi. dsred.
    match goal with |- context [ds_pending_buf (put_byte (put_byte ?s1 ?a) ?b)] =>
      pose proof (put_byte_PBB (put_byte s1 a) b (put_byte_PBB s1 a ltac:(intros j Hj; apply HP; exact Hj))) as Q end.
    apply Q. exact Hi.
  - intros i Hi. dsred in Hi. dsred. apply HP. exact Hi.
Qed.

Lemma sbs_PBB : forall cs s, PBB s -> PBB (sbs_run s cs).
Proof. induction cs as [|[v l] cs IH]; intros s HP; cbn; [exact HP|]. apply IH. apply send_bits_PBB. exact HP. Qed.


Definition calls_of (lfc ldl dfc ddl : arr) (dl : Z * Z) : list (Z * Z) :=
  let '(dist, lc) := dl in
  if dist =? 0 then [(arr_get lfc lc, arr_get ldl lc)]
  else
    let code := arr_get length_code_a lc in
    let extra := arr_get extra_lbits_a code in
    let dist' := dist - 1 in
    let dcode := d_code dist' in
    let dextra := arr_get extra_dbits_a dcode in
    [(arr_get lfc (code + LITERALS + 1), arr_get ldl (code + LITERALS + 1))]
    ++ (if negb (extra =? 0) then [(lc - arr_get base_length_a code, extra)] else [])
    ++ [(arr_get dfc dcode, arr_get ddl dcode)]
    ++ (if negb (dextra =? 0) then [(wrap32 (dist' - arr_get base_dist_a dcode), dextra)] else []).

Definition cost_of (lfc ldl dfc ddl : arr) (dl : Z * Z) : Z := sumlen (calls_of lfc ldl dfc ddl dl).

Definition sym_at (s : deflate_state) (sx d lc : Z) : Prop :=
  arr_get (ds_pending_buf s) (ds_lit_bufsize s + sx) = d mod 256
  /\ arr_get (ds_pending_buf s) (ds_lit_bufsize s + sx + 1) = d / 256
  /\ arr_get (ds_pending_buf s) (ds_lit_bufsize s + sx + 2) = lc.

Lemma land_255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. replace 255 with (Z.ones 8) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma sym_read : forall s sx d lc, sym_at s sx d lc -> 0 <= d < 65536 ->
  sym_dist s sx = d /\ sym_lc s sx = lc.
Proof.
  intros s sx d lc (A & B & C) Hd. unfold sym_dist, sym_d0, sym_d1, sym_lc, sym_buf_get.
  replace (ds_lit_bufsize s + (sx + 1)) with (ds_lit_bufsize s + sx + 1) by lia.
  replace (ds_lit_bufsize s + (sx + 1 + 1)) with (ds_lit_bufsize s + sx + 2) by lia.
  rewrite A, B, C. split; [|reflexivity].
  rewrite !land_255_small by (first [split; [apply Z.mod_pos_bound|apply Z.mod_pos_bound] | split; [apply Z.div_pos|apply Z.div_lt_upper_bound]]; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite (Z_div_mod_eq_full d 256) at 3. lia.
Qed.

Lemma sym_calls_of : forall s lfc ldl dfc ddl sx d lc, sym_at s sx d lc -> 0 <= d < 65536 ->
  sym_calls s lfc ldl dfc ddl sx = calls_of lfc ldl dfc ddl (d, lc).
Proof.
  intros s lfc ldl dfc ddl sx d lc SA Hd. destruct (sym_read s sx d lc SA Hd) as [D L].
  unfold sym_calls, calls_of. rewrite D, L. reflexivity.
Qed.


Fixpoint csum (tabs : Z * Z -> Z) (l : list (Z * Z)) : Z :=
  match l with [] => 0 | x :: r => tabs x + csum tabs r end.

Lemma csum_app : forall f a b, csum f (a ++ b) = csum f a + csum f b.
Proof. induction a; intros; cbn; [lia|]. rewrite IHa. lia. Qed.

Lemma sumlen_flat_map : forall (g : Z * Z -> list (Z * Z)) l,
  sumlen (flat_map g l) = csum (fun x => sumlen (g x)) l.
Proof. induction l; cbn; [reflexivity|]. rewrite sumlen_app, IHl. reflexivity. Qed.

Lemma lens_ok_app : forall a b, lens_ok a -> lens_ok b -> lens_ok (a ++ b).
Proof. intros. apply Forall_app. auto. Qed.

Lemma lens_ok_flat_map : forall (g : Z * Z -> list (Z * Z)) l,
  (forall x, In x l -> lens_ok (g x)) -> lens_ok (flat_map g l).
Proof.
  induction l as [|x l IH]; intros H; cbn; [constructor|].
  apply lens_ok_app; [apply H; left; reflexivity | apply IH; intros; apply H; right; assumption].
Qed.

Lemma In_firstn : forall {A} k (l : list A) x, In x (firstn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_app_iff. left. exact H. Qed.
Lemma In_skipn : forall {A} k (l : list A) x, In x (skipn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_app_iff. right. exact H. Qed.
Lemma Forall_nth_error_In : forall {A} (P : A -> Prop) l k x, Forall P l -> nth_error l k = Some x -> P x.
Proof. intros A P l k x HF Hk. apply (proj1 (Forall_forall P l) HF). eapply nth_error_In. exact Hk. Qed.

Section Race.
  Variable s0 : deflate_state.
  Variables lfc ldl dfc ddl : arr.
  Variable syms : list (Z * Z).

  Let L : Z := ds_lit_bufsize s0.
  Let CO := calls_of lfc ldl dfc ddl.
  Let CC := cost_of lfc ldl dfc ddl.
  Let n : nat := length syms.

  Hypothesis SYMN : ds_sym_next s0 = 3 * Z.of_nat n.
  Hypothesis BYTES : forall i d lc, nth_error syms i = Some (d, lc) -> sym_at s0 (3 * Z.of_nat i) d lc.
  Hypothesis DRANGE : Forall (fun dl => 0 <= fst dl < 65536) syms.
  Hypothesis BV0 : 0 <= ds_bi_valid s0 <= 16.
  Hypothesis LENS : forall dl, In dl syms -> lens_ok (CO dl).
  Hypothesis RACE : forall k, (k < n)%nat -> vsize s0 + csum CC (firstn k syms) <= 8 * (L + 3 * Z.of_nat k) + 7.

  Definition SK (k : nat) : deflate_state := sbs_run s0 (flat_map CO (firstn k syms)).

  Lemma firstn_S_nth : forall {A} (l : list A) k x, nth_error l k = Some x -> firstn (S k) l = firstn k l ++ [x].
  Proof.
    induction l as [|y l IH]; intros [|k] x H; cbn in *; try discriminate.
    - inversion H. reflexivity.
    - rewrite (IH k x H). reflexivity.
  Qed.

  Lemma LENS_firstn : forall k, lens_ok (flat_map CO (firstn k syms)).
  Proof. intros k. apply lens_ok_flat_map. intros x Hx. apply LENS. eapply In_firstn. exact Hx. Qed.

  Lemma SK_facts : forall k,
    ds_pending s0 <= ds_pending (SK k)
    /\ arr_len (ds_pending_buf (SK k)) = arr_len (ds_pending_buf s0)
    /\ (forall i, ds_pending (SK k) <= i -> arr_get (ds_pending_buf (SK k)) i = arr_get (ds_pending_buf s0) i)
    /\ ds_lit_bufsize (SK k) = L /\ ds_sym_next (SK k) = 3 * Z.of_nat n
    /\ 0 <= ds_bi_valid (SK k) <= 16
    /\ vsize (SK k) = vsize s0 + csum CC (firstn k syms).
  Proof.
    intros k. unfold SK. pose proof (sbs_fp (flat_map CO (firstn k syms)) s0 (LENS_firstn k) BV0) as H. cbv zeta in H.
    destruct H as (P & AL & O & LB & SN & BV & VS).
    split; [lia|]. split; [exact AL|]. split; [intros i Hi; apply O; lia|].
    split; [exact LB|]. split; [rewrite SN, SYMN; reflexivity|]. split; [exact BV|].
    rewrite VS, sumlen_flat_map. reflexivity.
  Qed.

  Lemma SK_sym : forall k d lc, nth_error syms k = Some (d, lc) ->
    sym_at (SK k) (3 * Z.of_nat k) d lc /\ sym_calls (SK k) lfc ldl dfc ddl (3 * Z.of_nat k) = CO (d, lc)
    /\ SK (S k) = sbs_run (SK k) (CO (d, lc)).
  Proof.
    intros k d lc Hk.
    assert (Hkn : (k < n)%nat) by (unfold n; apply (proj1 (nth_error_Some syms k)); rewrite Hk; discriminate).
    destruct (SK_facts k) as (P & AL & O & LB & SN & BV & VS).
    pose proof (RACE k Hkn) as R.
    assert (PD : ds_pending (SK k) <= L + 3 * Z.of_nat k).
    { pose proof (pending_le_vsize (SK k) ltac:(lia)). lia. }
    assert (SA : sym_at (SK k) (3 * Z.of_nat k) d lc).
    { destruct (BYTES k d lc Hk) as (A & B & C). unfold sym_at. rewrite LB. fold L in A, B, C.
      rewrite !O by lia. auto. }
    assert (DR : 0 <= d < 65536).
    { exact (Forall_nth_error_In _ _ _ _ DRANGE Hk). }
    split; [exact SA|]. split; [apply sym_calls_of; assumption|].
    unfold SK. rewrite (firstn_S_nth syms k (d, lc) Hk), flat_map_app, sbs_run_app. cbn [flat_map]. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma cb_loop_SK : forall f k, (k < n)%nat -> (n - k <= f)%nat ->
    compress_block_loop f (SK k) lfc ldl dfc ddl (3 * Z.of_nat k) = SK n.
  Proof.
    induction f as [|f IH]; intros k Hk Hf; [lia|].
    destruct (nth_error syms k) as [[d lc]|] eqn:Hnth; [| apply nth_error_None in Hnth; unfold n in Hk; lia].
    destruct (SK_sym k d lc Hnth) as (SA & SC & SE).
    rewrite cb_loop_S. cbv zeta. rewrite SC, <- SE.
    destruct (SK_facts (S k)) as (_ & _ & _ & _ & SN & _).
    rewrite SN. replace (3 * Z.of_nat k + 1 + 1 + 1) with (3 * Z.of_nat (S k)) by lia.
    destruct (Z.ltb_spec (3 * Z.of_nat (S k)) (3 * Z.of_nat n)).
    - apply IH; lia.
    - replace n with (S k) by lia. reflexivity.
  Qed.

  Theorem cb_loop_run : (0 < n)%nat ->
    compress_block_loop (Z.to_nat (ds_sym_next s0)) s0 lfc ldl dfc ddl 0 = sbs_run s0 (flat_map CO syms).
  Proof.
    intros Hn. transitivity (compress_block_loop (Z.to_nat (ds_sym_next s0)) (SK 0) lfc ldl dfc ddl (3 * Z.of_nat 0)); [reflexivity|].
    rewrite cb_loop_SK by lia. unfold SK. rewrite firstn_all2 by lia. reflexivity.
  Qed.

  Variable PBL : Z.
  Hypothesis PBLeq : arr_len (ds_pending_buf s0) = PBL.
  Hypothesis ROOM : vsize s0 + csum CC syms <= 8 * PBL.
  Hypothesis SYMROOM : L + 3 * Z.of_nat n <= PBL.
  Hypothesis BINV0 : BINV PBL s0.
  Hypothesis DISTS : Forall (fun dl => fst dl <= 32768) syms.
  Definition tabs_ok (dl : Z * Z) : Prop :=
    (fst dl = 0 -> 0 <= arr_get ldl (snd dl) <= 15)
    /\ (fst dl <> 0 -> 0 <= arr_get ldl (arr_get length_code_a (snd dl) + LITERALS + 1) <= 15
                     /\ 0 <= arr_get ddl (d_code (fst dl - 1)) <= 15).
  Hypothesis TABS : Forall tabs_ok syms.

  Lemma csum_firstn_le : forall k, csum CC (firstn k syms) <= csum CC syms.
  Proof.
    intros k. rewrite <- (firstn_skipn k syms) at 2. rewrite csum_app.
    enough (0 <= csum CC (skipn k syms)) by lia.
    pose proof (sumlen_nonneg (flat_map CO (skipn k syms))) as X.
    rewrite sumlen_flat_map in X. apply X. apply lens_ok_flat_map. intros x Hx. apply LENS. eapply In_skipn. exact Hx.
  Qed.

  Lemma SK_BINV : forall k, (k <= n)%nat -> BINV PBL (SK k).
  Proof.
    intros k Hk. unfold SK. apply sbs_BINV; [exact BINV0|]. apply sbs_ok_of_total; [exact BINV0| apply LENS_firstn|].
    rewrite sumlen_flat_map. change (csum (fun x => sumlen (CO x)) (firstn k syms)) with (csum CC (firstn k syms)).
    pose proof (csum_firstn_le k). lia.
  Qed.

  Lemma cb_ok_SK : forall f k, (k < n)%nat -> cb_ok PBL f (SK k) lfc ldl dfc ddl (3 * Z.of_nat k).
  Proof.
    induction f as [|f IH]; intros k Hk; [exact I|].
    destruct (nth_error syms k) as [[d lc]|] eqn:Hnth; [| apply nth_error_None in Hnth; unfold n in Hk; lia].
    destruct (SK_sym k d lc Hnth) as (SA & SC & SE).
    destruct (SK_facts k) as (P & AL & O & LB & SN & BV & VS).
    assert (DR : 0 <= d < 65536) by exact (Forall_nth_error_In _ _ _ _ DRANGE Hnth).
    assert (DM : d <= 32768) by exact (Forall_nth_error_In _ _ _ _ DISTS Hnth).
    cbn [cb_ok]. split.
    - unfold sym_ok. split; [lia|]. split; [rewrite LB; lia|].
      destruct (sym_read (SK k) (3 * Z.of_nat k) d lc SA DR) as [D Lc]. rewrite D, Lc.
      pose proof (Forall_nth_error_In _ _ _ _ TABS Hnth) as [T1 T2]. cbn [fst snd] in T1, T2.
      split; [lia|]. split; [exact T1|]. split; [exact T2|].
      rewrite SC. apply sbs_ok_of_total; [apply SK_BINV; lia| apply LENS; eapply nth_error_In; eauto|].
      rewrite VS. pose proof (csum_firstn_le (S k)) as X. rewrite (firstn_S_nth syms k (d, lc) Hnth), csum_app in X. cbn [csum] in X.
      change (sumlen (CO (d, lc))) with (CC (d, lc)). lia.
    - cbv zeta. rewrite SC, <- SE. destruct (SK_facts (S k)) as (_ & _ & _ & _ & SN' & _). rewrite SN'.
      replace (3 * Z.of_nat k + 1 + 1 + 1) with (3 * Z.of_nat (S k)) by lia.
      destruct (Z.ltb_spec (3 * Z.of_nat (S k)) (3 * Z.of_nat n)); [|exact I].
      apply IH. lia.
  Qed.

  Theorem cb_race_ok :
    PBB s0 -> 0 <= arr_get ldl END_BLOCK <= 15 ->
    vsize s0 + csum CC syms + arr_get ldl END_BLOCK <= 8 * PBL ->
    compress_block_ok PBL s0 lfc ldl dfc ddl
    /\ compress_block s0 lfc ldl dfc ddl = send_bits (sbs_run s0 (flat_map CO syms)) (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)
    /\ vsize (compress_block s0 lfc ldl dfc ddl) = vsize s0 + csum CC syms + arr_get ldl END_BLOCK
    /\ BINV PBL (compress_block s0 lfc ldl dfc ddl) /\ PBB (compress_block s0 lfc ldl dfc ddl)
    /\ (forall i, ds_pending (compress_block s0 lfc ldl dfc ddl) <= i ->
          arr_get (ds_pending_buf (compress_block s0 lfc ldl dfc ddl)) i = arr_get (ds_pending_buf s0) i)
    /\ arr_len (ds_pending_buf (compress_block s0 lfc ldl dfc ddl)) = PBL.
  Proof.
    intros PB0 HE TOT.
    assert (RUN : (if negb (ds_sym_next s0 =? 0) then compress_block_loop (Z.to_nat (ds_sym_next s0)) s0 lfc ldl dfc ddl 0 else s0)
                  = SK n).
    { rewrite SYMN. destruct (Z.eqb_spec (3 * Z.of_nat n) 0); cbn [negb].
      - unfold SK. replace n with 0%nat by lia. reflexivity.
      - rewrite <- SYMN. rewrite cb_loop_run by lia. unfold SK. rewrite firstn_all2 by lia. reflexivity. }
    assert (SKn : SK n = sbs_run s0 (flat_map CO syms)) by (unfold SK; rewrite firstn_all2 by lia; reflexivity).
    destruct (SK_facts n) as (P & AL & O & LB & SN & BV & VS). rewrite firstn_all2 in VS by lia.
    pose proof (SK_BINV n ltac:(lia)) as BN.
    assert (OKE : sbs_ok PBL (SK n) [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)]).
    { apply sbs_ok_of_total; [exact BN| constructor; [cbn; lia| constructor] | cbn; lia]. }
    assert (CB : compress_block s0 lfc ldl dfc ddl = send_bits (SK n) (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)).
    { unfold compress_block, send_code. rewrite RUN. reflexivity. }
    split.
    { unfold compress_block_ok. split; [exact BINV0|]. split; [exact PB0|]. split; [| split; [exact HE|]].
      - intros Hs. change (cb_ok PBL (Z.to_nat (ds_sym_next s0)) (SK 0) lfc ldl dfc ddl (3 * Z.of_nat 0)). apply cb_ok_SK. rewrite SYMN in Hs. lia.
      - cbv zeta. rewrite RUN. exact OKE. }
    split; [rewrite CB, SKn; reflexivity|].
    rewrite CB. split; [rewrite send_bits_size, VS; lia|].
    split. { apply send_bits_BINV; [exact BN| lia|]. cbn in OKE. tauto. }
    split. { apply send_bits_PBB. unfold SK. apply sbs_PBB. exact PB0. }
    pose proof (send_bits_fp (SK n) (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)) as (P1 & L1 & O1 & _). cbv zeta in *.
    split. { intros i Hi. rewrite O1 by lia. apply O. lia. }
    rewrite L1, AL. exact PBLeq.
  Qed.
End Race.


Definition excess (tabs : Z * Z -> Z) (l : list (Z * Z)) : Z := csum (fun x => Z.max 0 (tabs x - 24)) l.

Lemma csum_le_excess : forall tabs l, csum tabs l <= 24 * Z.of_nat (length l) + excess tabs l.
Proof. induction l; cbn -[Z.of_nat]; [lia|]. unfold excess in *. cbn. lia. Qed.

Lemma excess_firstn_le : forall tabs k l, excess tabs (firstn k l) <= excess tabs l.
Proof.
  intros tabs k l. unfold excess. rewrite <- (firstn_skipn k l) at 2. rewrite csum_app.
  enough (0 <= csum (fun x => Z.max 0 (tabs x - 24)) (skipn k l)) by lia.
  induction (skipn k l); cbn; lia.
Qed.

Theorem cb_race_suff : forall V0 L tabs (syms : list (Z * Z)),
  V0 + excess tabs syms <= 8 * L + 7 ->
  forall k, (k < length syms)%nat -> V0 + csum tabs (firstn k syms) <= 8 * (L + 3 * Z.of_nat k) + 7.
Proof.
  intros V0 L tabs syms H k Hk.
  pose proof (csum_le_excess tabs (firstn k syms)) as A. rewrite firstn_length_le in A by lia.
  pose proof (excess_firstn_le tabs k syms). lia.
Qed.
