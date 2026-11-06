(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma two64_pos' : 0 < two64. Proof. unfold two64; lia. Qed.

Lemma u_lden : forall E l, bv_unsigned (lden E l) = lz E l mod two64.
Proof. intros. unfold lden. apply u_Z_to_bv. Qed.

Lemma u_small64 : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite u_Z_to_bv. apply Z.mod_small. exact Hz. Qed.

Lemma word_add1 : forall z, (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
Proof.
  intros z. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1. unfold bv_wrap. rewrite Z.add_mod_idemp_l by (unfold bv_modulus; lia). reflexivity.
Qed.

Lemma lden_Z_to_bv_u : forall E l, Z_to_bv 64 (bv_unsigned (lden E l)) = lden E l.
Proof. intros. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma terms_eqb_eq : forall x y, terms_eqb x y = true -> x = y.
Proof.
  induction x as [|[p k] x IH]; intros [|[q k'] y] H; cbn in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H4 H5]. apply Pos.eqb_eq in H4. apply Z.eqb_eq in H5. subst.
    f_equal. apply IH. exact H3.
Qed.

Lemma lin_off_sound : forall E a b c, lin_off a b = Some c -> lden E (lsub a b) = Z_to_bv 64 c /\ 0 <= c < two64.
Proof.
  intros E a b c H. unfold lin_off in H. destruct (terms_eqb (l_t a) (l_t b)) eqn:Ht.
  - injection H as <-. apply terms_eqb_eq in Ht. split; [|apply w64_range].
    unfold lden. apply Z_to_bv_eqm. eapply eqm_trans; [apply lz_lsub|].
    unfold lz. rewrite Ht. eapply eqm_trans; [|apply eqm_sym, eqm_w64].
    replace (l_c a + tsum E (l_t b) - (l_c b + tsum E (l_t b))) with (l_c a - l_c b) by lia. apply eqm_refl.
  - discriminate.
Qed.

Lemma rg_off_sound : forall E fs R a w o,
  size_lo fs R <= rsz E R ->
  rg_off fs R a w = Some o ->
  0 <= o /\ o + w <= rsz E R /\
  lden E a = Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + o).
Proof.
  intros E fs R a w o Hsz H. unfold rg_off in H.
  destruct (lin_off a (rg_base R)) as [c|] eqn:Hc; [|discriminate].
  destruct (Z.leb 0 c && Z.leb (c + w) (size_lo fs R))%bool eqn:Hb; [|discriminate].
  injection H as <-. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2.
  split; [exact H1|]. split; [lia|].
  destruct (lin_off_sound E _ _ _ Hc) as [Hv _].
  rewrite lden_lsub in Hv.
  assert (Hx : lden E a = bv_add (lden E (rg_base R)) (Z_to_bv 64 c)).
  { rewrite <- Hv. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite Z.add_mod_idemp_r by (unfold two64; lia).
    replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned (lden E a) - bv_unsigned (lden E (rg_base R))))
      with (bv_unsigned (lden E a)) by lia.
    symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
  rewrite Hx. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_from : forall m n (X : Z),
  0 <= X -> X + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> rd1 segs m (Z_to_bv 64 (X + i)) <> None) ->
  exists bs, rdn segs m (Z_to_bv 64 X) n = Some bs /\ length bs = n /\
    (forall i b, nth_error bs i = Some b -> rd1 segs m (Z_to_bv 64 (X + Z.of_nat i)) = Some b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m n. induction n as [|n IH]; intros X HX Hn Hall.
  - exists []. split; [reflexivity|]. split; [reflexivity|]. intros [|i] b H; discriminate.
  - cbn [rdn]. pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    unfold rd1 in H0. destruct (match m (Z_to_bv 64 X) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 X) end) as [b|] eqn:Hb;
      [|exfalso; exact (H0 eq_refl)].
    rewrite word_add1.
    destruct (IH (X + 1)) as (bs & Hbs & Hlen & Hnth); [lia | lia | |].
    { intros i Hi. replace (X + 1 + i) with (X + (i + 1)) by lia. apply Hall. lia. }
    rewrite Hbs. exists (b :: bs). split; [reflexivity|]. split; [cbn; lia|].
    intros [|i] b' H; cbn [nth_error] in H.
    + injection H as <-. rewrite Z.add_0_r. unfold rd1. exact Hb.
    + replace (X + Z.of_nat (S i)) with (X + 1 + Z.of_nat i) by lia. exact (Hnth i b' H).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma store_ok_from : forall m n (X : Z),
  0 <= X -> X + Z.of_nat n <= two64 ->
  (forall i, 0 <= i < Z.of_nat n -> wview segs m (Z_to_bv 64 (X + i)) <> None) ->
  store_ok segs m (Z_to_bv 64 X) n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m n. induction n as [|n IH]; intros X HX Hn Hall; [reflexivity|].
  cbn [store_ok]. pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (wview segs m (Z_to_bv 64 X)) as [b|]; [|exfalso; exact (H0 eq_refl)].
  rewrite word_add1. apply IH; [lia | lia |]. intros i Hi. replace (X + 1 + i) with (X + (i + 1)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_spec : forall bs m (X : Z) (x : word),
  0 <= X -> X + Z.of_nat (length bs) <= two64 ->
  write_to_mem m (Z_to_bv 64 X) bs x =
    if (Z.leb X (bv_unsigned x) && Z.ltb (bv_unsigned x) (X + Z.of_nat (length bs)))%bool
    then nth_error bs (Z.to_nat (bv_unsigned x - X)) else m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b bs IH]; intros m X x HX Hn.
  - cbn [write_to_mem length]. replace (X + Z.of_nat 0) with X by lia.
    destruct (Z.leb X (bv_unsigned x) && Z.ltb (bv_unsigned x) X)%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - cbn [write_to_mem length] in Hn |- *. rewrite word_add1. rewrite IH by lia.
    pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64) with two64 in Hx.
    destruct (Z.eq_dec (bv_unsigned x) X) as [Heq|Hne].
    + rewrite Heq. replace (Z.leb (X + 1) X) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
      replace (Z.leb X X && Z.ltb X (X + Z.of_nat (S (length bs))))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace (X - X) with 0 by lia. cbn.
      assert (Hxw : x = Z_to_bv 64 X) by (apply bv_eq; rewrite u_small64 by lia; exact Heq).
      rewrite Hxw. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
    + assert (Hb : bv_eqb x (Z_to_bv 64 X) = false).
      { unfold bv_eqb. apply Z.eqb_neq. rewrite u_small64 by lia. exact Hne. }
      destruct (Z.leb (X + 1) (bv_unsigned x) && Z.ltb (bv_unsigned x) (X + 1 + Z.of_nat (length bs)))%bool eqn:E1.
      * apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        replace (Z.leb X (bv_unsigned x) && Z.ltb (bv_unsigned x) (X + Z.of_nat (S (length bs))))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
        replace (Z.to_nat (bv_unsigned x - X)) with (S (Z.to_nat (bv_unsigned x - (X + 1)))) by lia. reflexivity.
      * replace (Z.leb X (bv_unsigned x) && Z.ltb (bv_unsigned x) (X + Z.of_nat (S (length bs))))%bool with false.
        { rewrite Hb. reflexivity. }
        symmetry. apply andb_false_iff. apply andb_false_iff in E1. destruct E1 as [E1|E1].
        -- apply Z.leb_gt in E1. left. apply Z.leb_gt. lia.
        -- apply Z.ltb_ge in E1. right. apply Z.ltb_ge. lia.
Qed.

End WithSegs.

(* [comment removed for export] *)
Lemma okey_pos : forall o, 0 <= o -> Zpos (okey o) - 1 = o.
Proof. intros o Ho. unfold okey. rewrite Z2Pos.id by lia. lia. Qed.

Lemma okey_inj : forall o1 o2, 0 <= o1 -> 0 <= o2 -> okey o1 = okey o2 -> o1 = o2.
Proof. intros o1 o2 H1 H2 H. rewrite <- (okey_pos o1 H1), <- (okey_pos o2 H2), H. reflexivity. Qed.

Lemma get_bytes_spec : forall t n o bvs,
  get_bytes t o n = Some bvs ->
  length bvs = n /\ forall i v, nth_error bvs i = Some v -> tget (okey (o + Z.of_nat i)) t = Some v.
Proof.
  intros t n. induction n as [|n IH]; intros o bvs H; cbn [get_bytes] in H.
  - injection H as <-. split; [reflexivity|]. intros [|i] v Hv; discriminate.
  - destruct (tget (okey o) t) as [v|] eqn:Ho; [|discriminate].
    destruct (get_bytes t (o + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (o + 1) r Hr) as [Hlen Hnth]. split; [cbn; lia|].
    intros [|i] v' Hv; cbn [nth_error] in Hv.
    + injection Hv as <-. rewrite Z.add_0_r. exact Ho.
    + rewrite <- (Hnth i v' Hv). f_equal. f_equal. lia.
Qed.

Lemma put_bytes_spec : forall l t o p,
  0 <= o ->
  tget p (put_bytes t o l) =
    if (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length l)))%bool
    then nth_error l (Z.to_nat (Zpos p - 1 - o)) else tget p t.
Proof.
  induction l as [|v l IH]; intros t o p Ho; cbn [put_bytes length].
  - destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat 0))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - rewrite IH by lia.
    destruct (Pos.eq_dec p (okey o)) as [->|Hne].
    + rewrite okey_pos by lia. replace (Z.leb (o + 1) o) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
      rewrite tget_tset_same.
      replace (Z.leb o o && Z.ltb o (o + Z.of_nat (S (length l))))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace (o - o) with 0 by lia. reflexivity.
    + rewrite tget_tset_other by congruence.
      assert (Hp : Zpos p - 1 <> o) by (intros Hc; apply Hne; unfold okey; rewrite <- Hc; rewrite Z.sub_add; reflexivity).
      destruct (Z.leb (o + 1) (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + 1 + Z.of_nat (length l)))%bool eqn:E1.
      * apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        replace (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (S (length l))))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
        replace (Z.to_nat (Zpos p - 1 - o)) with (S (Z.to_nat (Zpos p - 1 - (o + 1)))) by lia. reflexivity.
      * replace (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (S (length l))))%bool with false; [reflexivity|].
        symmetry. apply andb_false_iff. apply andb_false_iff in E1. destruct E1 as [E1|E1].
        -- apply Z.leb_gt in E1. left. apply Z.leb_gt. lia.
        -- apply Z.ltb_ge in E1. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma tget_tclr_same : forall {A} p (t : tree A), tget p (tclr p t) = None.
Proof. intros A p. induction p as [p IH|p IH|]; intros [|l v r]; cbn [tclr tget]; auto. Qed.
Lemma tget_tclr_other : forall {A} p q (t : tree A), p <> q -> tget q (tclr p t) = tget q t.
Proof.
  intros A p. induction p as [p IH|p IH|]; intros q [|l v r] Hne; cbn [tclr tget]; auto;
    destruct q as [q|q|]; cbn [tget]; auto; try (apply IH; congruence); congruence.
Qed.
Lemma put_bytes_z_spec : forall l t o p,
  0 <= o ->
  tget p (put_bytes_z t o l) =
    if (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (length l)))%bool
    then match nth_error l (Z.to_nat (Zpos p - 1 - o)) with Some v => if is_bk0 v then None else Some v | None => None end
    else tget p t.
Proof.
  induction l as [|v l IH]; intros t o p Ho; cbn [put_bytes_z length].
  - destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat 0))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - rewrite IH by lia.
    destruct (Pos.eq_dec p (okey o)) as [->|Hne].
    + rewrite okey_pos by lia. replace (Z.leb (o + 1) o) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
      replace (Z.leb o o && Z.ltb o (o + Z.of_nat (S (length l))))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      replace (o - o) with 0 by lia. change (Z.to_nat 0) with 0%nat. cbn [nth_error].
      destruct (is_bk0 v); [apply tget_tclr_same | apply tget_tset_same].
    + assert (Hp : Zpos p - 1 <> o) by (intros Hc; apply Hne; unfold okey; rewrite <- Hc; rewrite Z.sub_add; reflexivity).
      assert (Ht : tget p (if is_bk0 v then tclr (okey o) t else tset (okey o) v t) = tget p t)
        by (destruct (is_bk0 v); [apply tget_tclr_other | apply tget_tset_other]; congruence).
      rewrite Ht.
      destruct (Z.leb (o + 1) (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + 1 + Z.of_nat (length l)))%bool eqn:E1.
      * apply andb_prop in E1 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        replace (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (S (length l))))%bool with true
          by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
        replace (Z.to_nat (Zpos p - 1 - o)) with (S (Z.to_nat (Zpos p - 1 - (o + 1)))) by lia. reflexivity.
      * destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat (S (length l))))%bool eqn:E2; [|reflexivity].
        apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
        apply andb_false_iff in E1 as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia.
Qed.

(* [comment removed for export] *)
Lemma nth_Z_to_le_bytes : forall n z j, (j < n)%nat -> nth_error (Z_to_le_bytes n z) j = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j))).
Proof.
  induction n as [|n IH]; intros z j Hj; [lia|]. destruct j as [|j]; cbn [Z_to_le_bytes nth_error].
  - rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma Z_to_bv8_bits : forall x y, (forall k, 0 <= k < 8 -> Z.testbit x k = Z.testbit y k) -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
  apply Z.bits_inj'. intros k Hk. destruct (Z.lt_ge_cases k 8) as [Hl|Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. apply H. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_of_mod : forall u n j, 0 <= j -> 8 * j + 8 <= n ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ n) (8 * j)) = Z_to_bv 8 (Z.shiftr u (8 * j)).
Proof.
  intros u n j Hj Hn. apply Z_to_bv8_bits. intros k Hk.
  rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma byte_land255 : forall z, Z_to_bv 8 (Z.land z 255) = Z_to_bv 8 z.
Proof.
  intros z. apply Z_to_bv8_bits. intros k Hk. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma lin_eqb_eq : forall a b, lin_eqb a b = true -> a = b.
Proof.
  intros [ca ta] [cb tb] H. unfold lin_eqb in H. cbn [l_c l_t] in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. subst cb. f_equal. revert tb H2. induction ta as [|[p k] ta IH]; intros [|[q k'] tb] H; cbn in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H4 H5]. apply Pos.eqb_eq in H4. apply Z.eqb_eq in H5. subst.
    f_equal. apply IH. exact H3.
Qed.

Lemma is_bv_of_spec : forall v l j, is_bv_of v j l = true -> forall i x, nth_error l i = Some x -> x = BV v (j + Z.of_nat i).
Proof.
  intros v l. induction l as [|x l IH]; intros j H i y Hy; [destruct i; discriminate|].
  destruct x as [b|v' j']; cbn [is_bv_of] in H; [discriminate|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. apply Z.eqb_eq in H2. subst v' j'.
  destruct i as [|i]; cbn [nth_error] in Hy.
  - injection Hy as <-. rewrite Z.add_0_r. reflexivity.
  - rewrite (IH (j + 1) H3 i y Hy). f_equal. lia.
Qed.

Lemma all_bk_spec : forall l bks, all_bk l = Some bks -> l = map BK bks.
Proof.
  induction l as [|x l IH]; intros bks H; cbn [all_bk] in H.
  - injection H as <-. reflexivity.
  - destruct x as [b|v j]; [|discriminate]. destruct (all_bk l) as [r|] eqn:E; [|discriminate]. injection H as <-.
    cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma st_bytes_nth : forall v z j n i x, nth_error (st_bytes v z j n) i = Some x ->
  (i < n)%nat /\ x = match z with Some c => BK (Z.land (Z.shiftr c (8 * (j + Z.of_nat i))) 255) | None => BV v (j + Z.of_nat i) end.
Proof.
  intros v z j n. revert j. induction n as [|n IH]; intros j i x H; cbn [st_bytes] in H; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in H.
  - injection H as <-. split; [lia|]. rewrite Z.add_0_r. reflexivity.
  - destruct (IH (j + 1) i x H) as [Hi Hx]. split; [lia|]. rewrite Hx. replace (j + 1 + Z.of_nat i) with (j + Z.of_nat (S i)) by lia. reflexivity.
Qed.

Lemma length_st_bytes : forall v z j n, length (st_bytes v z j n) = n.
Proof. intros v z j n. revert j. induction n as [|n IH]; intros j; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
