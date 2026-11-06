From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c box_name_ucall.
Import ListNotations.
Open Scope Z_scope.

Lemma bbuf_bytes : forall m A n c, bbuf m A n c -> bytes_at rsegs m A (bn_bytes c).
Proof. intros m A n c (r & _ & B & _). apply bytes_at_app in B. tauto. Qed.

Lemma bbuf_stk : forall m A n c, bbuf m A n c -> stk rsegs m A (A + Z.of_nat n).
Proof.
  intros m A n c (r & L & H). apply u8arr_stk in H. rewrite length_app, bn_bytes_length, L in H. exact H.
Qed.

Lemma rw_CB_prefix : forall m A n j k, rw_cells rsegs m A [CB n j] -> (k <= n)%nat ->
  rw_cells rsegs m A [CB k (firstn k j)].
Proof.
  intros m A n j k [[Hwf Hb] Hw] Hk. cbn in Hwf. destruct Hwf as [Lj _].
  cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn. split; [rewrite length_firstn; lia|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite <- (firstn_skipn k j) in Hb.
    apply bytes_at_app in Hb. tauto.
  - cbn [cells_size csize]. eapply wr_at_prefix; [exact Hw|lia].
Qed.

Lemma stk_cpy : forall m m' lo hi d k bs,
  stk rsegs m lo hi -> munch [(d, d + k)] m m' -> Z.of_nat (length bs) = k -> wmono rsegs m m' ->
  bytes_at rsegs m' d bs -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi d k bs (H1 & H2 & H) MU <- WM (Hd & Hdl & HB). split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.leb_spec d a) as [L1|L1]; [destruct (Z.ltb_spec a (d + Z.of_nat (length bs))) as [L2|L2]|].
  - replace a with (d + Z.of_nat (Z.to_nat (a - d))) by lia. rewrite HB by lia.
    destruct (nth_error bs (Z.to_nat (a - d))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn. split; [lia|exact I].
Qed.

Lemma bbuf_upd : forall m A n c r x,
  u8arr rsegs m A (upd (bn_bytes c ++ r) (Z.to_nat (Z.of_nat (length c))) (Z_to_bv 8 x)) ->
  (length c + length r = n)%nat -> (length c < n)%nat -> bbuf m A n (c ++ [x]).
Proof.
  intros m A n c r x H L Lt. destruct r as [|y r]; [cbn in L; lia|].
  rewrite Nat2Z.id in H. rewrite <- (bn_bytes_length c) in H at 1. rewrite bl_upd_mid in H.
  exists r. split; [rewrite length_app; cbn in L |- *; lia|].
  rewrite bn_bytes_app, <- app_assoc. exact H.
Qed.

Ltac bst H :=
  try lazymatch goal with |- context [le1 (Z_to_bv 64 ?c)] => rewrite (bl_le1 c) by lia end;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 (Z_to_bv 64 (?A + ?k)) [?b]) _) =>
      let H' := fresh "HW" in
      pose proof (u8arr_write rsegs m1 A _ k b H ltac:(rewrite ?length_app, ?bn_bytes_length; lia)) as H';
      clear H;
      store_done
  end.

Lemma bn_leq_eq : forall a b, bn_leq a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn; try (split; congruence).
  rewrite andb_true_iff, Z.eqb_eq, IH. split; [intros [-> ->]; reflexivity | intros E; inversion E; tauto].
Qed.

Definition dig_b (l : list Z) : bool := forallb (fun c => (48 <=? c) && (c <=? 57)) l.

Definition dec_chk (x : Z) : bool :=
  (0 <=? x) && (x <=? 40) && Nat.eqb (length (bn_dec x 2)) 2 && Nat.leb 1 (length (bn_dec x 1)) &&
  Nat.leb (length (bn_dec x 1)) 2 && bn_leq (sb_dec_D x 2) (bn_dec x 2) && bn_leq (sb_dec_D x 1) (bn_dec x 1) &&
  dig_b (bn_dec x 2) && dig_b (bn_dec x 1).

Lemma dig_b_ok : forall l, dig_b l = true -> Forall (fun c => 48 <= c <= 57) l.
Proof.
  intros l H. unfold dig_b in H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc.
  specialize (H c Hc). apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma bn_ok_dec : forall x, bn_ok x = true ->
  0 <= x <= 40 /\ length (bn_dec x 2) = 2%nat /\ (1 <= length (bn_dec x 1) <= 2)%nat /\
  sb_dec_D x 2 = bn_dec x 2 /\ sb_dec_D x 1 = bn_dec x 1 /\
  Forall (fun c => 48 <= c <= 57) (bn_dec x 2) /\ Forall (fun c => 48 <= c <= 57) (bn_dec x 1).
Proof.
  intros x H. apply bn_ok_in in H.
  assert (A : forallb dec_chk bn_oks = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A x H). unfold dec_chk in A.
  repeat match type of A with andb _ _ = true => apply andb_true_iff in A; destruct A as [A ?] end.
  repeat match goal with
  | E : Z.leb _ _ = true |- _ => apply Z.leb_le in E
  | E : Nat.leb _ _ = true |- _ => apply Nat.leb_le in E
  | E : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in E
  | E : bn_leq _ _ = true |- _ => apply bn_leq_eq in E
  | E : dig_b _ = true |- _ => apply dig_b_ok in E
  end.
  repeat split; first [assumption | lia].
Qed.

Lemma args_ok_split : forall nm nl tk tl dp dl x y, bn_args_ok nm nl tk tl dp dl x y = true ->
  nm <> 0 /\ tk <> 0 /\ dp <> 0 /\ nl <> 0 /\ tl <> 0 /\ dl <> 0 /\ bn_ok x = true /\ bn_ok y = true /\
  (x = 0 /\ y = 0 -> False).
Proof.
  intros nm nl tk tl dp dl x y H. unfold bn_args_ok in H.
  repeat match type of H with andb _ _ = true => apply andb_true_iff in H; destruct H as [H ?] end.
  repeat match goal with
  | E : negb (Z.eqb _ _) = true |- _ => apply negb_true_iff in E; apply Z.eqb_neq in E
  | E : negb (andb (Z.eqb _ _) (Z.eqb _ _)) = true |- _ => apply negb_true_iff in E
  end.
  repeat split; try assumption.
  intros [-> ->]. lazymatch goal with E : (0 =? 0) && (0 =? 0) = false |- _ => discriminate E end.
Qed.

Lemma bn_DP_len : forall l x y, bn_ok x = true -> bn_ok y = true ->
  (length l + 15 <= length (bn_DP l x y) <= length l + 17)%nat.
Proof.
  intros l x y Hx Hy. destruct (bn_ok_dec x Hx) as (_ & _ & Lx & _). destruct (bn_ok_dec y Hy) as (_ & _ & Ly & _).
  unfold bn_DP. rewrite !length_app. cbn [length]. lia.
Qed.

Lemma stk_glue : forall m lo mid A hi, stk rsegs m lo mid -> stk rsegs m A hi -> A = mid -> lo <= mid <= hi ->
  stk rsegs m lo hi.
Proof. intros m lo mid A hi H1 H2 E L. subst A. eapply stk_merge; eassumption. Qed.

Lemma stk_ext : forall m lo hi hi', stk rsegs m lo hi -> hi = hi' -> stk rsegs m lo hi'.
Proof. intros; subst; assumption. Qed.

Lemma outside_app : forall W W' x, outside (W ++ W') x -> outside W x /\ outside W' x.
Proof.
  induction W as [|[a b] W IH]; intros W' x H; cbn [app outside] in *; [split; [exact I|exact H]|].
  destruct H as [H1 H2]. destruct (IH W' x H2) as [A B]. split; [split; assumption|exact B].
Qed.

Lemma munch_snoc : forall W a b m m0 m1, munch W m m0 -> munch [(a, b)] m0 m1 -> munch (W ++ [(a, b)]) m m1.
Proof.
  intros W a b m m0 m1 H0 H1 x Hx. apply outside_app in Hx. destruct Hx as [A B].
  rewrite (H1 x B). apply H0. exact A.
Qed.

Lemma bl_ltu_l : forall a (y : word), 0 <= a < 2^64 -> bv_ltu (Z_to_bv 64 a) y = (a <? bv_unsigned y).
Proof. intros a y Ha. unfold bv_ltu. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma acc_eq : forall f sd i o nm nl tk tl dp dl, bn_args_ok nm nl tk tl dp dl i o = true ->
  bn_accept f sd i o nm nl tk tl dp dl =
  (Z.of_nat (length (bn_NM f sd i o)) <=? 23) && (Z.of_nat (length (bn_NM f sd i o)) <? nl) &&
  (Z.of_nat (length (bn_TK (bn_NM f sd i o))) <? tl) && (Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) <? dl).
Proof.
  intros f sd i o nm nl tk tl dp dl H. pose proof H as H'. unfold bn_args_ok in H'.
  repeat match type of H' with andb _ _ = true => apply andb_true_iff in H'; destruct H' as [H' ?] end.
  unfold bn_accept, bn_ret. rewrite H.
  repeat match goal with E : ?b = true |- context [?b] => rewrite E end.
  cbn [andb]. destruct (Z.of_nat (length (bn_NM f sd i o)) <=? 23); reflexivity.
Qed.

Ltac xport m0 m3 MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells rsegs m0 ?A ?cs |- _ =>
      apply (rw_cells_transport rsegs W m0 m3 A cs) in H;
      [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; first [exact I | lia]]
  | H : u8arr rsegs m0 ?A ?bs |- _ =>
      apply (u8arr_transport rsegs W m0 m3 A bs) in H;
      [| exact MU | exact WM | cbn [disjoint_from];
         rewrite ?length_app, ?bn_bytes_length, ?upd_length, ?length_app, ?bn_bytes_length; cbn [length];
         repeat split; first [exact I | lia]]
  | H : bytes_at rsegs m0 ?A ?bs |- _ =>
      apply (bytes_at_transport rsegs W m0 m3 A bs) in H;
      [| exact MU | cbn [disjoint_from];
         rewrite ?length_app, ?bn_bytes_length, ?length_app; cbn [length]; repeat split; first [exact I | lia]]
  end.

Lemma munch_sub : forall lo hi W m m0 m1, munch [(lo, hi)] m m0 -> munch W m0 m1 ->
  (forall x, outside [(lo, hi)] x -> outside W x) -> munch [(lo, hi)] m m1.
Proof. intros lo hi W m m0 m1 H0 H1 Hs x Hx. rewrite (H1 x (Hs _ Hx)). apply H0. exact Hx. Qed.

Ltac out_tac := intros ?x ?Hx; cbn [outside] in *; repeat split; first [exact I | intro; lia].

Ltac ulit_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.
Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.


Lemma rw_cells_conv : forall mm A cs cs', rw_cells rsegs mm A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs mm A cs'.
Proof.
  intros mm A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'|rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs') by exact Hwf'. rewrite E, cells_bytes_length by exact Hwf. exact Hw.
Qed.

Lemma conv_z8 : forall mm A pre, rw_cells rsegs mm A (pre ++ [C8 (Z_to_bv 64 0)]) ->
  rw_cells rsegs mm A (pre ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
Proof.
  intros mm A pre H. eapply rw_cells_conv; [exact H| |].
  - pose proof (proj1 (proj1 H)) as W. apply cells_wf_app in W. apply cells_wf_app. split; [tauto|cbn; tauto].
  - rewrite !cells_bytes_app. reflexivity.
Qed.


Lemma bbuf_upd0 : forall mm A bs xs, u8arr rsegs mm A (upd_bytes bs 0 (bn_bytes xs)) -> (length xs <= length bs)%nat ->
  bbuf mm A (length bs) xs.
Proof.
  intros mm A bs xs U L. exists (skipn (length xs) bs). split; [rewrite length_skipn; lia|].
  unfold upd_bytes in U. cbn [firstn app Nat.add] in U. rewrite bn_bytes_length in U. exact U.
Qed.


Lemma firstn_firstn_app : forall {X} n (a b : list X), firstn n (firstn n a ++ b) = firstn n (a ++ b).
Proof.
  intros X n a b. rewrite !firstn_app, firstn_firstn, Nat.min_id, length_firstn.
  destruct (Nat.le_ge_cases n (length a)) as [H|H].
  - rewrite Nat.min_l by lia. replace (n - n)%nat with 0%nat by lia.
    replace (n - length a)%nat with 0%nat by lia. reflexivity.
  - rewrite Nat.min_r by lia. reflexivity.
Qed.


Lemma bn_lor_add : forall hi lw k, 0 <= k -> 0 <= lw < 2^k -> hi mod 2^k = 0 -> Z.lor hi lw = hi + lw.
Proof.
  intros hi lw k Hk Hlw Hhi.
  assert (HL : Z.land hi lw = 0).
  { rewrite <- (Z.mod_small lw (2^k)) by lia. rewrite <- Z.land_ones by lia.
    rewrite (Z.land_comm lw), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
  pose proof (Z.add_lor_land hi lw). lia.
Qed.

Definition c4v (b0 b1 b2 b3 : Z) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 b3)) ≪ 24)))
                                                    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b2)) ≪ 16))))))
                    (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b1)) ≪ 8)))
                                                    (bv_unsigned (zxb (Z_to_bv 8 b0))))))).

Definition c4z (b0 b1 b2 b3 : Z) : Z :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + (if b3 <? 128 then 0 else 18446744069414584320).

Lemma c4v_val : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  c4v b0 b1 b2 b3 = Z_to_bv 64 (c4z b0 b1 b2 b3).
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold c4v, c4z, zxb, sxb.
  assert (U : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b).
  { intros b Hb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. }
  rewrite (U b0), (U b1), (U b2) by assumption.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^24) with 16777216. change (2^16) with 65536. change (2^8) with 256.
  rewrite (unsigned_lit b2), (unsigned_lit b1), (unsigned_lit b0) by lia.
  rewrite (unsigned_lit (b2 * 65536)), (unsigned_lit (b1 * 256)) by lia.
  assert (LO : Z.lor (b1 * 256) b0 = b1 * 256 + b0).
  { apply (bn_lor_add _ _ 8); [lia | change (2^8) with 256; lia | change (2^8) with 256; apply Z.mod_mul; lia]. }
  rewrite LO, (unsigned_lit (b1 * 256 + b0)) by lia.
  assert (MID : forall h, h mod 16777216 = 0 -> Z.lor h (b2 * 65536) = h + b2 * 65536).
  { intros h Hh. apply (bn_lor_add _ _ 24); [lia | change (2^24) with 16777216; lia | change (2^24) with 16777216; exact Hh]. }
  assert (TOP : forall h, h mod 65536 = 0 -> Z.lor h (b1 * 256 + b0) = h + (b1 * 256 + b0)).
  { intros h Hh. apply (bn_lor_add _ _ 16); [lia | change (2^16) with 65536; lia | change (2^16) with 65536; exact Hh]. }
  assert (SG : bv_signed (Z_to_bv 8 b3) = if b3 <? 128 then b3 else b3 - 256).
  { rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128.
    change (bv_modulus 8) with 256.
    destruct (Z.ltb_spec b3 128).
    - rewrite Z.mod_small by lia. lia.
    - replace (b3 + 128) with ((b3 - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  rewrite SG.
  destruct (Z.ltb_spec b3 128) as [Hb|Hb].
  - rewrite (unsigned_lit b3), (unsigned_lit (b3 * 16777216)) by lia.
    rewrite MID by (apply Z.mod_mul; lia).
    rewrite (unsigned_lit (b3 * 16777216 + b2 * 65536)) by lia.
    rewrite TOP by (replace (b3 * 16777216 + b2 * 65536) with ((b3 * 256 + b2) * 65536) by lia; apply Z.mod_mul; lia).
    f_equal. lia.
  - rewrite (unsigned_lit_wrap (b3 - 256)).
    replace ((b3 - 256) mod 2^64) with (b3 - 256 + 2^64)
      by (symmetry; rewrite <- (Z.mod_add _ 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    rewrite (unsigned_lit_wrap ((b3 - 256 + 2^64) * 16777216)).
    replace (((b3 - 256 + 2^64) * 16777216) mod 2^64) with (b3 * 16777216 + 18446744069414584320)
      by (symmetry; rewrite <- (Z.mod_add _ (- 16777215) (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    rewrite MID by (replace (b3 * 16777216 + 18446744069414584320) with ((b3 + 1099511627520) * 16777216) by lia;
                    apply Z.mod_mul; lia).
    rewrite (unsigned_lit (b3 * 16777216 + 18446744069414584320 + b2 * 65536)) by lia.
    rewrite TOP by (replace (b3 * 16777216 + 18446744069414584320 + b2 * 65536)
                      with ((b3 * 256 + 281474976645120 + b2) * 65536) by lia; apply Z.mod_mul; lia).
    f_equal. lia.
Qed.

Lemma c4z_inj : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  c4z b0 b1 b2 b3 = c4z c0 c1 c2 c3 -> b0 = c0 /\ b1 = c1 /\ b2 = c2 /\ b3 = c3.
Proof.
  intros b0 b1 b2 b3 c0 c1 c2 c3 H0 H1 H2 H3 K0 K1 K2 K3 E. unfold c4z in E.
  destruct (Z.ltb_spec b3 128); destruct (Z.ltb_spec c3 128); lia.
Qed.

Lemma c4z_rng : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c4z b0 b1 b2 b3 < 2^64.
Proof. intros. unfold c4z. destruct (Z.ltb_spec b3 128); lia. Qed.

Lemma c4v_eqb : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  bv_eqb (c4v b0 b1 b2 b3) (c4v c0 c1 c2 c3) = (b0 =? c0) && (b1 =? c1) && (b2 =? c2) && (b3 =? c3).
Proof.
  intros b0 b1 b2 b3 c0 c1 c2 c3 H0 H1 H2 H3 K0 K1 K2 K3.
  rewrite !c4v_val by assumption. unfold bv_eqb.
  rewrite !unsigned_lit by (apply c4z_rng; assumption).
  destruct (Z.eqb_spec (c4z b0 b1 b2 b3) (c4z c0 c1 c2 c3)) as [E|E].
  - destruct (c4z_inj _ _ _ _ _ _ _ _ H0 H1 H2 H3 K0 K1 K2 K3 E) as (-> & -> & -> & ->). rewrite !Z.eqb_refl. reflexivity.
  - symmetry. destruct (Z.eqb_spec b0 c0); destruct (Z.eqb_spec b1 c1); destruct (Z.eqb_spec b2 c2);
      destruct (Z.eqb_spec b3 c3); try reflexivity. subst. contradiction.
Qed.

Lemma c4v_eqb_x : forall b0 b1 b2 b3 c0 c1 c2 c3,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  bv_eqb
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 b3)) ≪ 24)))
                                                      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b2)) ≪ 16))))))
                      (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 b1)) ≪ 8)))
                                                      (bv_unsigned (zxb (Z_to_bv 8 b0))))))))
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (sxb (Z_to_bv 8 c3)) ≪ 24)))
                                                      (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 c2)) ≪ 16))))))
                      (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb (Z_to_bv 8 c1)) ≪ 8)))
                                                      (bv_unsigned (zxb (Z_to_bv 8 c0))))))))
  = (b0 =? c0) && (b1 =? c1) && (b2 =? c2) && (b3 =? c3).
Proof. intros. apply (c4v_eqb b0 b1 b2 b3 c0 c1 c2 c3); assumption. Qed.

Lemma bn_leq_nth4 : forall a b, length a = 4%nat -> length b = 4%nat ->
  bn_leq a b = (nth 0 a 0 =? nth 0 b 0) && (nth 1 a 0 =? nth 1 b 0) && (nth 2 a 0 =? nth 2 b 0) &&
               (nth 3 a 0 =? nth 3 b 0).
Proof.
  intros [|u0 [|u1 [|u2 [|u3 [|u4 u]]]]] [|v0 [|v1 [|v2 [|v3 [|v4 v]]]]] Ha Hb; cbn in Ha, Hb; try discriminate.
  cbn [bn_leq nth]. destruct (u0 =? v0), (u1 =? v1), (u2 =? v2), (u3 =? v3); reflexivity.
Qed.

Lemma bytes_skipn : forall mm A (l : list Z) k, bytes_at rsegs mm A (bn_bytes l) -> (k <= length l)%nat ->
  bytes_at rsegs mm (A + Z.of_nat k) (bn_bytes (skipn k l)).
Proof.
  intros mm A l k H Hk. rewrite <- (firstn_skipn k l) in H. rewrite bn_bytes_app in H. apply bytes_at_app in H.
  destruct H as [_ H]. rewrite bn_bytes_length, length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  exact H.
Qed.

Lemma bn_nz : forall l, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (bn_bytes l).
Proof.
  intros l H I. unfold bn_bytes in I. apply in_map_iff in I. destruct I as (c & E & Hc).
  rewrite Forall_forall in H. specialize (H c Hc).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite (Z.mod_small c) in E by lia. change (0 mod 256) with 0 in E. lia.
Qed.


Lemma rw_u8_cat : forall mm A n x y, rw_cells rsegs mm A [CB n x] -> u8arr rsegs mm (A + Z.of_nat n) y ->
  rw_cells rsegs mm A [CB (n + length y) (x ++ y)].
Proof.
  intros mm A n x y Hx Hy.
  assert (Lx : length x = n) by (destruct Hx as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in Hx. destruct Hx as [Bx Wx]. destruct Hy as [By Wy].
  rewrite <- Lx, <- length_app. apply rw_cells_of_u8arr. split.
  - apply bytes_at_app. split; [exact Bx|]. rewrite Lx. exact By.
  - destruct Wx as (W1 & W2 & Wx). destruct Wy as (V1 & V2 & Wy). rewrite length_app.
    split; [lia|]. split; [lia|]. intros j Hj.
    destruct (Z.ltb_spec j (Z.of_nat (length x))) as [Hjx|Hjx].
    + apply Wx. lia.
    + replace (A + j) with (A + Z.of_nat n + (j - Z.of_nat n)) by lia. apply Wy. lia.
Qed.


Lemma skipn0 : forall {X} (l : list X), skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma rw_bbuf : forall mm A n j, rw_cells rsegs mm A [CB n j] -> bbuf mm A n [].
Proof.
  intros mm A n j H. assert (L : length j = n) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto).
  apply u8arr_of_rw_cells in H. exists j. split; [cbn [length]; lia | exact H].
Qed.

Lemma stem_ne : forall ff ss, bn_stem ff ss <> [].
Proof.
  intros ff ss. unfold bn_stem, bn_STEM. destruct ss; [|discriminate].
  destruct (ff =? 1); [discriminate|]. destruct (ff =? 2); [discriminate|]. destruct (ff =? 3); discriminate.
Qed.

Lemma stem_sd : forall ff l, l <> [] -> bn_stem ff l = l.
Proof. intros ff l H. destruct l; [contradiction|reflexivity]. Qed.

Lemma NM_chars : forall ff ss ii oo, Forall (fun c => 0 < c < 256) (bn_stem ff ss) -> bn_ok ii = true -> bn_ok oo = true ->
  Forall (fun c => 0 < c < 256) (bn_NM ff ss ii oo).
Proof.
  intros ff ss ii oo H Hi Ho. unfold bn_NM. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [exact H|].
  apply Forall_app. split; [exact H|]. constructor; [lia|].
  destruct (bn_ok_dec ii Hi) as (_ & _ & _ & _ & _ & Di & _).
  destruct (bn_ok_dec oo Ho) as (_ & _ & _ & _ & _ & Do & _).
  unfold bn_w4. apply Forall_app. split.
  - eapply Forall_impl; [|exact Di]. intros c Hc. cbv beta in Hc |- *. lia.
  - eapply Forall_impl; [|exact Do]. intros c Hc. cbv beta in Hc |- *. lia.
Qed.

Lemma NM_len : forall ff ss ii oo, (length (bn_stem ff ss) <= length (bn_NM ff ss ii oo))%nat.
Proof.
  intros ff ss ii oo. unfold bn_NM. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [lia|]. rewrite length_app. lia.
Qed.


Lemma bl_eqb0 : forall w : word, bv_eqb w (Z_to_bv 64 0) = (bv_unsigned w =? 0).
Proof. intros w. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. reflexivity. Qed.

Lemma bl_eqb0s : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.ltb_spec v 0).
  - replace (v mod 2^64) with (v + 2^64)
      by (symmetry; rewrite <- (Z.mod_add v 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
    destruct (Z.eqb_spec (v + 2^64) 0); destruct (Z.eqb_spec v 0); first [reflexivity | exfalso; lia].
  - rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma addiw_chk : forall v, -2^31 <= v < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + -41))) (Z_to_bv 64 (-39)) =
  negb ((2 <=? v) && (v <=? 40)).
Proof.
  intros v Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
  change (2^64) with 18446744073709551616 in *. change (2^31) with 2147483648 in *.
  destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma tbl_chk : forall v, -2^31 <= v < 2^31 ->
  bv_ltu (Z_to_bv 64 2) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + -1))) =
  negb ((1 <=? v) && (v <=? 3)).
Proof.
  intros v Hv. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
  change (2^64) with 18446744073709551616 in *. change (2^31) with 2147483648 in *.
  destruct (Z.leb_spec 1 v); destruct (Z.leb_spec v 3); cbn [andb negb];
    [apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.

Lemma land_chk : forall v, 0 <= v < 2^63 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 v)) 1)) (Z_to_bv 64 0) = Z.even v.
Proof.
  intros v Hv. rewrite (unsigned_lit v) by lia.
  replace (Z.land v 1) with (v mod 2)
    by (symmetry; change 2 with (2^1); rewrite <- Z.land_ones by lia; reflexivity).
  rewrite bl_eqb by (pose proof (Z.mod_pos_bound v 2); lia).
  rewrite Zmod_even. destruct (Z.even v); reflexivity.
Qed.

Lemma args_ok_false : forall nm nl tk tl dp dl x y,
  (nm = 0 \/ tk = 0 \/ dp = 0 \/ nl = 0 \/ tl = 0 \/ dl = 0 \/ bn_ok x = false \/ bn_ok y = false \/
   (x = 0 /\ y = 0)) ->
  bn_args_ok nm nl tk tl dp dl x y = false.
Proof.
  intros nm nl tk tl dp dl x y H. destruct (bn_args_ok nm nl tk tl dp dl x y) eqn:E; [|reflexivity].
  apply args_ok_split in E. exfalso. intuition congruence.
Qed.

Lemma args_ok_true : forall nm nl tk tl dp dl x y, nm <> 0 -> tk <> 0 -> dp <> 0 -> nl <> 0 -> tl <> 0 -> dl <> 0 ->
  bn_ok x = true -> bn_ok y = true -> ~ (x = 0 /\ y = 0) -> bn_args_ok nm nl tk tl dp dl x y = true.
Proof.
  intros nm nl tk tl dp dl x y H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold bn_args_ok. rewrite H7, H8.
  replace (nm =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  replace (tk =? 0) with false by (symmetry; apply Z.eqb_neq; exact H2).
  replace (dp =? 0) with false by (symmetry; apply Z.eqb_neq; exact H3).
  replace (nl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H4).
  replace (tl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H5).
  replace (dl =? 0) with false by (symmetry; apply Z.eqb_neq; exact H6).
  destruct (Z.eqb_spec x 0); destruct (Z.eqb_spec y 0); first [reflexivity | exfalso; tauto].
Qed.

Lemma bn_ok_out : forall v, v <> 0 -> (v < 2 \/ 40 < v) -> bn_ok v = false.
Proof.
  intros v H1 H2. unfold bn_ok. destruct (Z.eqb_spec v 0) as [E|E]; [lia|].
  destruct (Z.leb_spec 2 v); destruct (Z.leb_spec v 40); cbn [orb andb]; first [reflexivity | exfalso; lia].
Qed.

Lemma bn_ok_odd : forall v, v <> 0 -> Z.even v = false -> bn_ok v = false.
Proof.
  intros v H1 H2. unfold bn_ok. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact H1).
  rewrite H2, andb_false_r. reflexivity.
Qed.

Lemma bn_ok_in : forall v, 2 <= v <= 40 -> Z.even v = true -> bn_ok v = true.
Proof.
  intros v H1 H2. unfold bn_ok. replace (2 <=? v) with true by (symmetry; apply Z.leb_le; lia).
  replace (v <=? 40) with true by (symmetry; apply Z.leb_le; lia). rewrite H2, orb_true_r. reflexivity.
Qed.

Lemma bn_ok_0 : forall v, v = 0 -> bn_ok v = true.
Proof. intros v ->. reflexivity. Qed.

Lemma STEM_other : forall ff, (ff < 1 \/ 3 < ff) -> bn_STEM ff = bn_STEM 0.
Proof.
  intros ff H. unfold bn_STEM.
  replace (ff =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ff =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (ff =? 3) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Ltac fold_tbl :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | context [bv_swrap] => let v := eval vm_compute in e in change e with v
      end
  end.


Lemma lxor_lit : forall x, 0 <= x < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) = 2^64 - 1 - x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
Qed.

Lemma zl_c : forall c, 0 <= c < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (zxb (Z_to_bv 8 c))) 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. rewrite (bl_zxb c Hc). rewrite unsigned_lit by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma m1_lit : bv_unsigned (Z_to_bv 64 (-1)) = 2^64 - 1.
Proof. reflexivity. Qed.

Ltac bsolve :=
  rewrite ?bl_zxb by lia;
  cbn [negb]; unfold bv_ltu, bv_eqb;
  rewrite ?lxor_lit by lia; rewrite ?m1_lit;
  rewrite ?unsigned_lit by lia;
  lazymatch goal with
  | |- (_ <? _) = false => apply Z.ltb_ge; lia
  | |- (_ <? _) = true => apply Z.ltb_lt; lia
  | |- (_ =? _) = false => apply Z.eqb_neq; lia
  | |- (_ =? _) = true => apply Z.eqb_eq; lia
  | |- negb (_ <? _) = false => apply negb_false_iff, Z.ltb_lt; lia
  | |- negb (_ <? _) = true => apply negb_true_iff, Z.ltb_ge; lia
  | |- negb (_ =? _) = false => apply negb_false_iff, Z.eqb_eq; lia
  | |- negb (_ =? _) = true => apply negb_true_iff, Z.eqb_neq; lia
  end.

Ltac bfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota | symmetry; bsolve] end.
Ltac btrue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota | symmetry; bsolve] end.
