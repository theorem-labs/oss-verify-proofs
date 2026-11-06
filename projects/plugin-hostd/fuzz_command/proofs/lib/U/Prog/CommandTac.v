From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Image Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel sup_reply_code_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof.
  intros m A v H. split.
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma bytes_ro4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof.
  intros m A v H. split.
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma lit_at : forall m A bs,
  mem_inv rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs m A bs.
Proof.
  intros m A bs HI Hb HA Hl.
  destruct (ro_cells_image rsegs m A bs HI Hb HA Hl) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma swrap32_range : forall z, -2^31 <= bv_swrap 32 z < 2^31.
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  pose proof (Z.mod_pos_bound (z + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma atoi_digits_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= atoi_digits n s < 2^31.
Proof.
  induction s as [|c s IH]; intros n Hn; cbn [atoi_digits]; [exact Hn|].
  destruct (_ && _); [apply IH, swrap32_range | exact Hn].
Qed.

Lemma atoi_musl_range : forall s, -2^31 <= atoi_musl s < 2^31.
Proof.
  induction s as [|c s IH]; cbn [atoi_musl]; [lia|].
  destruct (_ || _); [exact IH|].
  destruct (_ =? 45); [apply atoi_digits_range; lia|].
  destruct (_ =? 43); apply swrap32_range.
Qed.

Lemma reply_code_range : forall x, -2^31 <= reply_code x < 2^31.
Proof.
  intros x. unfold reply_code. destruct (list_eq_dec _ _ _); [apply atoi_musl_range | lia].
Qed.

Lemma nul_neq : forall b : byte, ~ In NUL [b] -> bv_unsigned b <> 0.
Proof.
  intros b H E. apply H. left. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma notin_nul_cons : forall b l, ~ In NUL (b :: l) -> bv_unsigned b <> 0 /\ ~ In NUL l.
Proof.
  intros b l H. split.
  - intros E. apply H. left. apply bv_eq. rewrite E. reflexivity.
  - intros Hi. apply H. right. exact Hi.
Qed.

Lemma byte_eq_iff : forall a b : byte, bv_unsigned a = bv_unsigned b <-> a = b.
Proof. intros a b. split; [apply bv_eq | intros ->; reflexivity]. Qed.

Lemma walk_prefix : forall k s, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_walk (s ++ [NUL]) (k ++ [NUL]) (length k - 1) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  induction k as [|c k IH]; intros s Hs Hk Hne; [congruence|].
  destruct (notin_nul_cons c k Hk) as [Hc Hk'].
  destruct s as [|a s'].
  - cbn [app strncmp_walk]. unfold NUL. rewrite Z_to_bv_unsigned. cbn [bv_wrap].
    eexists. split; [reflexivity|]. split; [intros E; exfalso; change (bv_wrap 8 0) with 0 in E; lia | intros E; discriminate].
  - destruct (notin_nul_cons a s' Hs) as [Ha Hs'].
    cbn [app length].
    destruct k as [|c2 k2].
    + cbn [strncmp_walk Nat.sub Nat.eqb]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb]. replace (0 - 0)%nat with 0%nat by reflexivity.
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * eexists. split; [reflexivity|]. split; [intros _; cbn; f_equal; apply bv_eq; exact E | intros _; lia].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E; subst; lia].
    + replace (S (length (c2 :: k2)) - 1)%nat with (S (length (c2 :: k2) - 1)) by (cbn; lia).
      cbn [strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc).
      cbn [orb Nat.eqb].
      destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|NE]; cbn [negb orb].
      * destruct (IH s' Hs' Hk' ltac:(discriminate)) as (v & Hw & Hv).
        exists v. split; [exact Hw|]. rewrite Hv. cbn [firstn length].
        replace a with c by (apply bv_eq; symmetry; exact E).
        split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
      * eexists. split; [reflexivity|]. split; [intros E; lia | intros E; cbn in E; injection E as E1 _; subst; lia].
Qed.

Lemma strncmp_prefix : forall s k, ~ In NUL s -> ~ In NUL k -> k <> [] ->
  exists v, strncmp_model (s ++ [NUL]) (k ++ [NUL]) (Z.of_nat (length k)) = Some v /\ (v = 0 <-> firstn (length k) s = k).
Proof.
  intros s k Hs Hk Hne. unfold strncmp_model.
  destruct k as [|c k']; [congruence|].
  replace (Z.of_nat (length (c :: k')) =? 0) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
  replace (Z.to_nat (Z.of_nat (length (c :: k')) - 1)) with (length (c :: k') - 1)%nat by lia.
  apply walk_prefix; assumption.
Qed.

Lemma prefixb_iff : forall s k, prefixb s k = true <-> firstn (length k) s = k.
Proof.
  intros s k. unfold prefixb, bytes_eqb.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE].
  - split; [intros _; apply map_unsigned_inj; exact E | reflexivity].
  - split; [discriminate | intros H; exfalso; apply NE; rewrite H; reflexivity].
Qed.

Lemma bytes_eqb_iff : forall a b, bytes_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold bytes_eqb.
  destruct (list_eq_dec Z.eq_dec _ _) as [E|NE].
  - split; [intros _; apply map_unsigned_inj; exact E | reflexivity].
  - split; [discriminate | intros H; exfalso; apply NE; rewrite H; reflexivity].
Qed.

Lemma bytes_at_skipn : forall m a l k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k (Ha & Hl & H) Hk. split; [lia|]. split; [rewrite skipn_length; lia|].
  intros i Hi. rewrite skipn_length in Hi. rewrite nth_error_skipn.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. apply H. lia.
Qed.

Lemma notin_nul_lit : forall l, forallb (fun z => negb (z =? 0)) (map bv_unsigned l) = true -> ~ In NUL l.
Proof.
  intros l H Hin. apply In0_map_unsigned in Hin. rewrite forallb_forall in H.
  specialize (H 0 Hin). cbn in H. discriminate.
Qed.

Lemma bv0_iff : forall r : word, bv_unsigned r = 0 <-> r = Z_to_bv 64 0.
Proof.
  intros r. split.
  - intros H. apply bv_eq. rewrite H. reflexivity.
  - intros ->. reflexivity.
Qed.

Lemma strncmp_walk_range : forall l r k v, strncmp_walk l r k = Some v -> -256 < v < 256.
Proof.
  induction l as [|a l IH]; intros [|b r] k v H; cbn in H; try discriminate.
  pose proof (byte_range a). pose proof (byte_range b).
  destruct (_ || _ || _ || _)%bool.
  - injection H as <-. lia.
  - destruct k as [|k]; [injection H as <-; lia | eapply IH; exact H].
Qed.

Lemma strncmp_model_range : forall l r n v, strncmp_model l r n = Some v -> -256 < v < 256.
Proof.
  intros l r n v H. unfold strncmp_model in H. destruct (n =? 0).
  - injection H as <-. lia.
  - eapply strncmp_walk_range. exact H.
Qed.

Lemma sel8_zero : Z.b2z (0 mod 18446744073709551616 <? 1) ≪ 3 = 8.
Proof. reflexivity. Qed.

Lemma sel8_nonzero : forall v, v <> 0 -> -256 < v < 256 -> Z.b2z (v mod 18446744073709551616 <? 1) ≪ 3 = 0.
Proof.
  intros v Hv Hr.
  assert (E : v mod 18446744073709551616 <? 1 = false).
  { apply Z.ltb_ge. destruct (Z_lt_le_dec v 0).
    - assert (M : v mod 18446744073709551616 = v + 18446744073709551616)
        by (symmetry; apply Z.mod_unique with (-1); lia).
      rewrite M. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite E. reflexivity.
Qed.

Lemma skipn_cstr : forall (w : list byte) k, (k <= length w)%nat -> skipn k (w ++ [NUL]) = skipn k w ++ [NUL].
Proof. intros w k Hk. rewrite skipn_app. replace (k - length w)%nat with 0%nat by lia. reflexivity. Qed.

Lemma notin_skipn : forall (w : list byte) k, ~ In NUL w -> ~ In NUL (skipn k w).
Proof. intros w k H Hi. apply H. rewrite <- (firstn_skipn k w). apply in_or_app. right. exact Hi. Qed.
