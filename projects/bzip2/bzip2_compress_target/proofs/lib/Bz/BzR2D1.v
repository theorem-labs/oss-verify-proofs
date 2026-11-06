(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzDState BzDBlock BzR2Theory.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Forall_nth_Z : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> (k < length l)%nat -> P (nth k l 0).
Proof.
  intros P l k H Hk. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Lemma lexle_hd : forall u v, u <> [] -> length u = length v -> lexle u v -> hd 0 u <= hd 0 v.
Proof.
  intros u v Hu Hl [LT|EQ]; [|subst; lia].
  destruct u as [|a u']; [congruence|]. destruct v as [|b v']; [cbn in Hl; lia|]. cbn in LT |- *. lia.
Qed.

(* [comment removed for export] *)
Record bwt (t : list Z) (pi rho : nat -> nat) : Prop := BWT {
  bwt_n : (0 < length t)%nat;
  bwt_pi_lt : forall i, (i < length t)%nat -> (pi i < length t)%nat;
  bwt_rho_lt : forall p, (p < length t)%nat -> (rho p < length t)%nat;
  bwt_rho_pi : forall i, (i < length t)%nat -> rho (pi i) = i;
  bwt_pi_rho : forall p, (p < length t)%nat -> pi (rho p) = p;
  bwt_sorted : forall i j, (i <= j)%nat -> (j < length t)%nat -> lexle (rot t (pi i)) (rot t (pi j));
  bwt_bytes : Forall (fun x => 0 <= x < 256) t }.

Section Ctx.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.
  Let Hn : (0 < n)%nat := bwt_n t pi rho HB.
  Let pi_lt : forall i, (i < n)%nat -> (pi i < n)%nat := bwt_pi_lt t pi rho HB.
  Let rho_lt : forall p, (p < n)%nat -> (rho p < n)%nat := bwt_rho_lt t pi rho HB.
  Let rho_pi : forall i, (i < n)%nat -> rho (pi i) = i := bwt_rho_pi t pi rho HB.
  Let pi_rho : forall p, (p < n)%nat -> pi (rho p) = p := bwt_pi_rho t pi rho HB.
  Let sorted : forall i j, (i <= j)%nat -> (j < n)%nat -> lexle (rot t (pi i)) (rot t (pi j)) := bwt_sorted t pi rho HB.
  Let BYT : Forall (fun x => 0 <= x < 256) t := bwt_bytes t pi rho HB.

  Local Abbreviation Fc := (Fc t pi).
  Local Abbreviation Lc := (Lc t pi).
  Local Abbreviation Ccnt := (Ccnt t pi).
  Let cls_hd' := cls_hd t pi pi_lt.
  Let cls_nonnil' := cls_nonnil t Hn pi pi_lt.
  Let cls_length' := cls_length t Hn pi pi_lt.
  Let cntFL := cntF_eq_cntL t Hn pi rho pi_lt rho_lt rho_pi pi_rho.
  (* [comment removed for export] *)
  Definition Lcnt (c : Z) : nat := cnt (fun j => Lc j =? c) n.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma nth_byte : forall p, 0 <= nth p t 0 < 256.
  Proof.
    intros p. destruct (Nat.lt_ge_cases p n) as [H|H].
    - exact (Forall_nth_Z _ t p BYT H).
    - rewrite nth_overflow by (unfold n in H; lia). lia.
  Qed.
  Lemma Fc_byte : forall i, 0 <= Fc i < 256. Proof. intros; unfold BzR2Theory.Fc; apply nth_byte. Qed.
  Lemma Lc_byte : forall i, 0 <= Lc i < 256. Proof. intros; unfold BzR2Theory.Lc; apply nth_byte. Qed.

  Lemma Fc_mono : forall i j, (i <= j)%nat -> (j < n)%nat -> Fc i <= Fc j.
  Proof.
    intros i j Hij Hj. rewrite <- !cls_hd' by lia. apply lexle_hd.
    - apply cls_nonnil'. lia.
    - rewrite !cls_length' by lia. reflexivity.
    - exact (sorted i j Hij Hj).
  Qed.

  Lemma Ccnt_0 : Ccnt 0 = 0%nat.
  Proof. unfold BzR2Theory.Ccnt. apply cnt_none. intros k Hk. pose proof (Fc_byte k). apply Z.ltb_ge. lia. Qed.

  Lemma Ccnt_256 : Ccnt 256 = n.
  Proof. unfold BzR2Theory.Ccnt. apply cnt_all. intros k Hk. pose proof (Fc_byte k). apply Z.ltb_lt. lia. Qed.

  Lemma Ccnt_S : forall c, Ccnt (c + 1) = (Ccnt c + Lcnt c)%nat.
  Proof.
    intros c. unfold BzR2Theory.Ccnt, Lcnt.
    rewrite <- cntFL, <- cnt_split.
    - apply cnt_ext. intros k Hk.
      destruct (Z.ltb_spec (Fc k) (c + 1)), (Z.ltb_spec (Fc k) c), (Z.eqb_spec (Fc k) c); cbn; try reflexivity; lia.
    - intros k Hk A B. apply Z.ltb_lt in A. apply Z.eqb_eq in B. lia.
  Qed.

  Lemma Ccnt_mono : forall c c', c <= c' -> (Ccnt c <= Ccnt c')%nat.
  Proof.
    intros c c' H. unfold BzR2Theory.Ccnt. apply cnt_mono. intros k Hk A. apply Z.ltb_lt in A. apply Z.ltb_lt. lia.
  Qed.

  Lemma Ccnt_le_n : forall c, (Ccnt c <= n)%nat.
  Proof. intros; unfold BzR2Theory.Ccnt; apply cnt_le. Qed.

  (* [comment removed for export] *)
  Lemma Fc_lt_iff : forall r c, (r < n)%nat -> (Fc r < c <-> (r < Ccnt c)%nat).
  Proof.
    intros r c Hr. unfold BzR2Theory.Ccnt.
    assert (DC : forall k k', (k' <= k)%nat -> (k < n)%nat -> (Fc k <? c) = true -> (Fc k' <? c) = true).
    { intros k k' Hk' Hk A. apply Z.ltb_lt in A. apply Z.ltb_lt. pose proof (Fc_mono k' k Hk' Hk). lia. }
    pose proof (cnt_down_closed (fun r0 => Fc r0 <? c) n DC r Hr) as [A B]. cbn beta in A, B.
    split; intros H; [apply A; apply Z.ltb_lt; exact H|apply Z.ltb_lt; apply B; exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma Fc_band : forall r c, (r < n)%nat -> (Fc r = c <-> (Ccnt c <= r < Ccnt (c + 1))%nat).
  Proof.
    intros r c Hr. pose proof (Fc_lt_iff r c Hr) as A. pose proof (Fc_lt_iff r (c + 1) Hr) as B. split.
    - intros E. split; [|apply B; lia]. destruct (Nat.lt_ge_cases r (Ccnt c)) as [C|C]; [|exact C]. apply A in C. lia.
    - intros [C D]. apply B in D. destruct (Z.lt_ge_cases (Fc r) c) as [E|E]; [apply A in E; lia|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition HIST (unz : zarr) : Prop := forall c, 0 <= c <= 255 -> zget unz c = Z.of_nat (Lcnt c).
  (* [comment removed for export] *)
  Definition CF (cf : zarr) : Prop := forall c, 0 <= c <= 256 -> zget cf c = Z.of_nat (Ccnt c).

  Lemma CF_mono : forall cf a b, CF cf -> 0 <= a -> a <= b -> b <= 256 -> zget cf a <= zget cf b.
  Proof. intros cf a b H Ha Hab Hb. rewrite !H by lia. pose proof (Ccnt_mono a b Hab). lia. Qed.
  Lemma CF_0 : forall cf, CF cf -> zget cf 0 = 0.
  Proof. intros cf H. rewrite H by lia. rewrite Ccnt_0. reflexivity. Qed.
  Lemma CF_256 : forall cf, CF cf -> zget cf 256 = Z.of_nat n.
  Proof. intros cf H. rewrite H by lia. rewrite Ccnt_256. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma unz_check_pass : forall k i unz nb,
    (forall j, i <= j < i + Z.of_nat k -> 0 <= zget unz j <= nb) ->
    unz_check k i unz nb = i + Z.of_nat k.
  Proof.
    induction k as [|k IH]; intros i unz nb H; cbn [unz_check]; [lia|].
    pose proof (H i ltac:(lia)) as Hi.
    destruct (Z.ltb_spec (zget unz i) 0); [lia|]. destruct (Z.ltb_spec nb (zget unz i)); [lia|]. cbn.
    rewrite IH; [lia|]. intros j Hj. apply H. lia.
  Qed.

  Lemma cf_copy_get : forall k i unz cf j,
    zget (cf_copy k i unz cf) j = if (i <=? j) && (j <? i + Z.of_nat k) then zget unz (j - 1) else zget cf j.
  Proof.
    induction k as [|k IH]; intros i unz cf j; cbn [cf_copy].
    - destruct (Z.leb_spec i j), (Z.ltb_spec j (i + Z.of_nat 0)); cbn; try reflexivity. lia.
    - rewrite IH, zget_zset.
      destruct (Z.leb_spec (i + 1) j), (Z.ltb_spec j (i + 1 + Z.of_nat k)), (Z.leb_spec i j),
        (Z.ltb_spec j (i + Z.of_nat (S k))), (Z.eqb_spec j i); cbn; subst; try reflexivity; lia.
  Qed.

  Lemma cf_accum_CF : forall k i cf, 1 <= i -> i + Z.of_nat k = 257 ->
    (forall j, 0 <= j < i -> zget cf j = Z.of_nat (Ccnt j)) ->
    (forall j, i <= j <= 256 -> zget cf j = Z.of_nat (Lcnt (j - 1))) ->
    CF (cf_accum k i cf).
  Proof.
    induction k as [|k IH]; intros i cf Hi Hk LO HI; cbn [cf_accum].
    - intros c Hc. apply LO. lia.
    - apply IH; [lia|lia| |].
      + intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j i).
        * subst j. rewrite HI, LO by lia. replace i with (i - 1 + 1) at 3 by lia. rewrite Ccnt_S. lia.
        * apply LO. lia.
      + intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j i); [lia|]. apply HI. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cftab_CF : forall unz cf, HIST unz ->
    CF (cf_accum 256 1 (cf_copy 256 1 unz (zset cf 0 0))).
  Proof.
    intros unz cf H. apply cf_accum_CF; [lia|reflexivity| |].
    - intros j Hj. rewrite cf_copy_get. destruct (Z.leb_spec 1 j); cbn [andb]; [lia|].
      rewrite zget_zset. replace j with 0 by lia. rewrite Z.eqb_refl, Ccnt_0. reflexivity.
    - intros j Hj. rewrite cf_copy_get. destruct (Z.leb_spec 1 j), (Z.ltb_spec j (1 + Z.of_nat 256)); cbn [andb]; try lia.
      apply H. lia.
  Qed.

  Lemma cf_check1_pass : forall k i cf nb,
    (forall j, i <= j < i + Z.of_nat k -> 0 <= zget cf j <= nb) ->
    cf_check1 k i cf nb = i + Z.of_nat k.
  Proof.
    induction k as [|k IH]; intros i cf nb H; cbn [cf_check1]; [lia|].
    pose proof (H i ltac:(lia)) as Hi.
    destruct (Z.ltb_spec (zget cf i) 0); [lia|]. destruct (Z.ltb_spec nb (zget cf i)); [lia|]. cbn.
    rewrite IH; [lia|]. intros j Hj. apply H. lia.
  Qed.

  Lemma cf_check2_pass : forall k i cf,
    (forall j, i <= j < i + Z.of_nat k -> zget cf (j - 1) <= zget cf j) ->
    cf_check2 k i cf = i + Z.of_nat k.
  Proof.
    induction k as [|k IH]; intros i cf H; cbn [cf_check2]; [lia|].
    pose proof (H i ltac:(lia)) as Hi.
    destruct (Z.ltb_spec (zget cf i) (zget cf (i - 1))); [lia|].
    rewrite IH; [lia|]. intros j Hj. apply H. lia.
  Qed.

  Lemma cf_dup_get : forall k i cf cfc j,
    zget (cf_dup k i cf cfc) j = if (i <=? j) && (j <? i + Z.of_nat k) then zget cf j else zget cfc j.
  Proof.
    induction k as [|k IH]; intros i cf cfc j; cbn [cf_dup].
    - destruct (Z.leb_spec i j), (Z.ltb_spec j (i + Z.of_nat 0)); cbn; try reflexivity. lia.
    - rewrite IH, zget_zset.
      destruct (Z.leb_spec (i + 1) j), (Z.ltb_spec j (i + 1 + Z.of_nat k)), (Z.leb_spec i j),
        (Z.ltb_spec j (i + Z.of_nat (S k))), (Z.eqb_spec j i); cbn; subst; try reflexivity; lia.
  Qed.

  Lemma cf_dup_CF : forall cf cfc, CF cf -> CF (cf_dup 257 0 cf cfc).
  Proof.
    intros cf cfc H c Hc. rewrite cf_dup_get. destruct (Z.leb_spec 0 c), (Z.ltb_spec c (0 + Z.of_nat 257)); cbn [andb]; try lia.
    apply H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma unz_check_ok : forall unz, HIST unz -> unz_check 256 0 unz (Z.of_nat n) = 256.
  Proof.
    intros unz H. rewrite unz_check_pass; [reflexivity|]. intros j Hj. rewrite H by lia.
    pose proof (cnt_le (fun j0 => Lc j0 =? j) n). unfold Lcnt. lia.
  Qed.

  Lemma cf_check1_ok : forall cf, CF cf -> cf_check1 257 0 cf (Z.of_nat n) = 257.
  Proof.
    intros cf H. rewrite cf_check1_pass; [reflexivity|]. intros j Hj. rewrite H by lia.
    pose proof (Ccnt_le_n j). lia.
  Qed.

  Lemma cf_check2_ok : forall cf, CF cf -> cf_check2 256 1 cf = 257.
  Proof.
    intros cf H. rewrite cf_check2_pass; [reflexivity|]. intros j Hj. apply CF_mono; [exact H|lia|lia|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma iif_loop_spec : forall f cf indx nb na, CF cf ->
    0 <= nb -> na <= 256 -> 2 <= na - nb <= 2 ^ Z.of_nat f ->
    zget cf nb <= indx < zget cf na ->
    let r := iif_loop f cf indx nb na in 0 <= r <= 255 /\ zget cf r <= indx < zget cf (r + 1).
  Proof.
    induction f as [|f IH]; intros cf indx nb na HC Hnb Hna Hw Hin; [cbn in Hw; lia|].
    cbn [iif_loop]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    set (mid := (nb + na) / 2).
    pose proof (Z.div_mod (nb + na) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nb + na) 2 ltac:(lia)) as MB.
    fold mid in DM.
    assert (Hpow : 2 ^ Z.of_nat (S f) = 2 * 2 ^ Z.of_nat f) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    rewrite Hpow in Hw.
    destruct (Z.leb_spec (zget cf mid) indx).
    - destruct (Z.eqb_spec (na - mid) 1).
      + cbv zeta. replace (mid + 1) with na by lia. lia.
      + apply IH; [exact HC|lia|lia|lia|lia].
    - destruct (Z.eqb_spec (mid - nb) 1).
      + cbv zeta. replace (nb + 1) with mid by lia. lia.
      + apply IH; [exact HC|lia|lia|lia|lia].
  Qed.

  Theorem indexIntoF_Fc : forall cf r, CF cf -> (r < n)%nat -> indexIntoF (Z.of_nat r) cf = Fc r.
  Proof.
    intros cf r HC Hr. unfold indexIntoF.
    pose proof (iif_loop_spec 9 cf (Z.of_nat r) 0 256 HC ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as S.
    rewrite (CF_0 cf HC), (CF_256 cf HC) in S. specialize (S ltac:(lia)). cbv zeta in S. destruct S as [R B].
    rewrite !HC in B by lia. symmetry. apply (Fc_band r _ Hr). lia.
  Qed.
End Ctx.
