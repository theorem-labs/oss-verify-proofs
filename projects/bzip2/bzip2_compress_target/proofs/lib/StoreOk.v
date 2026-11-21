(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the argument block over the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv and the init stack window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec StepTac StreamSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Footprint.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Footprint.
From Stdlib Require Lia. 
From Stdlib Require NArith Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SeqExec.
Module MuslStrlen.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StepTac.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Import ListNotations.
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module HZ.
Local Open Scope Z_scope.


(* [comment removed for export] *)
Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.

Fixpoint zdig (ds : list Z) : Z :=
  match ds with [] => 0 | d :: r => d + 256 * zdig r end.

Lemma pow2_8i_pos : forall i : nat, 0 < 2^(8 * Z.of_nat i).
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zb_bound : forall x i, 0 <= zb x i < 256.
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.

Lemma zb_0 : forall i, zb 0 i = 0.
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.

(* [comment removed for export] *)

Lemma land_land_m : forall a b m, Z.land (Z.land a b) m = Z.land (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma land_lxor_m : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zb_alt : forall x i, zb x i = Z.land (Z.shiftr x (8 * Z.of_nat i)) 255.
Proof.
  intros x i. unfold zb.
  rewrite Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zb_land : forall u w i, zb (Z.land u w) i = Z.land (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.

Lemma zb_lxor : forall u w i, zb (Z.lxor u w) i = Z.lxor (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zdig_nonneg : forall ds, Forall (fun d => 0 <= d < 256) ds -> 0 <= zdig ds.
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  specialize (IH Hds). lia.
Qed.

Lemma zdig_lt : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  zdig ds < 2^(8 * Z.of_nat (length ds)).
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig length].
  - cbn. lia.
  - apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
    specialize (IH Hds).
    replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

Lemma zb_zdig : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  forall i, (i < length ds)%nat -> zb (zdig ds) i = nth i ds 0.
Proof.
  induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  pose proof (zdig_nonneg ds Hds) as Hnn.
  destruct i as [|i]; cbn [nth].
  - cbn [zdig]. unfold zb.
    change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
    rewrite Z.div_1_r.
    replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  - cbn [length] in Hi.
    rewrite <- (IH Hds i ltac:(lia)).
    cbn [zdig]. unfold zb.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256.
    rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
    replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
    replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
    rewrite Z.div_add_l by lia.
    rewrite (Z.div_small d 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma zdig_recon8 : forall x, 0 <= x < 2^64 ->
  x = zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7].
Proof.
  intros x Hx. cbn [zdig]. unfold zb.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
  change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
  change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
  change (2^0) with 1. rewrite Z.div_1_r.
  change (2^8) with 256.
  change (2^16) with (256*256).
  change (2^24) with (256*256*256).
  change (2^32) with (256*256*256*256).
  change (2^40) with (256*256*256*256*256).
  change (2^48) with (256*256*256*256*256*256).
  change (2^56) with (256*256*256*256*256*256*256).
  rewrite <- !Z.div_div by lia.
  pose proof (Z.div_mod x 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
  assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
  { rewrite !Z.div_div by lia. apply Z.div_small. lia. }
  lia.
Qed.

Lemma zb_eq0 : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i = 0) -> x = 0.
Proof.
  intros x Hx H. rewrite (zdig_recon8 x Hx).
  rewrite !H by lia. cbn [zdig]. lia.
Qed.

Lemma zb_neq0 : forall x i, zb x i <> 0 -> x <> 0.
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.

(* [comment removed for export] *)

Lemma zb_split : forall lo hi i,
  0 <= lo < 2^(8 * Z.of_nat i) -> 0 <= hi ->
  zb (lo + 2^(8 * Z.of_nat i) * hi) i = hi mod 256.
Proof.
  intros lo hi i Hlo Hhi. unfold zb.
  rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
  rewrite (Z.div_small lo) by lia. reflexivity.
Qed.

Lemma zb_mod64 : forall y i, (i < 8)%nat -> 0 <= y < 2^65 ->
  zb (y mod 2^64) i = zb y i.
Proof.
  intros y i Hi Hy.
  destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. reflexivity.
  - assert (Hm : y mod 2^64 = y - 2^64).
    { replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Hm. unfold zb.
    pose proof (pow2_8i_pos i) as Hk.
    assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
    { replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
      rewrite Z.pow_add_r by lia. change (2^8) with 256.
      apply Z.divide_factor_l. }
    destruct Hdiv as [q Hq].
    replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
      by (rewrite Hd, Hq; lia).
    rewrite Z.div_add by lia.
    replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
      with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Definition ONESNEG : Z := 18374403900871474943.   (* [comment removed for export] *)
Definition HIGHS   : Z := 9259542123273814144.    (* [comment removed for export] *)
Definition ALLONES : Z := 18446744073709551615.   (* [comment removed for export] *)

Definition Tz (x : Z) : Z :=
  Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb.
  rewrite Z.land_comm.
  pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
  lia.
Qed.

(* [comment removed for export] *)

Lemma Tz_range : forall x, 0 <= Tz x < 2^64.
Proof.
  intro x. unfold Tz. split.
  - apply Z.land_nonneg. right. unfold HIGHS. lia.
  - pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
                  ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.

Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.

Lemma zb_ALLONES : forall i, (i < 8)%nat -> zb ALLONES i = 255.
Proof. intros i Hi. by8 i. Qed.

Lemma zb_HIGHS : forall i, (i < 8)%nat -> zb HIGHS i = 128.
Proof. intros i Hi. by8 i. Qed.

Lemma Tz_byte : forall x i, (i < 8)%nat ->
  zb (Tz x) i
  = Z.land (Z.land (zb ((x + ONESNEG) mod 2^64) i) (Z.lxor (zb x i) 255)) 128.
Proof.
  intros x i Hi. unfold Tz.
  rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
  rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_nozero : forall c, 1 <= c <= 255 ->
  Z.land (Z.land (c - 1) (Z.lxor c 255)) 128 = 0.
Proof.
  intros c Hc.
  assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
  assert (Hall : forallb (fun n =>
      Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
      (seq 1 255) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply Z.eqb_eq in Hall.
  replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.

(* [comment removed for export] *)
Lemma Tz_nozero : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i <> 0) -> Tz x = 0.
Proof.
  intros x Hx Hnz.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
  pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
  pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
  pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
  pose proof (zdig_recon8 x Hx) as Hrec.
  set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
               zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
  assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
  { unfold ds'. repeat constructor; lia. }
  assert (Hlt' : 0 <= zdig ds' < 2^64).
  { split; [apply zdig_nonneg; exact Hds'|].
    pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
    cbn [length] in H'. exact H'. }
  assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
  { rewrite Hrec at 1.
    replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
             + ONESNEG)
      with (zdig ds' + 1 * 2^64)
      by (unfold ds', ONESNEG; cbn [zdig]; lia).
    rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
  apply zb_eq0; [apply Tz_range|].
  intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
  rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
    unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.

Lemma zb_split_255 : forall v lo Q i p,
  p = 2^(8 * Z.of_nat i) -> v = lo + p * (255 + 256 * Q) ->
  0 <= lo < p -> 0 <= Q -> zb v i = 255.
Proof.
  intros v lo Q i p Hp Hv Hlo HQ. subst p v.
  rewrite zb_split by (try lia; assumption).
  replace (255 + 256 * Q) with (255 + Q * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sum_byte_255 : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) ->
  zb (x + ONESNEG) i = 255.
Proof.
  intros x i Hx Hi Hz Hlow.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
  unfold ONESNEG.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  - (* [comment removed for export] *)
    apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    pose proof (Hlow 6%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
      [ vm_compute; reflexivity | lia | lia | lia ].
Qed.


(* [comment removed for export] *)
Lemma Tz_haszero : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) -> Tz x <> 0.
Proof.
  intros x i Hx Hi Hz Hlow.
  apply (zb_neq0 _ i).
  rewrite Tz_byte by exact Hi.
  rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
  rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
  vm_compute. discriminate.
Qed.

End HZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma lor_shiftl8 : forall a y : Z, (0 <= a < 256)%Z -> (0 <= y)%Z ->
  Z.lor a (Z.shiftl y 8) = (a + 256 * y)%Z.
Proof.
  intros a y Ha Hy.
  assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
  assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb n 8) eqn:E.
    - apply Z.ltb_lt in E.
      rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - apply Z.ltb_ge in E.
      replace (Z.testbit a n) with false; [reflexivity|].
      symmetry. apply Z.testbit_false; [lia|].
      rewrite Z.div_small; [reflexivity|].
      split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
      change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact Hland.
  rewrite <- Z.add_nocarry_lxor by exact Hland.
  rewrite Hs. lia.
Qed.

Lemma bytes_le_to_Z_zdig : forall bs : list byte,
  bytes_le_to_Z bs = HZ.zdig (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
  apply lor_shiftl8; [apply u8_range|].
  apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
  intros x _. apply u8_range.
Qed.

Lemma zb_of_bytes : forall (bs : list byte) i, (i < length bs)%nat ->
  HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
  intros bs i Hi. rewrite bytes_le_to_Z_zdig.
  rewrite HZ.zb_zdig
    by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
              | rewrite length_map; exact Hi ]).
  rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, length bs = 8%nat ->
  (0 <= bytes_le_to_Z bs < 2^64)%Z.
Proof.
  intros bs Hl. rewrite bytes_le_to_Z_zdig.
  assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
    by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
  split; [apply HZ.zdig_nonneg; exact HF|].
  pose proof (HZ.zdig_lt _ HF) as H.
  rewrite length_map, Hl in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma total_arg_bytes_firstn_S : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  total_arg_bytes_nat (firstn (S k) l)
  = (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
  induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; cbn [firstn nth].
  - cbv [total_arg_bytes_nat]. cbn [firstn fold_right].
    rewrite firstn_O. cbn [fold_right]. lia.
  - rewrite !total_arg_bytes_cons. cbn [length] in Hk.
    rewrite (IH k ltac:(lia)). lia.
Qed.

(** The image's exact length, without the launch premise: Linux's block
    is the head and the [arch_align_stack] pad ([cat_string_off]), the
    strings, and the 8 zero bytes at the stack VMA's end. *)
Lemma length_entry_stack_image_off : forall inp mbase ph entry (sp : word) draw,
  length (entry_stack_image inp mbase ph entry sp draw)
  = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
       (in_argv inp) (in_envp inp) (in_execfn inp)
     + launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp) + 8)%nat.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block, length_build_stack_bytes, la_rseq_launch_auxv.
  unfold cat_string_off. lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_word_k : forall inp mbase ph entry (sp : word) draw k m,
  (k < length (in_argv inp))%nat ->
  (m <= length (nth k (in_argv inp) []))%nat ->
  exists pre post,
    entry_stack_image inp mbase ph entry sp draw = pre ++ post
    /\ length pre
       = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
            (in_argv inp) (in_envp inp) (in_execfn inp)
          + total_arg_bytes_nat (firstn k (in_argv inp)) + m)%nat
    /\ (8 <= length post)%nat.
Proof.
  intros inp mbase ph entry sp draw k m Hk Hm.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre0 [post0 [E Hlen0]]].
  pose proof (length_entry_stack_image_off inp mbase ph entry sp draw) as Hall.
  pose proof (total_arg_bytes_firstn_le (S k) (in_argv inp)) as Hmono.
  pose proof (total_arg_bytes_firstn_S (in_argv inp) k Hk) as Hstep.
  set (s1 := (nth k (in_argv inp) [] ++ [Z_to_bv 8 0])) in *.
  assert (Hs1 : length s1 = (length (nth k (in_argv inp) []) + 1)%nat)
    by (unfold s1; rewrite length_app; cbn [length]; lia).
  assert (HL : (total_arg_bytes_nat (in_argv inp)
                <= launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))%nat)
    by (unfold launch_string_bytes; rewrite length_flatten_strings; lia).
  assert (Hpost0 : (8 <= length post0)%nat).
  { assert (Hl : length (entry_stack_image inp mbase ph entry sp draw)
                 = (length pre0 + length s1 + length post0)%nat)
      by (rewrite E, !length_app; lia).
    lia. }
  exists (pre0 ++ firstn m s1), (skipn m s1 ++ post0).
  split; [|split].
  - rewrite E, <- !app_assoc. f_equal.
    rewrite app_assoc, firstn_skipn. reflexivity.
  - rewrite length_app, Hlen0, firstn_length_le by lia. lia.
  - rewrite length_app, length_skipn. lia.
Qed.

Lemma read_word_stack :
  forall v segs inp mbase ph entry (sp brk : word) draw k m,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat -> (m <= length (nth k (in_argv inp) []))%nat ->
  exists bs, length bs = 8%nat /\
    rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
        (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
         + nat_to_word m) 8%nat = Some bs.
Proof.
  intros v segs inp mbase ph entry sp brk draw k m Hlaunch Hk Hm.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_word_k inp mbase ph entry sp draw k m Hk Hm)
    as [pre [post [E [Hlen Hpost]]]].
  exists (firstn 8 post). split; [apply firstn_length_le; lia|].
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
           + nat_to_word m)
    with (sp + nat_to_word (length pre)).
  2:{ rewrite Hlen, (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply (read_at_offset_image segs inp mbase ph entry sp draw
           pre (firstn 8 post) (skipn 8 post) 8%nat).
  - rewrite E. f_equal. symmetry. apply firstn_skipn.
  - apply firstn_length_le. lia.
  - exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ArgvWord.

  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End ArgvWord.
End MuslStrlen.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : forall segs n m m' a,
  mem_grows m m' ->
  store_ok segs m a n = true -> store_ok segs m' a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : forall segs n m a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      wview segs m x <> None) ->
  store_ok segs m a n = true.
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined :
  forall inp mbase ph entry sp (x : word) draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned x ->
  bv_unsigned x < bv_unsigned sp ->
  wrap_mem inp mbase ph entry sp draw x <> None.
Proof.
  intros inp mbase ph entry sp x draw Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw) x)
    as [b|]; [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window :
  forall segs inp mbase ph entry sp a n draw,
  stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp a n draw Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem inp mbase ph entry sp draw x) as [b|] eqn:Hw;
    [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Definition stack_window_reach : Z := 2244095.

(* [comment removed for export] *)
Definition stack_window_depth : Z := stack_max_size - stack_window_reach.

Lemma stack_window_depth_val : stack_window_depth = 6144513.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  (* [comment removed for export] *)
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

(* [comment removed for export] *)
Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
Qed.

(* [comment removed for export] *)
Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_aligned
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

(* [comment removed for export] *)
Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  stack_window_lo (in_kernel inp) mbase draw
  <= bv_unsigned sp + stack_window_reach - stack_max_size.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_window_reach, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wrap_window_valid :
  forall segs inp mbase ph entry (sp brk0 : word) a n draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  bv_unsigned sp + stack_window_reach - stack_max_size <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned sp ->
  store_ok segs (wrap_mem inp mbase ph entry sp draw) a n = true.
Proof.
  intros segs inp mbase ph entry sp brk0 a n draw Hvl Hlau Hlo Hhi.
  apply store_ok_wrap_window; [|exact Hhi].
  pose proof (stack_window_lo_valid inp sp brk0 mbase draw Hvl Hlau). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : forall segs m zs a n,
  zs <> [] ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word,
      bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
      zeros_cover zs x = true) ->
  store_ok segs (apply_zeros m zs) a n = true.
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : forall segs m (b l a : word) (n : nat),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned b + bv_unsigned l ->
  store_ok segs (zmem m b l) a n = true.
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : forall segs m n a,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m a n = true ->
  forall x : word,
    bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n ->
    wview segs m x <> None.
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : forall segs m (lo a : word) (N n : nat),
  bv_unsigned lo + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m lo N = true ->
  bv_unsigned lo <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= bv_unsigned lo + Z.of_nat N ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : forall segs m (lo a : word) (N n : nat) (base hi : Z),
  bv_unsigned lo = base ->
  base + Z.of_nat N = hi ->
  hi <= 2 ^ 64 ->
  wseg_ok segs lo N = true ->
  base <= bv_unsigned a ->
  bv_unsigned a + Z.of_nat n <= hi ->
  store_ok segs m a n = true.
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : forall segs m n (a : word),
  store_ok segs m a n = true ->
  exists w, read_bytes_aux (wview segs m) a n = Some w.
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint wbytes_chain (m : word -> option byte) (l : list (word * list byte)) : word -> option byte :=
  match l with
  | nil => m
  | (a, bs) :: l' => wbytes (wbytes_chain m l') a bs
  end.
Lemma wbytes_chain_grows : forall l m, mem_grows m (wbytes_chain m l).
Proof.
  induction l as [|[a bs] l IH]; intros m; cbn [wbytes_chain]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply IH | apply wbytes_grows].
Qed.
Lemma store_ok_chain : forall segs n m l a,
  store_ok segs m a n = true -> store_ok segs (wbytes_chain m l) a n = true.
Proof. intros segs n m l a H. eapply store_ok_mono; [apply wbytes_chain_grows | exact H]. Qed.

Ltac wchain_base m := lazymatch m with wbytes ?m' _ _ => wchain_base m' | _ => m end.
Ltac wchain_list m :=
  lazymatch m with
  | wbytes ?m' ?a ?bs => let l := wchain_list m' in uconstr:(@cons (word * list byte) (@pair word (list byte) a bs) l)
  | _ => uconstr:(@nil (word * list byte))
  end.
Ltac wchain_deep m := lazymatch m with wbytes (wbytes (wbytes _ _ _) _ _) _ _ => idtac end.
Ltac store_ok_peel_fast :=
  lazymatch goal with
  | |- store_ok ?segs ?m ?a ?n = true =>
      wchain_deep m;
      let b := wchain_base m in
      let l := wchain_list m in
      refine (store_ok_chain segs n b l a _ : store_ok segs m a n = true)
  end.

Ltac store_ok_peel :=
  try store_ok_peel_fast;
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
