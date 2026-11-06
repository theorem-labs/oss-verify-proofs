(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HasZero.HZ"; "zb"; "zdig"; "Tz"; "ONESNEG"; "ALLONES"; "HIGHS"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "land"; "lt"; "pow"; "mul"; "lxor"; "add"; "of_nat"; "modulo"; "div"; "lor"; "shiftl"; "shiftr"; "sub"; "@Corelib.Init.Datatypes"; "nat"; "cons"; "list"; "length"; "nil"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module HZ.
Local Open Scope Z_scope.

Definition zb (x : Z) (i : nat) : Z := ltac2:(tb__ "0|0|
S12S13Vx;SdZ2SeZ8S11Vi;A1A2A2A2Z100A2").

Fixpoint zdig (ds : list Z) : Z :=
  match ds with [] => 0 | d :: r => d + 256 * zdig r end.

Lemma pow2_8i_pos : ltac2:(tb__ "0|0|
S18ScZ0SdZ2SeZ8S11R1A1A2A2A2Fi;").
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zb_bound : ltac2:(tb__ "0|1|
S0S18S8SaZ0S1R2R1A2M0A2ScG0Z100A2A2Fi;Fx;").
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.

Lemma zb_0 : ltac2:(tb__ "0|1|
S18S7S0S1Z0M0R1A2G0A3Fi;").
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.

Lemma land_land_m : ltac2:(tb__ "0|0|
S0S0S0S7S0SbSbR3R2A2R1A2SbSbR3R1A2SbR2R1A2A2A3Fm;Fb;Fa;").
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma land_lxor_m : ltac2:(tb__ "0|0|
S0S0S0S7S0SbSfR3R2A2R1A2SfSbR3R1A2SbR2R1A2A2A3Fm;Fb;Fa;").
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma lxor_lt64 : ltac2:(tb__ "0|4|
S0S0S8SaZ0M0R2A2ScR2SdZ2Z40A2M1A2A2M2G2S8SaG0SfR4R3A2M3A2ScG3G1A2A2F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb.
  assert (Hn : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [lia|].
  assert (E : Z.lxor a b mod 2^64 = Z.lxor a b).
  { rewrite <- Z.land_ones by lia. rewrite land_lxor_m.
    rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

Lemma zb_alt : ltac2:(tb__ "0|0|
S0S18S7S0S1R2R1A2SbS16R2SeZ8S11R1A1A2A2ZffA2A3Fi;Fx;").
Proof.
  intros x i. unfold zb.
  rewrite Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zb_land : ltac2:(tb__ "0|0|
S0S0S18S7S0S1SbR3R2A2R1A2SbS1R3R1A2S1R2R1A2A2A3Fi;Fw;Fu;").
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.

Lemma zb_lxor : ltac2:(tb__ "0|0|
S0S0S18S7S0S1SfR3R2A2R1A2SfS1R3R1A2S1R2R1A2A2A3Fi;Fw;Fu;").
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.

Lemma zdig_nonneg : ltac2:(tb__ "0|1|
S1aS0A1S1eS0S0S8SaZ0M0R1A2ScR1Z100A2A2Ld;R1A3SaG0S2R2A1A2F_;Fds;").
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  specialize (IH Hds). lia.
Qed.

Lemma zdig_lt : ltac2:(tb__ "0|0|
S1aS0A1S1eS0S0S8SaZ0R1A2ScR1Z100A2A2Ld;R1A3ScS2R2A1SdZ2SeZ8S11S1bS0R2A2A1A2A2A2F_;Fds;").
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig length].
  - cbn. lia.
  - apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
    specialize (IH Hds).
    replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

Lemma zb_zdig : ltac2:(tb__ "0|1|
S1aS0A1S1eS0S0S8SaZ0M0R1A2ScR1Z100A2A2Ld;R1A3S18S1dR1S1bS0R3A2A2S7S0S1S2R4A1R2A2S1fS0R2R4G0A4A3F_;Fi;F_;Fds;").
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

Lemma zdig_recon8 : ltac2:(tb__ "0|0|
S0S8SaZ0R1A2ScR1SdZ2Z40A2A2A2S7S0R2S2S19S0S1R2U0A2S19S0S1R2U1A2S19S0S1R2U2A2S19S0S1R2U3A2S19S0S1R2U4A2S19S0S1R2U5A2S19S0S1R2U6A2S19S0S1R2U7A2S1cS0A1A3A3A3A3A3A3A3A3A1A3F_;Fx;").
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

Lemma zb_eq0 : ltac2:(tb__ "0|1|
S0S8SaZ0M0R1A2ScR1SdZ2Z40A2A2A2S18S1dR1U8A2S7S0S1R4R2A2G0A3F_;Fi;S7S0R3G0A3F_;F_;Fx;").
Proof.
  intros x Hx H. rewrite (zdig_recon8 x Hx).
  rewrite !H by lia. cbn [zdig]. lia.
Qed.

Lemma zb_neq0 : ltac2:(tb__ "0|1|
S0S18S9S7S0S1R2R1A2Z0M0A3A1S9S7S0R3G0A3A1F_;Fi;Fx;").
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.

Lemma zb_split : ltac2:(tb__ "0|3|
S0S0S18S8SaZ0R3A2M0ScR3SdZ2M1SeZ8M2S11R1A1A2A2A2A2G0S7S0S1S10R5SeSdG1SeG2S11R3A1A2A2R4A2A2R3A2S12R4Z100A2A3F_;F_;Fi;Fhi;Flo;").
Proof.
  intros lo hi i Hlo Hhi. unfold zb.
  rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
  rewrite (Z.div_small lo) by lia. reflexivity.
Qed.

Lemma zb_mod64 : ltac2:(tb__ "0|1|
S0S18S1dR1U8A2S8SaZ0R3A2ScR3SdZ2M0Z41A2A2A2S7S0S1S12R4SdG0Z40A2A2R3A2S1R4R3A2A3F_;F_;Fi;Fy;").
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

Definition ONESNEG : Z := 18374403900871474943.
Definition HIGHS   : Z := 9259542123273814144.
Definition ALLONES : Z := 18446744073709551615.

Definition Tz (x : Z) : Z := ltac2:(tb__ "0|0|
SbSbS12S10Vx;S4A2SdZ2Z40A2A2SfVx;S5A2A2S6A2").

Lemma land_le_r : ltac2:(tb__ "0|0|
S0S0SaZ0R1A2SaSbR3R2A2R2A2F_;Fb;Fa;").
Proof.
  intros a b Hb.
  rewrite Z.land_comm.
  pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
  lia.
Qed.

Lemma land_le_l : ltac2:(tb__ "0|0|
S0S0SaZ0R2A2SaSbR3R2A2R3A2F_;Fb;Fa;").
Proof. intros a b Ha. rewrite Z.land_comm. apply land_le_r. exact Ha. Qed.

Lemma Tz_range : ltac2:(tb__ "0|1|
S0S8SaZ0S3R1A1M0A2ScG0SdZ2Z40A2A2A2Fx;").
Proof.
  intro x. unfold Tz. split.
  - apply Z.land_nonneg. right. unfold HIGHS. lia.
  - pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
                  ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.

Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.

Lemma zb_ALLONES : ltac2:(tb__ "0|0|
S18S1dR1U8A2S7S0S1S5R2A2ZffA3F_;Fi;").
Proof. intros i Hi. by8 i. Qed.

Lemma zb_HIGHS : ltac2:(tb__ "0|0|
S18S1dR1U8A2S7S0S1S6R2A2Z80A3F_;Fi;").
Proof. intros i Hi. by8 i. Qed.

Lemma Tz_byte : ltac2:(tb__ "0|0|
S0S18S1dR1U8A2S7S0S1S3R3A1R2A2SbSbS1S12S10R3S4A2SdZ2Z40A2A2R2A2SfS1R3R2A2ZffA2A2Z80A2A3F_;Fi;Fx;").
Proof.
  intros x i Hi. unfold Tz.
  rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
  rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.

Lemma byte_nozero : ltac2:(tb__ "0|2|
S0S8SaZ1M0R1A2SaR1ZffM1A2A2S7S0SbSbS17R2G0A2SfR2G1A2A2Z80A2Z0A3F_;Fc;").
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

Lemma Tz_nozero : ltac2:(tb__ "0|1|
S0S8SaZ0M0R1A2ScR1SdZ2Z40A2A2A2S18S1dR1U8A2S9S7S0S1R4R2A2G0A3A1F_;Fi;S7S0S3R3A1G0A3F_;F_;Fx;").
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

Lemma zb_split_255 : ltac2:(tb__ "0|2|
S0S0S0S18S0S7S0R1SdZ2SeZ8S11R2A1A2A2A3S7S0R6S10R5SeR2S10ZffM0SeZ100R4A2A2A2A2A3S8SaZ0R6A2M1ScR6R3A2A2G1S7S0S1R9R6A2G0A3F_;F_;F_;F_;Fp;Fi;FQ;Flo;Fv;").
Proof.
  intros v lo Q i p Hp Hv Hlo HQ. subst p v.
  rewrite zb_split by (try lia; assumption).
  replace (255 + 256 * Q) with (255 + Q * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sum_byte_255 : ltac2:(tb__ "0|1|
S0S18S8SaZ0M0R2A2ScR2SdZ2Z40A2A2A2S1dR2U8A2S7S0S1R4R3A2G0A3S18S1dR1R5A2S9S7S0S1R7R2A2G0A3A1F_;Fj;S7S0S1S10R6S4A2R5A2ZffA3F_;F_;F_;F_;Fi;Fx;").
Proof.
  intros x i Hx Hi Hz Hlow.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
  unfold ONESNEG.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  -
    apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
      [ vm_compute; reflexivity | lia | lia | lia ].
  -
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

Lemma Tz_haszero : ltac2:(tb__ "0|1|
S0S18S8SaZ0M0R2A2ScR2SdZ2Z40A2A2A2S1dR2U8A2S7S0S1R4R3A2G0A3S18S1dR1R5A2S9S7S0S1R7R2A2G0A3A1F_;Fj;S9S7S0S3R6A1G0A3A1F_;F_;F_;F_;Fi;Fx;").
Proof.
  intros x i Hx Hi Hz Hlow.
  apply (zb_neq0 _ i).
  rewrite Tz_byte by exact Hi.
  rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
  rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
  vm_compute. discriminate.
Qed.

End HZ.

Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma lor_shiftl8 : ltac2:(tb__ "0|2|
S0S0S8SaZ0R2A2M0ScR2Z100M1A2A2G0S7S0S14R4S15R3Z8A2A2S10R4SeG1R3A2A2A3F_;F_;Fy;Fa;").
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

Lemma bytes_le_to_Z_zdig : ltac2:(tb__ "0|2|
S1aS22Q8M0A1M1A1S7S0S21R1A1S2S20G1S0S23G0A1R1A4A1A3Fbs;").
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
  apply lor_shiftl8; [apply u8_range|].
  apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
  intros x _. apply u8_range.
Qed.

Lemma zb_of_bytes : ltac2:(tb__ "0|2|
S1aS22Q8M0A1M1A1S18S1dR1S1bG1R2A2A2S7S0S1S21R3A1R2A2S23G0S1fG1R2R3S24G0Z0A2A4A2A3F_;Fi;Fbs;").
Proof.
  intros bs i Hi. rewrite bytes_le_to_Z_zdig.
  rewrite HZ.zb_zdig
    by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
              | rewrite length_map; exact Hi ]).
  rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.

Lemma bytes_le_to_Z_range : ltac2:(tb__ "0|2|
S1aS22Q8A1M0A1S7S18S1bG0R1A2U8A3S8SaZ0S21R2A1M1A2ScG1SdZ2Z40A2A2A2F_;Fbs;").
Proof.
  intros bs Hl. rewrite bytes_le_to_Z_zdig.
  assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
    by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
  split; [apply HZ.zdig_nonneg; exact HF|].
  pose proof (HZ.zdig_lt _ HF) as H.
  rewrite length_map, Hl in H. exact H.
Qed.
