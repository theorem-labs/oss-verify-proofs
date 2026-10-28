(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzCHuff BzCHuffF1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require KeepVars. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record hmenv := HE {
  he_ra : word; he_sp : word; he_gp : word; he_tp : word;
  he_s0 : word; he_s1 : word; he_s2 : word; he_s3 : word; he_s4 : word; he_s5 : word;
  he_s6 : word; he_s7 : word; he_s8 : word; he_s9 : word; he_s10 : word; he_s11 : word;
  he_F : bvmap 5 word; he_fc : bv 32;
  he_El : Z; he_Ef : Z; he_lb : Z; he_fb : Z; he_A : Z; he_NL : Z; he_NF : Z; he_lo : Z;
  he_qsp : Z; he_qf : Z;                  (* [comment removed for export] *)
  he_len : zarr; he_freq : zarr; he_Jl : list byte; he_Jf : list byte;
  he_sv : word; he_m0 : word -> option byte
}.

Definition CEILh : Z := alloc_ceiling.  (* [comment removed for export] *)

Definition hmenv_ok (X : hmenv) : Prop :=
  let usp := bv_unsigned (he_sp X) in
  0 <= he_lb X /\ he_lb X + he_A X <= he_NL X /\ 0 <= he_fb X /\ he_fb X + he_A X <= he_NF X /\ 3 <= he_A X <= 258 /\
  0 < he_El X /\ he_El X + he_NL X <= CEILh /\ 0 < he_Ef X /\ he_Ef X + 4 * he_NF X <= CEILh /\ he_Ef X = 4 * he_qf X /\
  (he_El X + he_NL X <= he_Ef X \/ he_Ef X + 4 * he_NF X <= he_El X) /\
  CEILh <= he_lo X /\ he_lo X + 5328 <= usp /\ usp < 18446744073709551616 /\ usp = 16 * he_qsp X /\
  (forall v, 0 <= v < he_A X -> zdef (he_freq X) (he_fb X + v) = true /\ 0 <= zget (he_freq X) (he_fb X + v) < 8388608).

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
Ltac hmenv_open XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; unfold hmenv_ok, CEILh in H; cbv zeta in H;
  let FRQ := fresh "FRQ" in
  cps_destruct H as (?XLB & ?XLBN & ?XFB & ?XFBN & ?XA & ?XEL & ?XELC & ?XEF & ?XEFC & ?XEF4 & ?XAP & ?XLO & ?XLOF & ?XSP & ?XAL & FRQ).
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32s_cons : forall w ws, u32s (w :: ws) = le4 w ++ u32s ws.
Proof. reflexivity. Qed.
Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = repeat (Z_to_bv 8 255) 4.
Proof.
  rewrite le4_bytes. cbn [repeat]. change (-1 / 256) with (-1). change (-1 / 65536) with (-1). change (-1 / 16777216) with (-1).
  rewrite <- (Z_to_bv8_mod256 (-1)). reflexivity.
Qed.
Lemma u32s_repeat_m1 : forall n, u32s (repeat (Z_to_bv 64 (-1)) n) = repeat (Z_to_bv 8 255) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat]. rewrite u32s_cons, IH, le4_m1.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Section WithSegs.
  Variable segs : list Segment.

  Lemma u32arr_u8arr' : forall m A ws, u32arr segs m A ws <-> u8arr segs m A (u32s ws).
  Proof. intros. unfold u32arr, u8arr. rewrite u32s_length, Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z. tauto. Qed.

  (* [comment removed for export] *)
  Lemma u32arr_m1_init : forall m P n,
    rw_cells segs m P [CB (Z.to_nat (4 * n)) (repeat (Z_to_bv 8 255) (Z.to_nat (4 * n)))] -> 0 <= n ->
    u32arr segs m P (repeat (Z_to_bv 64 (-1)) (Z.to_nat n)).
  Proof.
    intros m P n H Hn. apply (proj2 (u32arr_u8arr' m P _)). rewrite u32s_repeat_m1.
    replace (4 * Z.to_nat n)%nat with (Z.to_nat (4 * n)) by lia.
    exact (u8arr_of_rw_cells segs m P _ _ H).
  Qed.

  (* [comment removed for export] *)
  Lemma ovw_pneg_split : forall p J N i n, 0 <= i -> i + Z.of_nat n <= N ->
    ovw (pneg p i n) J N = firstn (Z.to_nat i) (ovw p J N) ++ repeat (Z_to_bv 64 (-1)) n ++ skipn (Z.to_nat i + n) (ovw p J N).
  Proof.
    intros p J N i n Hi HN. apply nth_error_ext. intros k.
    pose proof (ovw_length_nat p J N) as L. pose proof (ovw_length_nat (pneg p i n) J N) as L'.
    destruct (Nat.lt_ge_cases k (Z.to_nat N)) as [Hk|Hk].
    2:{ rewrite (proj2 (nth_error_None _ _)) by lia. symmetry. apply (proj2 (nth_error_None _ _)).
        rewrite !length_app, length_firstn, repeat_length, length_skipn. lia. }
    replace k with (Z.to_nat (Z.of_nat k)) by lia.
    destruct (Nat.lt_ge_cases k (Z.to_nat i)) as [H1|H1].
    - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn' by lia.
      rewrite !ovw_nth_raw by lia. rewrite pneg_def, pneg_get.
      replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity.
    - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      destruct (Nat.lt_ge_cases k (Z.to_nat i + n)) as [H2|H2].
      + rewrite nth_error_app1 by (rewrite repeat_length; lia).
        rewrite nth_error_repeat by lia.
        rewrite ovw_nth_raw by lia. rewrite pneg_def, pneg_get.
        replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        reflexivity.
      + rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat i + n + (Z.to_nat (Z.of_nat k) - Nat.min (Z.to_nat i) (length (ovw p J N)) - n))%nat with (Z.to_nat (Z.of_nat k)) by lia.
        rewrite !ovw_nth_raw by lia. rewrite pneg_def, pneg_get.
        replace ((i <=? Z.of_nat k) && (Z.of_nat k <? i + Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
        reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma par_after_fill : forall m P p J N A,
    u32arr segs m P (firstn 1 (ovw p J N)) ->
    u32arr segs m (P + 4) (repeat (Z_to_bv 64 (-1)) (Z.to_nat A)) ->
    u32arr segs m (P + 4 + 4 * A) (skipn (Z.to_nat (1 + A)) (ovw p J N)) ->
    0 <= A -> 1 + A <= N ->
    u32arr segs m P (ovw (pneg p 1 (Z.to_nat A)) J N).
  Proof.
    intros m P p J N A H0 H1 H2 HA HN.
    rewrite (ovw_pneg_split p J N 1 (Z.to_nat A)) by lia.
    apply (proj2 (u32arr_app segs m P _ _)). split.
    - exact H0.
    - rewrite length_firstn, ovw_length_nat. replace (P + 4 * Z.of_nat (Nat.min (Z.to_nat 1) (Z.to_nat N))) with (P + 4) by lia.
      apply (proj2 (u32arr_app segs m (P + 4) _ _)). split; [exact H1|].
      rewrite repeat_length. replace (P + 4 + 4 * Z.of_nat (Z.to_nat A)) with (P + 4 + 4 * A) by lia.
      replace (Z.to_nat 1 + Z.to_nat A)%nat with (Z.to_nat (1 + A)) by lia. exact H2.
  Qed.

  (* [comment removed for export] *)
  Lemma par_before_memset : forall m P p J N A,
    u32arr segs m P (ovw p J N) -> 0 <= A -> 1 + A <= N ->
    u32arr segs m P (firstn 1 (ovw p J N)) /\
    rw_cells segs m (P + 4) [CB (Z.to_nat (4 * A)) (u32s (firstn (Z.to_nat A) (skipn 1 (ovw p J N))))] /\
    u32arr segs m (P + 4 + 4 * A) (skipn (Z.to_nat (1 + A)) (ovw p J N)).
  Proof.
    intros m P p J N A H HA HN. pose proof (ovw_length_nat p J N) as L.
    rewrite <- (firstn_skipn 1 (ovw p J N)) in H. apply (proj1 (u32arr_app segs m P _ _)) in H. destruct H as [H0 H].
    rewrite length_firstn, L in H. replace (P + 4 * Z.of_nat (Nat.min 1 (Z.to_nat N))) with (P + 4) in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat A) (skipn 1 (ovw p J N))) in H. apply (proj1 (u32arr_app segs m (P + 4) _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn, length_skipn, L, skipn_skipn in H2.
    replace (P + 4 + 4 * Z.of_nat (Nat.min (Z.to_nat A) (Z.to_nat N - 1))) with (P + 4 + 4 * A) in H2 by lia.
    replace (Z.to_nat A + 1)%nat with (Z.to_nat (1 + A)) in H2 by lia.
    split; [exact H0|]. split; [|exact H2].
    apply (proj1 (u32arr_u8arr' m (P + 4) _)) in H1. apply (rw_cells_of_u8arr segs) in H1.
    rewrite u32s_length, length_firstn, length_skipn, L in H1.
    replace (4 * Nat.min (Z.to_nat A) (Z.to_nat N - 1))%nat with (Z.to_nat (4 * A)) in H1 by lia. exact H1.
  Qed.
End WithSegs.
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ovb_store1 ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le1 ?w)) _) =>
    lazymatch type of ARR with u8arr ?segs m ?A (ovb ?a ?J ?n) =>
      let H := fresh "ARRw" in
      pose proof (ovb_write1 segs m A a J n i w ARR ltac:(lia)) as H; clear ARR; store_done; rename H into ARR
    end end.
(* [comment removed for export] *)
Ltac store_addr E' :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad ?bs) _) =>
    replace (write_to_mem m0 ad bs) with (write_to_mem m0 (wa E') bs) by (f_equal; unfold wa; f_equal; lia) end.
Section ACeilS3. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma shiftr1_div2 : forall z, Z.shiftr z 1 = z / 2.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shiftl1_mul2 : forall z, Z.shiftl z 1 = z * 2.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma shiftl8_mul : forall z, Z.shiftl z 8 = z * 256.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma shiftr8_div : forall z, Z.shiftr z 8 = z / 256.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma addweights_range : forall a b, 0 <= a < 2147483648 -> 0 <= b < 2147483648 -> weightof a + weightof b <= 2147483136 ->
  0 <= addweights a b < 2147483648.
Proof.
  intros a b Ha Hb Hs. pose proof (addweights_bounds a b ltac:(unfold W32; lia) ltac:(unfold W32; lia)) as B.
  rewrite !weightof_eq in Hs by (unfold W32; lia).
  pose proof (tw_nonneg a ltac:(lia)). pose proof (tw_nonneg b ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hm_bveqb0_true : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> x = 0%Z.
Proof.
  intros x Hx H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma hm_bvlts0_true : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> (x < 0)%Z.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_le in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. change (2^63)%Z with 9223372036854775808%Z in H. Z.div_mod_to_equations. lia.
Qed.
Lemma hm_bvlts0_false : forall x, (- 9223372036854775808 <= x < 9223372036854775808)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = false -> (0 <= x)%Z.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_gt in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616%Z in H. change (2^63)%Z with 9223372036854775808%Z in H. Z.div_mod_to_equations. lia.
Qed.
Lemma hm_zbv_sub_mod_r : forall a b, Z_to_bv 64 (a - b mod 18446744073709551616) = Z_to_bv 64 (a - b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma hm_zbv_sub_mod_l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 - b) = Z_to_bv 64 (a - b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma hm_zbv_add_mod_r : forall a b, Z_to_bv 64 (a + b mod 18446744073709551616) = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma hm_zbv_add_mod_l : forall a b, Z_to_bv 64 (a mod 18446744073709551616 + b) = Z_to_bv 64 (a + b).
Proof. intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
Lemma hm_zbv_mod : forall a, Z_to_bv 64 (a mod 18446744073709551616) = Z_to_bv 64 a.
Proof. intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
End ACeilS3.

(* [comment removed for export] *)
Section ACeilS4. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma land_hi_weightof : forall v, 0 <= v < 4294967296 -> Z.land v 18446744073709551360 = weightof v.
Proof.
  intros v Hv. unfold weightof.
  change 18446744073709551360 with (Z.ldiff (Z.ones 64) (Z.ones 8)). change 4294967040 with (Z.ldiff (Z.ones 32) (Z.ones 8)).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.ldiff_spec.
  destruct (Z_lt_le_dec n 32).
  - rewrite (Z.ones_spec_low 64), (Z.ones_spec_low 32) by lia. reflexivity.
  - rewrite (Z.ones_spec_high 32) by lia.
    replace (Z.testbit v n) with false; [reflexivity|]. symmetry.
    destruct (Z.eq_dec v 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply (Z.lt_le_trans _ 32); [|lia]. apply Z.log2_lt_pow2; [lia|]. change (2^32) with 4294967296. lia.
Qed.
Lemma swrap32_small : forall x, - 2147483648 <= x < 2147483648 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.
Lemma weightof_range : forall v, 0 <= v < 4294967296 -> 0 <= weightof v <= v.
Proof. intros v Hv. rewrite weightof_eq by (unfold W32; lia). pose proof (tw_bounds v). pose proof (tw_nonneg v ltac:(lia)). lia. Qed.
(* [comment removed for export] *)
Lemma addweights_compiled : forall w1 w2 dm, 0 <= w1 < 2147483648 -> 0 <= w2 < 2147483648 -> weightof w1 + weightof w2 <= 2147483136 ->
  dm = Z.max (depthof w1) (depthof w2) ->
  Z.lor (dm + 1) (bv_swrap 32 (Z.land w2 18446744073709551360 + Z.land w1 18446744073709551360) mod 18446744073709551616) = addweights w1 w2.
Proof.
  intros w1 w2 dm H1 H2 Hs ->. rewrite !land_hi_weightof by lia.
  pose proof (weightof_range w1 ltac:(lia)). pose proof (weightof_range w2 ltac:(lia)).
  rewrite swrap32_small by lia. rewrite Z.mod_small by lia.
  unfold addweights. rewrite Z.lor_comm. f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod16_linq : forall x, (x mod 16 = 0)%Z -> exists q, (x = 16 * q)%Z.
Proof. intros x H. exists (x / 16)%Z. Z.div_mod_to_equations. lia. Qed.
Lemma mod4_linq : forall x, (x mod 4 = 0)%Z -> exists q, (x = 4 * q)%Z.
Proof. intros x H. exists (x / 4)%Z. Z.div_mod_to_equations. lia. Qed.
End ACeilS4.


(* [comment removed for export] *)
Ltac u8take FRu H n newbase :=
  lazymatch type of FRu with u8arr ?segs ?m ?A ?bs =>
    rewrite <- (firstn_skipn (Z.to_nat n) bs) in FRu;
    apply (proj1 (u8arr_app segs m A _ _)) in FRu;
    let H' := fresh in destruct FRu as [H' FRu]; rename H' into H;
    lazymatch type of FRu with u8arr _ _ ?A' _ => replace A' with newbase in FRu by (rewrite ?length_firstn, ?length_skipn; first [ KeepVars.keep_vars1 bs; lia | lia ]) end
  end.
(* [comment removed for export] *)
Ltac name_bytes H j n :=
  lazymatch type of H with u8arr _ _ _ ?bs =>
    let L := fresh "L" j in
    set (j := bs) in H; assert (L : Z.of_nat (length j) = n) by (subst j; rewrite ?length_firstn, ?length_skipn; first [ KeepVars.keep_vars1 bs; lia | lia ]); clearbody j
  end.
Section ACeilS5. Context {ACEIL__ : ACeil}.

Lemma stk_of_u8arr : forall segs m A bs, u8arr segs m A bs -> stk segs m A (A + Z.of_nat (length bs)).
Proof.
  intros segs m A bs H. pose proof (stk_of_rw_cells segs m A _ (rw_cells_of_u8arr segs m A bs H)) as S.
  cbn [cells_size csize] in S. rewrite Nat.add_0_r in S. exact S.
Qed.
Lemma stk_of_u32arr : forall segs m A ws, u32arr segs m A ws -> stk segs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros segs m A ws H. apply (proj1 (u32arr_u8arr' segs m A ws)) in H. pose proof (stk_of_u8arr segs m A _ H) as S.
  rewrite u32s_length, Nat2Z.inj_mul in S. exact S.
Qed.
Lemma stk_join : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
End ACeilS5.

Ltac stk_add ST K :=
  lazymatch type of K with stk _ _ ?b' ?c =>
  lazymatch type of ST with stk ?segs ?m ?lo ?b =>
    let H := fresh in pose proof (stk_join segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.
(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Section ACeilS6. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Lemma rw_cells_junk16_C8 : forall segs m A (j : list byte), rw_cells segs m A [CB 16 j] ->
  exists nd rr : Z, rw_cells segs m A [C8 (Z_to_bv 64 nd); C8 (Z_to_bv 64 rr)].
Proof.
  intros segs m A j H.
  pose proof (proj1 (proj1 H)) as W. cbn in W. destruct W as [L _].
  exists (bv_unsigned (le_bytes_to_word (firstn 8 j))), (bv_unsigned (le_bytes_to_word (skipn 8 j))).
  rewrite !Z_to_bv_bv_unsigned.
  destruct H as [[Hwf Hb] Hw]. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in Hb. rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn; lia).
    rewrite app_nil_r, firstn_skipn. exact Hb.
  - cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.
(* [comment removed for export] *)
Lemma hw_round0 : forall A s, (0 <= A)%Z -> rf_w A s -> hw (hr_h0 s) (hr_w0 s) 0 A.
Proof.
  intros A s HA RW. unfold hr_h0, hr_w0. split; [apply zget_zset_same|]. split; [apply zget_zset_same|]. split.
  - intros z Hz. replace z with 0%Z by lia. rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| lia].
  - intros x Hx. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec x 0); cbn [orb]; [split; [reflexivity| lia]|]. apply RW. lia.
Qed.
Lemma hpar_round0 : forall q (A : Z), (0 <= A)%Z -> hpar (pneg (zset q 0 (-2)) 1 (Z.to_nat A)) A.
Proof.
  intros q A HA x Hx. rewrite pneg_def, pneg_get, zdef_zset, zget_zset.
  destruct (Z.eq_dec x 0) as [->|NE].
  - replace ((1 <=? 0) && (0 <? 1 + Z.of_nat (Z.to_nat A)))%bool with false by reflexivity. cbn. split; [reflexivity| lia].
  - replace ((1 <=? x) && (x <? 1 + Z.of_nat (Z.to_nat A)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). cbn. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB8_C8 : forall segs m A pre bs post,
  rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros segs m A pre bs post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 [W2 W3]]. cbn in W2.
  split; [split|].
  - apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le8_of_bytes by exact W2. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land3_mul4 : forall q, (0 <= q)%Z -> Z.land (4 * q) 3 = 0%Z.
Proof. intros q Hq. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2)%Z with 4%Z. Z.div_mod_to_equations. lia. Qed.

End ACeilS6.
