(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasT BzLemmasT2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bs_rest3 (L : dsv) (i5 j5 : Z) (d5 : dst) (s : dstrm) : dres :=
  let L5 := sv_set_j (sv_set_i L i5) j5 in
  let d6 := d_set_nused (d_set_tPos d5 (d_origPtr d5)) 0 in
  let d7 := if d_rand d6 =? 0 then d6 else d_set_rTPos (d_set_rNToGo d6 0) 0 in
  if 100000 * d_bs100k d5 <=? d_tPos d7 then DRetNoSave 1 L5 d7 s else
  let k0 := indexIntoF (d_tPos d7) (d_cftab d7) in
  let d8 := d_set_nused (d_set_tPos (d_set_k0 d7 k0) (get_ll d7 (d_tPos d7))) 1 in
  let d9 := if d_rand d8 =? 0 then d8 else let d' := rand_upd d8 in d_set_k0 d' (Z.lxor (d_k0 d') (rand_mask d')) in
  DRet BZ_OK L5 d9 s.
Definition bs_rest2 (L : dsv) (d4 : dst) (s : dstrm) : dres :=
  let i0 := d_origPtr d4 in let j0 := get_ll d4 i0 in
  let '(i5, j5, d5) := prev_loop (S (Z.to_nat (sv_nblock L))) i0 j0 d4 in bs_rest3 L i5 j5 d5 s.
Definition bs_rest1 (L : dsv) (d3 : dst) (s : dstrm) : dres := bs_rest2 L (tvec_small (Z.to_nat (sv_nblock L)) 0 d3) s.

Lemma d_bs100k_set_ll : forall d i n, d_bs100k (set_ll d i n) = d_bs100k d.
Proof. intros [] i n; reflexivity. Qed.
Lemma d_bs100k_tvec_small : forall n i d, d_bs100k (tvec_small n i d) = d_bs100k d.
Proof. induction n as [|n IH]; intros i d; [reflexivity|]. cbn [tvec_small]. rewrite IH. destruct d; reflexivity. Qed.
Lemma d_bs100k_prev_loop : forall n i j d, d_bs100k (snd (prev_loop n i j d)) = d_bs100k d.
Proof.
  induction n as [|n IH]; intros i j d; [reflexivity|]. cbn [prev_loop].
  destruct (j =? d_origPtr d); [cbn [snd]; apply d_bs100k_set_ll|]. rewrite IH. apply d_bs100k_set_ll.
Qed.

Lemma be_small_eq : forall L d s, be_small L d s = bs_rest1 L (d_set_cftabCopy d (cf_dup 257 0 (d_cftab d) (d_cftabCopy d))) s.
Proof.
  intros L d s. unfold be_small, bs_rest1, bs_rest2, bs_rest3.
  set (d3 := d_set_cftabCopy d _). set (d4 := tvec_small _ 0 d3).
  destruct (prev_loop _ _ _ d4) as [[i5 j5] d5] eqn:E.
  pose proof (d_bs100k_prev_loop (S (Z.to_nat (sv_nblock L))) (d_origPtr d4) (get_ll d4 (d_origPtr d4)) d4) as B. rewrite E in B. cbn [snd] in B.
  rewrite B. subst d4. rewrite d_bs100k_tvec_small. subst d3. destruct d; reflexivity.
Qed.

Definition K_L26 (F : nat) (L : dsv) (d : dst) (s : dstrm) (k : Z) : dres :=
  dgo F (bs_rest1 L (d_set_cftabCopy d (cf_dup (Z.to_nat (257 - k)) k (d_cftab d) (d_cftabCopy d))) s).
Definition K_L27 (F : nat) (L : dsv) (d : dst) (s : dstrm) (i : Z) : dres :=
  dgo F (bs_rest2 L (tvec_small (Z.to_nat (sv_nblock L - i)) i d) s).
Definition K_PR (F : nat) (L : dsv) (d : dst) (s : dstrm) (i j : Z) (n : nat) : dres :=
  dgo F (let '(i5, j5, d5) := prev_loop n i j d in bs_rest3 L i5 j5 d5 s).
Definition K_TAIL (F : nat) (L : dsv) (d : dst) (s : dstrm) (j5 : Z) : dres := dgo F (bs_rest3 L (d_origPtr d) j5 d s).

Lemma K_HSMALL_L26 : forall F L d s, K_HSMALL F L d s = K_L26 F L d s 0.
Proof. intros. unfold K_HSMALL, K_L26. rewrite be_small_eq. reflexivity. Qed.
Lemma K_L26_step : forall F L d s k, 0 <= k <= 256 ->
  K_L26 F L d s k = K_L26 F L (d_set_cftabCopy d (zset (d_cftabCopy d) k (zget (d_cftab d) k))) s (k + 1).
Proof.
  intros F L d s k Hk. unfold K_L26. replace (Z.to_nat (257 - k)) with (S (Z.to_nat (257 - (k + 1)))) by lia.
  cbn [cf_dup]. destruct d; reflexivity.
Qed.
Lemma K_L26_exit : forall F L d s, K_L26 F L d s 257 = K_L27 F L d s 0.
Proof. intros. unfold K_L26, K_L27, bs_rest1. cbn [Z.sub Z.to_nat cf_dup]. rewrite Z.sub_0_r. destruct d; reflexivity. Qed.

(* [comment removed for export] *)
Definition tv1 (d : dst) (i : Z) : dst :=
  let uc := Z.land (zget (d_ll16 d) i) 255 in
  let k := zget (d_cftabCopy d) uc in
  let d1 := set_ll d i k in
  d_set_cftabCopy d1 (zset (d_cftabCopy d1) uc (k + 1)).
Lemma K_L27_step : forall F L d s i, 0 <= i < sv_nblock L -> K_L27 F L d s i = K_L27 F L (tv1 d i) s (i + 1).
Proof.
  intros F L d s i Hi. unfold K_L27. replace (Z.to_nat (sv_nblock L - i)) with (S (Z.to_nat (sv_nblock L - (i + 1)))) by lia.
  cbn [tvec_small]. reflexivity.
Qed.
Lemma K_L27_exit : forall F L d s, K_L27 F L d s (sv_nblock L) = dgo F (bs_rest2 L d s).
Proof. intros. unfold K_L27. rewrite Z.sub_diag. reflexivity. Qed.
Lemma bs_rest2_PR : forall F L d s,
  dgo F (bs_rest2 L d s) = K_PR F L d s (d_origPtr d) (get_ll d (d_origPtr d)) (S (Z.to_nat (sv_nblock L))).
Proof. reflexivity. Qed.
Lemma K_PR_step : forall F L d s i j n, j <> d_origPtr d ->
  K_PR F L d s i j (S n) = K_PR F L (set_ll d j i) s j (get_ll d j) n.
Proof. intros F L d s i j n H. unfold K_PR. cbn [prev_loop]. destruct (Z.eqb_spec j (d_origPtr d)); [contradiction| reflexivity]. Qed.
Lemma K_PR_exit : forall F L d s i j n, j = d_origPtr d ->
  K_PR F L d s i j (S n) = K_TAIL F L (set_ll d j i) s (get_ll d j).
Proof.
  intros F L d s i j n H. unfold K_PR, K_TAIL. cbn [prev_loop]. destruct (Z.eqb_spec j (d_origPtr d)); [| contradiction].
  replace (d_origPtr (set_ll d j i)) with j by (destruct d; cbn in *; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_ll_view : forall d i, get_ll d i = BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) i.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sft_nr (d : dst) (k0 tp2 : Z) : dst :=
  d_set_nused (d_set_tPos (d_set_k0 (d_set_nused (d_set_tPos d (d_origPtr d)) 0) k0) tp2) 1.
Definition sft_r (d : dst) (k0 tp2 : Z) : dst :=
  d_set_k0 (d_set_rNToGo (d_set_rTPos (d_set_rNToGo
    (d_set_nused (d_set_tPos (d_set_k0 (d_set_rTPos (d_set_rNToGo (d_set_nused (d_set_tPos d (d_origPtr d)) 0) 0) 0) k0) tp2) 1)
    619) 1) 618) k0.
(* [comment removed for export] *)
Lemma bs_rest3_nr : forall L i5 j5 d s, d_rand d = 0 -> d_origPtr d < 100000 * d_bs100k d ->
  bs_rest3 L i5 j5 d s = DRet BZ_OK (sv_set_j (sv_set_i L i5) j5) (sft_nr d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s.
Proof.
  intros L i5 j5 d s R TP. unfold bs_rest3, sft_nr.
  destruct d; cbv -[Z.leb Z.eqb Z.mul Z.lt Z.lxor Z.add Z.sub indexIntoF get_ll rNums rand_upd rand_mask] in *. rewrite R. cbv -[Z.leb Z.mul Z.lt Z.lxor Z.add Z.sub indexIntoF get_ll rNums rand_upd rand_mask].
  destruct (Z.leb_spec (100000 * d_bs100k) d_origPtr); [lia|]. reflexivity.
Qed.
Lemma bs_rest3_r : forall L i5 j5 d s, d_rand d = 1 -> d_origPtr d < 100000 * d_bs100k d ->
  bs_rest3 L i5 j5 d s = DRet BZ_OK (sv_set_j (sv_set_i L i5) j5) (sft_r d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s.
Proof.
  intros L i5 j5 d s R TP. unfold bs_rest3, sft_r.
  destruct d; cbv -[Z.leb Z.eqb Z.mul Z.lt Z.lxor Z.add Z.sub indexIntoF get_ll rNums rand_upd rand_mask] in *. rewrite R. cbv -[Z.leb Z.mul Z.lt Z.lxor Z.add Z.sub indexIntoF get_ll rNums rand_upd rand_mask].
  destruct (Z.leb_spec (100000 * d_bs100k) d_origPtr); [lia|].
  unfold rand_upd, rand_mask. cbv -[Z.mul Z.lxor indexIntoF get_ll rNums]. rewrite rNums_0. cbv -[Z.mul Z.lxor indexIntoF get_ll].
  rewrite Z.lxor_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smallF (L : dsv) (d : dst) (sym unz ll16_0 ll4_0 : Z -> Z) : Prop :=
  tset d /\ d_small d = 1 /\ hdr_ok d /\ 0 <= d_origPtr d < sv_nblock L /\
  sv_nblock L <= 100000 * d_bs100k d /\ sv_nblock L <= 900000 /\
  hist_ok unz sym (Z.to_nat (sv_nblock L)) /\ (forall k, 0 <= k < sv_nblock L -> 0 <= sym k < 256) /\
  zget (d_unzftab d) = unz /\ (forall j, 0 <= j <= 256 -> zget (d_cftab d) j = psum unz j) /\
  (forall k, 0 <= k < sv_nblock L -> ll16_0 k = sym k) /\ (forall k, 0 <= ll16_0 k < 65536) /\ (forall y, 0 <= ll4_0 y < 256).

Lemma smallF_frame : forall L d d' sym unz a b, smallF L d sym unz a b ->
  d_state d' = d_state d -> d_out_len d' = d_out_len d -> d_out_ch d' = d_out_ch d -> d_cbcrc d' = d_cbcrc d ->
  d_small d' = d_small d -> d_rand d' = d_rand d -> d_sbcrc d' = d_sbcrc d -> d_origPtr d' = d_origPtr d ->
  d_bs100k d' = d_bs100k d -> d_unzftab d' = d_unzftab d -> d_cftab d' = d_cftab d ->
  smallF L d' sym unz a b.
Proof.
  intros L d d' sym unz a b H E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11. unfold smallF, tset, hdr_ok in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11. exact H.
Qed.
Lemma smallF_of_HSMALL : forall L d, dinv_HSMALL L d -> (forall k, 0 <= zget (d_ll16 d) k < 2 ^ 16) -> (forall y, 0 <= zget (d_ll4 d) y < 256) ->
  smallF L d (bsym d) (zget (d_unzftab d)) (zget (d_ll16 d)) (zget (d_ll4 d)).
Proof.
  (intros L d; cps_intros (EOB & ORIG & CFP & TS & SM); intros R16 R4). cps_destruct EOB as (NB1 & NB9 & SYMB & HIST & HDR).
  unfold smallF. split; [exact TS|]. split; [exact SM|]. split; [exact HDR|]. split; [exact ORIG|]. split; [lia|]. split; [lia|].
  split; [exact HIST|]. split; [exact SYMB|]. split; [reflexivity|]. split; [exact CFP|].
  split; [intros k Hk; unfold bsym; rewrite SM; reflexivity|]. split; [exact R16| exact R4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_65535_mod' : forall v, Z.land v 65535 = v mod 65536.
Proof. intros v. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_255_mod' : forall v, Z.land v 255 = v mod 256.
Proof. intros v. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Local Ltac dcbn_all := cbn [BzDState.d_ll16 BzDState.d_ll4 BzDState.d_cftabCopy BzDState.d_cftab BzDState.d_unzftab BzDState.d_origPtr
                             BzDState.d_set_ll16 BzDState.d_set_ll4 BzDState.d_set_cftabCopy] in *.
Lemma nib_odd_range' : forall old n, 0 <= old < 256 -> 0 <= n < 16 -> 0 <= Z.lor (Z.land old 15) (n * 16) < 256.
Proof.
  intros old n Ho Hn. apply (lor_lt_pow2 _ _ 8); [| lia].
  split; [apply Z.land_nonneg; lia|].
  assert (Z.land old 15 <= 15); [| lia].
  change (Z.land old 15) with (Z.land old (Z.ones 4)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound old (2 ^ 4) ltac:(lia)). lia.
Qed.
Lemma K_L27_step_even : forall F L d s i, 0 <= i < sv_nblock L -> Z.land i 1 = 0 ->
  let uc := zget (d_ll16 d) i mod 256 in let k := zget (d_cftabCopy d) uc in 0 <= k ->
  K_L27 F L d s i =
  K_L27 F L (d_set_cftabCopy (d_set_ll4 (d_set_ll16 d (zset (d_ll16 d) i (k mod 65536)))
                                        (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 240) (k / 65536))))
               (zset (d_cftabCopy d) uc (k + 1))) s (i + 1).
Proof.
  intros F L d s i Hi EV. cbv zeta. intros Hk. rewrite K_L27_step by lia. unfold tv1, set_ll, set_ll4.
  destruct d; dcbn_all.
  rewrite EV. cbn [Z.eqb]. rewrite !land_255_mod', !land_65535_mod'.
  rewrite !(Z.shiftr_div_pow2 _ 16), (Z.shiftr_div_pow2 i 1) by lia. change (2 ^ 16) with 65536. change (2 ^ 1) with 2.
  reflexivity.
Qed.
Lemma K_L27_step_odd : forall F L d s i, 0 <= i < sv_nblock L -> Z.land i 1 <> 0 ->
  let uc := zget (d_ll16 d) i mod 256 in let k := zget (d_cftabCopy d) uc in 0 <= k -> k / 65536 < 16 -> 0 <= zget (d_ll4 d) (i / 2) < 256 ->
  K_L27 F L d s i =
  K_L27 F L (d_set_cftabCopy (d_set_ll4 (d_set_ll16 d (zset (d_ll16 d) i (k mod 65536)))
                                        (zset (d_ll4 d) (i / 2) (Z.lor (Z.land (zget (d_ll4 d) (i / 2)) 15) (k / 65536 * 16))))
               (zset (d_cftabCopy d) uc (k + 1))) s (i + 1).
Proof.
  intros F L d s i Hi OD. cbv zeta. intros Hk Hk16 Hold. rewrite K_L27_step by lia. unfold tv1, set_ll, set_ll4.
  destruct d; dcbn_all.
  destruct (Z.eqb_spec (Z.land i 1) 0); [lia|]. rewrite !land_255_mod', !land_65535_mod'.
  rewrite !(Z.shiftr_div_pow2 _ 16), (Z.shiftr_div_pow2 i 1), Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536. change (2 ^ 1) with 2. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (Z.lor _ _) 256) by (apply nib_odd_range'; [exact Hold| split; [apply Z.div_pos; lia| exact Hk16]]).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_ll_ext : forall a b a' b' j, a j = a' j -> b (Z.shiftr j 1) = b' (Z.shiftr j 1) ->
  BzModel.get_ll a b j = BzModel.get_ll a' b' j.
Proof. intros a b a' b' j E1 E2. unfold BzModel.get_ll, BzModel.get_ll4. rewrite E1, E2. reflexivity. Qed.

(* [comment removed for export] *)
Definition sl_even (d : dst) (j i : Z) : dst :=
  d_set_ll4 (d_set_ll16 d (zset (d_ll16 d) j (i mod 65536)))
            (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 240) (i / 65536))).
Definition sl_odd (d : dst) (j i : Z) : dst :=
  d_set_ll4 (d_set_ll16 d (zset (d_ll16 d) j (i mod 65536)))
            (zset (d_ll4 d) (j / 2) (Z.lor (Z.land (zget (d_ll4 d) (j / 2)) 15) (i / 65536 * 16))).
Lemma set_ll_even : forall d j i, 0 <= j -> Z.land j 1 = 0 -> 0 <= i -> set_ll d j i = sl_even d j i.
Proof.
  intros d j i Hj EV Hi. unfold set_ll, set_ll4, sl_even. destruct d; dcbn_all.
  rewrite EV. cbn [Z.eqb]. rewrite !land_65535_mod'.
  rewrite !(Z.shiftr_div_pow2 _ 16), (Z.shiftr_div_pow2 j 1) by lia. change (2 ^ 16) with 65536. change (2 ^ 1) with 2.
  reflexivity.
Qed.
Lemma set_ll_odd : forall d j i, 0 <= j -> Z.land j 1 <> 0 -> 0 <= i -> i / 65536 < 16 -> 0 <= zget (d_ll4 d) (j / 2) < 256 ->
  set_ll d j i = sl_odd d j i.
Proof.
  intros d j i Hj OD Hi Hi16 Hold. unfold set_ll, set_ll4, sl_odd. destruct d; dcbn_all.
  destruct (Z.eqb_spec (Z.land j 1) 0); [lia|]. rewrite !land_255_mod', !land_65535_mod'.
  rewrite !(Z.shiftr_div_pow2 _ 16), (Z.shiftr_div_pow2 j 1), Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536. change (2 ^ 1) with 2. change (2 ^ 4) with 16.
  rewrite (Z.mod_small (Z.lor _ _) 256) by (apply nib_odd_range'; [exact Hold| split; [apply Z.div_pos; lia| exact Hi16]]).
  reflexivity.
Qed.
Lemma K_PR_step_sl : forall F L d s i j n d1, j <> d_origPtr d -> set_ll d j i = d1 ->
  K_PR F L d s i j (S n) = K_PR F L d1 s j (BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) j) n.
Proof. intros F L d s i j n d1 NE <-. rewrite K_PR_step by exact NE. reflexivity. Qed.
Lemma K_PR_exit_sl : forall F L d s i j n d1, j = d_origPtr d -> set_ll d j i = d1 ->
  K_PR F L d s i j (S n) = K_TAIL F L d1 s (BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) j).
Proof. intros F L d s i j n d1 E <-. rewrite (K_PR_exit F L d s i j n E). reflexivity. Qed.
(* [comment removed for export] *)
Lemma K_L27_PR : forall F L d s,
  K_L27 F L d s (sv_nblock L) = K_PR F L d s (d_origPtr d) (BzModel.get_ll (zget (d_ll16 d)) (zget (d_ll4 d)) (d_origPtr d)) (S (Z.to_nat (sv_nblock L)) - 0)%nat.
Proof. intros. rewrite K_L27_exit, bs_rest2_PR, Nat.sub_0_r. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_TAIL_nr : forall F L d s j5, d_rand d = 0 -> d_origPtr d < 100000 * d_bs100k d ->
  K_TAIL F L d s j5 = DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_nr d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s.
Proof. intros F L d s j5 R TP. unfold K_TAIL. rewrite bs_rest3_nr by assumption. reflexivity. Qed.
Lemma K_TAIL_r : forall F L d s j5, d_rand d = 1 -> d_origPtr d < 100000 * d_bs100k d ->
  K_TAIL F L d s j5 = DRet BZ_OK (sv_set_j (sv_set_i L (d_origPtr d)) j5) (sft_r d (indexIntoF (d_origPtr d) (d_cftab d)) (get_ll d (d_origPtr d))) s.
Proof. intros F L d s j5 R TP. unfold K_TAIL. rewrite bs_rest3_r by assumption. reflexivity. Qed.
