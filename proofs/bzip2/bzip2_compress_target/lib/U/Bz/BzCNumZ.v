(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf
  BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCRebuildF BzCLemmas1 BzCFactsGm BzCHuffF6 BzCSmF1.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bits (b : bw) : Z := 8 * bw_numZ b + bw_live b.

(* [comment removed for export] *)
Definition EM (d : Z) (b b' : bw) : Prop :=
  bits b' <= bits b + d /\ bw_numZ b <= bw_numZ b' /\ (0 <= bw_live b -> 0 <= bw_live b').

Lemma EM_refl : forall b, EM 0 b b.
Proof. intros b. unfold EM. repeat split; try lia; tauto. Qed.
Lemma EM_trans : forall d1 d2 b1 b2 b3, EM d1 b1 b2 -> EM d2 b2 b3 -> EM (d1 + d2) b1 b3.
Proof. (intros d1 d2 b1 b2 b3; cps_intros (A1 & B1 & C1); cps_intros (A2 & B2 & C2)). unfold EM. repeat split; try lia; tauto. Qed.
Lemma EM_weak : forall d d' b b', EM d b b' -> d <= d' -> EM d' b b'.
Proof. (intros d d' b b'; cps_intros (A & B & C); intros L). unfold EM. repeat split; try lia; tauto. Qed.

Lemma EM_emit : forall b, 8 <= bw_live b -> EM 0 b (bw_emit b).
Proof. intros b H. unfold EM, bits, bw_emit. cbn [bw_numZ bw_live]. repeat split; lia. Qed.

Lemma needw_EM : forall f b, EM 0 b (bs_needw f b) /\ bits (bs_needw f b) = bits b.
Proof.
  induction f as [|f IH]; intros b; cbn [bs_needw].
  - split; [apply EM_refl| reflexivity].
  - destruct (Z.leb_spec 8 (bw_live b)) as [L|L].
    + destruct (IH (bw_emit b)) as [E1 E2]. split.
      * replace 0 with (0 + 0) by lia. eapply EM_trans; [apply EM_emit; exact L| exact E1].
      * rewrite E2. unfold bits, bw_emit. cbn [bw_numZ bw_live]. lia.
    + split; [apply EM_refl| reflexivity].
Qed.

Lemma bsW_EM : forall b n v, 0 <= n -> EM n b (bsW b n v).
Proof.
  intros b n v Hn. destruct (needw_EM BS_FUEL b) as [(A & B & C) E].
  unfold EM, bsW. cbn [bw_numZ bw_live bw_buff bw_zb]. unfold bits in *. cbn [bw_numZ bw_live]. repeat split; try lia.
  all: intros H; specialize (C H); lia.
Qed.
Lemma bsW_bits : forall b n v, bits (bsW b n v) = bits b + n.
Proof. intros b n v. destruct (needw_EM BS_FUEL b) as [_ E]. unfold bsW, bits in *. cbn [bw_numZ bw_live]. lia. Qed.

Lemma bsPutUChar_EM : forall b c, EM 8 b (bsPutUChar b c).
Proof. intros. unfold bsPutUChar. apply bsW_EM. lia. Qed.
Lemma bsPutUInt32_EM : forall b u, EM 32 b (bsPutUInt32 b u).
Proof.
  intros b u. unfold bsPutUInt32.
  replace 32 with (8 + 8 + 8 + 8) by lia.
  eapply EM_trans; [eapply EM_trans; [eapply EM_trans|]|]; apply bsW_EM; lia.
Qed.

(* [comment removed for export] *)
Lemma finish_facts : forall f b, bits (bs_finish f b) = bits b /\ bw_numZ b <= bw_numZ (bs_finish f b) /\
  (-7 <= bw_live b -> -7 <= bw_live (bs_finish f b)).
Proof.
  induction f as [|f IH]; intros b; cbn [bs_finish].
  - repeat split; lia.
  - destruct (Z.ltb_spec 0 (bw_live b)) as [L|L].
    + cps_destruct (IH (bw_emit b)) as (A & B & C). unfold bits, bw_emit in *. cbn [bw_numZ bw_live] in *.
      repeat split; try lia.
    + repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma numZ_of_bits : forall b, 0 <= bw_live b -> 8 * bw_numZ b <= bits b.
Proof. intros b H. unfold bits. lia. Qed.
Lemma numZ_of_bits_fin : forall b, -7 <= bw_live b -> 8 * bw_numZ b <= bits b + 7.
Proof. intros b H. unfold bits. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma put_in16_EM : forall n b in16 i, EM (Z.of_nat n) b (sm_put_in16 n b in16 i).
Proof.
  induction n as [|n IH]; intros b in16 i; cbn [sm_put_in16]; [apply EM_refl|].
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia. eapply EM_trans; [apply bsW_EM; lia| apply IH].
Qed.
Lemma put_inuse_row_EM : forall n b inUse i j, EM (Z.of_nat n) b (sm_put_inuse_row n b inUse i j).
Proof.
  induction n as [|n IH]; intros b inUse i j; cbn [sm_put_inuse_row]; [apply EM_refl|].
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia. eapply EM_trans; [apply bsW_EM; lia| apply IH].
Qed.
Lemma put_inuse_EM : forall n b in16 inUse i, EM (16 * Z.of_nat n) b (sm_put_inuse n b in16 inUse i).
Proof.
  induction n as [|n IH]; intros b in16 inUse i; cbn [sm_put_inuse]; [apply EM_refl|].
  replace (16 * Z.of_nat (S n)) with (16 + 16 * Z.of_nat n) by lia. eapply EM_trans; [| apply IH].
  destruct (negb (zget in16 i =? 0)); [| apply EM_weak with 0; [apply EM_refl| lia]].
  pose proof (put_inuse_row_EM 16 b inUse i 0). cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H.
Qed.
Lemma put_ones_EM : forall n b, EM (Z.of_nat n) b (sm_put_ones n b).
Proof.
  induction n as [|n IH]; intros b; cbn [sm_put_ones]; [apply EM_refl|].
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia. eapply EM_trans; [apply bsW_EM; lia| apply IH].
Qed.
Lemma put_sels_EM : forall n b selMtf i, (forall k, i <= k < i + Z.of_nat n -> 0 <= zget selMtf k <= 8) ->
  EM (9 * Z.of_nat n) b (sm_put_sels n b selMtf i).
Proof.
  induction n as [|n IH]; intros b selMtf i H; cbn [sm_put_sels]; [apply EM_refl|].
  replace (9 * Z.of_nat (S n)) with (9 + 9 * Z.of_nat n) by lia. eapply EM_trans; [| apply IH; intros; apply H; lia].
  pose proof (H i ltac:(lia)) as Hi.
  apply EM_weak with (Z.of_nat (Z.to_nat (zget selMtf i)) + 1); [| lia].
  eapply EM_trans; [apply put_ones_EM| apply bsW_EM; lia].
Qed.

Lemma put_up_spec : forall f b curr tgt,
  let r := sm_put_up f b curr tgt in
  curr <= snd r <= Z.max curr tgt /\ EM (2 * (snd r - curr)) b (fst r).
Proof.
  induction f as [|f IH]; intros b curr tgt; cbv zeta; cbn [sm_put_up].
  - cbn [fst snd]. split; [lia|]. replace (2 * (curr - curr)) with 0 by lia. apply EM_refl.
  - destruct (Z.ltb_spec curr tgt) as [L|L].
    + destruct (IH (bsW b 2 2) (curr + 1) tgt) as [R1 R2]. split; [lia|].
      replace (2 * (snd (sm_put_up f (bsW b 2 2) (curr + 1) tgt) - curr)) with (2 + 2 * (snd (sm_put_up f (bsW b 2 2) (curr + 1) tgt) - (curr + 1))) by lia.
      eapply EM_trans; [apply bsW_EM; lia| exact R2].
    + cbn [fst snd]. split; [lia|]. replace (2 * (curr - curr)) with 0 by lia. apply EM_refl.
Qed.
Lemma put_down_spec : forall f b curr tgt,
  let r := sm_put_down f b curr tgt in
  Z.min curr tgt <= snd r <= curr /\ EM (2 * (curr - snd r)) b (fst r).
Proof.
  induction f as [|f IH]; intros b curr tgt; cbv zeta; cbn [sm_put_down].
  - cbn [fst snd]. split; [lia|]. replace (2 * (curr - curr)) with 0 by lia. apply EM_refl.
  - destruct (Z.ltb_spec tgt curr) as [L|L].
    + destruct (IH (bsW b 2 3) (curr - 1) tgt) as [R1 R2]. split; [lia|].
      replace (2 * (curr - snd (sm_put_down f (bsW b 2 3) (curr - 1) tgt))) with (2 + 2 * (curr - 1 - snd (sm_put_down f (bsW b 2 3) (curr - 1) tgt))) by lia.
      eapply EM_trans; [apply bsW_EM; lia| exact R2].
    + cbn [fst snd]. split; [lia|]. replace (2 * (curr - curr)) with 0 by lia. apply EM_refl.
Qed.

Lemma put_lens_row_spec : forall n b len t i curr,
  1 <= curr <= 17 -> (forall v, i <= v < i + Z.of_nat n -> 1 <= zget len (258 * t + v) <= 17) ->
  let r := sm_put_lens_row n b len t i curr in
  1 <= snd r <= 17 /\ EM (33 * Z.of_nat n) b (fst r).
Proof.
  induction n as [|n IH]; intros b len t i curr Hc Hl; cbv zeta; cbn [sm_put_lens_row].
  - cbn [fst snd]. split; [lia|]. replace (33 * Z.of_nat 0) with 0 by lia. apply EM_refl.
  - pose proof (Hl i ltac:(lia)) as Li. set (tgt := zget len (258 * t + i)) in *.
    pose proof (put_up_spec 40 b curr tgt) as U. cbv zeta in U. destruct (sm_put_up 40 b curr tgt) as [b1 c1]. cbn [fst snd] in U.
    destruct U as [U1 U2].
    pose proof (put_down_spec 40 b1 c1 tgt) as D. cbv zeta in D. destruct (sm_put_down 40 b1 c1 tgt) as [b2 c2]. cbn [fst snd] in D.
    destruct D as [D1 D2].
    destruct (IH (bsW b2 1 0) len t (i + 1) c2 ltac:(lia) ltac:(intros; apply Hl; lia)) as [R1 R2].
    split; [exact R1|].
    replace (33 * Z.of_nat (S n)) with (33 + 33 * Z.of_nat n) by lia. eapply EM_trans; [| exact R2].
    apply EM_weak with (2 * (c1 - curr) + 2 * (c1 - c2) + 1); [| lia].
    eapply EM_trans; [eapply EM_trans; [exact U2| exact D2]| apply bsW_EM; lia].
Qed.

Lemma put_lens_EM : forall A n b len t, 1 <= A <= 258 ->
  (forall t', t <= t' < t + Z.of_nat n -> forall v, 0 <= v < A -> 1 <= zget len (258 * t' + v) <= 17) ->
  EM (Z.of_nat n * (5 + 33 * A)) b (sm_put_lens n b len A t).
Proof.
  intros A n. induction n as [|n IH]; intros b len t HA RO; cbn [sm_put_lens].
  - apply EM_weak with 0; [apply EM_refl| lia].
  - pose proof (RO t ltac:(lia)) as Rt.
    pose proof (put_lens_row_spec (Z.to_nat A) (bsW b 5 (zget len (258 * t + 0))) len t 0 (zget len (258 * t + 0)) (Rt 0 ltac:(lia))
                  ltac:(intros v Hv; apply Rt; lia)) as RS. cbv zeta in RS.
    destruct (sm_put_lens_row _ _ _ _ _ _) as [b' c']. cbn [fst snd] in RS. destruct RS as [_ R2].
    replace (Z.of_nat (S n) * (5 + 33 * A)) with ((5 + 33 * Z.of_nat (Z.to_nat A)) + Z.of_nat n * (5 + 33 * A)) by lia.
    eapply EM_trans; [| apply IH; [exact HA| intros; apply RO; lia]].
    eapply EM_trans; [apply bsW_EM; lia| exact R2].
Qed.

Lemma put_syms_EM : forall A n b len code arr1 sel i, 
  (forall v, 0 <= v < A -> 1 <= zget len (258 * sel + v) <= 17) ->
  (forall k, i <= k < i + Z.of_nat n -> 0 <= mtfv_at arr1 k < A) ->
  EM (17 * Z.of_nat n) b (sm_put_syms n b len code arr1 sel i).
Proof.
  intros A n. induction n as [|n IH]; intros b len code arr1 sel i RO MV; cbn [sm_put_syms].
  - apply EM_weak with 0; [apply EM_refl| lia].
  - replace (17 * Z.of_nat (S n)) with (17 + 17 * Z.of_nat n) by lia.
    eapply EM_trans; [| apply IH; [exact RO| intros; apply MV; lia]].
    pose proof (RO (mtfv_at arr1 i) (MV i ltac:(lia))) as L.
    apply EM_weak with (zget len (258 * sel + mtfv_at arr1 i)); [apply bsW_EM; lia| lia].
Qed.

Lemma put_data_EM : forall A nGroups nMTF K (len code arr1 sel : zarr) fuel b c,
  1 <= nMTF -> nMTF <= 50 * K ->
  (forall c', 0 <= c' < K -> 0 <= zget sel c' < nGroups) ->
  (forall t, 0 <= t < nGroups -> forall v, 0 <= v < A -> 1 <= zget len (258 * t + v) <= 17) ->
  (forall k, 0 <= k < nMTF -> 0 <= mtfv_at arr1 k < A) ->
  0 <= c ->
  EM (17 * (nMTF - Z.min (50 * c) nMTF)) b (fst (sm_put_data fuel b len code arr1 sel nMTF (Z.min (50 * c) nMTF) c)).
Proof.
  intros A nGroups nMTF K len code arr1 sel fuel. induction fuel as [|fuel IH]; intros b c HM HK SEL RO MV Hc; cbn [sm_put_data].
  - cbn [fst]. apply EM_weak with 0; [apply EM_refl| lia].
  - destruct (Z.leb_spec nMTF (Z.min (50 * c) nMTF)) as [L|L].
    + cbn [fst]. apply EM_weak with 0; [apply EM_refl| lia].
    + cbv zeta. set (gs := Z.min (50 * c) nMTF) in *.
      assert (Egs : gs = 50 * c) by lia.
      change (if nMTF <=? gs + BZ_G_SIZE - 1 then nMTF - 1 else gs + BZ_G_SIZE - 1) with (GE nMTF gs).
      cps_destruct (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
      assert (CK : 0 <= c < K) by lia.
      replace (GE nMTF gs + 1) with (Z.min (50 * (c + 1)) nMTF) by lia.
      replace (17 * (nMTF - gs)) with (17 * Z.of_nat (Z.to_nat (GE nMTF gs - gs + 1)) + 17 * (nMTF - Z.min (50 * (c + 1)) nMTF)) by lia.
      eapply EM_trans; [| apply IH; try assumption; lia].
      apply (put_syms_EM A); [apply RO; apply SEL; exact CK| intros; apply MV; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_nGroups_range : forall n, 2 <= sm_nGroups n <= 6.
Proof. intros n. unfold sm_nGroups. repeat (destruct (n <? _)); lia. Qed.

Theorem sendMTF_EM : forall e c0 f0 p0 i0 h0 w0 q0,
  1 <= e_nInUse e <= 256 -> 1 <= e_nMTF e <= 4194304 ->
  (forall k, 0 <= k < e_nMTF e -> 0 <= mtfv_at (e_arr1 e) k < e_nInUse e + 2) ->
  exists K, 50 * (K - 1) < e_nMTF e <= 50 * K /\
    EM (290 + 9 * K + 51114 + 17 * e_nMTF e) (e_bw e) (e_bw (fst (sendMTFValues e c0 f0 p0 i0 h0 w0 q0))).
Proof.
  intros e c0 f0 p0 i0 h0 w0 q0 HI HM MV.
  set (A := e_nInUse e + 2) in *. set (nMTF := e_nMTF e) in *.
  pose proof (sm_nGroups_range nMTF) as NG. set (nGroups := sm_nGroups nMTF) in *.
  unfold sendMTFValues. fold nMTF. fold A. fold nGroups.
  set (ip := sm_init_tables 8 _ _ _ _).
  pose proof (sm_iters_ITF A nGroups ltac:(lia) ltac:(lia) BZ_N_ITERS (e_arr1 e) nMTF
                (SITS (ip_len ip) (e_rfreq e) (e_len_pack e) (e_selector e) c0 f0 0 h0 w0 q0) ltac:(unfold BZ_N_ITERS; lia) HM MV) as IT.
  set (it := sm_iters BZ_N_ITERS _ _ _ _ _) in *.
  cps_destruct IT as (K & K1 & NS & KB & SEL & RO & _).
  pose proof (selmtf_spec (Z.to_nat (it_nSel it)) (yy_init (Z.to_nat nGroups) p0 0) (it_sel it) (e_selectorMtf e) 0) as [SM _].
  destruct (sm_selmtf _ _ _ _ _) as [pos selMtf]. cbn [snd] in SM.
  set (code := sm_assign _ _ _ _ _). set (in16 := sm_in16 _ _ _ _).
  pose proof (put_data_EM A nGroups nMTF K (it_len it) code (e_arr1 e) (it_sel it) (Z.to_nat (nMTF + 1))) as PD.
  set (b4 := sm_put_lens _ _ _ _ _).
  specialize (PD b4 0 ltac:(lia) ltac:(lia) SEL RO MV ltac:(lia)).
  replace (Z.min (50 * 0) nMTF) with 0 in PD by lia.
  destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b5 selCtr]. cbn [fst] in PD. cbn [fst e_bw].
  exists K. split; [exact KB|].
  replace (290 + 9 * K + 51114 + 17 * nMTF) with ((16 + 256 + 3 + 15 + 9 * K + 51114) + 17 * (nMTF - 0)) by lia.
  eapply EM_trans; [| exact PD].
  eapply EM_trans.
  2:{ apply EM_weak with (Z.of_nat (Z.to_nat nGroups) * (5 + 33 * A)); [apply put_lens_EM; [lia|] | nia].
      intros t' Ht' v Hv. apply RO; lia. }
  eapply EM_trans.
  2:{ apply EM_weak with (9 * Z.of_nat (Z.to_nat (it_nSel it))); [apply put_sels_EM; exact SM| lia]. }
  eapply EM_trans. 2:{ apply bsW_EM; lia. } eapply EM_trans. 2:{ apply bsW_EM; lia. }
  eapply EM_trans.
  2:{ pose proof (put_inuse_EM 16 (sm_put_in16 16 (e_bw e) in16 0) in16 (e_inUse e) 0) as PI. exact PI. }
  pose proof (put_in16_EM 16 (e_bw e) in16 0) as P16. exact P16.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cb_e0 (e : est) : est :=
  let nblock := e_nblock e in
  let blockCRC := crc_final (e_blockCRC e) in
  let c := e_combinedCRC e in
  let c := Z.lor ((Z.shiftl c 1) mod 4294967296) (Z.shiftr c 31) in
  let c := Z.lxor c blockCRC in
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) nblock (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) blockCRC c (e_blockNo e) (e_nMTF e) (e_mtfFreq e)
      (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
(* [comment removed for export] *)
Definition cb_sorted (e : est) : est := fst (fst (fst (blockSort (cb_e0 e) znew))).

(* [comment removed for export] *)
Definition cb_hdr (e1 : est) : bw :=
  let b := e_bw e1 in
  if e_blockNo e1 =? 1 then
    let b := BW 0 0 (bw_numZ b) (bw_zb b) in
    let b := bsPutUChar b BZ_HDR_B in let b := bsPutUChar b BZ_HDR_Z in
    let b := bsPutUChar b BZ_HDR_h in bsPutUChar b (BZ_HDR_0 + BLOCKSIZE100K)
  else b.
Definition cb_bhdr (b : bw) (e1 : est) : bw :=
  let b := bsPutUChar b 49 in let b := bsPutUChar b 65 in let b := bsPutUChar b 89 in
  let b := bsPutUChar b 38 in let b := bsPutUChar b 83 in let b := bsPutUChar b 89 in
  let b := bsPutUInt32 b (e_blockCRC e1) in
  let b := bsW b 1 0 in
  bsW b 24 (e_origPtr e1).
Definition cb_trailer (is_last : bool) (b : bw) (ccrc : Z) : bw :=
  if is_last then
    let b := bsPutUChar b 23 in let b := bsPutUChar b 114 in let b := bsPutUChar b 69 in
    let b := bsPutUChar b 56 in let b := bsPutUChar b 80 in let b := bsPutUChar b 144 in
    let b := bsPutUInt32 b ccrc in
    bs_finish BS_FUEL b
  else b.

Lemma blockSort_shape : forall e lj, exists arr1 arr2 ftab op,
  fst (fst (fst (blockSort e lj))) =
  EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 arr2 ftab op
       (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
       (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
       (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Proof.
  intros e lj. unfold blockSort.
  destruct (e_nblock e <? 10000).
  - do 4 eexists. reflexivity.
  - destruct (mr_budget _ <? 0); do 4 eexists; reflexivity.
Qed.

Lemma cb_sorted_fields : forall e,
  e_nblock (cb_sorted e) = e_nblock e /\ e_blockNo (cb_sorted e) = e_blockNo e /\ e_inUse (cb_sorted e) = e_inUse e /\
  e_bw (cb_sorted e) = BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew.
Proof.
  intros e. unfold cb_sorted. cps_destruct (blockSort_shape (cb_e0 e) znew) as (a1 & a2 & ft & op & E). rewrite E.
  cbn [e_nblock e_blockNo e_inUse e_bw cb_e0]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma compressBlock_bw : forall e is_last,
  e_bw (fst (compressBlock e is_last znew)) =
    (if 0 <? e_nblock e then
       let e1 := cb_sorted e in
       let eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew) in
       let es := fst (sendMTFValues eg znew znew znew znew znew znew znew) in
       cb_trailer is_last (e_bw es) (e_combinedCRC es)
     else cb_trailer is_last (cb_hdr (est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew))) (e_combinedCRC e)).
Proof.
  intros e is_last. unfold compressBlock, cb_sorted, cb_e0, cb_trailer, cb_bhdr, cb_hdr. cbv zeta.
  destruct (0 <? e_nblock e).
  - destruct (blockSort _ znew) as [[[e1 fs] ms] bu].
    destruct (generateMTFValues _ znew) as [eg yy].
    destruct (sendMTFValues _ _ _ _ _ _ _ _) as [es sm].
    cbn [fst snd e_bw est_set_bw e_combinedCRC]. reflexivity.
  - cbn [fst snd e_bw est_set_bw e_combinedCRC e_blockNo]. reflexivity.
Qed.

Lemma gm_bw : forall e yy0, e_bw (fst (generateMTFValues e yy0)) = e_bw e /\ e_nblock (fst (generateMTFValues e yy0)) = e_nblock e.
Proof.
  intros e yy0. unfold generateMTFValues.
  destruct (mk_maps _ _ _ _ _) as [unseq nInUse]. cbv zeta.
  destruct (if 0 <? _ then _ else _) as [[a1 mf] wr].
  unfold mtf_emit. cbn [fst e_bw e_nblock]. split; reflexivity.
Qed.

Lemma gm_facts_set_bw : forall e b, gm_facts e -> gm_facts (est_set_bw e b).
Proof. intros e b H. exact H. Qed.

Lemma cb_hdr_EM : forall e1, 0 <= bw_live (e_bw e1) <= 32 \/ e_blockNo e1 = 1 ->
  exists bS, bits bS <= 8 * bw_numZ (e_bw e1) + 32 /\ 0 <= bw_live bS /\ bw_numZ bS = bw_numZ (e_bw e1) /\ EM 32 bS (cb_hdr e1).
Proof.
  intros e1 H. unfold cb_hdr. destruct (Z.eqb_spec (e_blockNo e1) 1) as [E|NE].
  - exists (BW 0 0 (bw_numZ (e_bw e1)) (bw_zb (e_bw e1))). cbn [bw_live bw_numZ]. unfold bits; cbn [bw_numZ bw_live].
    split; [lia|]. split; [lia|]. split; [reflexivity|].
    replace 32 with (8 + 8 + 8 + 8) by lia.
    eapply EM_trans; [eapply EM_trans; [eapply EM_trans|]|]; apply bsPutUChar_EM.
  - exists (e_bw e1). unfold bits. split; [lia|]. split; [lia|]. split; [reflexivity|]. apply EM_weak with 0; [apply EM_refl| lia].
Qed.

Lemma cb_bhdr_EM : forall b e1, EM 105 b (cb_bhdr b e1).
Proof.
  intros b e1. unfold cb_bhdr.
  replace 105 with (8 + 8 + 8 + 8 + 8 + 8 + 32 + 1 + 24) by lia.
  eapply EM_trans; [ | apply bsW_EM; lia ]. eapply EM_trans; [ | apply bsW_EM; lia ].
  eapply EM_trans; [ | apply bsPutUInt32_EM ].
  do 5 (eapply EM_trans; [ | apply bsPutUChar_EM ]). apply bsPutUChar_EM.
Qed.

Lemma cb_trailer_numZ : forall is_last b ccrc, 0 <= bw_live b ->
  bw_numZ b <= bw_numZ (cb_trailer is_last b ccrc) /\ 8 * bw_numZ (cb_trailer is_last b ccrc) <= bits b + 87.
Proof.
  intros is_last b ccrc L. unfold cb_trailer. destruct is_last.
  - set (b1 := bsPutUInt32 _ ccrc).
    assert (E1 : EM 80 b b1).
    { subst b1. replace 80 with (8 + 8 + 8 + 8 + 8 + 8 + 32) by lia.
      eapply EM_trans; [ | apply bsPutUInt32_EM ].
      do 5 (eapply EM_trans; [ | apply bsPutUChar_EM ]). apply bsPutUChar_EM. }
    cps_destruct E1 as (A1 & B1 & C1). cps_destruct (finish_facts BS_FUEL b1) as (A2 & B2 & C2).
    split; [lia|]. pose proof (numZ_of_bits_fin (bs_finish BS_FUEL b1) ltac:(apply C2; specialize (C1 L); lia)). lia.
  - split; [lia|]. pose proof (numZ_of_bits b L). lia.
Qed.

Theorem compressBlock_numZ : forall e is_last,
  0 <= e_nblock e -> 0 <= bw_numZ (e_bw e) ->
  (0 <= bw_live (e_bw e) <= 32 \/ e_blockNo e = 1) ->
  (0 < e_nblock e -> gm_facts (cb_sorted e)) ->
  let b' := e_bw (fst (compressBlock e is_last znew)) in
  2 * bw_numZ b' <= 2 * bw_numZ (e_bw e) + 5 * e_nblock e + 40000 /\
  bw_numZ b' <= bw_numZ (e_bw e) + 2 * e_nblock e + e_nblock e / 4 + 20000 /\
  bw_numZ (e_bw e) <= bw_numZ b' + (if 0 <? e_nblock e then bw_numZ (e_bw e) else 0).
Proof.
  intros e is_last NB NZ LV GMF. cbv zeta. rewrite compressBlock_bw.
  destruct (Z.ltb_spec 0 (e_nblock e)) as [POS|ZERO].
  - cbv zeta. specialize (GMF POS).
    cps_destruct (cb_sorted_fields e) as (F1 & F2 & F3 & F4).
    set (e1 := cb_sorted e) in *.
    cps_destruct (cb_hdr_EM e1) as (bS & S1 & S2 & S3 & S4). { rewrite F4, F2. cbn [bw_live]. exact LV. }
    rewrite F4 in S1, S3. cbn [bw_numZ] in S1, S3.
    pose proof (cb_bhdr_EM (cb_hdr e1) e1) as E2.
    set (b1 := cb_bhdr (cb_hdr e1) e1) in *.
    pose proof (generateMTFValues_post (est_set_bw e1 b1) (gm_facts_set_bw e1 b1 GMF)) as GP.
    destruct (gm_bw (est_set_bw e1 b1) znew) as [GB GN].
    set (eg := fst (generateMTFValues (est_set_bw e1 b1) znew)) in *.
    cbn [e_bw e_nblock est_set_bw] in GB, GN. rewrite F1 in GN.
    unfold gm_post in GP. cbv zeta in GP. cbn [e_nblock est_set_bw] in GP. rewrite F1 in GP.
    cps_destruct GP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
    cps_destruct GMF as (_ & _ & NBR & _).  fold e1 in NBR. rewrite F1 in NBR.
    cps_destruct (sendMTF_EM eg znew znew znew znew znew znew znew P1 ltac:(lia)) as (K & KB & E3).
    { intros k Hk. unfold mtfv_at. pose proof (P7 k Hk). lia. }
    rewrite GB in E3.
    set (es := fst (sendMTFValues eg znew znew znew znew znew znew znew)) in *.
    pose proof (EM_trans _ _ _ _ _ S4 (EM_trans _ _ _ _ _ E2 E3)) as ET. cps_destruct ET as (T1 & T2 & T3).
    destruct (cb_trailer_numZ is_last (e_bw es) (e_combinedCRC es) (T3 S2)) as [R1 R2].
    set (q := e_nblock e / 4). assert (4 * q <= e_nblock e /\ e_nblock e < 4 * q + 4) by (subst q; pose proof (Z.div_mod (e_nblock e) 4); pose proof (Z.mod_pos_bound (e_nblock e) 4); lia).
    split; [lia|]. split; [lia|]. lia.
  - cps_destruct (cb_hdr_EM (est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew))) as (bS & S1 & S2 & S3 & S4).
    { cbn [e_bw est_set_bw e_blockNo bw_live]. exact LV. }
    cbn [e_bw est_set_bw bw_numZ] in S1, S3.
    cps_destruct S4 as (T1 & T2 & T3).
    destruct (cb_trailer_numZ is_last (cb_hdr (est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew))) (e_combinedCRC e) (T3 S2)) as [R1 R2].
    split; [lia|]. split; [| lia]. pose proof (Z.div_pos (e_nblock e) 4). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NZM (b b' : bw) : Prop := bw_numZ b <= bw_numZ b'.
Lemma NZM_refl : forall b, NZM b b. Proof. intros; unfold NZM; lia. Qed.
Lemma NZM_trans : forall a b c, NZM a b -> NZM b c -> NZM a c. Proof. unfold NZM; intros; lia. Qed.
Lemma needw_NZM : forall f b, NZM b (bs_needw f b).
Proof. induction f as [|f IH]; intros b; cbn [bs_needw]; [apply NZM_refl|]. destruct (8 <=? bw_live b); [|apply NZM_refl].
  eapply NZM_trans; [| apply IH]. unfold NZM, bw_emit; cbn [bw_numZ]; lia. Qed.
Lemma bsW_NZM : forall b n v, NZM b (bsW b n v).
Proof. intros. unfold bsW. pose proof (needw_NZM BS_FUEL b). unfold NZM in *; cbn [bw_numZ]. exact H. Qed.
Lemma finish_NZM : forall f b, NZM b (bs_finish f b).
Proof. intros. cps_destruct (finish_facts f b) as (_ & B & _). exact B. Qed.
Lemma bsPutUChar_NZM : forall b c, NZM b (bsPutUChar b c). Proof. intros; unfold bsPutUChar; apply bsW_NZM. Qed.
Lemma bsPutUInt32_NZM : forall b u, NZM b (bsPutUInt32 b u).
Proof. intros; unfold bsPutUInt32. do 3 (eapply NZM_trans; [| apply bsW_NZM]). apply bsW_NZM. Qed.

Lemma put_in16_NZM : forall n b in16 i, NZM b (sm_put_in16 n b in16 i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_in16]; [apply NZM_refl|]. eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_inuse_row_NZM : forall n b inUse i j, NZM b (sm_put_inuse_row n b inUse i j).
Proof. induction n as [|n IH]; intros; cbn [sm_put_inuse_row]; [apply NZM_refl|]. eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_inuse_NZM : forall n b in16 inUse i, NZM b (sm_put_inuse n b in16 inUse i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_inuse]; [apply NZM_refl|]. eapply NZM_trans; [| apply IH].
  destruct (negb _); [apply put_inuse_row_NZM| apply NZM_refl]. Qed.
Lemma put_ones_NZM : forall n b, NZM b (sm_put_ones n b).
Proof. induction n as [|n IH]; intros; cbn [sm_put_ones]; [apply NZM_refl|]. eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_sels_NZM : forall n b selMtf i, NZM b (sm_put_sels n b selMtf i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_sels]; [apply NZM_refl|]. eapply NZM_trans; [| apply IH].
  eapply NZM_trans; [apply put_ones_NZM| apply bsW_NZM]. Qed.
Lemma put_up_NZM : forall f b curr tgt, NZM b (fst (sm_put_up f b curr tgt)).
Proof. induction f as [|f IH]; intros; cbn [sm_put_up]; [apply NZM_refl|]. destruct (curr <? tgt); [| apply NZM_refl].
  eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_down_NZM : forall f b curr tgt, NZM b (fst (sm_put_down f b curr tgt)).
Proof. induction f as [|f IH]; intros; cbn [sm_put_down]; [apply NZM_refl|]. destruct (tgt <? curr); [| apply NZM_refl].
  eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_lens_row_NZM : forall n b len t i curr, NZM b (fst (sm_put_lens_row n b len t i curr)).
Proof. induction n as [|n IH]; intros; cbn [sm_put_lens_row]; [apply NZM_refl|].
  pose proof (put_up_NZM 40 b curr (zget len (258 * t + i))) as U. destruct (sm_put_up _ _ _ _) as [b1 c1].
  pose proof (put_down_NZM 40 b1 c1 (zget len (258 * t + i))) as D. destruct (sm_put_down _ _ _ _) as [b2 c2]. cbn [fst] in *.
  eapply NZM_trans; [exact U|]. eapply NZM_trans; [exact D|]. eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_lens_NZM : forall n b len A t, NZM b (sm_put_lens n b len A t).
Proof. induction n as [|n IH]; intros; cbn [sm_put_lens]; [apply NZM_refl|].
  pose proof (put_lens_row_NZM (Z.to_nat A) (bsW b 5 (zget len (258 * t + 0))) len t 0 (zget len (258 * t + 0))) as R.
  destruct (sm_put_lens_row _ _ _ _ _ _) as [b' c']. cbn [fst] in R.
  eapply NZM_trans; [| apply IH]. eapply NZM_trans; [apply bsW_NZM| exact R]. Qed.
Lemma put_syms_NZM : forall n b len code arr1 sel i, NZM b (sm_put_syms n b len code arr1 sel i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_syms]; [apply NZM_refl|]. eapply NZM_trans; [apply bsW_NZM| apply IH]. Qed.
Lemma put_data_NZM : forall fuel b len code arr1 sel nMTF gs c, NZM b (fst (sm_put_data fuel b len code arr1 sel nMTF gs c)).
Proof. induction fuel as [|f IH]; intros; cbn [sm_put_data]; [apply NZM_refl|]. destruct (nMTF <=? gs); [apply NZM_refl|].
  cbv zeta. eapply NZM_trans; [apply put_syms_NZM| apply IH]. Qed.

Theorem sendMTF_numZ_mono : forall e c0 f0 p0 i0 h0 w0 q0,
  bw_numZ (e_bw e) <= bw_numZ (e_bw (fst (sendMTFValues e c0 f0 p0 i0 h0 w0 q0))).
Proof.
  intros. unfold sendMTFValues.
  destruct (sm_selmtf _ _ _ _ _) as [pos selMtf].
  match goal with |- context [sm_put_data ?f ?b ?l ?c ?a ?s ?n ?g ?k] => pose proof (put_data_NZM f b l c a s n g k) as PD; destruct (sm_put_data f b l c a s n g k) as [b5 sc] end.
  cbn [fst e_bw] in *. refine (NZM_trans _ _ _ _ PD).
  eapply NZM_trans; [| apply put_lens_NZM]. eapply NZM_trans; [| apply put_sels_NZM].
  eapply NZM_trans; [| apply bsW_NZM]. eapply NZM_trans; [| apply bsW_NZM].
  eapply NZM_trans; [| apply put_inuse_NZM]. apply put_in16_NZM.
Qed.

Lemma cb_trailer_numZ_mono : forall is_last b ccrc, bw_numZ b <= bw_numZ (cb_trailer is_last b ccrc).
Proof.
  intros. unfold cb_trailer. destruct is_last; [| lia].
  eapply NZM_trans; [| apply finish_NZM]. eapply NZM_trans; [| apply bsPutUInt32_NZM].
  do 5 (eapply NZM_trans; [| apply bsPutUChar_NZM]). apply bsPutUChar_NZM.
Qed.

End ACeilS1.
