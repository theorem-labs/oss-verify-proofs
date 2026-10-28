(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut
  CmpCutMtf CmpCutSM BzCNumZ CmpLaws. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortPost BzCEmit.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition est_set_arr2 (e : est) (a : zarr) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) a (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Lemma est_set_arr2_twice : forall x a a', est_set_arr2 (est_set_arr2 x a) a' = est_set_arr2 x a'. Proof. reflexivity. Qed.
Lemma est_set_bw_set_arr2 : forall x a b, est_set_bw (est_set_arr2 x a) b = est_set_arr2 (est_set_bw x b) a. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition agree_below (n : Z) (a a' : zarr) : Prop := forall j, 0 <= j < n -> zget a' j = zget a j.
Lemma agree_below_of_list_at : forall n a l, agree_below n a (zarr_of_list_at a n l).
Proof. intros n a l j Hj. apply zget_of_list_at_below. lia. Qed.

(* [comment removed for export] *)
Definition cb_glue_gm : Prop :=
  forall e a', gm_facts e -> agree_below (e_nblock e) (e_arr2 e) a' ->
  fst (generateMTFValues (est_set_arr2 e a') znew) = est_set_arr2 (fst (generateMTFValues e znew)) a'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gm_facts_set_arr2 : forall e a', gm_facts e -> zbok a' -> agree_below (e_nblock e) (e_arr2 e) a' -> gm_facts (est_set_arr2 e a').
Proof.
  (intros e a'; cps_intros (B1 & B2 & NB & DI & IU & F5 & M1); intros BOK AG). unfold gm_facts.
  cbn [e_arr1 e_arr2 e_nblock e_inUse est_set_arr2].
  split; [exact B1|]. split; [exact BOK|]. split; [exact NB|]. split; [exact DI|]. split; [exact IU|]. split; [| exact M1].
  intros j Hj. unfold rd8. rewrite (AG j Hj). apply F5. exact Hj.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cbE0 (e : est) : est := cb_e0 e.
Definition cbE1 (e : est) : est := cb_sorted e.
Definition cbBS (e : est) : bw := cb_hdr (cbE1 e).
Definition cbBH (e : est) : bw := cb_bhdr (cbBS e) (cbE1 e).
(* [comment removed for export] *)
Definition cbZBL (e : est) (b : bw) : zarr := zbl (e_arr2 (cbE1 e)) (e_nblock e) b.
Definition cbEU5 (e : est) : est := est_set_arr2 (est_set_bw (cbE1 e) (cbBH e)) (cbZBL e (cbBH e)).
Definition cbEG (e : est) : est := gm_e (cbEU5 e).
Definition cbED (e : est) : est := est_D (cbEG e) znew znew znew znew znew znew znew.
Definition cbBT (e : est) (il : bool) : bw := cb_trailer il (e_bw (cbED e)) (e_combinedCRC (cbED e)).
Definition cbEF (e : est) (il : bool) : est := est_set_arr2 (est_set_bw (cbED e) (cbBT e il)) (cbZBL e (cbBT e il)).
(* [comment removed for export] *)
Definition cbZ0 (e : est) : est := est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew).
Definition cbZS (e : est) : bw := cb_hdr (cbZ0 e).
Definition cbZT (e : est) (il : bool) : bw := cb_trailer il (cbZS e) (e_combinedCRC e).
Definition cbZF (e : est) (il : bool) : est := est_set_arr2 (est_set_bw e (cbZT e il)) (zbl (e_arr2 e) (e_nblock e) (cbZT e il)).

(* [comment removed for export] *)
Definition bz_hdr4 (b : bw) : bw :=
  bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar b BZ_HDR_B) BZ_HDR_Z) BZ_HDR_h) (BZ_HDR_0 + BLOCKSIZE100K).
(* [comment removed for export] *)
Definition bz_magic6 (b : bw) : bw := bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar b 49) 65) 89) 38) 83) 89.
Definition bz_fin6 (b : bw) : bw := bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar b 23) 114) 69) 56) 80) 144.

Lemma cb_hdr_cases : forall e1,
  (e_blockNo e1 = 1 -> cb_hdr e1 = bz_hdr4 (BW 0 0 (bw_numZ (e_bw e1)) (bw_zb (e_bw e1)))) /\
  (e_blockNo e1 <> 1 -> cb_hdr e1 = e_bw e1).
Proof.
  intros e1. unfold cb_hdr, bz_hdr4. split; intros H.
  - rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
Qed.
Lemma cb_bhdr_eq : forall b e1, cb_bhdr b e1 = bsW (bsW (bsPutUInt32 (bz_magic6 b) (e_blockCRC e1)) 1 0) 24 (e_origPtr e1).
Proof. reflexivity. Qed.
Lemma cb_trailer_true : forall b c, cb_trailer true b c = bs_finish BS_FUEL (bsPutUInt32 (bz_fin6 b) c).
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zget_of_list_at_above : forall l a lo j, lo + Z.of_nat (length l) <= j -> zget (zarr_of_list_at a lo l) j = zget a j.
Proof.
  induction l as [|x l IH]; intros a lo j Hj; cbn in Hj |- *; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.
Lemma zget_of_list_at_in : forall l a lo j, lo <= j < lo + Z.of_nat (length l) ->
  zget (zarr_of_list_at a lo l) j = nth (Z.to_nat (j - lo)) l 0.
Proof.
  intros l a lo j Hj. replace j with (lo + Z.of_nat (Z.to_nat (j - lo))) at 1 by lia.
  apply zget_of_list_at. lia.
Qed.
(* [comment removed for export] *)
Lemma zget_of_list_at_absorb : forall a lo l0 l j, (length l0 <= length l)%nat ->
  zget (zarr_of_list_at (zarr_of_list_at a lo l0) lo l) j = zget (zarr_of_list_at a lo l) j.
Proof.
  intros a lo l0 l j Hl.
  destruct (Z_lt_le_dec j lo) as [B|B].
  { rewrite !zget_of_list_at_below by lia. reflexivity. }
  destruct (Z_lt_le_dec j (lo + Z.of_nat (length l))) as [I|A].
  { rewrite !zget_of_list_at_in by lia. reflexivity. }
  rewrite !zget_of_list_at_above by lia. reflexivity.
Qed.
Lemma zbl_absorb_get : forall a n b0 b j, 0 <= bw_numZ b0 <= bw_numZ b -> zget (zbl (zbl a n b0) n b) j = zget (zbl a n b) j.
Proof.
  intros a n b0 b j H. unfold zbl. apply zget_of_list_at_absorb. rewrite !bw_bytes_length. lia.
Qed.
Lemma zb8_zbl_absorb : forall a n b0 b N, 0 <= bw_numZ b0 <= bw_numZ b -> zb8 (zbl (zbl a n b0) n b) N = zb8 (zbl a n b) N.
Proof. intros a n b0 b N H. apply zb8_ext. intros i _. apply zbl_absorb_get. exact H. Qed.
Lemma agree_below_zbl : forall a n b, agree_below n a (zbl a n b).
Proof. intros a n b. unfold zbl. apply agree_below_of_list_at. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bz_hdr4_ok : forall b, bw_ok b -> bw_ok (bz_hdr4 b) /\ bw_numZ b <= bw_numZ (bz_hdr4 b) /\ bits (bz_hdr4 b) = bits b + 32.
Proof.
  intros b OK. unfold bz_hdr4, bsPutUChar. unfold BZ_HDR_B, BZ_HDR_Z, BZ_HDR_h, BZ_HDR_0.
  cps_destruct (bsW8_ok b 66 OK ltac:(lia)) as (O1 & N1 & _). cps_destruct (bsW8_ok _ 90 O1 ltac:(lia)) as (O2 & N2 & _).
  cps_destruct (bsW8_ok _ 104 O2 ltac:(lia)) as (O3 & N3 & _). cps_destruct (bsW8_ok _ (48 + BLOCKSIZE100K) O3 ltac:(bz_params; lia)) as (O4 & N4 & _).
  split; [exact O4|]. split; [lia|]. rewrite !bsW_bits. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma est_D_fields : forall x c0 f0 p0 i0 h0 w0 q0, let d := est_D x c0 f0 p0 i0 h0 w0 q0 in
  e_mode d = e_mode x /\ e_state d = e_state x /\ e_avail_in_expect d = e_avail_in_expect x /\
  e_arr1 d = e_arr1 x /\ e_arr2 d = e_arr2 x /\ e_ftab d = e_ftab x /\ e_origPtr d = e_origPtr x /\
  e_state_in_ch d = e_state_in_ch x /\ e_state_in_len d = e_state_in_len x /\ e_nblock d = e_nblock x /\
  e_state_out_pos d = e_state_out_pos x /\ e_nInUse d = e_nInUse x /\ e_inUse d = e_inUse x /\ e_unseqToSeq d = e_unseqToSeq x /\
  e_blockCRC d = e_blockCRC x /\ e_combinedCRC d = e_combinedCRC x /\ e_blockNo d = e_blockNo x /\ e_nMTF d = e_nMTF x /\ e_mtfFreq d = e_mtfFreq x.
Proof. intros. cbv zeta. repeat split; reflexivity. Qed.
Lemma est_D_set_arr2 : forall x a c0 f0 p0 i0 h0 w0 q0,
  est_D (est_set_arr2 x a) c0 f0 p0 i0 h0 w0 q0 = est_set_arr2 (est_D x c0 f0 p0 i0 h0 w0 q0) a.
Proof.
  intros. unfold est_D, smD_bd, smD_b4, smD_b3, smD_b2, smD_b1, smD_b0, smD_in16, smC_code, smC_pm, smC_pos0, smB_nsel, smB_it,
    smA_ip, smA_ng, smA_len, sm_nmtf, sm_alpha, est_set_arr2.
  cbn [e_nInUse e_nMTF e_len e_mtfFreq e_arr1 e_rfreq e_len_pack e_selector e_selectorMtf e_code e_inUse e_bw e_mode e_state e_avail_in_expect
       e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_unseqToSeq e_blockCRC e_combinedCRC e_blockNo].
  reflexivity.
Qed.
Lemma est_D_is_sendMTF : forall x c0 f0 p0 i0 h0 w0 q0,
  est_D x c0 f0 p0 i0 h0 w0 q0 = fst (sendMTFValues x c0 f0 p0 i0 h0 w0 q0).
Proof. intros. symmetry. apply sendMTF_phases. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Spine.
  Variables (g : eg) (e : est).
  Hypothesis CE : cb_entry g e.
  Hypothesis POS : 0 < e_nblock e.

  (* [comment removed for export] *)
  Lemma cb_entry_facts :
    est_ok e /\ 0 <= e_nblock e <= NBLOCKMAX + 9 /\ zdefr (e_inUse e) 0 256 /\ inuse01 (e_inUse e) /\
    e_state_out_pos e = 0 /\ bw_numZ (e_bw e) = 0 /\ 1 <= e_blockNo e /\
    (e_blockNo e = 1 \/ (g_bs g = true /\ bw_ok (e_bw e))).
  Proof.
    destruct CE as [(OK & NBR & DEFR & COV & B1 & NZ1 & ALT) (POS0 & NZ & RL & IU)].
    split; [exact OK|]. split; [exact NBR|]. split; [exact DEFR|]. split; [exact IU|]. split; [exact POS0|]. split; [exact NZ|]. split; [exact B1|].
    destruct ALT as [A|(A & B & C)]; [left; exact A| right; split; assumption].
  Qed.

  Lemma cbE0_eq : cbE0 e =
    EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) (crc_final (e_blockCRC e))
        (Z.lxor (Z.lor ((Z.shiftl (e_combinedCRC e) 1) mod 4294967296) (Z.shiftr (e_combinedCRC e) 31)) (crc_final (e_blockCRC e)))
        (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
  Proof. reflexivity. Qed.
  Lemma cbE0_crcs : 0 <= e_blockCRC (cbE0 e) < 4294967296 /\ 0 <= e_combinedCRC (cbE0 e) < 4294967296.
  Proof.
    destruct cb_entry_facts as (OK & _). cps_pose OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & _).
    split; [| exact (combinedCRC_e0_range e BC CC)]. unfold cbE0, cb_e0. cbv zeta. cbn [e_blockCRC]. apply crc_final_range. exact BC.
  Qed.
  Lemma cbE0_ok : est_ok (cbE0 e) /\ 1 <= e_nblock (cbE0 e) <= NBLOCKMAX + 19.
  Proof.
    cps_destruct cb_entry_facts as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT). destruct cbE0_crcs as [BC' CC'].
    cps_pose OK as (Z1 & Z2 & FTR & NB2 & NZ0 & OP0 & MD & ST & CH & LN & BC & CC & BN).
    revert BC' CC'. rewrite cbE0_eq. unfold est_ok.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_inUse
         e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack bw_numZ].
    intros BC' CC'.
    split; [| lia]. split; [exact Z1|]. split; [exact Z2|]. split; [exact FTR|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact MD|]. split; [exact ST|]. split; [exact CH|]. split; [exact LN|]. split; [exact BC'|]. split; [exact CC'|]. exact BN.
  Qed.

  (* [comment removed for export] *)
  Lemma cbE1_shape : exists arr1 arr2 ftab op,
    cbE1 e = EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 arr2 ftab op
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) (e_blockCRC (cbE0 e)) (e_combinedCRC (cbE0 e))
        (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e) /\
    zbok arr1 /\ zbok arr2 /\ (forall i, 0 <= zget ftab i < 4294967296) /\ 0 <= op < e_nblock e.
  Proof.
    cps_destruct cb_entry_facts as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
    cps_pose OK as (Z1 & Z2 & FTR & _).
    pose proof (blockSort_out (cb_e0 e)) as BO. cbv zeta in BO.
    cps_destruct (cb_e0_fields e) as (E1 & E2 & E3 & E4 & E5 & E6). rewrite E1, E2, E3, E4 in BO.
    specialize (BO Z1 Z2 FTR ltac:(bz_params; lia)).
    unfold cbE1, cb_sorted. cps_destruct (blockSort_shape (cb_e0 e) znew) as (a1 & a2 & ft & op & E). rewrite E in BO |- *.
    cbn [e_arr1 e_arr2 e_ftab e_origPtr e_nblock e_inUse e_nInUse] in BO.
    cps_destruct BO as (Y1 & Y2 & Y3 & _ & _ & OP & _).
    exists a1, a2, ft, op. split; [| split; [exact Y1| split; [exact Y2| split; [exact Y3| exact OP]]]].
    unfold cbE0, cb_e0. cbv zeta.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_inUse
         e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack bw_buff bw_live].
    reflexivity.
  Qed.
  Lemma cbE1_gm_facts : gm_facts (cbE1 e).
  Proof. exact (cbm_gmf_ok g e CE POS). Qed.

  (* [comment removed for export] *)
  Lemma cbBS_facts : bw_ok (cbBS e) /\ 0 <= bw_numZ (cbBS e) <= 4 /\ bits (cbBS e) <= 32 /\
    (e_blockNo e = 1 -> cbBS e = bz_hdr4 (BW 0 0 0 znew)) /\
    (e_blockNo e <> 1 -> cbBS e = BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew /\ g_bs g = true /\ bw_ok (e_bw e)) /\
    BWZ (cbBS e).
  Proof.
    cps_destruct cb_entry_facts as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
    cps_destruct cbE1_shape as (a1 & a2 & ft & op & E & _). unfold cbBS. destruct (cb_hdr_cases (cbE1 e)) as [C1 C2].
    assert (BWS : BWZ (cb_hdr (cbE1 e))).
    { apply cb_hdr_BWZ; rewrite E; cbn [e_blockNo e_bw bw_zb bw_numZ]; [| apply zbok_znew| lia].
      destruct ALT as [A|(GB & BOK)]; [left; exact A| right]. split; [apply bw_ok_reset; exact BOK| cbn [bw_zb]; apply zbok_znew]. }
    rewrite E in C1, C2, BWS |- *. cbn [e_blockNo e_bw bw_numZ bw_zb] in C1, C2, BWS |- *.
    destruct (Z.eq_dec (e_blockNo e) 1) as [Q|Q].
    - rewrite (C1 Q) in BWS |- *. cps_destruct (bz_hdr4_ok (BW 0 0 0 znew) ltac:(unfold bw_ok; cbn; lia)) as (O & N & B).
      cbn [bw_numZ] in N. unfold bits in B |- *. cbn [bw_numZ bw_live] in B. cps_destruct O as (O1 & O2 & O3).
      split; [unfold bw_ok; repeat split; lia|]. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|]. split; [intros X; exfalso; lia|]. exact BWS.
    - rewrite (C2 Q) in BWS |- *. destruct ALT as [A|(GB & BOK)]; [exfalso; lia|]. cps_destruct BOK as (O1 & O2 & O3).
      unfold bits. cbn [bw_buff bw_live bw_numZ].
      split; [unfold bw_ok; cbn [bw_buff bw_live bw_numZ]; lia|]. split; [lia|]. split; [lia|]. split; [intros X; exfalso; lia|].
      split; [| exact BWS]. intros _. split; [reflexivity|]. split; [exact GB|]. unfold bw_ok; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cbBH_facts : bw_ok (cbBH e) /\ bw_numZ (cbBS e) <= bw_numZ (cbBH e) <= 18 /\ bits (cbBH e) = bits (cbBS e) + 105 /\ 0 <= bw_live (cbBH e) /\
    0 <= e_blockCRC (cbE1 e) < 4294967296 /\ 0 <= e_origPtr (cbE1 e) < 16777216 /\ BWZ (cbBH e).
  Proof.
    cps_destruct cbBS_facts as (OKS & NS & BS & _ & _ & BWS). destruct cbE0_crcs as [BC CC]. cps_destruct cb_entry_facts as (_ & NBR & _).
    cps_destruct cbE1_shape as (a1 & a2 & ft & op & E & _ & _ & _ & OP).
    unfold cbBH. pose proof (bhdr_ok (cbBS e) (cbE1 e) OKS) as OKH. pose proof (bits_bhdr (cbBS e) (cbE1 e)) as BH.
    cps_pose (cb_bhdr_EM (cbBS e) (cbE1 e)) as (_ & NZM & _).
    cps_pose OKH as (O1 & O2 & O3). pose proof (numZ_of_bits (cb_bhdr (cbBS e) (cbE1 e)) ltac:(lia)) as NB.
    split; [exact OKH|]. split; [lia|]. split; [exact BH|]. split; [lia|].
    rewrite E at 1 2 3 4. cbn [e_blockCRC e_origPtr]. split; [exact BC|]. split; [bz_params; lia|].
    apply cb_bhdr_BWZ. exact BWS.
  Qed.

  (* [comment removed for export] *)
  Lemma cbEU5_facts : gm_facts (cbEU5 e) /\ e_nblock (cbEU5 e) = e_nblock e /\ e_bw (cbEU5 e) = cbBH e /\
    e_arr2 (cbEU5 e) = cbZBL e (cbBH e) /\ e_arr1 (cbEU5 e) = e_arr1 (cbE1 e) /\ e_ftab (cbEU5 e) = e_ftab (cbE1 e) /\
    e_inUse (cbEU5 e) = e_inUse e /\ e_nInUse (cbEU5 e) = e_nInUse e /\ e_blockNo (cbEU5 e) = e_blockNo e /\
    zbok (cbZBL e (cbBH e)).
  Proof.
    cps_destruct cbE1_shape as (a1 & a2 & ft & op & E & Y1 & Y2 & Y3 & OP). pose proof cbE1_gm_facts as GF. cps_destruct cbBH_facts as (OKH & _ & _ & _ & _ & _ & BWH).
    assert (ZB : zbok (cbZBL e (cbBH e))).
    { unfold cbZBL. apply zbok_zbl; [rewrite E; cbn [e_arr2]; exact Y2| cps_destruct OKH as (?&?&?); lia|].
      intros i Hi. apply (proj2 BWH). }
    unfold cbEU5. split.
    { apply gm_facts_set_arr2; [apply gm_facts_set_bw; exact GF| exact ZB|].
      cbn [e_nblock e_arr2 est_set_bw]. unfold cbZBL. rewrite E at 2 3. cbn [e_nblock e_arr2]. rewrite E. cbn [e_arr2]. apply agree_below_zbl. }
    rewrite E. unfold est_set_arr2, est_set_bw. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock
      e_state_out_pos e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact ZB.
  Qed.

  (* [comment removed for export] *)
  Lemma cbEG_facts : gm_post (cbEU5 e) (cbEG e).
  Proof. destruct cbEU5_facts as (GF5 & _). unfold cbEG, gm_e. apply generateMTFValues_post. exact GF5. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cbED_fields :
    e_nblock (cbED e) = e_nblock e /\ e_arr2 (cbED e) = cbZBL e (cbBH e) /\ e_arr1 (cbED e) = e_arr1 (cbEG e) /\ e_ftab (cbED e) = e_ftab (cbE1 e) /\
    e_inUse (cbED e) = e_inUse e /\ e_blockNo (cbED e) = e_blockNo e /\ e_nInUse (cbED e) = e_nInUse (cbEG e) /\ e_nMTF (cbED e) = e_nMTF (cbEG e) /\
    e_blockCRC (cbED e) = e_blockCRC (cbE0 e) /\ e_combinedCRC (cbED e) = e_combinedCRC (cbE0 e) /\
    0 <= e_combinedCRC (cbED e) < 4294967296.
  Proof.
    cps_destruct cbE1_shape as (a1 & a2 & ft & op & E & Y1 & Y2 & Y3 & OP). destruct cbE0_crcs as [BC CC].
    cps_destruct cbEU5_facts as (GF5 & N5 & B5 & A5 & A15 & F5 & I5 & NI5 & BN5 & ZB). pose proof cbEG_facts as GP.
    unfold gm_post in GP. cbv zeta in GP.
    cps_destruct GP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & _).
    pose proof (est_D_fields (cbEG e) znew znew znew znew znew znew znew) as DF. cbv zeta in DF.
    cps_destruct DF as (_ & _ & _ & D4 & D5 & D6 & _ & _ & _ & D10 & _ & D12 & D13 & _ & D15 & D16 & D17 & D18 & _).
    assert (CR : e_blockCRC (cbEU5 e) = e_blockCRC (cbE0 e) /\ e_combinedCRC (cbEU5 e) = e_combinedCRC (cbE0 e)).
    { unfold cbEU5. rewrite E. split; reflexivity. }
    destruct CR as [CR1 CR2]. unfold cbED.
    split; [rewrite D10, Q1; exact N5|]. split; [rewrite D5, Q2; exact A5|]. split; [exact D4|]. split; [rewrite D6, Q5; exact F5|].
    split; [rewrite D13, Q3; exact I5|]. split; [rewrite D17, Q7; exact BN5|]. split; [exact D12|]. split; [exact D18|].
    split; [rewrite D15, Q8; exact CR1|]. split; [rewrite D16, Q9; exact CR2|]. rewrite D16, Q9, CR2. exact CC.
  Qed.

  (* [comment removed for export] *)
  Lemma cbED_room :
    bw_numZ (cbBH e) <= bw_numZ (e_bw (cbED e)) /\ 0 <= bw_live (e_bw (cbED e)) /\
    e_nblock e + bw_numZ (e_bw (cbED e)) + 64 <= ARR2_SIZE.
  Proof.
    cps_destruct cb_entry_facts as (OK & NBR & DEFR & IU & POS0 & NZ & B1 & ALT).
    cps_destruct cbBS_facts as (OKS & NS & BS & _). cps_destruct cbBH_facts as (OKH & NH & BH & LH & _).
    cps_destruct cbEU5_facts as (GF5 & N5 & B5 & _). pose proof cbEG_facts as GP.
    unfold gm_post in GP. cbv zeta in GP.
    cps_destruct GP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & Q1 & Q2 & Q3 & Q4 & _).
    rewrite N5 in P2. rewrite B5 in Q4.
    cps_destruct (sendMTF_EM (cbEG e) znew znew znew znew znew znew znew P1 ltac:(bz_params; lia)) as (K & KB & EMD).
    { intros k Hk. unfold mtfv_at. pose proof (P7 k Hk). lia. }
    rewrite Q4 in EMD. rewrite <- est_D_is_sendMTF in EMD. unfold cbED.
    (* [comment removed for export] *)
    generalize EMD NH BH LH BS NS NBR P2 KB. clear.
    generalize (e_bw (est_D (cbEG e) znew znew znew znew znew znew znew)) as bD. generalize (cbBH e) as bH. generalize (cbBS e) as bS.
    generalize (e_nMTF (cbEG e)) as nM. generalize (e_nblock e) as nb.
    intros nb nM bS bH bD EMD NH BH LH BS NS NBR P2 KB.
    cps_destruct EMD as (T1 & T2 & T3). specialize (T3 LH). unfold bits in *. lia.
  Qed.
End Spine.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cb_final_eq : cb_glue_gm -> forall g e il, cb_entry g e -> 0 < e_nblock e -> fst (compressBlock e il znew) = cbEF e il.
Proof.
  intros GL g e il CE POS.
  pose proof (cbm_gmf_ok g e CE POS) as GF. unfold cb_sorted in GF.
  cps_destruct (cbE1_shape g e CE POS) as (a1 & a2 & ft & op & E1 & _ & Y2 & _). unfold cbE1, cb_sorted in E1.
  cps_pose (cbBH_facts g e CE POS) as (OKH & _ & _ & _ & _ & _ & BWH).
  unfold cbEF, cbBT, cbED, cbEG, cbEU5, cbZBL, cbBH, cbBS, cbE1, cb_sorted, gm_e in *.
  unfold compressBlock. cbv zeta.
  replace (0 <? e_nblock e) with true by (symmetry; apply Z.ltb_lt; exact POS).
  replace (blockSort _ znew) with (blockSort (cb_e0 e) znew) by reflexivity.
  destruct (blockSort (cb_e0 e) znew) as [[[e1 fs] ms] bu]. cbn [fst] in GF, E1, OKH, BWH |- *.
  change (bsW (bsW (bsPutUInt32 (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar
           (if e_blockNo e1 =? 1 then bsPutUChar (bsPutUChar (bsPutUChar (bsPutUChar (BW 0 0 (bw_numZ (e_bw e1)) (bw_zb (e_bw e1))) BZ_HDR_B) BZ_HDR_Z) BZ_HDR_h) (BZ_HDR_0 + BLOCKSIZE100K) else e_bw e1)
           49) 65) 89) 38) 83) 89) (e_blockCRC e1)) 1 0) 24 (e_origPtr e1))
    with (cb_bhdr (cb_hdr e1) e1).
  set (BH := cb_bhdr (cb_hdr e1) e1) in *. set (L := zbl (e_arr2 e1) (e_nblock e) BH) in *.
  assert (AG : agree_below (e_nblock (est_set_bw e1 BH)) (e_arr2 (est_set_bw e1 BH)) L).
  { cbn [e_nblock e_arr2 est_set_bw]. subst L. rewrite E1. cbn [e_nblock e_arr2]. apply agree_below_zbl. }
  assert (ZB : zbok L).
  { subst L. apply zbok_zbl; [rewrite E1; cbn [e_arr2]; exact Y2| cps_destruct OKH as (?&?&?); lia|]. intros i Hi. apply (proj2 BWH). }
  pose proof (GL (est_set_bw e1 BH) L (gm_facts_set_bw _ _ GF) AG) as GQ.
  cps_destruct (gm_shape (est_set_bw e1 BH) znew) as (ga1 & gni & gus & gwr & gmf & GM).
  (* [comment removed for export] *)
  destruct (generateMTFValues (est_set_bw e1 BH) znew) as [eg yy] eqn:GE. cbn [fst snd] in GQ, GM.
  destruct (sendMTFValues eg znew znew znew znew znew znew znew) as [es sm] eqn:SM. cbn [fst snd].
  (* [comment removed for export] *)
  change (fst (generateMTFValues (est_set_arr2 (est_set_bw e1 BH) L) znew)) with (fst (generateMTFValues (est_set_arr2 (est_set_bw e1 BH) L) znew)).
  rewrite GQ. rewrite est_D_set_arr2, est_D_is_sendMTF, SM. cbn [fst snd].
  assert (A2 : e_arr2 es = e_arr2 e1).
  { replace es with (fst (sendMTFValues eg znew znew znew znew znew znew znew)) by (rewrite SM; reflexivity).
    rewrite <- est_D_is_sendMTF. pose proof (est_D_fields eg znew znew znew znew znew znew znew) as DF. cbv zeta in DF.
    cps_destruct DF as (_ & _ & _ & _ & D5 & _). rewrite D5, GM. reflexivity. }
  rewrite est_set_bw_set_arr2, est_set_arr2_twice.
  unfold est_set_arr2, est_set_bw, cb_trailer, zbl, lay_zbits.
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_inUse
       e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
  rewrite A2. destruct il; reflexivity.
Qed.

Theorem cb_final_eq0 : forall e il, e_nblock e <= 0 -> fst (compressBlock e il znew) = cbZF e il.
Proof.
  intros e il ZE. unfold cbZF, cbZT, cbZS, cbZ0, compressBlock. cbv zeta.
  replace (0 <? e_nblock e) with false by (symmetry; apply Z.ltb_ge; exact ZE).
  unfold est_set_arr2, est_set_bw, cb_trailer, cb_hdr, zbl, lay_zbits.
  cbn [fst snd e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse e_inUse
       e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack].
  destruct il; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cbZ_facts : forall g e, cb_entry g e -> e_nblock e <= 0 ->
  bw_ok (cbZS e) /\ 0 <= bw_numZ (cbZS e) <= 4 /\ bits (cbZS e) <= 32 /\
  (e_blockNo e = 1 -> cbZS e = bz_hdr4 (BW 0 0 0 znew)) /\
  (e_blockNo e <> 1 -> cbZS e = e_bw (cbZ0 e) /\ g_bs g = true /\ bw_ok (e_bw e)) /\
  e_bw (cbZ0 e) = BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew /\ BWZ (cbZS e) /\
  0 <= e_combinedCRC e < 4294967296 /\ e_nblock e = 0.
Proof.
  intros g e CE ZE.
  destruct CE as [(OK & NBR & DEFR & COV & B1 & NZ1 & ALT) (POS0 & NZ & RL & IU)].
  cps_pose OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & _).
  assert (EB : e_bw (cbZ0 e) = BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) by (unfold cbZ0, est_set_bw; cbn [e_bw]; rewrite NZ; reflexivity).
  assert (EN : e_blockNo (cbZ0 e) = e_blockNo e) by reflexivity.
  assert (BWS : BWZ (cbZS e)).
  { unfold cbZS. apply cb_hdr_BWZ; rewrite ?EB, ?EN; cbn [bw_zb bw_numZ]; [| apply zbok_znew| lia].
    destruct ALT as [A|(GB & BOK & _)]; [left; exact A| right]. split; [apply bw_ok_reset; exact BOK| cbn [bw_zb]; apply zbok_znew]. }
  unfold cbZS in BWS |- *. destruct (cb_hdr_cases (cbZ0 e)) as [C1 C2]. rewrite EN, EB in C1, C2. cbn [bw_numZ bw_zb] in C1.
  destruct (Z.eq_dec (e_blockNo e) 1) as [Q|Q].
  - rewrite (C1 Q) in BWS |- *. cps_destruct (bz_hdr4_ok (BW 0 0 0 znew) ltac:(unfold bw_ok; cbn; lia)) as (O & N & B).
    cbn [bw_numZ] in N. unfold bits in B |- *. cbn [bw_numZ bw_live] in B. cps_destruct O as (O1 & O2 & O3).
    split; [unfold bw_ok; repeat split; lia|]. split; [lia|]. split; [lia|]. split; [intros _; reflexivity|]. split; [intros X; exfalso; lia|].
    split; [exact EB|]. split; [exact BWS|]. split; [exact CC| lia].
  - rewrite (C2 Q) in BWS |- *. rewrite ?EB in BWS. rewrite ?EB. destruct ALT as [A|(GB & BOK & _)]; [exfalso; lia|]. cps_destruct BOK as (O1 & O2 & O3).
    unfold bits. cbn [bw_buff bw_live bw_numZ].
    split; [unfold bw_ok; cbn [bw_buff bw_live bw_numZ]; lia|]. split; [lia|]. split; [lia|]. split; [intros X; exfalso; lia|].
    split; [intros _; split; [reflexivity| split; [exact GB| unfold bw_ok; lia]]|].
    split; [reflexivity|]. split; [exact BWS|]. split; [exact CC| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
