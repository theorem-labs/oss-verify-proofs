(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState BzCStream BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import
  BzCLemmas1 BzCLemmasFs BzCPermF BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCSortPost CmpCut CmpLaws.
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
Definition BWZ (b : bw) : Prop := bw_ok b /\ zbok (bw_zb b).

Lemma emit_BWZ : forall b, BWZ b -> 8 <= bw_live b -> BWZ (bw_emit b).
Proof.
  intros b [(A & B & C) Z] L. unfold BWZ, bw_ok, bw_emit. cbn [bw_buff bw_live bw_numZ bw_zb].
  pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)).
  split; [lia|]. apply zbok_zset; [exact Z| apply bw_emit_byte; lia].
Qed.
Lemma needw_BWZ : forall f b, BWZ b -> BWZ (bs_needw f b) /\ (bw_live b < 8 * Z.of_nat f -> bw_live (bs_needw f b) < 8) /\ 0 <= bw_live (bs_needw f b).
Proof.
  induction f as [|f IH]; intros b H.
  - cbn [bs_needw]. split; [exact H|]. destruct H as [(A & B & C) _]. split; [cbn; intros; lia| lia].
  - rewrite bs_needw_S. destruct (Z.leb_spec 8 (bw_live b)) as [L|L].
    + cps_destruct (IH (bw_emit b) (emit_BWZ b H L)) as (P & Q & R). split; [exact P|]. split; [| exact R].
      intros Hf. apply Q. unfold bw_emit. cbn [bw_live]. lia.
    + split; [exact H|]. destruct H as [(A & B & C) _]. split; intros; lia.
Qed.
Lemma bsW_BWZ : forall b n v, BWZ b -> 0 <= n <= 24 -> BWZ (bsW b n v).
Proof.
  intros b n v H Hn. unfold bsW. cps_destruct (needw_BWZ BS_FUEL b H) as ([(A & B & C) Z] & Q & R).
  specialize (Q ltac:(destruct H as [(A0 & B0 & C0) _]; unfold BS_FUEL; cbn; lia)).
  unfold BWZ, bw_ok. cbn [bw_buff bw_live bw_numZ bw_zb]. split; [| exact Z].
  pose proof (Z.mod_pos_bound (Z.shiftl v (32 - bw_live (bs_needw BS_FUEL b) - n)) 4294967296 ltac:(lia)) as M.
  pose proof (lor_w32 _ _ A M). repeat split; lia.
Qed.
Lemma bsPutUChar_BWZ : forall b c, BWZ b -> BWZ (bsPutUChar b c).
Proof. intros. unfold bsPutUChar. apply bsW_BWZ; [assumption| lia]. Qed.
Lemma bsPutUInt32_BWZ : forall b u, BWZ b -> BWZ (bsPutUInt32 b u).
Proof. intros. unfold bsPutUInt32. repeat (apply bsW_BWZ; [| lia]). assumption. Qed.
Lemma bs_finish_zbok : forall f b, BWZ b -> zbok (bw_zb (bs_finish f b)) /\ 0 <= bw_numZ (bs_finish f b) /\ 0 <= bw_buff (bs_finish f b) < 4294967296.
Proof.
  induction f as [|f IH]; intros b H.
  - cbn [bs_finish]. destruct H as [(A & B & C) Z]. split; [exact Z| lia].
  - rewrite bs_finish_S. destruct (Z.ltb_spec 0 (bw_live b)) as [L|L]; [| destruct H as [(A & B & C) Z]; split; [exact Z| lia]].
    destruct (Z.le_gt_cases 8 (bw_live b)) as [L8|L8]; [apply IH; apply emit_BWZ; assumption|].
    (* [comment removed for export] *)
    destruct H as [(A & B & C) Z].
    assert (E1 : zbok (bw_zb (bw_emit b)) /\ 0 <= bw_numZ (bw_emit b) /\ 0 <= bw_buff (bw_emit b) < 4294967296 /\ bw_live (bw_emit b) <= 0).
    { unfold bw_emit. cbn [bw_zb bw_numZ bw_buff bw_live]. pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)).
      split; [apply zbok_zset; [exact Z| apply bw_emit_byte; lia]|]. lia. }
    cps_destruct E1 as (Y1 & Y2 & Y3 & Y4).
    assert (STOP : forall g b', bw_live b' <= 0 -> bs_finish g b' = b') by (intros g b' Hb'; destruct g; [reflexivity|]; rewrite bs_finish_S; destruct (Z.ltb_spec 0 (bw_live b')); [lia| reflexivity]).
    rewrite STOP by exact Y4. split; [exact Y1| lia].
Qed.

Lemma put_in16_BWZ : forall n b in16 i, BWZ b -> BWZ (sm_put_in16 n b in16 i).
Proof. induction n; intros; cbn [sm_put_in16]; [assumption|]. apply IHn. apply bsW_BWZ; [assumption| lia]. Qed.
Lemma put_inuse_row_BWZ : forall n b iu i j, BWZ b -> BWZ (sm_put_inuse_row n b iu i j).
Proof. induction n; intros; cbn [sm_put_inuse_row]; [assumption|]. apply IHn. apply bsW_BWZ; [assumption| lia]. Qed.
Lemma put_inuse_BWZ : forall n b in16 iu i, BWZ b -> BWZ (sm_put_inuse n b in16 iu i).
Proof. induction n; intros; cbn [sm_put_inuse]; [assumption|]. apply IHn. destruct (negb _); [apply put_inuse_row_BWZ|]; assumption. Qed.
Lemma put_ones_BWZ : forall n b, BWZ b -> BWZ (sm_put_ones n b).
Proof. induction n; intros; cbn [sm_put_ones]; [assumption|]. apply IHn. apply bsW_BWZ; [assumption| lia]. Qed.
Lemma put_sels_BWZ : forall n b sm i, BWZ b -> BWZ (sm_put_sels n b sm i).
Proof. induction n; intros; cbn [sm_put_sels]; [assumption|]. apply IHn. apply bsW_BWZ; [apply put_ones_BWZ; assumption| lia]. Qed.
Lemma put_up_BWZ : forall f b c t, BWZ b -> BWZ (fst (sm_put_up f b c t)).
Proof. induction f; intros; cbn [sm_put_up]; [assumption|]. destruct (_ <? _); [apply IHf; apply bsW_BWZ; [assumption| lia]| assumption]. Qed.
Lemma put_down_BWZ : forall f b c t, BWZ b -> BWZ (fst (sm_put_down f b c t)).
Proof. induction f; intros; cbn [sm_put_down]; [assumption|]. destruct (_ <? _); [apply IHf; apply bsW_BWZ; [assumption| lia]| assumption]. Qed.
Lemma put_lens_row_BWZ : forall n b len t i c, BWZ b -> BWZ (fst (sm_put_lens_row n b len t i c)).
Proof.
  induction n; intros; cbn [sm_put_lens_row]; [assumption|].
  pose proof (put_up_BWZ 40 b c (zget len (258 * t + i)) H) as U. destruct (sm_put_up _ _ _ _) as [b1 c1]. cbn [fst] in U.
  pose proof (put_down_BWZ 40 b1 c1 (zget len (258 * t + i)) U) as D. destruct (sm_put_down _ _ _ _) as [b2 c2]. cbn [fst] in D.
  apply IHn. apply bsW_BWZ; [exact D| lia].
Qed.
Lemma put_lens_BWZ : forall n b len A t, BWZ b -> BWZ (sm_put_lens n b len A t).
Proof.
  induction n; intros; cbn [sm_put_lens]; [assumption|].
  pose proof (put_lens_row_BWZ (Z.to_nat A) (bsW b 5 (zget len (258 * t + 0))) len t 0 (zget len (258 * t + 0)) ltac:(apply bsW_BWZ; [assumption| lia])) as R.
  destruct (sm_put_lens_row _ _ _ _ _ _) as [b1 c1]. cbn [fst] in R. apply IHn. exact R.
Qed.
Section Data.
  Variables (A nGroups : Z) (len code arr1 sel : zarr) (nMTF K : Z).
  Hypothesis SEL : forall c, 0 <= c < K -> 0 <= zget sel c < nGroups.
  Hypothesis RO : forall t, 0 <= t < nGroups -> forall v, 0 <= v < A -> 1 <= zget len (258 * t + v) <= 17.
  Hypothesis MV : forall k, 0 <= k < nMTF -> 0 <= mtfv_at arr1 k < A.
  Lemma put_syms_BWZ : forall n b s i, 0 <= s < nGroups -> 0 <= i -> i + Z.of_nat n <= nMTF -> BWZ b -> BWZ (sm_put_syms n b len code arr1 s i).
  Proof.
    induction n; intros b s i Hs Hi Hn H; cbn [sm_put_syms]; [exact H|].
    apply IHn; [exact Hs| lia| lia|]. apply bsW_BWZ; [exact H|]. pose proof (RO s Hs (mtfv_at arr1 i) (MV i ltac:(lia))). lia.
  Qed.
  Lemma put_data_BWZ : forall fuel b c, 1 <= nMTF -> nMTF <= 50 * K -> 0 <= c ->
    BWZ b -> BWZ (fst (sm_put_data fuel b len code arr1 sel nMTF (Z.min (50 * c) nMTF) c)).
  Proof.
    induction fuel as [|fuel IH]; intros b c HM HK Hc H; cbn [sm_put_data]; [exact H|].
    destruct (Z.leb_spec nMTF (Z.min (50 * c) nMTF)) as [L|L]; [exact H|]. cbv zeta.
    set (gs := Z.min (50 * c) nMTF) in *. assert (Egs : gs = 50 * c) by lia.
    change (if nMTF <=? gs + BZ_G_SIZE - 1 then nMTF - 1 else gs + BZ_G_SIZE - 1) with (GE nMTF gs).
    cps_destruct (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    assert (CK : 0 <= c < K) by lia.
    replace (GE nMTF gs + 1) with (Z.min (50 * (c + 1)) nMTF) by lia.
    apply IH; [lia| lia| lia|]. apply put_syms_BWZ; [apply SEL; exact CK| lia| lia| exact H].
  Qed.
End Data.

Theorem sendMTF_BWZ : forall e c0 f0 p0 i0 h0 w0 q0,
  1 <= e_nInUse e <= 256 -> 1 <= e_nMTF e <= 4194304 ->
  (forall k, 0 <= k < e_nMTF e -> 0 <= mtfv_at (e_arr1 e) k < e_nInUse e + 2) ->
  BWZ (e_bw e) -> BWZ (e_bw (fst (sendMTFValues e c0 f0 p0 i0 h0 w0 q0))).
Proof.
  intros e c0 f0 p0 i0 h0 w0 q0 HI HM MV HB.
  set (A := e_nInUse e + 2) in *. set (nMTF := e_nMTF e) in *.
  pose proof (sm_nGroups_range nMTF) as NG. set (nGroups := sm_nGroups nMTF) in *.
  unfold sendMTFValues. fold nMTF. fold A. fold nGroups.
  set (ip := sm_init_tables 8 _ _ _ _).
  pose proof (sm_iters_ITF A nGroups ltac:(lia) ltac:(lia) BZ_N_ITERS (e_arr1 e) nMTF
                (SITS (ip_len ip) (e_rfreq e) (e_len_pack e) (e_selector e) c0 f0 0 h0 w0 q0) ltac:(unfold BZ_N_ITERS; lia) HM MV) as IT.
  set (it := sm_iters BZ_N_ITERS _ _ _ _ _) in *.
  cps_destruct IT as (K & K1 & NS & KB & SEL & RO & _).
  destruct (sm_selmtf _ _ _ _ _) as [pos selMtf].
  set (code := sm_assign _ _ _ _ _). set (in16 := sm_in16 _ _ _ _).
  pose proof (put_data_BWZ A nGroups (it_len it) code (e_arr1 e) (it_sel it) nMTF K SEL RO MV (Z.to_nat (nMTF + 1))) as PD.
  set (b4 := sm_put_lens _ _ _ _ _).
  specialize (PD b4 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  replace (Z.min (50 * 0) nMTF) with 0 in PD by lia.
  destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b5 selCtr]. cbn [fst] in PD. cbn [fst e_bw]. apply PD.
  subst b4. apply put_lens_BWZ. apply put_sels_BWZ. apply bsW_BWZ; [| lia]. apply bsW_BWZ; [| lia].
  apply put_inuse_BWZ. apply put_in16_BWZ. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma compressBlock_fields : forall e is_last,
  let e' := fst (compressBlock e is_last znew) in
  if 0 <? e_nblock e then
    let e1 := cb_sorted e in
    let eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew) in
    let es := fst (sendMTFValues eg znew znew znew znew znew znew znew) in
    e_arr1 e' = e_arr1 es /\ e_ftab e' = e_ftab es /\
    e_arr2 e' = lay_zbits (e_arr2 es) (e_nblock e) (bw_bytes (e_bw e')) /\
    e_bw e' = cb_trailer is_last (e_bw es) (e_combinedCRC es)
  else
    e_arr1 e' = e_arr1 e /\ e_ftab e' = e_ftab e /\
    e_arr2 e' = lay_zbits (e_arr2 e) (e_nblock e) (bw_bytes (e_bw e')) /\
    e_bw e' = cb_trailer is_last (cb_hdr (est_set_bw e (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) (bw_numZ (e_bw e)) znew))) (e_combinedCRC e).
Proof.
  intros e is_last. unfold compressBlock, cb_sorted, cb_e0, cb_trailer, cb_bhdr, cb_hdr. cbv zeta.
  destruct (0 <? e_nblock e).
  - destruct (blockSort _ znew) as [[[e1 fs] ms] bu].
    destruct (generateMTFValues _ znew) as [eg yy].
    destruct (sendMTFValues _ _ _ _ _ _ _ _) as [es sm].
    cbn [fst snd e_bw est_set_bw e_combinedCRC e_arr1 e_arr2 e_ftab]. repeat split; reflexivity.
  - cbn [fst snd e_bw est_set_bw e_combinedCRC e_blockNo e_arr1 e_arr2 e_ftab]. repeat split; reflexivity.
Qed.

Lemma cb_hdr_BWZ : forall e1, (e_blockNo e1 = 1 \/ BWZ (e_bw e1)) -> zbok (bw_zb (e_bw e1)) -> 0 <= bw_numZ (e_bw e1) -> BWZ (cb_hdr e1).
Proof.
  intros e1 H Z N. unfold cb_hdr. destruct (Z.eqb_spec (e_blockNo e1) 1) as [E|NE].
  - repeat apply bsPutUChar_BWZ. split; [unfold bw_ok; cbn; lia| cbn; exact Z].
  - destruct H as [H|H]; [congruence| exact H].
Qed.
Lemma cb_bhdr_BWZ : forall b e1, BWZ b -> BWZ (cb_bhdr b e1).
Proof. intros. unfold cb_bhdr. apply bsW_BWZ; [| lia]. apply bsW_BWZ; [| lia]. apply bsPutUInt32_BWZ. repeat apply bsPutUChar_BWZ. assumption. Qed.
Lemma cb_trailer_false : forall b c, cb_trailer false b c = b. Proof. reflexivity. Qed.
Lemma cb_trailer_zbok : forall il b c, BWZ b -> zbok (bw_zb (cb_trailer il b c)) /\ 0 <= bw_numZ (cb_trailer il b c).
Proof.
  intros il b c H. unfold cb_trailer. destruct il.
  - match goal with |- zbok (bw_zb (bs_finish ?f ?b7)) /\ _ => assert (H7 : BWZ b7) by (apply bsPutUInt32_BWZ; repeat apply bsPutUChar_BWZ; exact H); destruct (bs_finish_zbok f b7 H7) as (A & B & _) end.
    split; assumption.
  - destruct H as [(A & B & C) Z]. split; assumption.
Qed.

Lemma Forall_zarr_to_list : forall (P : Z -> Prop) a lo n, (forall i, P (zget a i)) -> Forall P (zarr_to_list a lo n).
Proof. intros P a lo n H. revert lo. induction n; intros lo; cbn; constructor; [apply H| apply IHn]. Qed.
Lemma lay_zbits_zbok : forall a nb b, zbok a -> zbok (bw_zb b) -> zbok (lay_zbits a nb (bw_bytes b)).
Proof.
  intros a nb b ZA ZB. unfold lay_zbits, bw_bytes. apply zbok_of_list_at; [exact ZA|].
  apply Forall_zarr_to_list. intros i. apply ZB.
Qed.

Lemma set_bw_nblock : forall e b, e_nblock (est_set_bw e b) = e_nblock e. Proof. reflexivity. Qed.
Lemma set_bw_arr2 : forall e b, e_arr2 (est_set_bw e b) = e_arr2 e. Proof. reflexivity. Qed.
Lemma set_bw_ftab : forall e b, e_ftab (est_set_bw e b) = e_ftab e. Proof. reflexivity. Qed.
Lemma set_bw_bw : forall e b, e_bw (est_set_bw e b) = b. Proof. reflexivity. Qed.

Section CB.
  Variables (g : eg) (e : est).
  Hypothesis CE : cb_entry g e.

  (* [comment removed for export] *)
  Lemma cb_emit_facts : 0 < e_nblock e ->
    let e1 := cb_sorted e in
    let eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew) in
    gm_post (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) eg /\ BWZ (e_bw eg) /\
    zbok (e_arr2 e1) /\ (forall i, 0 <= zget (e_ftab e1) i < 4294967296).
  Proof.
    intros NB0. cbv zeta.
    pose proof (cbm_gmf_ok g e CE NB0) as GF.
    pose proof CE as [PRE' CF]. cps_destruct PRE' as (OK & NBR & DEFR & COV & BN1 & NZ1 & ALT). cps_destruct OK as (B1 & B2 & FTR & _).
    cps_destruct (cb_e0_fields e) as (E1 & E2 & E3 & E4 & E5 & E6).
    pose proof (blockSort_out (cb_e0 e)) as BO. rewrite E1, E2, E3, E4, E5, E6 in BO.
    specialize (BO B1 B2 FTR ltac:(bz_params; lia)). cbv zeta in BO. fold (cb_sorted e) in BO.
    cps_destruct BO as (Z1 & Z2 & W3 & _).
    pose proof (generateMTFValues_post _ (gm_facts_set_bw _ (cb_bhdr (cb_hdr (cb_sorted e)) (cb_sorted e)) GF)) as GP.
    split; [exact GP|]. split; [| split; [exact Z2| exact W3]].
    destruct (gm_bw (est_set_bw (cb_sorted e) (cb_bhdr (cb_hdr (cb_sorted e)) (cb_sorted e))) znew) as [EB _]. rewrite EB.
    rewrite set_bw_bw. apply cb_bhdr_BWZ.
    cps_destruct (cb_sorted_fields e) as (SN & SB & SI & SW).
    apply cb_hdr_BWZ; rewrite ?SB, ?SW; cbn [bw_zb bw_numZ]; [| apply zbok_znew| lia].
    destruct ALT as [B1'|(GB & BOK & NZ0)]; [left; exact B1'| right].
    cps_destruct BOK as (A & B & C). split; [unfold bw_ok; cbn; lia| cbn; apply zbok_znew].
  Qed.

  Theorem cbm_bw_ok : bw_ok (e_bw (fst (compressBlock e false znew))).
  Proof.
    pose proof (compressBlock_fields e false) as CFD. cbv zeta in CFD.
    pose proof CE as [PRE' CF]. cps_destruct PRE' as (OK & NBR & DEFR & COV & BN1 & NZ1 & ALT). cps_destruct OK as (B1 & B2 & FTR & _).
    destruct (Z.ltb_spec 0 (e_nblock e)) as [NB0|NB0].
    - cps_destruct CFD as (_ & _ & _ & EB). rewrite EB, cb_trailer_false.
      cps_destruct (cb_emit_facts NB0) as (GP & BWG & _).
      apply sendMTF_BWZ; [| | | exact BWG].
      + destruct GP as (NI & _). exact NI.
      + cps_destruct GP as (_ & NM & _). rewrite set_bw_nblock in NM. destruct (cb_sorted_fields e) as (SN & _). rewrite SN in NM.
        bz_params. lia.
      + cps_destruct GP as (NI & NM & _ & _ & _ & _ & MV & _). intros k Hk. pose proof (MV k Hk). unfold mtfv_at. lia.
    - cps_destruct CFD as (_ & _ & _ & EB). rewrite EB, cb_trailer_false.
      apply cb_hdr_BWZ; unfold est_set_bw; cbn [e_bw e_blockNo bw_zb bw_numZ]; [| apply zbok_znew| destruct ALT as [B1'|(GB & (A & B & C) & NZ0)]; [rewrite NZ1 by exact B1'; lia| lia]].
      destruct ALT as [B1'|(GB & BOK & NZ0)]; [left; exact B1'| right].
      cps_destruct BOK as (A & B & C). split; [unfold bw_ok; cbn; lia| cbn; apply zbok_znew].
  Qed.

  Theorem cbm_arrs_ok : forall b, let e' := fst (compressBlock e b znew) in
    zbok (e_arr1 e') /\ zbok (e_arr2 e') /\ (forall i, 0 <= zget (e_ftab e') i < 4294967296).
  Proof.
    intros il. cbv zeta. pose proof (compressBlock_fields e il) as CFD. cbv zeta in CFD.
    pose proof CE as [PRE' CF]. cps_destruct PRE' as (OK & NBR & DEFR & COV & BN1 & NZ1 & ALT). cps_destruct OK as (B1 & B2 & FTR & _).
    destruct (Z.ltb_spec 0 (e_nblock e)) as [NB0|NB0].
    - cps_destruct CFD as (EA1 & EFT & EA2 & EB).
      cps_destruct (cb_emit_facts NB0) as (GP & BWG & Z2s & FTs).
      set (e1 := cb_sorted e) in *. set (eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew)) in *.
      assert (SZ : BWZ (e_bw (fst (sendMTFValues eg znew znew znew znew znew znew znew)))).
      { apply sendMTF_BWZ; [| | | exact BWG].
        + destruct GP as (NI & _). exact NI.
        + cps_destruct GP as (_ & NM & _). rewrite set_bw_nblock in NM. destruct (cb_sorted_fields e) as (SN & _). fold e1 in SN. rewrite SN in NM.
          bz_params. lia.
        + cps_destruct GP as (NI & NM & _ & _ & _ & _ & MV & _). intros k Hk. pose proof (MV k Hk). unfold mtfv_at. lia. }
      assert (SF : e_arr1 (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_arr1 eg /\
                   e_arr2 (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_arr2 eg /\
                   e_ftab (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = e_ftab eg).
      { unfold sendMTFValues. destruct (sm_selmtf _ _ _ _ _) as [p s]. destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b5 sc]. cbn. repeat split; reflexivity. }
      cps_destruct SF as (SA1 & SA2 & SFT).
      cps_destruct GP as (_ & _ & _ & _ & _ & ZA1 & _ & _ & _ & GA2 & _ & _ & GFT & _).
      rewrite set_bw_arr2 in GA2. rewrite set_bw_ftab in GFT.
      rewrite EA1, EFT, EA2, SA1, SA2, SFT, GA2, GFT.
      split; [exact ZA1|]. split; [| exact FTs].
      apply lay_zbits_zbok; [exact Z2s|]. rewrite EB. apply (proj1 (cb_trailer_zbok il _ _ SZ)).
    - cps_destruct CFD as (EA1 & EFT & EA2 & EB). rewrite EA1, EFT, EA2. split; [exact B1|]. split; [| exact FTR].
      apply lay_zbits_zbok; [exact B2|]. rewrite EB.
      match goal with |- zbok (bw_zb (cb_trailer _ ?h _)) => assert (HH : BWZ h) end.
      { apply cb_hdr_BWZ; unfold est_set_bw; cbn [e_bw e_blockNo bw_zb bw_numZ]; [| apply zbok_znew| destruct ALT as [B1'|(GB & (A & B & C) & NZ0)]; [rewrite NZ1 by exact B1'; lia| lia]].
        destruct ALT as [B1'|(GB & BOK & NZ0)]; [left; exact B1'| right].
        cps_destruct BOK as (A & B & C). split; [unfold bw_ok; cbn; lia| cbn; apply zbok_znew]. }
      apply (proj1 (cb_trailer_zbok il _ _ HH)).
  Qed.
End CB.

(* [comment removed for export] *)
Theorem cbm_ok : cbm.
Proof.
  constructor.
  - exact cbm_gmf_ok.
  - intros g e b CE. exact (cbm_arrs_ok g e CE b).
  - intros g e CE. exact (cbm_bw_ok g e CE).
Qed.

End ACeilS1.
