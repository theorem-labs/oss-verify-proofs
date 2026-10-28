(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmas1 BzCLemmasFs BzCRebuildF BzCPermF BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortPost. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCEmit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpSess.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory BzR3aFs BzR2D1 BzR2D. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzR2E BzR2Eb.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5a.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS BzR4a BzR4d.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.BzR5cX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4d OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.BzR4e OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR1a BzR1e. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRT1 BzRT2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRTB1.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section BZPS. Context {BZP : BzParams}.

(* [comment removed for export] *)
Definition SI (s : est) : Prop :=
  zbok (e_arr1 s) /\ zbok (e_arr2 s) /\ bh_w32 (e_ftab s) /\ zdefr (e_inUse s) 0 256 /\ RLI (est_rl s) /\ e_nblock s = 0 /\
  0 <= e_combinedCRC s < 4294967296 /\ bw_numZ (e_bw s) = 0 /\ bw_zb (e_bw s) = znew /\ (e_blockNo s = 1 \/ BWZ (e_bw s)).

Lemma SI_rl : forall s, SI s -> RLI (est_rl s).
Proof. intros s H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
Lemma SI_cc : forall s, SI s -> 0 <= e_combinedCRC s < 4294967296.
Proof. intros s H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
Lemma EB_crc : forall e, EB e -> 0 <= e_blockCRC e < 4294967296.
Proof.
  (intros e; cps_intros (_ & _ & _ & _ & _ & RL)). cps_pose (RLI_facts _ RL) as (_ & _ & _ & _ & _ & _ & _ & [(_ & R2 & _) _] & _). exact R2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma add_pair_inUse_def : forall r, zdefr (rl_inUse r) 0 256 -> zdefr (rl_inUse (add_pair_to_block r)) 0 256.
Proof.
  intros r D. unfold add_pair_to_block.
  destruct (rl_len r =? 1); [cbn; apply zdefr_mono; exact D|].
  destruct (rl_len r =? 2); [cbn; apply zdefr_mono; exact D|].
  destruct (rl_len r =? 3); [cbn; apply zdefr_mono; exact D|].
  cbn. apply zdefr_mono. apply zdefr_mono. exact D.
Qed.
Lemma add_char_inUse_def : forall r c, zdefr (rl_inUse r) 0 256 -> zdefr (rl_inUse (add_char_to_block r c)) 0 256.
Proof.
  intros r c D. unfold add_char_to_block.
  destruct (negb (c =? rl_ch r) && (rl_len r =? 1))%bool; [cbn; apply zdefr_mono; exact D|].
  destruct (negb (c =? rl_ch r) || (rl_len r =? 255))%bool; [| cbn; exact D].
  cbn [rl_inUse]. destruct (rl_ch r <? 256); [apply add_pair_inUse_def; exact D| exact D].
Qed.
Lemma flush_inUse_def : forall r, zdefr (rl_inUse r) 0 256 -> zdefr (rl_inUse (flush_RL r)) 0 256.
Proof.
  intros r D. unfold flush_RL, init_RL. cbn [rl_inUse]. destruct (rl_ch r <? 256); [apply add_pair_inUse_def; exact D| exact D].
Qed.
Lemma rle_fill_inv : forall fuel r inp, zdefr (rl_inUse r) 0 256 -> RLI r -> Forall (fun c => 0 <= c < 256) inp ->
  (rl_ch r = 256 -> rl_nblock r = 0) -> rl_nblock r <= NBLOCKMAX + 4 ->
  let '(r', inp') := rle_fill fuel r inp in zdefr (rl_inUse r') 0 256 /\ rl_nblock r' <= NBLOCKMAX + 4.
Proof.
  induction fuel as [|f IH]; intros r inp D RL HB HE NB; cbn [rle_fill].
  - split; [exact D| exact NB].
  - destruct (Z.leb_spec NBLOCKMAX (rl_nblock r)) as [L|L]. { split; [exact D| exact NB]. }
    destruct inp as [|c rest]. { split; [exact D| exact NB]. }
    apply Forall_cons_iff in HB as [Hc HB].
    pose proof (add_char_RLI r c RL Hc HE) as X. cbv zeta in X. cps_destruct X as (RL' & _ & NB' & CH & _).
    apply IH; [apply add_char_inUse_def; exact D| exact RL'| exact HB| intros E; rewrite CH in E; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RLI_frame0 : forall r r', RLI r -> rl_nblock r' = 0 -> rl_crc r' = crc_init -> rl_ch r' = rl_ch r -> rl_len r' = rl_len r ->
  zbok (rl_block r') -> (forall i, 0 <= i < 256 -> zget (rl_inUse r') i = 0) -> RLI r'.
Proof.
  intros r r' RL0 N C CH LN ZB IU. cps_pose RL0 as (RI & _ & _ & runs & W & EB & EC & PD & CV).
  destruct RI as [(A1 & A2 & A3 & A4 & A5) P].
  split. { unfold rl_inv, rl_ok. rewrite N, C, CH, LN. unfold crc_init. split; [repeat split; try lia|]. exact P. }
  split; [exact ZB|]. split; [intros i Hi; left; apply IU; exact Hi|].
  exists []. cbn [RWF rl_enc rl_dec crc_list fold_left]. split; [exact I|]. split; [unfold rl_bytes; rewrite N; reflexivity|].
  split; [rewrite C; reflexivity|]. split; [| intros b []].
  rewrite CH, LN. destruct PD as [[P1 P2]|(P1 & P2 & P3)]; [left; auto| right]. split; [lia|]. split; [lia|]. cbn [last]. unfold ADJ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma set_rl_fields : forall s m st x r, let e := est_set_rl (est_set_modes s m st x) r in
  e_arr1 e = e_arr1 s /\ e_arr2 e = rl_block r /\ e_ftab e = e_ftab s /\ e_nblock e = rl_nblock r /\ e_inUse e = rl_inUse r /\
  est_rl e = r /\ e_bw e = e_bw s /\ e_blockNo e = e_blockNo s /\ e_combinedCRC e = e_combinedCRC s /\ e_blockCRC e = rl_crc r /\
  e_state_in_ch e = rl_ch r /\ e_state_in_len e = rl_len r.
Proof. intros. subst e. destruct s, r; cbn. repeat split; reflexivity. Qed.

Lemma EB_intro : forall s m st x r, SI s -> RLI r -> zdefr (rl_inUse r) 0 256 -> 1 <= rl_nblock r <= NBLOCKMAX + 9 ->
  EB (est_set_rl (est_set_modes s m st x) r).
Proof.
  intros s m st x r HS RL D NB. cps_pose HS as (A1 & A2 & FT & _).
  pose proof (set_rl_fields s m st x r) as F. cbv zeta in F. cps_destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & _).
  cps_pose (RLI_facts _ RL) as (_ & _ & _ & _ & _ & _ & ZB & _).
  unfold EB. rewrite F1, F2, F3, F4, F5, F6. split; [exact A1|]. split; [exact ZB|]. split; [exact FT|]. split; [exact NB|]. split; [exact D| exact RL].
Qed.

Lemma BWZ_reset : forall b, BWZ b -> BWZ (BW (bw_buff b) (bw_live b) 0 znew).
Proof. intros b [(A & B & C) Z]. split; [unfold bw_ok; cbn; lia| cbn; apply zbok_znew]. Qed.

Lemma exit_fields : forall e1 last, let x := enc_exit e1 last in
  e_arr1 x = e_arr1 (fst (compressBlock e1 last znew)) /\ e_arr2 x = e_arr2 (fst (compressBlock e1 last znew)) /\
  e_ftab x = e_ftab (fst (compressBlock e1 last znew)) /\ e_state_in_ch x = e_state_in_ch (fst (compressBlock e1 last znew)) /\
  e_state_in_len x = e_state_in_len (fst (compressBlock e1 last znew)) /\ e_bw x = e_bw (fst (compressBlock e1 last znew)).
Proof. intros. subst x. unfold enc_exit. generalize (fst (compressBlock e1 last znew)). intros y. destruct y; repeat split; reflexivity. Qed.
Lemma rl_crc_est_rl : forall x, rl_crc (est_rl x) = e_blockCRC x. Proof. reflexivity. Qed.
Lemma rl_ch_est_rl : forall x, rl_ch (est_rl x) = e_state_in_ch x. Proof. reflexivity. Qed.
Lemma rl_len_est_rl : forall x, rl_len (est_rl x) = e_state_in_len x. Proof. reflexivity. Qed.
Lemma rl_block_est_rl : forall x, rl_block (est_rl x) = e_arr2 x. Proof. reflexivity. Qed.
Lemma rl_inUse_est_rl : forall x, rl_inUse (est_rl x) = e_inUse x. Proof. reflexivity. Qed.

Theorem SI_entry : forall s inp, SI s -> START s inp -> bytes inp ->
  let '(e1, inp', last) := enc_entry s inp in (0 < e_nblock e1 -> EB e1) /\ (last = false -> SI (enc_next (enc_exit e1 false))).
Proof.
  intros s inp HS ST HB. cps_pose HS as (A1 & A2 & FT & DEF & RL & NB0 & CC & NZ & ZB & ALT). cps_pose ST as (M & S & X & NB & OP).
  assert (CH0 : rl_ch (est_rl s) = 256 -> rl_nblock (est_rl s) = 0) by (intros _; rewrite rl_nblock_est_rl; exact NB).
  pose proof (rle_fill_data (Datatypes.S (length inp)) (est_rl s) inp RL HB CH0) as D.
  pose proof (rle_fill_inv (Datatypes.S (length inp)) (est_rl s) inp DEF RL HB CH0 ltac:(rewrite rl_nblock_est_rl; bz_params; lia)) as V.
  pose proof (rle_fill_stop (Datatypes.S (length inp)) (est_rl s) inp ltac:(lia)) as STP.
  unfold enc_entry. destruct (rle_fill _ (est_rl s) inp) as [r' inp']. cps_destruct D as (RL' & _ & _). destruct V as [DEF' NB4].
  destruct inp' as [|c rest].
  - split; [| intros; discriminate]. intros NBP.
    rewrite est_set_rl_set_rl.
    cps_pose (flush_RL_RLI r' RL') as (RLf & _ & _ & NBf & _).
    rewrite est_set_rl_set_rl in NBP. rewrite e_nblock_set_rl in NBP.
    apply EB_intro; [exact HS| exact RLf| apply flush_inUse_def; exact DEF'| lia].
  - destruct STP as [STP|STP]; [discriminate|]. split.
    + intros NBP. apply EB_intro; [exact HS| exact RL'| exact DEF'| lia].
    + intros _. set (e1 := est_set_rl (est_set_modes s (e_mode s) (e_state s) (e_avail_in_expect s - Z.of_nat (length inp - length (c :: rest)))) r').
      assert (HEB : EB e1) by (subst e1; apply EB_intro; [exact HS| exact RL'| exact DEF'| bz_params; lia]).
      pose proof (set_rl_fields s (e_mode s) (e_state s) (e_avail_in_expect s - Z.of_nat (length inp - length (c :: rest))) r') as F. cbv zeta in F. fold e1 in F.
      cps_destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
      cps_destruct (eb_arrs e1 HEB false ltac:(rewrite F8, F7; exact ALT) ltac:(rewrite F7; exact ZB) ltac:(rewrite F7; exact NZ)) as (Y1 & Y2 & Y3 & Y4).
      specialize (Y4 eq_refl).
      pose proof (enc_next_fields (enc_exit e1 false)) as G. cbv zeta in G.
      cps_destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
      pose proof (cb_keep e1 false) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & Kn & Kch & Klen & _ & Kno & _ & Kcrc & Kcc).
      cps_pose (exit_fields e1 false) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      unfold SI. rewrite e_cc_next, G9, G10, G11, G15, G4, G8, G6, Q1, Q2, Q3, Q6. cbn [bw_numZ bw_zb].
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [apply inUse_clear_zdefr|]. split.
      { apply (RLI_frame0 (est_rl e1)); rewrite ?rl_nblock_est_rl, ?rl_crc_est_rl, ?rl_ch_est_rl, ?rl_len_est_rl, ?rl_block_est_rl, ?rl_inUse_est_rl.
        - rewrite F6. exact RL'.
        - exact G4.
        - exact G14.
        - rewrite G12, Q4, Kch. reflexivity.
        - rewrite G13, Q5, Klen. reflexivity.
        - rewrite G10, Q2. exact Y2.
        - intros i Hi. rewrite G15, inUse_clear_spec. change (Z.of_nat 256) with 256.
          replace ((0 <=? i) && (i <? 0 + 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
      split; [reflexivity|]. split.
      { unfold cc_after. replace (0 <? e_nblock e1) with true by (symmetry; apply Z.ltb_lt; rewrite F4; bz_params; lia).
        apply cc_next_range; [rewrite F9; exact CC| apply crc_final_range; exact (EB_crc e1 HEB)]. }
      split; [reflexivity|]. split; [reflexivity|]. right. apply BWZ_reset. exact Y4.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem init_ok : forall a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM,
  zbok a1 -> zbok a2 -> bh_w32 ft ->
  let e0 := est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM in
  E0OK' e0 /\ forall n, SI (e_fin e0 n).
Proof.
  intros a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM Z1 Z2 FT. cbv zeta. split.
  - unfold E0OK', E0OK, est_init. cbn. repeat split; reflexivity.
  - intros n. unfold SI, e_fin, est_init. cbn -[inUse_clear zbok bh_w32 zdefr RLI Z.le Z.lt].
    split; [exact Z1|]. split; [exact Z2|]. split; [exact FT|]. split; [apply inUse_clear_zdefr|]. split.
    { match goal with |- RLI ?r => apply (fun H => proj1 (RLI_init r eq_refl eq_refl eq_refl eq_refl Z2 H)) end. intros i Hi. cbn [rl_inUse est_rl e_inUse est_set_modes]. rewrite inUse_clear_spec. change (Z.of_nat 256) with 256.
      replace ((0 <=? i) && (i <? 0 + 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity| left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma zbok_znew' : zbok znew. Proof. intros i. rewrite zget_znew. lia. Qed.
Lemma bh_w32_znew : bh_w32 znew. Proof. intros i. rewrite zget_znew. lia. Qed.
(* [comment removed for export] *)
End BZPS.
