(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kitL RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil LiaTuning.
(* [comment removed for export] *)
Definition CEIL {ACEIL : Ceil} : Z := alloc_ceiling.
Ltac ceilF_add C :=
  lazymatch goal with
  | _ : (@CEIL C = @alloc_ceiling C) |- _ => fail
  | _ => pose proof (eq_refl : @CEIL C = @alloc_ceiling C)
  end.
Ltac ceilF_saturate :=
  repeat match goal with
  | |- context [@CEIL ?C] => ceilF_add C
  | _ : context [@CEIL ?C] |- _ => ceilF_add C
  end.
(* [comment removed for export] *)
Ltac ceil_inst_evars :=
  repeat match goal with
  | |- context [@CEIL ?C] => is_evar C; let I := constr:(_ : Ceil) in unify C I
  | |- context [@alloc_ceiling ?C] => is_evar C; let I := constr:(_ : Ceil) in unify C I
  end.
(* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= nat_diet; ceil_inst_evars; ceilF_saturate; ceil_saturate.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma CEIL_eq : alloc_ceiling = CEIL. Proof. reflexivity. Qed.
Lemma SH_CEIL : SH CEIL = 0x7fff8000 + alloc_ceiling / 8. Proof. reflexivity. Qed.   (* [comment removed for export] *)
Lemma SH_CEIL_range : 0x10006fef8000 <= SH CEIL <= 0x10007fef8000.
Proof. rewrite SH_CEIL. pose proof CEIL_eq. Z.div_mod_to_equations. lia. Qed.
Lemma KHIGH_val : KHIGHMEM_BEG = 0x10007fff8000. Proof. reflexivity. Qed.
Lemma AIMG_HI_val : AIMG_HI = 0x5ff000. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Z1.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (sp0 SPB : Z) (W : list (Z * Z)).
Hypothesis HSPB : SPB <= st_sp0 st.
Hypothesis FW : Forall (cj_write_ok sp0 SPB (st_lb st) (st_lf st)) W.
Hypothesis NE : Forall (fun iv : Z * Z => fst iv < snd iv) W.      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma disjoint_from_intro : forall a sz,
  (forall lo hi, In (lo, hi) W -> lo < hi -> cj_write_ok sp0 SPB (st_lb st) (st_lf st) (lo, hi) -> a + sz <= lo \/ hi <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H. induction W as [|[lo hi] W' IH]; [exact I|]. cbn. inversion FW; subst. inversion NE; subst. split.
  - apply H; [left; reflexivity| assumption| assumption].
  - apply IH; [assumption| assumption|]. intros lo' hi' Hin Hlt Hok. apply H; [right; exact Hin| exact Hlt| exact Hok].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blk_band : forall A n, In (A, n) (st_lb st) -> ablk (A - 16) (A + Z.max n 1).
Proof.
  intros A n H. (nelimp (block_geom st WF A n ltac:(unfold all_blocks; apply in_or_app; left; exact H)) 6%nat; intros _ _ K X Y _).
  apply (ablk_sub _ _ _ _ K); unfold usz in Y; lia.
Qed.
(* [comment removed for export] *)
Lemma fs_range : ablk (st_fs st) (st_fs st + FS_TOTAL) /\ st_fs st + FS_TOTAL <= CEIL /\ st_fs st mod 4096 = 0.
Proof.
  (nelimp (RT_fp.fs_range st WF) 3%nat; intros R1 R2 R3). unfold CEIL. auto.
Qed.
Lemma frame_range : forall F k, In (F, k) (st_lf st) ->
  (k = 1 \/ k = 2) /\ st_fs st + FS_FRAMES_OFF <= F /\ F + fsz k <= st_fs st + FS_TOTAL /\ F mod 8 = 0.
Proof.
  intros F k H. (nelim (wff_frame st (wf_fs_ok st WF) F k H) 3%nat; intros Hk Hpos EF).
  (nelim (fsz_12 k Hk) 5%nat; intros FZ FC _ _ _).
  assert (K2 : 2 <= 2 ^ k <= 4) by (destruct Hk as [-> | ->]; cbn; lia).
  rewrite EF. unfold fframe_addr, FS_FRAMES_OFF, FS_LOG, FS_TOTAL. rewrite Z.shiftl_mul_pow2 by lia. change (2^15) with 32768. change (2^20) with 1048576.
  rewrite FC in Hpos. rewrite FZ.
  split; [exact Hk|]. split; [nia|]. split.
  - destruct Hk as [-> | ->]; [change (2^(14-1)) with 8192 in Hpos| change (2^(14-2)) with 4096 in Hpos]; cbn -[Z.add Z.mul Z.le Z.lt] in *; lia.
  - (nelimp fs_range 3%nat; intros _ _ M).
    assert (M1 : st_fs st mod 8 = 0) by (apply (mod0_trans _ 8 4096); [lia|lia|reflexivity|exact M]).
    assert (M2 : (st_fs st + 36864) mod 8 = 0) by (apply mod0_add; [lia| exact M1| reflexivity]).
    assert (M3 : (st_fs st + 36864 + 1048576 * k) mod 8 = 0).
    { apply mod0_add; [lia| exact M2|]. replace (1048576 * k) with ((131072 * k) * 8) by lia. apply Z_mod_mult. }
    apply mod0_add; [lia| exact M3|]. replace (64 * 2^k * fpos st F k) with ((8 * 2^k * fpos st F k) * 8) by lia. apply Z_mod_mult.
Qed.
(* [comment removed for export] *)
Lemma frame_band : forall F k, In (F, k) (st_lf st) -> ablk F (F + fsz k).
Proof.
  intros F k H. (nelim (frame_range F k H) 4%nat; intros _ X Y _). (nelimp fs_range 3%nat; intros B _ _).
  apply (ablk_sub _ _ _ _ B); unfold FS_FRAMES_OFF in X; lia.
Qed.

(* [comment removed for export] *)
Definition static_ok_b : bool :=
  forallb (fun r : Z * Z => (ADATA_LO <=? fst r) && (snd r <=? AIMG_HI)
                            && ((snd r <=? AERRNO) || (AERRNO + 4 <=? fst r))
                            && ((snd r <=? AGERROR0) || (AGERROR0 + 8 <=? fst r))
                            && ((snd r <=? AGERROR1) || (AGERROR1 + 8 <=? fst r))) ART_STATIC.
Lemma static_facts : forall lo hi, In (lo, hi) ART_STATIC ->
  ADATA_LO <= lo /\ hi <= AIMG_HI /\ (hi <= AERRNO \/ AERRNO + 4 <= lo) /\ (hi <= AGERROR0 \/ AGERROR0 + 8 <= lo) /\ (hi <= AGERROR1 \/ AGERROR1 + 8 <= lo).
Proof.
  intros lo hi Hin. assert (F : static_ok_b = true) by (vm_compute; reflexivity). unfold static_ok_b in F. rewrite forallb_forall in F.
  specialize (F _ Hin). cbn [fst snd] in F.
  apply andb_true_iff in F as [F F5]. apply andb_true_iff in F as [F F4]. apply andb_true_iff in F as [F F3]. apply andb_true_iff in F as [F1 F2].
  apply Z.leb_le in F1. apply Z.leb_le in F2.
  apply orb_true_iff in F3. apply orb_true_iff in F4. apply orb_true_iff in F5.
  rewrite !Z.leb_le in F3, F4, F5. tauto.
Qed.

Lemma zone_img : forall a sz lo hi, In (lo, hi) ART_STATIC -> lo <= a -> a + sz <= hi -> 0 < sz -> disjoint_from W a sz.
Proof.
  intros a sz lo hi HS Ha Hsz Hpos. (nelimp (static_facts lo hi HS) 5%nat; intros S1 S2 S3 S4 S5).
  apply disjoint_from_intro. intros l h Hin HLT HOK.
  unfold cj_write_ok in HOK. cbn [fst snd] in HOK. rewrite CEIL_eq in HOK. rewrite AIMG_HI_val in *. unfold ADATA_LO in *.
  destruct HOK as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
  - lia.
  - unfold CEIL in H. lia.
  - rewrite SH_CEIL in H. lia.
  - lia. - lia. - lia.
  - (nelim H 3%nat; intros H1 H2 H3).
    destruct (Z_le_gt_dec (a + sz) l) as [|C1]; [left; lia|]. destruct (Z_le_gt_dec h a) as [|C2]; [right; lia|].
    exfalso. apply (H3 (Z.max a l)); [lia|]. exists lo, hi. split; [exact HS| lia].
  - (nelim H 5%nat; intros A n HB H2 H3). pose proof (ablk_img _ _ (blk_band A n HB)) as X. unfold AIMG_HI in X. lia.
  - (nelim H 5%nat; intros F k HF H2 H3). pose proof (ablk_img _ _ (frame_band F k HF)) as X. unfold AIMG_HI in X. lia.
  - (nelim H 5%nat; intros F k HF H2 H3). pose proof (ablk_img _ _ (frame_band F k HF)) as X. unfold AIMG_HI in X.
    assert (M : 0x7fff8000 <= SH F) by (unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma zone_heap : forall a sz, oclr a (a + sz) -> a + sz <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> a + sz <= A \/ A + n <= a) ->
  (forall F k, In (F, k) (st_lf st) -> a + sz <= F \/ F + fsz k - 8 <= a) ->
  disjoint_from W a sz.
Proof.
  intros a sz H0 H1 HBK HFR. apply disjoint_from_intro. intros lo hi Hin HLT HOK.
  unfold cj_write_ok in HOK. cbn [fst snd] in HOK. rewrite CEIL_eq in HOK.
  (nelimp (wb_sp0 st (wf_base_ok st WF)) 3%nat; intros _ SPH _).
  destruct HOK as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
  - lia.
  - lia.
  - pose proof (rt_SH_mono SPB (2^47) ltac:(lia)) as M. change (SH (2^47)) with 0x10007fff8000 in M.
    pose proof SH_CEIL_range as SC. clear - H0 H M SC HLT. blia.
  - unfold AERRNO, ATP in H. clear - H0 H HLT. blia.
  - unfold AGERROR0 in H. clear - H0 H HLT. blia.
  - unfold AGERROR1 in H. clear - H0 H HLT. blia.
  - (nelim H 3%nat; intros H2 H3 _). unfold ADATA_LO in H2. clear - H0 H2 H3 HLT. blia.
  - (nelim H 5%nat; intros A n HB H2 H3). destruct (HBK A n HB); lia.
  - (nelim H 5%nat; intros F k HF H2 H3). destruct (HFR F k HF); lia.
  - (nelim H 5%nat; intros F k HF H2 H3). (nelimp (frame_range F k HF) 4%nat; intros _ _ _ AL).
    (nelim (ablk_lin _ _ (frame_band F k HF)) 4%nat; intros L1 L2 L3 L4).
    pose proof (rt_SH_bounds F ltac:(destruct (fsz_12 k (proj1 (frame_range F k HF))) as (FZ & _); assert (0 < fsz k) by (rewrite FZ; destruct (proj1 (frame_range F k HF)) as [-> | ->]; cbn; lia); lia)) as B1.
    pose proof (rt_SH_bounds (F + fsz k) ltac:(destruct (fsz_12 k (proj1 (frame_range F k HF))) as (FZ & _); assert (0 < fsz k) by (rewrite FZ; destruct (proj1 (frame_range F k HF)) as [-> | ->]; cbn; lia); lia)) as B2.
    rewrite (rt_SH_aligned_add F (fsz k) AL) in B2. clear - H0 H2 H3 B1 B2 HLT. blia.
Qed.

(* [comment removed for export] *)
Lemma zone_sh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 ->
  (forall F k, In (F, k) (st_lf st) -> hi <= F \/ F + fsz k <= lo) ->
  disjoint_from W (SH lo) (SH hi - SH lo).
Proof.
  intros lo hi H0 H1 H2 AL HFR. apply disjoint_from_intro. intros l h Hin HLT HOK.
  unfold cj_write_ok in HOK. cbn [fst snd] in HOK. rewrite CEIL_eq in HOK.
  pose proof (rt_SH_bounds lo ltac:(unfold CEIL in *; lia)) as B1. pose proof (rt_SH_bounds hi ltac:(unfold CEIL in *; lia)) as B2.
  pose proof (rt_SH_mono hi CEIL H2) as M2. rewrite SH_CEIL in M2.
  replace (SH lo + (SH hi - SH lo)) with (SH hi) by lia.
  destruct HOK as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
  - lia.
  - unfold CEIL in H. lia.
  - rewrite SH_CEIL in H. lia.
  - unfold AERRNO, ATP in H. lia. - unfold AGERROR0 in H. lia. - unfold AGERROR1 in H. lia.
  - (nelim H 3%nat; intros H3 H4 _). rewrite AIMG_HI_val in H4. lia.
  - (nelim H 5%nat; intros A n HB H3 H4). destruct (ablk_disj_band _ _ (blk_band A n HB)) as [D|D]; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in D; lia.
  - (nelim H 5%nat; intros F k HF H3 H4). destruct (ablk_disj_band _ _ (frame_band F k HF)) as [D|D]; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in D; lia.
  - (nelim H 5%nat; intros F k HF H3 H4). (nelimp (frame_range F k HF) 4%nat; intros _ X Y FA). 
    rewrite <- (rt_SH_aligned_add F (fsz k) FA) in H4.
    destruct (HFR F k HF) as [D|D].
    + left. pose proof (rt_SH_mono hi F D). lia.
    + right. pose proof (rt_SH_mono (F + fsz k) lo D). lia.
Qed.
End Z1.

Lemma nodup_app_disj : forall {A} (a b : list A) x, List.NoDup (a ++ b) -> In x a -> In x b -> False.
Proof.
  induction a as [|y a IH]; intros b x ND Ha Hb; [destruct Ha|]. cbn in ND. inversion ND; subst.
  destruct Ha as [<-|Ha]; [apply H1; apply in_or_app; right; exact Hb| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Z2.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Let P := st_pbase st.
Let fs := st_fs st.

Definition blockfree (lo hi : Z) : Prop := forall A n, In (A, n) (all_blocks st) -> hi <= b_lo A n \/ b_hi A n <= lo.
Definition framefree (lo hi : Z) : Prop := hi <= fs \/ fs + FS_TOTAL <= lo.

Lemma blockfree_lb : forall lo hi, blockfree lo hi -> forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo.
Proof.
  intros lo hi H A n Hin. assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 6%nat; intros _ _ _ X Y _). unfold usz in Y. destruct (H A n J); lia.
Qed.
Lemma framefree_lf : forall lo hi, framefree lo hi -> forall F k, In (F, k) (st_lf st) -> hi <= F \/ F + fsz k - 8 <= lo.
Proof. intros lo hi H F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros _ X Y _). unfold framefree in H. unfold fs in H. unfold FS_FRAMES_OFF in X. lia. Qed.
Lemma framefree_sh : forall lo hi, framefree lo hi -> forall F k, In (F, k) (st_lf st) -> hi <= F \/ F + fsz k <= lo.
Proof. intros lo hi H F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros _ X Y _). unfold framefree in H. unfold fs in H. unfold FS_FRAMES_OFF in X. lia. Qed.
Lemma blockfree_sub : forall lo hi lo' hi', blockfree lo hi -> lo <= lo' -> hi' <= hi -> blockfree lo' hi'.
Proof. intros lo hi lo' hi' H H1 H2 A n J. destruct (H A n J); lia. Qed.
Lemma framefree_sub : forall lo hi lo' hi', framefree lo hi -> lo <= lo' -> hi' <= hi -> framefree lo' hi'.
Proof. intros. unfold framefree in *. lia. Qed.

(* [comment removed for export] *)
Let LOOSE := map (fun e : Z * Z => (fst e, fst e + snd e)) (st_loose0 st).
Let SECR := map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st).
Let NBR := map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)).
Let SBR := map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)).

Lemma PW_tail : pwdj (LOOSE ++ SECR ++ NBR ++ SBR)
  /\ Forall (fun r' => P + PRIM_RES_SIZE <= fst r' \/ snd r' <= P) ((st_pa st, st_pa st + PTRARR_RES_SIZE) :: LOOSE ++ SECR ++ NBR ++ SBR)
  /\ Forall (fun r' => st_pa st + PTRARR_RES_SIZE <= fst r' \/ snd r' <= st_pa st) (LOOSE ++ SECR ++ NBR ++ SBR).
Proof.
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW.
  (nelim PW 3%nat; intros F1 F2 PW). split; [exact PW|]. split.
  - eapply Forall_impl; [|exact F1]. intros [a b] H. cbn [fst snd] in *. unfold P. lia.
  - eapply Forall_impl; [|exact F2]. intros [a b] H. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Lemma fs_in_LOOSE : In (fs, fs + FS_TOTAL) LOOSE.
Proof. unfold LOOSE. apply in_map_iff. exists (fs, FS_TOTAL). split; [reflexivity| exact (wb_fs_loose st (wf_base_ok st WF))]. Qed.

Lemma prim_framefree : forall lo hi, P <= lo -> hi <= P + PRIM_RES_SIZE -> framefree lo hi.
Proof.
  intros lo hi H1 H2. (nelim PW_tail 3%nat; intros _ F1 _). rewrite Forall_forall in F1.
  specialize (F1 (fs, fs + FS_TOTAL) ltac:(right; apply in_or_app; left; apply fs_in_LOOSE)). cbn [fst snd] in F1.
  unfold framefree, FS_FRAMES_OFF. lia.
Qed.
Lemma pa_framefree : framefree (st_pa st) (st_pa st + PTRARR_RES_SIZE).
Proof.
  (nelim PW_tail 3%nat; intros _ _ F2). rewrite Forall_forall in F2.
  specialize (F2 (fs, fs + FS_TOTAL) ltac:(apply in_or_app; left; apply fs_in_LOOSE)). cbn [fst snd] in F2.
  unfold framefree, FS_FRAMES_OFF. lia.
Qed.
Lemma sec_framefree : forall mb n, In (mb, n) (st_sec st) -> framefree mb (mb + smapsize n).
Proof.
  intros mb n H. destruct PW_tail as (PW & _).
  pose proof (pwdj_app_disj _ _ (fs, fs + FS_TOTAL) (mb, mb + smapsize n) PW fs_in_LOOSE
                ltac:(apply in_or_app; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact H])) as D.
  cbn [fst snd] in D. unfold framefree, FS_FRAMES_OFF. lia.
Qed.
Lemma nbsb_framefree : forall r, In r (NBR ++ SBR) -> framefree (fst r) (snd r).
Proof.
  intros r H. destruct PW_tail as (PW & _).
  pose proof (pwdj_app_disj _ _ (fs, fs + FS_TOTAL) r PW fs_in_LOOSE ltac:(apply in_or_app; right; exact H)) as D.
  cbn [fst snd] in D. unfold framefree, FS_FRAMES_OFF. lia.
Qed.
Lemma pwdj_app_l : forall L1 L2, pwdj (L1 ++ L2) -> pwdj L1.
Proof.
  induction L1 as [|r L1 IH]; intros L2 H; [exact I|]. cbn in H |- *. destruct H as [HF HP].
  split; [| eapply IH; exact HP]. apply Forall_app in HF. tauto.
Qed.
Lemma loose_framefree : forall b k, In (b, k) (st_loose0 st) -> (b, b + k) <> (fs, fs + FS_TOTAL) -> framefree b (b + k).
Proof.
  intros b k H NEQ. destruct PW_tail as (PW & _). apply pwdj_app_l in PW.
  assert (INb : In (b, b + k) LOOSE) by (unfold LOOSE; apply in_map_iff; exists (b, k); split; [reflexivity| exact H]).
  destruct (pwdj_In _ _ _ PW INb fs_in_LOOSE) as [E|D]; [exfalso; exact (NEQ E)|].
  cbn [fst snd] in D. unfold framefree, FS_FRAMES_OFF. lia.
Qed.

(* [comment removed for export] *)
Lemma tail_blockfree : forall r, In r (LOOSE ++ SECR ++ NBR ++ SBR) -> In r LOOSE \/ In r (NBR ++ SBR) -> blockfree (fst r) (snd r).
Proof.
  intros r Hr Hcase A n HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _).
    (nelim PW_tail 3%nat; intros _ F1 _). rewrite Forall_forall in F1. specialize (F1 r ltac:(right; exact Hr)). unfold P in *. lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). destruct PW_tail as (PW & _).
    assert (INs : In (b_lo A n, b_lo A n + smapsize n) SECR).
    { unfold SECR. apply in_map_iff. exists (b_lo A n, n). split; [reflexivity| exact S1]. }
    rewrite T1. destruct Hcase as [HL|HN].
    + pose proof (pwdj_app_disj _ _ r _ PW HL ltac:(apply in_or_app; left; exact INs)) as D. cbn [fst snd] in D. lia.
    + apply pwdj_app_r in PW. pose proof (pwdj_app_disj _ _ _ r PW INs HN) as D. cbn [fst snd] in D. lia.
Qed.
Lemma loose_blockfree : forall b k, In (b, k) (st_loose0 st) -> blockfree b (b + k).
Proof.
  intros b k H. assert (IN : In (b, b + k) LOOSE) by (unfold LOOSE; apply in_map_iff; exists (b, k); split; [reflexivity| exact H]).
  exact (tail_blockfree (b, b + k) ltac:(apply in_or_app; left; exact IN) (or_introl IN)).
Qed.
Lemma nb_blockfree : forall b, In b (d_nblocks (st_depot st)) -> blockfree b (b + NODEBLOCK_SIZE) /\ framefree b (b + NODEBLOCK_SIZE).
Proof.
  intros b H. assert (IN : In (b, b + NODEBLOCK_SIZE) (NBR ++ SBR)) by (apply in_or_app; left; unfold NBR; apply in_map_iff; exists b; auto).
  split; [| exact (nbsb_framefree _ IN)].
  exact (tail_blockfree (b, b + NODEBLOCK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; right; exact IN) (or_intror IN)).
Qed.
Lemma sb_blockfree : forall b, In b (d_sblocks (st_depot st)) -> blockfree b (b + STOREBLOCK_SIZE) /\ framefree b (b + STOREBLOCK_SIZE).
Proof.
  intros b H. assert (IN : In (b, b + STOREBLOCK_SIZE) (NBR ++ SBR)) by (apply in_or_app; right; unfold SBR; apply in_map_iff; exists b; auto).
  split; [| exact (nbsb_framefree _ IN)].
  exact (tail_blockfree (b, b + STOREBLOCK_SIZE) ltac:(apply in_or_app; right; apply in_or_app; right; exact IN) (or_intror IN)).
Qed.
Lemma pa_blockfree : blockfree (st_pa st) (st_pa st + PTRARR_RES_SIZE).
Proof.
  intros A n HB. (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. (nelim PW 3%nat; intros F0 F1 _).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). inversion F0; subst. cbn [fst snd] in *. unfold P in *. lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). rewrite Forall_forall in F1.
    specialize (F1 (b_lo A n, b_lo A n + smapsize n) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1])).
    cbn [fst snd] in F1. rewrite T1. lia.
Qed.
(* [comment removed for export] *)
Lemma prim_nonuser_blockfree : forall lo hi, P <= lo -> hi <= P + PRIM_RES_SIZE ->
  (forall c, 0 <= c < KNUMCLASSES -> hi <= rbeg st c \/ rbeg st c + r_mapped (rg st c) <= lo) -> blockfree lo hi.
Proof.
  intros lo hi H1 H2 HC A n HB. (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 4%nat; intros Hc RB RE _). cbn zeta in *. destruct (HC (pclass n) ltac:(unfold KNUMCLASSES; lia)); lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). destruct (prim_vs_tail st WF (b_lo A n, b_lo A n + smapsize n)) as [D|D].
    { apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1]. }
    + cbn [fst snd] in D. unfold P in *. lia.
    + cbn [fst snd] in D. unfold P in *. lia.
Qed.
Lemma ris_blockfree : blockfree (ris st) (ris st + 4096).
Proof.
  (nelimp (S_range st WF) 3%nat; intros S1 S2 S3). unfold KSPACESIZE in S2. apply prim_nonuser_blockfree; [unfold ris, KSPACESIZE, P in *; lia| unfold ris, KSPACESIZE, P in *; lia|].
  intros c Hc. right. (nelim (region_range st WF c Hc) 4%nat; intros _ R2 R3 _).
  assert (rbeg st c + KREGIONSIZE <= rbeg st (KNUMCLASSES - 1) + KREGIONSIZE) by (rewrite !(rbeg_val st); unfold KNUMCLASSES, KREGIONSIZE in *; nia).
  unfold ris, KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KNUMCLASSES in *. lia.
Qed.
Lemma fa_blockfree : forall c, 0 <= c < KNUMCLASSES -> blockfree (fabeg st c) (fabeg st c + r_mapped_fa (rg st c)).
Proof.
  intros c Hc. (nelimp (S_range st WF) 3%nat; intros S1 S2 S3). (nelim (region_range st WF c Hc) 4%nat; intros R1 R2 R3 _).
  pose proof (wc_fa_max st c (wf_class_ok st WF c Hc)) as FM. pose proof (wc_fa_nonneg st c (wf_class_ok st WF c Hc)) as F0.
  assert (RB31 : rbeg st c + KREGIONSIZE <= rbeg st (KNUMCLASSES - 1) + KREGIONSIZE) by (rewrite !(rbeg_val st); unfold KNUMCLASSES, KREGIONSIZE in *; nia).
  unfold fabeg, free_array. fold (rbeg st c).
  apply prim_nonuser_blockfree; [unfold KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, KNUMCLASSES, P in *; lia| unfold KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, KNUMCLASSES, P in *; lia|].
  intros c' Hc'. (nelim (region_range st WF c' Hc') 3%nat; intros _ R2' _).
  rewrite (rbeg_val st c') in *. rewrite (rbeg_val st c) in *. unfold KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE, KNUMCLASSES in *.
  destruct (Z_lt_le_dec c' c) as [L|L]; [right; nia|]. destruct (Z.eq_dec c' c) as [->|N]; [right; lia| left; nia].
Qed.
(* [comment removed for export] *)
Lemma below_user_lb : forall A' n' lo hi, In (A', n') (all_blocks st) -> b_lo A' n' <= lo -> hi <= A' ->
  forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo.
Proof.
  intros A' n' lo hi H' H1 H2 A n Hin. assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 6%nat; intros Gn _ _ X Y _). unfold usz in Y.
  destruct (Z.eq_dec A A') as [->|NE]; [left; exact H2|].
  (nelimp (block_geom st WF A' n' H') 6%nat; intros _ _ _ X' Y' _). unfold usz in Y'.
  destruct (blocks_disj st WF A n A' n' J H' NE); lia.
Qed.
Lemma block_framefree : forall A n, In (A, n) (all_blocks st) -> framefree (b_lo A n) (b_hi A n).
Proof.
  intros A n H. (nelimp (block_geom st WF A n H) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply prim_framefree; unfold P; lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). rewrite T1. apply sec_framefree. exact S1.
Qed.
(* [comment removed for export] *)
Lemma batch_geom : forall b, In b (qall st) ->
  blockfree (qb_addr b) (qb_addr b + QBATCH_SIZE) /\ framefree (qb_addr b) (qb_addr b + QBATCH_SIZE)
  /\ rbeg st 24 <= qb_addr b /\ qb_addr b + QBATCH_SIZE <= rbeg st 24 + r_mapped (rg st 24) /\ qb_addr b mod 32 = 0.
Proof.
  intros b Hb. (nelim (wq_batch st (wf_quar_ok st WF) b Hb) 4%nat; intros _ k CV EQ).
  assert (Hc : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelim (carved_chunk st WF 24 k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3). change (csize 24) with 8192 in C2, C3.
  (nelim (region_range st WF 24 Hc) 6%nat; intros R1 R2 R3 R4 R5 R6). (nelimp (S_range st WF) 3%nat; intros S1 S2 S3).
  rewrite <- EQ in C1, C2, C3. unfold QBATCH_SIZE.
  assert (AL32 : qb_addr b mod 32 = 0).
  { apply (mod0_of_sub (qb_addr b) (rbeg st 24) 32 ltac:(lia)); [apply (mod0_trans _ 32 8192); [lia|lia|reflexivity|exact C3]| apply (mod0_trans _ 32 4096); [lia|lia|reflexivity|exact R4]]. }
  assert (RB31 : rbeg st 24 + KREGIONSIZE <= rbeg st (KNUMCLASSES - 1) + KREGIONSIZE) by (rewrite !(rbeg_val st); unfold KNUMCLASSES, KREGIONSIZE in *; nia).
  split; [| split; [apply prim_framefree; unfold P, KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KNUMCLASSES in *; lia| repeat split; try lia]].
  intros A n HB. (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros Hcl RB RE _ _ BH). cbn zeta in *.
    destruct (Z.eq_dec (pclass n) 24) as [E24|N24].
    + (* [comment removed for export] *)
      (nelim (prim_block_cptr st WF A n HB EP) 4%nat; intros IN1 IK1 CVb Lb). rewrite E24 in IK1, CVb, Lb.
      pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 Hc)) as ND. rewrite used_cptrs_split in ND.
      assert (INk : In k (batch_cptrs st 24)).
      { unfold batch_cptrs. rewrite Z.eqb_refl. apply in_map_iff. exists (qb_addr b). split; [rewrite EQ; unfold cptr_addr; Z.div_mod_to_equations; nia|].
        unfold qbatch_addrs. apply in_map. exact Hb. }
      assert (NK : b_cptr st A n <> k).
      { intros EK. apply NoDup_app_remove_l in ND.
        eapply (nodup_app_disj _ _ _ ND IK1). rewrite EK. apply in_or_app. left. exact INk. }
      (nelim (carved_chunk st WF 24 (b_cptr st A n) Hc ltac:(lia) CVb) 3%nat; intros X1 Y1 M1). rewrite <- Lb in X1, Y1, M1. change (csize 24) with 8192 in Y1, M1, BH.
      rewrite E24 in BH. change (csize 24) with 8192 in BH. rewrite BH.
      assert (NL : b_lo A n <> qb_addr b) by (rewrite Lb, EQ; unfold cptr_addr; intros E; apply NK; lia).
      apply Z.mod_divide in M1; [|lia]. apply Z.mod_divide in C3; [|lia]. destruct M1 as [q1 M1]. destruct C3 as [q2 C3].
      assert (q1 <> q2) by (intros ->; apply NL; lia).
      destruct (Z_lt_le_dec q1 q2); [right| left]; nia.
    + assert (MM : r_mapped (rg st (pclass n)) <= KFREEARRAY_OFF) by (apply (wc_mapped_max st (pclass n) (wf_class_ok st WF (pclass n) ltac:(unfold KNUMCLASSES; lia)))).
      rewrite (rbeg_val st (pclass n)) in *. rewrite (rbeg_val st 24) in *. unfold KREGIONSIZE, KFREEARRAY_OFF in *.
      destruct (Z_lt_le_dec (pclass n) 24); [right| left]; nia.
  - (nelim (Gs eq_refl) 3%nat; intros S1' T1 _).
    destruct (prim_vs_tail st WF (b_lo A n, b_lo A n + smapsize n)) as [D|D].
    { apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1']. }
    + cbn [fst snd] in D. unfold P, KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KNUMCLASSES in *. lia.
    + cbn [fst snd] in D. unfold P, KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KNUMCLASSES in *. lia.
Qed.
End Z2.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alink_range_all :
  forallb (fun p => ((0xa1140 <=? fst p) && (fst p + 8 <=? 0xa23f8)) || ((0xa3408 <=? fst p) && (fst p + 8 <=? 0xa3590))) ALINK_WORDS = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma alink_range : forall a v, In (a, v) ALINK_WORDS -> (0xa1140 <= a /\ a + 8 <= 0xa23f8) \/ (0xa3408 <= a /\ a + 8 <= 0xa3590).
Proof.
  intros a v H. pose proof alink_range_all as F. rewrite forallb_forall in F. specialize (F _ H). cbn [fst] in F.
  apply orb_true_iff in F as [F|F]; apply andb_true_iff in F as [F1 F2]; apply Z.leb_le in F1; apply Z.leb_le in F2; lia.
Qed.

Definition flags_ok_b : bool :=
  forallb (fun k => (4096 <=? fflags_off k) && (fflags_off k + fcap k <=? 0x9000)) (map Z.of_nat (seq 0 11)).
Lemma flags_ok : forall k, 0 <= k < 11 -> 4096 <= fflags_off k /\ fflags_off k + fcap k <= 0x9000.
Proof.
  intros k Hk. assert (F : flags_ok_b = true) by (vm_compute; reflexivity). unfold flags_ok_b in F. rewrite forallb_forall in F.
  specialize (F k ltac:(apply in_map_iff; exists (Z.to_nat k); split; [lia| apply in_seq; lia])).
  apply andb_true_iff in F as [F1 F2]. apply Z.leb_le in F1. apply Z.leb_le in F2. lia.
Qed.

Lemma cmaxcount_le16 : forall c, cmaxcount c <= 16.
Proof. intros c. unfold cmaxcount, clampz. lia. Qed.

Section ZN.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
(* [comment removed for export] *)
Hypothesis Zimg : forall a sz lo hi, In (lo, hi) ART_STATIC -> lo <= a -> a + sz <= hi -> 0 < sz -> disjoint_from W a sz.
(* [comment removed for export] *)
Hypothesis Zheap' : forall lo hi, oclr lo hi -> hi <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo) -> framefree st lo hi -> disjoint_from W lo (hi - lo).
Hypothesis Zsh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 -> framefree st lo hi ->
  disjoint_from W (SH lo) (SH hi - SH lo).


Lemma Zheap : forall lo hi, oclr lo hi -> hi <= CEIL -> blockfree st lo hi -> framefree st lo hi -> disjoint_from W lo (hi - lo).
Proof.
  intros lo hi H1 H2 HB HF. apply Zheap'; [exact H1| exact H2| | exact HF].
  intros A n Hin. exact (blockfree_lb st WF lo hi HB A n Hin).
Qed.
(* [comment removed for export] *)
Lemma Zobj : forall lo hi a sz, oclr lo hi -> hi <= CEIL -> blockfree st lo hi -> framefree st lo hi ->
  lo <= a -> a + sz <= hi -> disjoint_from W a sz.
Proof.
  intros lo hi a sz H1 H2 HB HF Ha Hs. replace sz with ((a + sz) - a) by lia.
  destruct (Z_le_gt_dec (a + sz) a) as [E|E].
  - (* [comment removed for export] *)
    apply Zheap; [clear - H1 Ha Hs E; blia| lia| eapply blockfree_sub; eauto; lia| eapply framefree_sub; eauto; lia].
  - apply Zheap; [apply (oclr_sub lo hi); [exact H1| lia| lia| lia]| lia| eapply blockfree_sub; eauto; lia| eapply framefree_sub; eauto; lia].
Qed.

(* [comment removed for export] *)
Ltac static_in := cbn; repeat (first [left; reflexivity | right]).
Ltac zimg1 lo hi := apply (Zimg _ _ lo hi); [static_in | lia | lia | lia].
(* [comment removed for export] *)
Ltac try_ranges L tac := lazymatch L with (?lo, ?hi) :: ?L' => first [ tac lo hi | try_ranges L' tac ] end.
Ltac zimg := unfold ADATA_LO, AIMG_HI, AERRNO, AGERROR0, AGERROR1, ATP, A_ALLOC, AHOOKS, A_TSD_MAIN in *; cbn -[Z.add Z.mul Z.le Z.lt Z.sub] in *;
  let L := eval cbv [ART_STATIC ART_WSTATIC app ADATA_LO] in ART_STATIC in try_ranges L zimg1.

(* [comment removed for export] *)
Lemma W_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); zimg| unfold A_GLOBREC_LO, A_GLOBREC_HI; zimg]. Qed.

(* [comment removed for export] *)
Lemma W_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; zimg.
Qed.

(* [comment removed for export] *)
Lemma W_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_ALLOC, A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; zimg.
Qed.

(* [comment removed for export] *)
Lemma W_rinfo : WOK_rinfo st W.
Proof.
  intros c Hc. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc.
  eapply (Zobj (ris st) (ris st + 4096)); [blia| unfold CEIL; lia| apply ris_blockfree; exact WF| apply prim_framefree; [exact WF| lia| lia]| unfold rinfo; lia|].
  unfold rinfo. lia.
Qed.

(* [comment removed for export] *)
Lemma W_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  pose proof (rt_SH_bounds (rbeg st c) ltac:(unfold KHIGHMEM_BEG, KREGIONSIZE in *; lia)) as B1.
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  pose proof (rt_SH_bounds (fabeg st c) ltac:(lia)) as B2.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF.
    eapply (Zobj (fabeg st c) (fabeg st c + r_mapped_fa (rg st c)));
      [unfold KHIGHMEM_BEG; blia | unfold CEIL; lia | apply fa_blockfree; [exact WF| exact Hc]
      | apply prim_framefree; [exact WF| |]; lia
      | lia | lia].
  - replace ((r_mapped (rg st c) - r_allocated (rg st c)) / 8) with (SH (rbeg st c + r_mapped (rg st c)) - SH (rbeg st c + r_allocated (rg st c)))
      by (rewrite !rt_SH_aligned_add by exact X8; Z.div_mod_to_equations; lia).
    apply Zsh; [lia| lia| unfold CEIL; lia| apply mod0_add; [lia| exact X8| exact X9]|].
    apply prim_framefree; [exact WF| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma W_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  (nelim (carved_chunk st WF c k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP. pose proof (csize_mod32 c ltac:(unfold KNUMCLASSES in Hc; lia)) as SM.
  assert (AL : cptr_addr st c k mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c) 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c)); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  replace (csize c / 8) with (SH (cptr_addr st c k + csize c) - SH (cptr_addr st c k)) by (rewrite rt_SH_aligned_add by exact AL; lia).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF in *.
  apply Zsh; [lia| lia| unfold CEIL; lia| exact AL|]. apply prim_framefree; [exact WF| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma t_page : oclr (st_t st) (st_t st + 4096) /\ st_t st + 4096 <= CEIL /\ blockfree st (st_t st) (st_t st + 4096) /\ framefree st (st_t st) (st_t st + 4096).
Proof.
  pose proof (wb_t_loose st (wf_base_ok st WF)) as TL. (nelim (loose0_range st WF _ _ TL) 4%nat; intros R1 R2 R3 R4).
  split; [exact R1|]. split; [unfold CEIL; lia|]. split; [apply loose_blockfree; [exact WF| exact TL]|].
  apply loose_framefree; [exact WF| exact TL|]. intros E. injection E. unfold FS_TOTAL. lia.
Qed.

Lemma W_cache : WOK_cache st W.
Proof.
  intros c Hc. (nelimp t_page 4%nat; intros T1 T2 T3 T4).
  pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - eapply (Zobj (st_t st) (st_t st + 4096)); eauto; unfold pcaddr, acache, T_ACACHE; lia.
  - intros i Hi. eapply (Zobj (st_t st) (st_t st + 4096)); eauto; unfold pcaddr, acache, T_ACACHE; lia.
Qed.

Lemma W_thread : WOK_thread st W.
Proof.
  (nelimp t_page 4%nat; intros T1 T2 T3 T4). unfold WOK_thread.
  split; [eapply (Zobj (st_t st) (st_t st + 4096)); eauto; lia|].
  split; [eapply (Zobj (st_t st) (st_t st + 4096)); eauto; unfold qcache_t, T_QCACHE; lia|].
  split; [eapply (Zobj (st_t st) (st_t st + 4096)); eauto; unfold T_UNWINDING; lia|].
  (* [comment removed for export] *)
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). (nelim (loose0_range st WF _ _ CL1) 4%nat; intros R1 R2 R3 R4).
  pose proof (loose_blockfree st WF _ _ CL1) as CB. pose proof (wb_ctx_fs st (wf_base_ok st WF)) as CF.
  assert (ZC : forall a sz, st_ctx st <= a -> a + sz <= st_ctx st + 160 -> disjoint_from W a sz).
  { intros a sz Ha Hs. replace sz with ((a + sz) - a) by lia. apply Zheap; [blia| unfold CEIL; lia| eapply blockfree_sub; [exact CB| lia| lia]|].
    unfold framefree. lia. }
  split; [apply ZC; unfold CTX_TID; lia|].
  split; [apply ZC; unfold CTX_THREAD; lia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [zimg|]. split; [zimg|]. split; [zimg|]. split; [zimg|]. split; [zimg|]. split; [zimg|].
  (* [comment removed for export] *)
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). (nelim (loose0_range st WF _ _ DL1) 4%nat; intros Q1 Q2 Q3 Q4).
  pose proof (loose_blockfree st WF _ _ DL1) as DB. pose proof (wb_dtls_fs st (wf_base_ok st WF)) as DF.
  replace 8 with ((tl_dtls_block (st_tls st) + 16 * 1 + 8 + 8) - (tl_dtls_block (st_tls st) + 16 * 1 + 8)) at 2 by lia.
  apply Zheap; [blia| unfold CEIL; lia| eapply blockfree_sub; [exact DB| lia| lia]| unfold framefree; lia].
Qed.

(* [comment removed for export] *)
Lemma W_block : forall A n, In (A, n) (all_blocks st) -> WOK_block W A n.
Proof.
  intros A n HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y. unfold KHIGHMEM_BEG in K.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  pose proof (block_framefree st WF A n HB) as BF. pose proof (rz_size_range n) as (Z1 & Z2).
  apply WOK_block_intro.
  - intros a sz Ha Hs. replace sz with ((a + sz) - a) by lia. apply Zheap'; [unfold KHIGHMEM_BEG; blia| unfold CEIL; lia| |].
    + intros A' n' Hin'. eapply (below_user_lb st WF A n); eauto; lia.
    + eapply framefree_sub; [exact BF| lia| lia].
  - replace (sh_tot n) with (SH (b_hi A n) - SH (b_lo A n)).
    2:{ unfold sh_tot. assert (EH : b_hi A n = b_lo A n + asz n) by reflexivity. rewrite EH, rt_SH_aligned_add by exact L8.
        destruct (bprim n) eqn:EP; [(nelim (prim_facts n EP) 5%nat; intros _ _ F3 F4 F5); rewrite F5 | (nelim (sec_facts n EP) 6%nat; intros _ _ F3 _ F5 _); rewrite F5]; Z.div_mod_to_equations; lia. }
    apply Zsh; [blia| lia| unfold CEIL; lia| exact L8| exact BF].
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n) eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n EP) 3%nat; intros _ F2 _). rewrite F2. cbn. lia.
Qed.
Lemma W_live : WOK_live st W.
Proof. intros A n Hin. apply W_block. unfold all_blocks; apply in_or_app; left; exact Hin. Qed.
Lemma W_quar : WOK_quar st W.
Proof. intros A n Hin. apply W_block. unfold all_blocks; apply in_or_app; right; exact Hin. Qed.

(* [comment removed for export] *)
Lemma spend_blockfree : forall e, In e (st_spend st) -> blockfree st (fst e) (fst e + smapsize (snd e)).
Proof.
  intros [mb n] He A' n' HB. cbn [fst snd]. destruct (ws_spend st (wf_sec_ok st WF) _ He) as [HE NB]. cbn [fst snd] in NB.
  (nelimp (block_geom st WF A' n' HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  destruct (bprim n') eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _).
    destruct (prim_vs_tail st WF (mb, mb + smapsize n)) as [D|D];
      [apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact HE]| |]; cbn [fst snd] in D; lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _). rewrite T1.
    destruct (Z.eq_dec (b_lo A' n') mb) as [E|NE].
    + exfalso. assert (n' = n).
      { pose proof (nodup_map_inj fst _ (b_lo A' n', n') (mb, n) (ws_nodup st (wf_sec_ok st WF)) S1 HE ltac:(cbn [fst]; exact E)). congruence. }
      subst n'. apply NB. replace (sec_user mb) with A'; [exact HB|]. rewrite <- E. unfold b_lo. rewrite EP. unfold b_map_beg, sec_user. lia.
    + pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. (nelim PW 3%nat; intros _ _ PW).
      apply pwdj_app_r in PW.
      assert (I1 : In (b_lo A' n', b_lo A' n' + smapsize n') (map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st))) by (apply in_map_iff; exists (b_lo A' n', n'); auto).
      assert (I2 : In (mb, mb + smapsize n) (map (fun e : Z * Z => (fst e, fst e + smapsize (snd e))) (st_sec st))) by (apply in_map_iff; exists (mb, n); auto).
      apply pwdj_app_l in PW.
      destruct (pwdj_In _ _ _ PW I1 I2) as [EQ|D]; [exfalso; apply NE; injection EQ; auto| cbn [fst snd] in D; lia].
Qed.

(* [comment removed for export] *)
Lemma W_batches : WOK_batches st W.
Proof.
  intros b Hb.
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  assert (OBJ : forall a sz, qb_addr b <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (Zobj (qb_addr b) (qb_addr b + 8192)); eauto; unfold KHIGHMEM_BEG, CEIL; blia. }
  split; [| split].
  - apply OBJ; lia.
  - intros i Hi. apply OBJ; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    replace 1024 with (SH (qb_addr b + 8192) - SH (qb_addr b)) by (rewrite rt_SH_aligned_add by exact AL8; change (8192 / 8) with 1024; lia).
    apply Zsh; [lia| lia| unfold CEIL; lia| exact AL8| exact BF].
Qed.

(* [comment removed for export] *)
Lemma W_ptrarr : WOK_ptrarr st W.
Proof.
  split.
  - intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). unfold KHIGHMEM_BEG, PTRARR_RES_SIZE in *.
    eapply (Zobj (st_pa st) (st_pa st + PTRARR_RES_SIZE)); [apply oclr_of_ablk; exact P1| unfold PTRARR_RES_SIZE, CEIL; lia| apply pa_blockfree; exact WF| apply pa_framefree; exact WF| lia| unfold PTRARR_RES_SIZE; lia].
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
    (nelim (ws_entry st (wf_sec_ok st WF) e HE) 4%nat; intros E1 E2 E3 _).
    pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
    specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
    destruct e as [mb n]. cbn [fst snd] in *. (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _). pose proof (usz_le_rounded8 n) as (U1 & _).
    eapply (Zobj mb (mb + smapsize n)); [exact (proj1 R)| unfold CEIL; lia| exact (spend_blockfree (mb, n) He)| apply sec_framefree; [exact WF| exact HE]| lia| unfold usz in *; lia].
Qed.

(* [comment removed for export] *)
Lemma W_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. zimg.
  - zimg.
  - intros k Hk. zimg.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. nia. }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    destruct (nb_blockfree st WF b Hb) as [B1 B2]. (nelim (nb_range st WF b Hb) 3%nat; intros R1 R2 R3).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    eapply (Zobj b (b + 1048576)); [apply oclr_of_ablk; exact R1| unfold CEIL; lia| exact B1| exact B2| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia].
  - zimg.
  - intros b Hb. zimg.
Qed.

(* [comment removed for export] *)
Lemma W_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. zimg. Qed.

Lemma W_lowshadow : WOK_lowshadow W.
Proof.
  intros g Hg.
  change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg.
  set (lo := 8 * (g - SHADOW_OFFSET)).
  assert (E1 : SH lo = g) by (subst lo; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  assert (E2 : SH (lo + 8) = g + 1) by (subst lo; unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
  replace 1 with (SH (lo + 8) - SH lo) by lia. rewrite <- E1 at 1.
  pose proof (fs_range st WF) as (F1 & _). unfold KHIGHMEM_BEG in F1.
  apply Zsh; subst lo; unfold SHADOW_OFFSET, CEIL; [lia| lia| lia| Z.div_mod_to_equations; lia|].
  unfold framefree. left. blia.
Qed.
End ZN.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FD.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Lemma frames_disj : forall F k F' k', In (F, k) (st_lf st) -> In (F', k') (st_lf st) -> F <> F' ->
  F + fsz k <= F' \/ F' + fsz k' <= F.
Proof.
  intros F k F' k' H H' NEQ.
  (nelim (wff_frame st (wf_fs_ok st WF) F k H) 3%nat; intros Hk Hp EF). (nelim (wff_frame st (wf_fs_ok st WF) F' k' H') 3%nat; intros Hk' Hp' EF').
  (nelim (fsz_12 k Hk) 3%nat; intros FZ FC _). (nelim (fsz_12 k' Hk') 3%nat; intros FZ' FC' _).
  rewrite FC in Hp. rewrite FC' in Hp'.
  set (p := fpos st F k) in *. set (p' := fpos st F' k') in *.
  rewrite EF, EF' in *. unfold fframe_addr, FS_FRAMES_OFF, FS_LOG in *. rewrite !Z.shiftl_mul_pow2 in * by lia. rewrite FZ, FZ'.
  change (2^15) with 32768 in *. change (1 * 2^20) with 1048576 in *.
  destruct Hk as [-> | ->]; destruct Hk' as [-> | ->]; cbn -[Z.add Z.mul Z.le Z.lt Z.sub] in *;
    change (2^(14-1)) with 8192 in *; change (2^(14-2)) with 4096 in *.
  - assert (p <> p') by (intros E; apply NEQ; lia). nia.
  - lia.
  - lia.
  - assert (p <> p') by (intros E; apply NEQ; lia). nia.
Qed.
End FD.

Section CW.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (sp0 SPB : Z) (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis HSPB : SPB <= st_sp0 st.
Hypothesis FW : Forall (cj_write_ok sp0 SPB (st_lb st) (st_lf st)) W.
Hypothesis NE : Forall (fun iv : Z * Z => fst iv < snd iv) W.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma cw_Zimg : forall a sz lo hi, In (lo, hi) ART_STATIC -> lo <= a -> a + sz <= hi -> 0 < sz -> disjoint_from W a sz.
Proof. intros. eapply zone_img; eauto. Qed.
Lemma cw_Zheap' : forall lo hi, oclr lo hi -> hi <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo) -> framefree st lo hi -> disjoint_from W lo (hi - lo).
Proof.
  intros lo hi H1 H2 HB HF.
  assert (O : oclr lo (lo + (hi - lo))) by (replace (lo + (hi - lo)) with hi by lia; exact H1).
  eapply zone_heap; eauto; [lia| |].
  - intros A n Hin. destruct (HB A n Hin); lia.
  - intros F k Hin. destruct (framefree_lf st WF lo hi HF F k Hin); lia.
Qed.
Lemma cw_Zsh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 -> framefree st lo hi ->
  disjoint_from W (SH lo) (SH hi - SH lo).
Proof. intros lo hi H0 H1 H2 AL HF. eapply zone_sh; eauto. intros F k Hin. exact (framefree_sh st WF lo hi HF F k Hin). Qed.

Lemma cw_fs : WOK_fs st W.
Proof.
  (nelimp (fs_range st WF) 3%nat; intros F1 F2 F3). unfold KHIGHMEM_BEG in F1.
  pose proof (loose_blockfree st WF _ _ (wb_fs_loose st (wf_base_ok st WF))) as FB.
  pose proof (oclr_of_ablk _ _ F1) as FO.
  assert (HDR : forall a sz, 0 <= sz -> st_fs st <= a -> a + sz <= st_fs st + FS_FRAMES_OFF -> disjoint_from W a sz).
  { intros a sz Hz Ha Hs. eapply zone_heap; eauto.
    - apply (oclr_sub _ _ _ _ FO); unfold FS_FRAMES_OFF, FS_TOTAL in *; lia.
    - unfold FS_FRAMES_OFF, FS_TOTAL, CEIL in *. lia.
    - intros A n HA. destruct (blockfree_lb st WF (st_fs st) (st_fs st + FS_TOTAL) FB A n HA); unfold FS_FRAMES_OFF, FS_TOTAL in *; lia.
    - intros F k HF. (nelimp (frame_range st WF F k HF) 3%nat; intros _ X _). left. lia. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply HDR; unfold FS_FRAMES_OFF; lia.
  - apply HDR; unfold FS_FRAMES_OFF; lia.
  - apply HDR; unfold FS_FRAMES_OFF; lia.
  - intros k pos Hk Hpos. pose proof (flags_ok k Hk) as [O1 O2]. apply HDR; unfold fflag_addr, FS_FRAMES_OFF; lia.
  - intros F k Hin.
    (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X Y AL). destruct (fsz_12 k Hk) as (FZ & _).
    assert (K2 : 128 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    eapply zone_heap; eauto.
    + apply (oclr_sub _ _ _ _ FO); unfold FS_FRAMES_OFF, FS_TOTAL in *; lia.
    + unfold FS_TOTAL, CEIL in *. lia.
    + intros A n HA. destruct (blockfree_lb st WF (st_fs st) (st_fs st + FS_TOTAL) FB A n HA); unfold FS_FRAMES_OFF in *; lia.
    + intros F' k' HF'. destruct (Z.eq_dec F F') as [<-|NEQ].
      * assert (k' = k).
        { pose proof (wff_nodup st (wf_fs_ok st WF)) as ND.
          pose proof (nodup_map_inj fst _ (F, k) (F, k') ND Hin HF' eq_refl) as E. congruence. }
        subst k'. right. lia.
      * destruct (frames_disj st WF F k F' k' Hin HF' NEQ); [left; lia| right]. pose proof (frame_range st WF F' k' HF') as (Hk' & _).
        destruct (fsz_12 k' Hk') as (FZ' & _). assert (128 <= fsz k') by (rewrite FZ'; destruct Hk' as [-> | ->]; cbn; lia). lia.
Qed.

Theorem cw_all : WOK_all st W.
Proof.
  pose proof cw_Zimg as ZI. pose proof cw_Zheap' as ZH. pose proof cw_Zsh as ZS.
  unfold WOK_all.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
    first [ exact cw_fs
          | eapply W_link | eapply W_consts | eapply W_alloc | eapply W_rinfo | eapply W_regions | eapply W_avail
          | eapply W_cache | eapply W_thread | eapply W_live | eapply W_quar | eapply W_batches | eapply W_ptrarr
          | eapply W_depot | eapply W_ia | eapply W_lowshadow ]; eauto.
Qed.

Theorem RTREP_frame : RTREP st m -> RTREP st m'.
Proof. intros HR. eapply RTREP_transport; [exact WF| exact MU| exact WM| exact HR| exact cw_all]. Qed.
End CW.

Lemma munch_nonempty : forall W m m', munch W m m' -> munch (List.filter (fun iv : Z * Z => fst iv <? snd iv) W) m m'.
Proof.
  intros W m m' H x Hx. apply H. clear H. induction W as [|[lo hi] W IH]; [exact I|].
  cbn in Hx |- *. destruct (Z.ltb_spec lo hi).
  - cbn in Hx. destruct Hx as [H1 H2]. split; [exact H1| apply IH; exact H2].
  - split; [lia| apply IH; exact Hx].
Qed.

Theorem artd_frame : forall sp0 SPB LB LF TRS B m m' mo g W,
  ARTd sp0 SPB LB LF TRS B m mo g -> munch W m m' -> wmono bsegs m m' ->
  Forall (cj_write_ok sp0 SPB LB LF) W -> ARTd sp0 SPB LB LF TRS B m' mo g.
Proof.
  intros sp0 SPB LB LF TRS B m m' mo g W H MU WM FW.
  (nelim H 17%nat; intros st HR WF HM HO HB HG HFR Hsp0 HLB HLF HTRS HQ HB0 HB1 HSPB HSW).
  exists st. split; [| split; [exact WF|]; split; [exact HM|]; split; [exact HO|]; split; [exact HB|];
                      split; [eapply GWIN_mem; eauto|]; repeat (split; [assumption|]); assumption].
  set (W' := List.filter (fun iv : Z * Z => fst iv <? snd iv) W).
  eapply (RTREP_frame st WF sp0 SPB W' m m'); try assumption.
  - rewrite Hsp0. exact HSPB.
  - subst LB LF. unfold W'. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. rewrite Forall_forall in FW. apply FW. exact Hiv.
  - unfold W'. apply Forall_forall. intros [lo hi] Hiv. apply filter_In in Hiv as [_ Hb]. cbn in Hb |- *. apply Z.ltb_lt. exact Hb.
  - apply munch_nonempty. exact MU.
Qed.

(* [comment removed for export] *)
Theorem artd_frames_disjoint : forall sp0 SPB LB LF TRS B m mo g F1 k1 F2 k2,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (F1, k1) LF -> In (F2, k2) LF -> F1 <> F2 ->
  F1 + fsz k1 <= F2 \/ F2 + fsz k2 <= F1.
Proof.
  intros sp0 SPB LB LF TRS B m mo g F1 k1 F2 k2 (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & _) H1 H2 NE.
  subst LF. exact (frames_disj st WF F1 k1 F2 k2 H1 H2 NE).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HIGH.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable W : list (Z * Z).
Hypothesis HW : Forall (fun iv : Z * Z => CEIL <= fst iv) W.

Lemma high_disjoint : forall a sz, a + sz <= CEIL -> disjoint_from W a sz.
Proof.
  intros a sz H. induction W as [|[lo hi] W' IH]; [exact I|]. inversion HW; subst. cbn [fst snd] in *. cbn.
  split; [lia| apply IH; assumption].
Qed.

Lemma high_Zimg : forall a sz lo hi, In (lo, hi) ART_STATIC -> lo <= a -> a + sz <= hi -> 0 < sz -> disjoint_from W a sz.
Proof. intros a sz lo hi HS Ha Hs Hp. (nelimp (static_facts lo hi HS) 3%nat; intros _ S2 _). apply high_disjoint. unfold AIMG_HI, CEIL in *. lia. Qed.
Lemma high_Zheap' : forall lo hi, oclr lo hi -> hi <= CEIL ->
  (forall A n, In (A, n) (st_lb st) -> hi <= A \/ A + n <= lo) -> framefree st lo hi -> disjoint_from W lo (hi - lo).
Proof. intros. apply high_disjoint. lia. Qed.
Lemma high_Zsh : forall lo hi, 0 <= lo -> lo <= hi -> hi <= CEIL -> lo mod 8 = 0 -> framefree st lo hi ->
  disjoint_from W (SH lo) (SH hi - SH lo).
Proof. intros lo hi H0 H1 H2 _ _. apply high_disjoint. pose proof (rt_SH_mono hi CEIL H2) as M. rewrite SH_CEIL in M. unfold CEIL. lia. Qed.

Lemma high_fs : WOK_fs st W.
Proof.
  (nelimp (fs_range st WF) 3%nat; intros F1 F2 F3).
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply high_disjoint. unfold FS_TOTAL in *. lia.
  - apply high_disjoint. unfold FS_TOTAL in *. lia.
  - apply high_disjoint. unfold FS_TOTAL in *. lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply high_disjoint. unfold fflag_addr, FS_TOTAL in *. lia.
  - intros F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X Y _). apply high_disjoint. lia.
Qed.

Theorem wok_all_high : WOK_all st W.
Proof.
  pose proof high_Zimg as ZI. pose proof high_Zheap' as ZH. pose proof high_Zsh as ZS.
  unfold WOK_all.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end;
    first [ exact high_fs
          | eapply W_link | eapply W_consts | eapply W_alloc | eapply W_rinfo | eapply W_regions | eapply W_avail
          | eapply W_cache | eapply W_thread | eapply W_live | eapply W_quar | eapply W_batches | eapply W_ptrarr
          | eapply W_depot | eapply W_ia | eapply W_lowshadow ]; eauto.
Qed.

(* [comment removed for export] *)
Theorem RTREP_stack_frame : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m -> RTREP st m'.
Proof. intros m m' MU WM HR. eapply RTREP_transport; [exact WF| exact MU| exact WM| exact HR| exact wok_all_high]. Qed.
End HIGH.


End CeilWrap.
