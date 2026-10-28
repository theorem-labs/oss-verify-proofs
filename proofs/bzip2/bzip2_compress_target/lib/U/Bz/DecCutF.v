(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record jk := JK {
  j_p1 : list byte; j_p2 : list byte; j_p3 : list byte;   (* [comment removed for export] *)
  j_s1 : list byte; j_s2 : list byte;                     (* [comment removed for export] *)
  j_til : word; j_tih : word; j_q1 : list byte;           (* [comment removed for export] *)
  j_tol : word; j_toh : word; j_q2 : list byte;           (* [comment removed for export] *)
  j_bzalloc : word; j_bzfree : word; j_opaque : word }.

Definition jk_set_t (J : jk) (til tih : word) : jk :=
  JK (j_p1 J) (j_p2 J) (j_p3 J) (j_s1 J) (j_s2 J) til tih (j_q1 J) (j_tol J) (j_toh J) (j_q2 J) (j_bzalloc J) (j_bzfree J) (j_opaque J).
Definition jk_set_s (J : jk) (s1 s2 : list byte) : jk :=
  JK (j_p1 J) (j_p2 J) (j_p3 J) s1 s2 (j_til J) (j_tih J) (j_q1 J) (j_tol J) (j_toh J) (j_q2 J) (j_bzalloc J) (j_bzfree J) (j_opaque J).

Definition jk_wf (J : jk) : Prop :=
  length (j_p1 J) = 3%nat /\ length (j_p2 J) = 3%nat /\ length (j_p3 J) = 3%nat /\
  length (j_s1 J) = 44%nat /\ length (j_s2 J) = 60%nat /\ length (j_q1 J) = 4%nat /\ length (j_q2 J) = 4%nat.

(* [comment removed for export] *)
Definition jk_static (b0 : bzs) (J : jk) : Prop :=
  j_q1 J = bs_q1 b0 /\ j_q2 J = bs_q2 b0 /\ j_tol J = bs_tol b0 /\ j_toh J = bs_toh b0 /\
  j_bzalloc J = bs_bzalloc b0 /\ j_bzfree J = bs_bzfree b0 /\ j_opaque J = bs_opaque b0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zh16 (a : zarr) (nbytes : Z) : list byte :=
  tab (fun k => Z_to_bv 8 (zget a (k / 2) / 2 ^ (8 * (k mod 2)))) nbytes.

Definition hd_of (cx : bctx) (J : jk) (d : dst) : dsh :=
  DSH (b_strm cx) (d_state d) (Z_to_bv 8 (d_out_ch d)) (j_p1 J) (d_out_len d) (Z_to_bv 8 (d_rand d)) (j_p2 J)
      (d_rNToGo d) (d_rTPos d) (d_bsBuff d) (d_bsLive d) (d_bs100k d) (Z_to_bv 8 (d_small d)) (j_p3 J)
      (d_blockNo d) (d_verb d) (d_origPtr d) (Z_to_bv 64 (d_tPos d)) (Z_to_bv 64 (d_k0 d)).

Definition mid_of (cx : bctx) (d : dst) : dsm :=
  DSM (b_tt cx) (b_ll16 cx) (b_ll4 cx)
      (Z_to_bv 64 (d_sbcrc d)) (Z_to_bv 64 (d_sccrc d)) (Z_to_bv 64 (d_cbcrc d)) (Z_to_bv 64 (d_cccrc d)) (d_nInUse d).

Definition r_of (d : dst) : drest :=
  DREST (zw32 (d_unzftab d) 256) (zw32 (d_cftabCopy d) 257) (zb8 (d_inUse d) 256) (zb8 (d_inUse16 d) 16)
        (zb8 (d_s2u d) 256) (zb8 (d_mtfa d) 4096) (zw32 (d_mtfbase d) 16) (zb8 (d_sel d) 18002)
        (zb8 (d_selMtf d) 18002) (zb8 (d_len d) 1548) (zw32 (d_limit d) 1548) (zw32 (d_base d) 1548)
        (zw32 (d_perm d) 1548) (zw32 (d_minLens d) 6).

Definition bs_of (cx : bctx) (J : jk) (s : dstrm) : bzs :=
  BZS (b_src cx) (b_len cx) (Z.of_nat (length (s_in s))) (j_til J) (j_tih J) (j_q1 J)
      (b_dst cx) (b_dlen cx) (s_avail_out s) (j_tol J) (j_toh J) (j_q2 J)
      (b_s cx) (j_bzalloc J) (j_bzfree J) (j_opaque J).

Definition blk_of (cx : bctx) (d : dst) : blk :=
  if (b_small cx =? 0)%Z then BlkF (zw32 (d_tt d) (100000 * b_n cx))
  else BlkS (zh16 (d_ll16 d) (200000 * b_n cx)) (zb8 (d_ll4 d) (50000 * b_n cx)).

Definition dvF (cx : bctx) (J : jk) (d : dst) (s : dstrm) : dv :=
  DV (hd_of cx J d) (d_nused d) (zw32 (d_cftab d) 257) (mid_of cx d) (j_s1 J) (sv_nblock (d_sv d)) (j_s2 J)
     (r_of d) (bs_of cx J s) (blk_of cx d).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition drep (d : dst) : Prop :=
  (forall i, 0 <= zget (d_tt d) i < 2^32)%Z /\
  (forall i, 0 <= zget (d_ll16 d) i < 2^16)%Z /\
  (forall i, 0 <= zget (d_ll4 d) i < 256)%Z /\
  (forall i, 0 <= zget (d_s2u d) i < 256)%Z /\
  (0 <= d_sccrc d < 2^32)%Z /\   (* [comment removed for export] *)
  (forall i, 0 <= zget (d_mtfa d) i < 256)%Z.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_rel (payload : list byte) (s : dstrm) : Prop :=
  exists k, s_in s = map bv_unsigned (skipn k payload).

Definition dpureF (cx : bctx) (b0 : bzs) (payload : list byte) (J : jk) (d : dst) (s : dstrm) : Prop :=
  jk_wf J /\ jk_static b0 J /\
  d_bs100k d = b_n cx /\ d_small d = b_small cx /\ d_verb d = 0%Z /\
  s_avail_out s = bs_av b0 /\ (Z.of_nat (length (s_in s)) <= bs_ai b0)%Z /\
  in_rel payload s /\
  (0 <= d_bsBuff d < 2^32)%Z /\ (0 <= d_bsLive d <= 32)%Z /\
  (0 <= d_blockNo d)%Z /\ (48 * d_blockNo d <= 8 * (bs_len b0 - Z.of_nat (length (s_in s))) - d_bsLive d)%Z /\
  (0 <= sv_nblock (d_sv d) <= 900000)%Z /\ (0 <= d_nused d)%Z /\
  drep d.

Section DpureF.
  Variables (cx : bctx) (b0 : bzs) (payload : list byte) (J : jk) (d : dst) (s : dstrm).
  Hypothesis DP : dpureF cx b0 payload J d s.
  Lemma dpureF_jwf : jk_wf J. Proof. exact (proj1 DP). Qed.
  Lemma dpureF_static : jk_static b0 J. Proof. exact (proj1 (proj2 DP)). Qed.
  Lemma dpureF_n : d_bs100k d = b_n cx. Proof. exact (proj1 (proj2 (proj2 DP))). Qed.
  Lemma dpureF_small : d_small d = b_small cx. Proof. exact (proj1 (proj2 (proj2 (proj2 DP)))). Qed.
  Lemma dpureF_verb : d_verb d = 0%Z. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 DP))))). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dpureF_in : in_rel payload s. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_bb : (0 <= d_bsBuff d < 2^32)%Z. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_bl : (0 <= d_bsLive d <= 32)%Z. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_cbn : (0 <= d_blockNo d)%Z /\ (48 * d_blockNo d <= 8 * (bs_len b0 - Z.of_nat (length (s_in s))) - d_bsLive d)%Z.
  Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_snb : (0 <= sv_nblock (d_sv d) <= 900000)%Z. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_nbu : (0 <= d_nused d)%Z. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
  Lemma dpureF_rep : drep d. Proof. pose proof DP as X; unfold dpureF in X; tauto. Qed.
End DpureF.

(* [comment removed for export] *)
Lemma dpureF_frame : forall cx b0 payload J J' d d' s s',
  dpureF cx b0 payload J d s ->
  jk_wf J' -> jk_static b0 J' ->
  d_bs100k d' = d_bs100k d -> d_small d' = d_small d -> d_verb d' = d_verb d ->
  s_avail_out s' = s_avail_out s -> in_rel payload s' -> (length (s_in s') <= length (s_in s))%nat ->
  (0 <= d_bsBuff d' < 2^32)%Z -> (0 <= d_bsLive d' <= 32)%Z ->
  (0 <= d_blockNo d')%Z ->
  (48 * d_blockNo d' <= 8 * (bs_len b0 - Z.of_nat (length (s_in s'))) - d_bsLive d')%Z ->
  (0 <= sv_nblock (d_sv d') <= 900000)%Z -> (0 <= d_nused d')%Z ->
  drep d' ->
  dpureF cx b0 payload J' d' s'.
Proof.
  intros cx b0 payload J J' d d' s s' DP WF ST E1 E2 E3 E4 IR LEN BB BL CB0 CB SNB NBU REP.
  unfold dpureF in *. decompose [and] DP. rewrite E1, E2, E3, E4.
  repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma in_rel_tail : forall payload s s' b rest,
  in_rel payload s -> s_in s = b :: rest -> s_in s' = rest ->
  in_rel payload s'.
Proof.
  intros payload s s' b rest [k E] Hs Hs'. exists (S k). rewrite Hs'.
  rewrite Hs in E. destruct (skipn k payload) as [|y t] eqn:ES; [discriminate|].
  cbn [map] in E. injection E as E1 E2. rewrite E2. f_equal.
  replace (S k) with (1 + k)%nat by lia. rewrite <- skipn_skipn, ES. reflexivity.
Qed.

Lemma in_rel_head : forall payload s b rest,
  in_rel payload s -> s_in s = b :: rest ->
  exists b8, nth_error payload (length payload - length (s_in s)) = Some b8 /\ b = bv_unsigned b8.
Proof.
  intros payload s b rest [k E] Hs. rewrite Hs in E |- *.
  destruct (skipn k payload) as [|y t] eqn:ES; [discriminate|].
  cbn [map] in E. injection E as E1 E2. exists y. split; [|exact E1].
  pose proof (f_equal (@length _) ES) as L. rewrite length_skipn in L. cbn [length] in L |- *.
  rewrite E2, length_map.
  replace (length payload - S (length t))%nat with (k + 0)%nat by lia.
  rewrite <- nth_error_skipn, ES. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_rel_length : forall payload s, in_rel payload s -> (length (s_in s) <= length payload)%nat.
Proof. intros payload s [k E]. rewrite E, length_map, length_skipn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dout_ok (d : dst) : Prop :=
  d_out_len d = 0%Z /\
  (0 <= d_tPos d < 4294967296)%Z /\
  ((d_nused d = 1%Z /\ (0 <= d_k0 d < 256)%Z) \/ (d_nused d = 0%Z /\ (100000 * d_bs100k d <= d_tPos d)%Z)) /\
  (1 <= sv_nblock (d_sv d))%Z /\
  d_cbcrc d = 4294967295%Z /\
  (0 <= d_sbcrc d < 4294967296)%Z /\
  (d_rand d = 0%Z \/ d_rand d = 1%Z) /\
  (d_rand d = 1%Z -> (0 <= d_rNToGo d < 2147483648)%Z /\ (0 <= d_rTPos d < 512)%Z) /\
  (d_small d <> 0%Z -> forall i, (0 <= i < 257)%Z -> (0 <= zget (d_cftab d) i <= sv_nblock (d_sv d))%Z) /\
  d_out_ch d = 0%Z /\
  (1 <= d_bs100k d <= 9)%Z.   (* [comment removed for export] *)
Definition dpost14 (d : dst) : Prop := d_state d = BZ_X_OUTPUT -> dout_ok d.
Lemma dpost14_ne : forall d, d_state d <> BZ_X_OUTPUT -> dpost14 d.
Proof. intros d H E. exfalso. exact (H E). Qed.

Section WithImg.
  Variable I : dimg.
  Let segs := di_segs I.

  Definition FPOST14 (A : act14) (R : Z * dst * dstrm) : machine_state -> Prop :=
    fun ms' =>
      let '(rv, d', s') := R in
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (J' : jk),
        ms' = MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                      (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                 (a_F A) (ret_pc (a_ra A)) (a_fc A) None m' (seg_rom segs)
        /\ munch (W14 I (a_cx A) (bv_unsigned (a_sp A))) (a_m0 A) m' /\ wmono segs (a_m0 A) m' /\ mem_inv segs m'
        /\ dmem I (a_cx A) (a_g1 A) (a_sv A) (a_payload A) m' (dvF (a_cx A) J' d' s')
        /\ stk segs m' (a_lo A) (bv_unsigned (a_sp A))
        /\ dpureF (a_cx A) (a_b0 A) (a_payload A) J' d' s'
        /\ dpost14 d'.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dmemF_intro : forall cx g1 sv payload m J d s,
    rw_cells segs m (b_s cx) (HEAD_CELLS (hd_of cx J d)) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 (d_nused d))] ->
    u32arr segs m (b_s cx + 1096) (zw32 (d_cftab d) 257) ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS (mid_of cx d)) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS (j_s1 J) (sv_nblock (d_sv d)) (j_s2 J)) ->
    drest_at segs m (b_s cx) (r_of d) ->
    rw_cells segs m (b_strm cx) (STRM_CELLS (bs_of cx J s)) ->
    blk_at segs m cx (blk_of cx d) ->
    bytes_at segs m (b_src cx) payload ->
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    rw_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    dmem I cx g1 sv payload m (dvF cx J d s).
  Proof. intros. unfold dmem, dvF. cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k]. repeat (split; [assumption|]). assumption. Qed.
End WithImg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zh16_length_nat : forall a n, length (zh16 a n) = Z.to_nat n.
Proof. intros. unfold zh16. apply tab_length_nat. Qed.
Lemma zh16_length : forall a n, (0 <= n)%Z -> Z.of_nat (length (zh16 a n)) = n.
Proof. intros. unfold zh16. apply tab_length. assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma act_linF : forall fr A J d s, act_ok fr A -> dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
  let cx := a_cx A in
  (0 < b_s cx /\ b_s cx + 64144 <= alloc_ceiling /\
    0 < b_src cx /\ 0 <= b_len cx < 134217728 /\ b_src cx + b_len cx <= alloc_ceiling /\
    0 < b_dst cx /\ 0 <= b_dlen cx /\ b_dlen cx < 134217728 /\ b_dst cx + b_dlen cx <= alloc_ceiling /\
    alloc_ceiling <= b_sp cx /\ b_sp cx + 176 <= 140737488355328 /\ b_strm cx = b_sp cx /\
    0 <= b_n cx <= 9 /\ 1 <= b_n cx /\
    alloc_ceiling <= a_lo A /\ a_lo A <= a_usp A - 1024 /\ a_usp A < 18446744073709551616 /\ a_usp A <= b_strm cx /\
    Z.of_nat (length (a_payload A)) = b_len cx /\
    length (j_p1 J) = 3%nat /\ length (j_p2 J) = 3%nat /\ length (j_p3 J) = 3%nat /\
    length (j_s1 J) = 44%nat /\ length (j_s2 J) = 60%nat /\ length (j_q1 J) = 4%nat /\ length (j_q2 J) = 4%nat /\
    0 <= sv_nblock (d_sv d) <= 900000 /\ 0 <= d_nused d /\
    0 <= Z.of_nat (length (s_in s)) <= bs_ai (a_b0 A) /\ bs_ai (a_b0 A) <= b_len cx /\
    (length (s_in s) <= length (a_payload A))%nat /\
    0 <= s_avail_out s <= b_dlen cx /\
    d_small d = b_small cx /\ (b_small cx = 0 \/ b_small cx = 1) /\
    d_bs100k d = b_n cx /\ d_verb d = 0 /\
    0 <= d_bsBuff d < 2^32 /\ 0 <= d_bsLive d <= 32 /\
    0 <= d_blockNo d /\ 48 * d_blockNo d <= 8 * (b_len cx - Z.of_nat (length (s_in s))) - d_bsLive d /\
    0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.
Proof.
  intros fr A J d s AOK DP. cbv zeta.
  cps_destruct AOK as (CTX & LO1 & LO2 & USP & ST14 & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & N1 & QS & QSRC & QLEN & QDST & QDLEN & USTRM & NZF & NZS & SM01).
  cps_destruct CTX as (LIN & AL & SEP).
  unfold ctx_lin in LIN. cbv zeta in LIN. bz_ceil; unfold IMG_HI_MAX, DSTATE_SIZE, CEILING, STACK_TOP in LIN.
  bz_ceil; unfold CEILING in LO2. unfold D14 in LO1.
  pose proof (in_rel_length _ _ (dpureF_in _ _ _ _ _ _ DP)) as IRL.
  unfold dpureF, jk_wf, jk_static, drep in DP. unfold bzs_wf in BWF0.
  decompose [and] DP. decompose [and] LIN. decompose [and] BWF0.
  rewrite <- QLEN, <- QDLEN in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
End ACeilS1.

(* [comment removed for export] *)
#[export] Hint Rewrite zb8_length_nat zw32_length_nat zh16_length_nat : dj_len.

(* [comment removed for export] *)
Notation JK_ := (JK _ _ _ _ _ _ _ _ _ _ _ _ _ _) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac dvF_cbn_in H :=
  cbn [dvF hd_of mid_of bs_of dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque
       j_p1 j_p2 j_p3 j_s1 j_s2 j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_set_t jk_set_s] in H.
Ltac dvF_cbn :=
  cbn [dvF hd_of mid_of bs_of dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque
       j_p1 j_p2 j_p3 j_s1 j_s2 j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_set_t jk_set_s].

(* [comment removed for export] *)
Ltac dmodel_cbn_in H :=
  cbn [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
       d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
       d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
       d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
       d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
       d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
       d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
       d_set_base d_set_perm d_set_minLens d_set_sv gbst
       sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock
       sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
       sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos
       sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj
       sv_set_gSel sv_set_gMinlen sv_set_gPtr
       s_in s_out s_avail_out s_tin s_tout s_set_in s_set_out s_set_avail_out s_set_tin s_set_tout] in H.
Ltac dmodel_cbn :=
  cbn [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
       d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
       d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
       d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
       d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
       d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
       d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
       d_set_base d_set_perm d_set_minLens d_set_sv gbst
       sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock
       sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
       sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos
       sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj
       sv_set_gSel sv_set_gMinlen sv_set_gPtr
       s_in s_out s_avail_out s_tin s_tout s_set_in s_set_out s_set_avail_out s_set_tin s_set_tout].

(* [comment removed for export] *)
Ltac open_dmemF DM :=
  unfold dmem in DM; dvF_cbn_in DM;
  cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).

(* [comment removed for export] *)
Section CellsEq. Context {ACEIL___ : ACeil}.
Lemma rw_cells_cells_eq : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' H <-. exact H. Qed.
End CellsEq.
Ltac unset_Z := repeat match goal with v := ?b : Z |- _ => cbv delta [v] in *; clear v end.
(* [comment removed for export] *)
Lemma lor_mul256_byte : forall a b, (0 <= a)%Z -> (0 <= b < 256)%Z -> Z.lor (a * 256) b = (a * 256 + b)%Z.
Proof.
  intros a b Ha Hb. rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8) as [L|L].
    + replace (a * 256)%Z with (a * 2 ^ 8)%Z by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 b < 8)%Z; [|lia]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n 8) as [L|L].
    + replace (a * 256)%Z with (a * 2 ^ 8)%Z by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia |].
      assert (Z.log2 b < 8)%Z; [|lia]. destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Ltac zleaf_norm :=
  repeat match goal with
         | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
         | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
         end;
  zb_fold_lits; rewrite ?Z.mul_0_l, ?Z.lor_0_l;
  repeat match goal with
         | |- context [Z.lor (?a * 256)%Z ?b] => rewrite (lor_mul256_byte a b) by (unfold u32; lia)
         end;
  first [ reflexivity | unfold u32; lia ].
Ltac cells_eq :=
  repeat first [ reflexivity
               | lazymatch goal with
                 | |- @eq Z _ _ => solve [unset_Z; first [lia | zleaf_norm]]
                 | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                 | |- @cons _ _ _ = @cons _ _ _ => f_equal
                 | |- C4 _ = C4 _ => f_equal
                 | |- C8 _ = C8 _ => f_equal
                 | |- C1 _ = C1 _ => f_equal
                 | |- CB _ _ = CB _ _ => f_equal
                 end ].
Ltac exact_cells H := first [ exact H | eapply (rw_cells_cells_eq _ _ _ _ _ H); solve [cells_eq] ].

(* [comment removed for export] *)
Ltac dr_pieceF :=
  lazymatch goal with
  | |- u8arr ?sg ?m ?A _ => match goal with H : u8arr sg m A _ |- _ => exact H end
  | |- u32arr ?sg ?m ?A _ => match goal with H : u32arr sg m A _ |- _ => exact H end
  | |- Z.of_nat (length _) = _ => rewrite ?zb8_length, ?zw32_length by lia; reflexivity
  end.
Ltac dr_closeF :=
  unfold drest_at; cbn [r_of r_unz r_cfc r_inUse r_in16 r_s2u r_mtfa r_mtfb r_sel r_selm r_len r_lim r_base r_perm r_minl
                        di_segs di_got di_stderrp di_crc di_rnums di_dec]; dmodel_cbn;
  repeat match goal with |- _ /\ _ => split end; dr_pieceF.

(* [comment removed for export] *)
Ltac close_dmemF :=
  lazymatch goal with
  | |- dmem _ ?cx _ _ _ ?m _ =>
      eapply dmemF_intro; dvF_cbn; try unfold r_of; try unfold blk_of; dmodel_cbn;
      [ match goal with H : rw_cells _ m (b_s cx) _ |- _ => exact_cells H end
      | match goal with H : rw_cells _ m (b_s cx + 1092)%Z _ |- _ => exact_cells H end
      | match goal with H : u32arr _ m (b_s cx + 1096)%Z _ |- _ => exact H end
      | match goal with H : rw_cells _ m (b_s cx + 3152)%Z _ |- _ => exact_cells H end
      | match goal with H : rw_cells _ m (b_s cx + 64036)%Z _ |- _ => exact_cells H end
      | (* [comment removed for export] *)
        first [ match goal with H : drest_at _ m _ ?r1 |- drest_at _ _ _ ?r2 =>
                  first [ constr_eq r1 r2; exact H | idtac "close_dmemF: DR not syntactic (slow Qed?)"; exact H ] end
              | dr_closeF ]
      | match goal with H : rw_cells _ m (b_strm cx) _ |- _ => exact_cells H end
      | match goal with H : blk_at _ m _ ?k1 |- blk_at _ _ _ ?k2 =>
          first [ constr_eq k1 k2; exact H | idtac "close_dmemF: BLK not syntactic (slow Qed?)"; exact H ] end
      | match goal with H : bytes_at _ m (b_src cx) _ |- _ => exact H end
      | match goal with H : rw_cells _ m _ [C8 _; C8 _; C8 _; C8 _; C8 _] |- _ => exact H end
      | match goal with H : rw_cells _ m _ [C8 _] |- _ => exact H end
      | match goal with H : u32arr _ m _ rnums_words |- _ => exact H end ]
  end.
