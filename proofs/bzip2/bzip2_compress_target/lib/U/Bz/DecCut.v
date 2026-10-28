(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts.
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
Record dv := DV {
  dv_h : dsh;            (* [comment removed for export] *)
  dv_nbu : Z;            (* [comment removed for export] *)
  dv_cf : list word;     (* [comment removed for export] *)
  dv_d : dsm;            (* [comment removed for export] *)
  dv_j1 : list byte; dv_snb : Z; dv_j2 : list byte;   (* [comment removed for export] *)
  dv_r : drest;          (* [comment removed for export] *)
  dv_b : bzs;            (* [comment removed for export] *)
  dv_k : blk             (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition bupd (b : bzs) (ai : Z) (til tih : word) : bzs :=
  BZS (bs_src b) (bs_len b) ai til tih (bs_q1 b) (bs_dst b) (bs_dlen b) (bs_av b)
      (bs_tol b) (bs_toh b) (bs_q2 b) (bs_S b) (bs_bzalloc b) (bs_bzfree b) (bs_opaque b).

Lemma bupd_id : forall b, bupd b (bs_ai b) (bs_til b) (bs_tih b) = b.
Proof. intros []; reflexivity. Qed.
Lemma bupd_bupd : forall b ai til tih ai' til' tih', bupd (bupd b ai til tih) ai' til' tih' = bupd b ai' til' tih'.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Definition bfields (b0 b : bzs) : Prop :=
  bs_src b = bs_src b0 /\ bs_len b = bs_len b0 /\ bs_q1 b = bs_q1 b0 /\ bs_dst b = bs_dst b0 /\ bs_dlen b = bs_dlen b0 /\
  bs_av b = bs_av b0 /\ bs_tol b = bs_tol b0 /\ bs_toh b = bs_toh b0 /\ bs_q2 b = bs_q2 b0 /\ bs_S b = bs_S b0 /\
  bs_bzalloc b = bs_bzalloc b0 /\ bs_bzfree b = bs_bzfree b0 /\ bs_opaque b = bs_opaque b0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition consumed (b : bzs) (h : dsh) : Z := (8 * (bs_len b - bs_ai b) - sh_bsLive h)%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition w1_inv14 (vw : Z * Z * Z * Z) (b : bzs) (r : drest) (cf : list word) : Prop :=
  let '(bsBuff, bsLive, cbn, origPtr) := vw in
  (48 * cbn <= 8 * (bs_len b - bs_ai b) - bsLive)%Z.

Section WithImg.
  Variable I : dimg.
  Let segs := di_segs I.

  Definition dmem (cx : bctx) (g1 sv : word) (payload : list byte) (m : word -> option byte) (v : dv) : Prop :=
    rw_cells segs m (b_s cx) (HEAD_CELLS (dv_h v)) /\
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 (dv_nbu v))] /\
    u32arr segs m (b_s cx + 1096) (dv_cf v) /\
    rw_cells segs m (b_s cx + 3152) (MID_CELLS (dv_d v)) /\
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS (dv_j1 v) (dv_snb v) (dv_j2 v)) /\
    drest_at segs m (b_s cx) (dv_r v) /\
    rw_cells segs m (b_strm cx) (STRM_CELLS (dv_b v)) /\
    blk_at segs m cx (dv_k v) /\
    bytes_at segs m (b_src cx) payload /\
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] /\
    rw_cells segs m (di_stderrp I) [C8 sv] /\
    u32arr segs m (di_rnums I) rnums_words.

  Lemma dmem_intro : forall cx g1 sv payload m h nbu cf d j1 snb j2 r b k,
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS d) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS b) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    rw_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    dmem cx g1 sv payload m (DV h nbu cf d j1 snb j2 r b k).
  Proof. intros. unfold dmem. cbn. repeat (split; [assumption|]). assumption. Qed.


  (* [comment removed for export] *)
  Lemma dmem_introF : forall cx g1 sv payload m
      x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      nbu cf y1 y2 y3 y4 y5 y6 y7 y8 j1 snb j2 r
      z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 k,
    let h := DSH x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 in
    let d := DSM y1 y2 y3 y4 y5 y6 y7 y8 in
    let b := BZS z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 in
    rw_cells segs m (b_s cx) (HEAD_CELLS h) ->
    rw_cells segs m (b_s cx + 1092) [C4 (Z_to_bv 64 nbu)] ->
    u32arr segs m (b_s cx + 1096) cf ->
    rw_cells segs m (b_s cx + 3152) (MID_CELLS d) ->
    rw_cells segs m (b_s cx + 64036) (SAVE_CELLS j1 snb j2) ->
    drest_at segs m (b_s cx) r ->
    rw_cells segs m (b_strm cx) (STRM_CELLS b) ->
    blk_at segs m cx k ->
    bytes_at segs m (b_src cx) payload ->
    rw_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    rw_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    dmem cx g1 sv payload m (DV h nbu cf d j1 snb j2 r b k).
  Proof.
    intros. cbv zeta in *. unfold dmem. cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k].
    repeat (split; [assumption|]). assumption.
  Qed.
End WithImg.

(* [comment removed for export] *)
Definition blk_range (cx : bctx) (A n : Z) : Prop :=
  (b_small cx = 0%Z /\ A = b_tt cx /\ n = 400000 * b_n cx)%Z \/
  (b_small cx = 1%Z /\ ((A = b_ll16 cx /\ n = 200000 * b_n cx) \/ (A = b_ll4 cx /\ n = 50000 * b_n cx)))%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dpure (cx : bctx) (h0 : dsh) (b0 : bzs) (payload : list byte) (v : dv) : Prop :=
  let h := dv_h v in let b := dv_b v in let d := dv_d v in
  dsh_wf h /\ sh_strm h = sh_strm h0 /\ sh_n h = sh_n h0 /\ sh_small h = sh_small h0 /\ sh_verb h = 0%Z /\
  (1 <= b_n cx <= 9)%Z /\ (0 <= dv_nbu v)%Z /\ length (dv_cf v) = 257%nat /\
  sm_tt d = b_tt cx /\ sm_ll16 d = b_ll16 cx /\ sm_ll4 d = b_ll4 cx /\
  length (dv_j1 v) = 44%nat /\ length (dv_j2 v) = 60%nat /\ (0 <= dv_snb v <= 900000)%Z /\
  bfields b0 b /\ bzs_wf b /\ (0 <= bs_ai b <= bs_ai b0)%Z /\
  Z.of_nat (length payload) = b_len cx /\
  w1_inv14 (w1_view h) b (dv_r v) (dv_cf v).

(* [comment removed for export] *)
Section Dpure.
  Variables (cx : bctx) (h0 : dsh) (b0 : bzs) (payload : list byte) (v : dv).
  Hypothesis DP : dpure cx h0 b0 payload v.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dpure_cf_len : length (dv_cf v) = 257%nat. Proof. pose proof DP as X; unfold dpure in X; cbv zeta in X; tauto. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Dpure.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record act14 := ACT {
  a_ra : word; a_sp : word; a_gp : word; a_tp : word;
  a_s0 : word; a_s1 : word; a_s2 : word; a_s3 : word; a_s4 : word; a_s5 : word;
  a_s6 : word; a_s7 : word; a_s8 : word; a_s9 : word; a_s10 : word; a_s11 : word;
  a_F : bvmap 5 word; a_fc : bv 32;
  a_m0 : word -> option byte;       (* [comment removed for export] *)
  a_cx : bctx; a_h0 : dsh; a_b0 : bzs; a_lo : Z; a_g1 : word; a_sv : word; a_payload : list byte
}.

Definition POST14 (I : dimg) (A : act14) : machine_state -> Prop :=
  decompress14_post I w1_inv14 (a_ra A) (a_sp A) (a_gp A) (a_tp A) (a_s0 A) (a_s1 A) (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A)
    (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) (a_F A) (a_fc A)
    (a_cx A) (a_h0 A) (a_b0 A) (a_lo A) (a_g1 A) (a_sv A) (a_payload A) (a_m0 A).
End ACeilS1.


Notation a_usp A := (bv_unsigned (a_sp A)).
Notation a_S A := (b_s (a_cx A)).
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition act_ok (frame : Z) (A : act14) : Prop :=
  ctx_ok (a_cx A) /\ (a_lo A <= a_usp A - D14)%Z /\ (CEILING <= a_lo A)%Z /\ (a_usp A < 2^64)%Z /\
  sh_state (a_h0 A) = 14%Z /\ dsh_wf (a_h0 A) /\ bzs_wf (a_b0 A) /\
  Z.of_nat (length (a_payload A)) = b_len (a_cx A) /\
  sh_strm (a_h0 A) = b_strm (a_cx A) /\ sh_n (a_h0 A) = b_n (a_cx A) /\
  bv_unsigned (sh_small (a_h0 A)) = b_small (a_cx A) /\ (1 <= b_n (a_cx A))%Z /\
  bs_S (a_b0 A) = b_s (a_cx A) /\ bs_src (a_b0 A) = b_src (a_cx A) /\ bs_len (a_b0 A) = b_len (a_cx A) /\
  bs_dst (a_b0 A) = b_dst (a_cx A) /\ bs_dlen (a_b0 A) = b_dlen (a_cx A) /\
  (a_usp A <= b_strm (a_cx A))%Z /\
  (b_small (a_cx A) = 0%Z -> b_tt (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 1%Z -> b_ll16 (a_cx A) <> 0%Z /\ b_ll4 (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 0%Z \/ b_small (a_cx A) = 1%Z).

(* [comment removed for export] *)
Lemma act_lin : forall fr A v, act_ok fr A -> dpure (a_cx A) (a_h0 A) (a_b0 A) (a_payload A) v ->
  let cx := a_cx A in
  (0 < b_s cx /\ b_s cx + 64144 <= alloc_ceiling /\
    0 < b_src cx /\ 0 <= b_len cx < 134217728 /\ b_src cx + b_len cx <= alloc_ceiling /\
    0 < b_dst cx /\ 0 <= b_dlen cx /\ b_dlen cx < 134217728 /\ b_dst cx + b_dlen cx <= alloc_ceiling /\
    alloc_ceiling <= b_sp cx /\ b_sp cx + 176 <= 140737488355328 /\ b_strm cx = b_sp cx /\
    0 <= b_n cx <= 9 /\ 1 <= b_n cx /\
    alloc_ceiling <= a_lo A /\ a_lo A <= a_usp A - 1024 /\ a_usp A < 18446744073709551616 /\ a_usp A <= b_strm cx /\
    Z.of_nat (length (a_payload A)) = b_len cx /\
    length (dv_cf v) = 257%nat /\ length (dv_j1 v) = 44%nat /\ length (dv_j2 v) = 60%nat /\
    0 <= dv_snb v <= 900000 /\ 0 <= dv_nbu v /\
    0 <= bs_ai (dv_b v) <= bs_ai (a_b0 A) /\ bs_ai (a_b0 A) <= b_len cx /\
    bs_src (dv_b v) = b_src cx /\ bs_len (dv_b v) = b_len cx /\ bs_S (dv_b v) = b_s cx /\
    bs_dst (dv_b v) = b_dst cx /\ bs_dlen (dv_b v) = b_dlen cx /\ 0 <= bs_av (dv_b v) <= b_dlen cx /\
    bv_unsigned (sh_small (dv_h v)) = b_small cx /\
    length (bs_q1 (dv_b v)) = 4%nat /\ length (bs_q2 (dv_b v)) = 4%nat /\
    sh_strm (dv_h v) = b_sp cx /\ sh_n (dv_h v) = b_n cx /\ sh_verb (dv_h v) = 0 /\
    length (sh_p1 (dv_h v)) = 3%nat /\ length (sh_p2 (dv_h v)) = 3%nat /\ length (sh_p3 (dv_h v)) = 3%nat /\
    0 <= sh_state (dv_h v) < 2^31 /\ 0 <= sh_solen (dv_h v) < 2^32 /\ 0 <= sh_rNToGo (dv_h v) < 2^32 /\
    0 <= sh_rTPos (dv_h v) < 2^32 /\ 0 <= sh_bsBuff (dv_h v) < 2^32 /\ 0 <= sh_bsLive (dv_h v) <= 32 /\
    0 <= sh_cbn (dv_h v) < 2^31 /\ 0 <= sh_origPtr (dv_h v) < 2^32 /\
    48 * sh_cbn (dv_h v) <= 8 * (b_len cx - bs_ai (dv_b v)) - sh_bsLive (dv_h v) /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.   (* [comment removed for export] *)
Proof.
  intros fr A v AOK DP. cbv zeta.
  cps_destruct AOK as (CTX & LO1 & LO2 & USP & ST14 & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & N1 & QS & QSRC & QLEN & QDST & QDLEN & USTRM & NZF & NZS & SM01).
  cps_destruct CTX as (LIN & AL & SEP).
  unfold ctx_lin in LIN. cbv zeta in LIN. bz_ceil; unfold IMG_HI_MAX, DSTATE_SIZE, CEILING, STACK_TOP in LIN.
  bz_ceil; unfold CEILING in LO2. unfold D14 in LO1.
  unfold dpure in DP. cbv zeta in DP.
  cps_destruct DP as (HWF & E1 & E2 & E3 & E4 & N19 & NBU & CFL & T1 & T2 & T3 & LJ1 & LJ2 & SNB & BU & BWF & AI & PAYL & W1).
  rewrite E3.
  unfold dsh_wf in HWF. unfold bzs_wf in BWF, BWF0. unfold w1_inv14, w1_view in W1.
  unfold bfields in BU. cps_destruct BU as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  cps_destruct LIN as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & SM01' & N09 & TT & L16 & L4).
  clear TT L16 L4 SM01' SM01 NZF NZS SEP AL.
  cps_destruct HWF as (W1' & W2' & W3' & W4' & W5' & W6' & W7' & W8' & W9' & W10' & W11' & W12' & W13' & W14').
  cps_destruct BWF as (B1 & B2 & B3 & B4 & B5 & B6).
  rewrite F3, F9 in *. rewrite <- F1, <- F2, <- F4, <- F5 in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.

(* [comment removed for export] *)
Section ActSeps.
  Variables (fr : Z) (A : act14).
  Hypothesis AOK : act_ok fr A.
  Let cx := a_cx A.
  Local Ltac prep :=
    let CTX := ident:(CTX) in let LIN := ident:(LIN) in pose proof AOK as X;
    cps_destruct X as (CTX & LO1 & LO2 & USP & ST14 & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & N1 & QS & QSRC & QLEN & QDST & QDLEN & USTRM & NZF & NZS & SM01);
    cps_destruct CTX as (LIN & AL & SEP);
    unfold ctx_lin in LIN; cbv zeta in LIN; bz_ceil; unfold IMG_HI_MAX, DSTATE_SIZE, CEILING, STACK_TOP in LIN; unfold cx, disj.
  Lemma act_sep_s_src : (b_s cx + 64144 <= b_src cx \/ b_src cx + b_len cx <= b_s cx)%Z.
  Proof. prep. pose proof (sep_s_src _ SEP) as Y. unfold disj, DSTATE_SIZE in Y. exact Y. Qed.
  Lemma act_sep_s_dst : (b_s cx + 64144 <= b_dst cx \/ b_dst cx + b_dlen cx <= b_s cx)%Z.
  Proof. prep. pose proof (sep_s_dst _ SEP) as Y. unfold disj, DSTATE_SIZE in Y. exact Y. Qed.
  (* [comment removed for export] *)
  Lemma act_small01 : b_small cx = 0%Z \/ b_small cx = 1%Z.
  Proof. prep. exact SM01. Qed.
  (* [comment removed for export] *)
  Lemma act_img_s : (b_s cx + 64144 <= 65536 \/ 212992 <= b_s cx)%Z.
  Proof. prep. pose proof (sep_img_s _ SEP) as Y. unfold img_apart, IHI, DSTATE_SIZE in Y. exact Y. Qed.
  (* [comment removed for export] *)
  Lemma act_img_tt : b_small cx = 0%Z -> (b_tt cx + 400000 * b_n cx <= 65536 \/ 212992 <= b_tt cx)%Z.
  Proof. prep. intros E. pose proof (sep_img_tt _ SEP (NZF E)) as Y. unfold img_apart, IHI in Y. exact Y. Qed.
  Lemma act_img_ll : b_small cx = 1%Z ->
    (b_ll16 cx + 200000 * b_n cx <= 65536 \/ 212992 <= b_ll16 cx)%Z /\ (b_ll4 cx + 50000 * b_n cx <= 65536 \/ 212992 <= b_ll4 cx)%Z.
  Proof. prep. intros E. destruct (NZS E) as [M1 M2]. split.
    - pose proof (sep_img_ll16 _ SEP M1) as Y. unfold img_apart, IHI in Y. exact Y.
    - pose proof (sep_img_ll4 _ SEP M2) as Y. unfold img_apart, IHI in Y. exact Y. Qed.
  (* [comment removed for export] *)
  Lemma act_tt : b_small cx = 0%Z ->
    (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_s cx)%Z /\
    (b_src cx + b_len cx <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_src cx)%Z /\
    (b_dst cx + b_dlen cx <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_dst cx)%Z.
  Proof.
    prep. intros E. specialize (NZF E).
    pose proof (sep_s_tt _ SEP NZF) as Y1. pose proof (sep_src_tt _ SEP NZF) as Y2. pose proof (sep_dst_tt _ SEP NZF) as Y3.
    unfold disj, DSTATE_SIZE in Y1, Y2, Y3.
    cps_destruct LIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TT & _ & _).
    destruct TT as [TT|TT]; [exfalso; exact (NZF TT)|].
    split; [exact TT|]. split; [exact Y1|]. split; [exact Y2| exact Y3].
  Qed.
  (* [comment removed for export] *)
  Lemma act_ll : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\
     0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_s cx)%Z /\
    (b_src cx + b_len cx <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_src cx)%Z /\
    (b_dst cx + b_dlen cx <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_dst cx)%Z /\
    (b_s cx + 64144 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_s cx)%Z /\
    (b_src cx + b_len cx <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_src cx)%Z /\
    (b_dst cx + b_dlen cx <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_dst cx)%Z /\
    (b_ll16 cx + 200000 * b_n cx <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_ll16 cx)%Z.
  Proof.
    prep. intros E. destruct (NZS E) as [M1 M2].
    pose proof (sep_s_ll16 _ SEP M1) as Y1. pose proof (sep_src_ll16 _ SEP M1) as Y2. pose proof (sep_dst_ll16 _ SEP M1) as Y3.
    pose proof (sep_s_ll4 _ SEP M2) as Y4. pose proof (sep_src_ll4 _ SEP M2) as Y5. pose proof (sep_dst_ll4 _ SEP M2) as Y6.
    pose proof (sep_ll16_ll4 _ SEP M1 M2) as Y7.
    unfold disj, DSTATE_SIZE in Y1, Y2, Y3, Y4, Y5, Y6, Y7.
    cps_destruct LIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L16 & L4).
    destruct L16 as [L16|L16]; [exfalso; exact (M1 L16)|]. destruct L4 as [L4|L4]; [exfalso; exact (M2 L4)|].
    split; [split; [exact (proj1 L16)| split; [exact (proj2 L16)| exact L4]]|].
    split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5|]. split; [exact Y6| exact Y7].
  Qed.

  (* [comment removed for export] *)
  Lemma act_tt_s : b_small cx = 0%Z ->
    (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_s cx)%Z.
  Proof. intros E. pose proof (act_tt E) as X. tauto. Qed.
  Lemma act_ll_s : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\
     0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_s cx)%Z /\
    (b_s cx + 64144 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_s cx)%Z.
  Proof. intros E. pose proof (act_ll E) as X. tauto. Qed.
  (* [comment removed for export] *)
  Lemma alin_core :
    (0 < b_s cx /\ b_s cx + 64144 <= alloc_ceiling /\ alloc_ceiling <= a_lo A /\ a_lo A <= a_usp A - 1024 /\
     a_usp A < 18446744073709551616 /\ a_usp A <= b_strm cx /\ b_strm cx = b_sp cx /\ alloc_ceiling <= b_sp cx /\
     b_sp cx + 176 <= 140737488355328 /\ 0 < b_src cx /\ 0 <= b_len cx /\ b_src cx + b_len cx <= alloc_ceiling /\
     Z.of_nat (length (a_payload A)) = b_len cx /\ 1 <= b_n cx <= 9 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.
  Proof.
    prep. bz_ceil; unfold CEILING in LO2. unfold D14 in LO1.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
  Lemma alin_tt : b_small cx = 0%Z -> (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z.
  Proof. intros E. pose proof (act_tt E) as X. tauto. Qed.
  Lemma alin_ll : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\ 0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z.
  Proof. intros E. pose proof (act_ll E) as X. tauto. Qed.
End ActSeps.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma act_ok_al : forall fr A, act_ok fr A -> ctx_al (a_cx A). Proof. intros fr A H; exact (proj1 (proj2 (proj1 H))). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Lemma hide_intro : forall P : Prop, P -> hidden P. Proof. exact (fun P p => p). Qed.
End ACeilS2.

Ltac hide H := apply hide_intro in H.
Ltac hide_all_but keep :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : u32arr _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : u8arr _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : bytes_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : drest_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : blk_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  end.
Section ACeilS3. Context {ACEIL__ : ACeil}.


Section BlkT.
  Variable segs : list Segment.
  Lemma blk_at_transport : forall W m m' cx k,
    blk_at segs m cx k -> munch W m m' -> wmono segs m m' ->
    (forall A n, blk_range cx A n -> disjoint_from W A n) -> blk_at segs m' cx k.
  Proof.
    intros W m m' cx k B MU WM D. destruct k as [ttw|l16 l4]; cbn in *.
    - cps_destruct B as (S0 & U & L). split; [exact S0|]. split; [|exact L].
      eapply u32arr_transport; [exact U| exact MU| exact WM|]. rewrite L.
      replace (4 * (100000 * b_n cx))%Z with (400000 * b_n cx)%Z by lia. apply D. left. auto.
    - cps_destruct B as (S1 & U1 & L1 & U2 & L2). split; [exact S1|]. split; [|split; [exact L1| split; [|exact L2]]].
      + eapply u8arr_transport; [exact U1| exact MU| exact WM|]. rewrite L1. apply D. right. auto.
      + eapply u8arr_transport; [exact U2| exact MU| exact WM|]. rewrite L2. apply D. right. auto.
  Qed.
End BlkT.
End ACeilS3.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac revive_slim_ctx :=
  repeat match goal with K : ?T |- _ =>
    lazymatch T with
    | Z.of_nat (length _) = _ => fail
    | length _ = _ => fail
    | act_ok _ _ => fail
    | (_ \/ _) => fail
    | b_small _ = _ => fail
    | dpure _ _ _ _ _ => fail
    | _ => clear K
    end end.
Ltac revive_dj_slim AOK SEPF :=
  revive_slim_ctx;
  pose proof alloc_ceiling_range;   (* [comment removed for export] *)
  pose proof (alin_core _ _ AOK);
  try match goal with SM : b_small _ = _ |- _ => first [ pose proof (alin_ll _ _ AOK SM) | pose proof (alin_tt _ _ AOK SM) ] end;
  try match goal with DP : dpure _ _ _ _ _ |- _ => pose proof (dpure_cf_len _ _ _ _ _ DP); clear DP end;
  pose proof SEPF;
  cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia.

Ltac revive H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs =>
      apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia ] ]
  | u32arr ?segs me ?A ?ws =>
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | u8arr ?segs me ?A ?bs =>
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_s _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_s _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | bytes_at ?segs me ?A ?bs =>
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL
        | first [ revive_dj_slim AOK (act_sep_s_src _ _ AOK)
                | let Y := fresh "SEPsrc" in pose proof (act_sep_s_src _ _ AOK) as Y; cbn [disjoint_from]; simpl_sizes; slia ] ]
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ] ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ pose proof (act_tt_s _ _ AOK E) as (? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ?) ];
          first [ revive_dj_slim AOK I | cbn [disjoint_from]; slia ] ]
  end end.

(* [comment removed for export] *)
Ltac revive_all MUL WML AOK :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive H MUL WML AOK | fail 100 "cannot revive" H ] end.
Section ACeilS4. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS4.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_dmem DM :=
  unfold dmem in DM; cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in DM;
  cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).

(* [comment removed for export] *)
Ltac close_dmem :=
  lazymatch goal with
  | |- dmem _ ?cx _ _ _ ?m _ =>
      eapply dmem_introF; cbv zeta;
      [ match goal with H : rw_cells _ m (b_s cx) _ |- _ => exact H end
      | match goal with H : rw_cells _ m (b_s cx + 1092)%Z _ |- _ => exact H end
      | match goal with H : u32arr _ m (b_s cx + 1096)%Z _ |- _ => exact H end
      | match goal with H : rw_cells _ m (b_s cx + 3152)%Z _ |- _ => exact H end
      | match goal with H : rw_cells _ m (b_s cx + 64036)%Z _ |- _ => exact H end
      | match goal with H : drest_at _ m _ _ |- _ => exact H end
      | match goal with H : rw_cells _ m (b_strm cx) _ |- _ => exact H end
      | match goal with H : blk_at _ m _ _ |- _ => exact H end
      | match goal with H : bytes_at _ m (b_src cx) _ |- _ => exact H end
      | match goal with H : rw_cells _ m _ [C8 _; C8 _; C8 _; C8 _; C8 _] |- _ => exact H end
      | match goal with H : rw_cells _ m _ [C8 _] |- _ => exact H end
      | match goal with H : u32arr _ m _ rnums_words |- _ => exact H end ]
  end.

(* [comment removed for export] *)
Ltac dpure_from DP :=
  lazymatch type of DP with dpure _ _ _ _ _ =>
    let X := fresh "DPX" in pose proof DP as X; unfold dpure in X; cbv zeta in X;
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in X;
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields in X;
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque] in X;
    decompose [and] X; clear X;
    unfold dpure; cbv zeta;
    cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k];
    unfold dsh_wf, bzs_wf, w1_inv14, w1_view, bupd, bfields;
    cbn [sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
         sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
         bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption | reflexivity | lia | congruence | idtac ]
  end.
