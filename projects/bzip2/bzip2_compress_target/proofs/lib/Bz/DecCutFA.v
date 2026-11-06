(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts DecCutA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecCutF.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecCutA.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section WithImg.
  Variable I : dimg.
  Let segs := di_segs I.

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
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    ro_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    dmem I cx g1 sv payload m (dvF cx J d s).
  Proof. intros. unfold dmem, dvF. cbn [dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k]. repeat (split; [assumption|]). assumption. Qed.
End WithImg.

(* [comment removed for export] *)
Lemma act_linF : forall ihi A J d s, act_ok ihi A -> dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
  let cx := a_cx A in
  (0 < b_s cx /\ b_s cx + 64144 <= alloc_ceiling /\
    0 < b_strm cx /\ b_strm cx + 80 <= alloc_ceiling /\
    0 < b_src cx /\ 0 <= b_len cx < 134217728 /\ b_src cx + b_len cx <= alloc_ceiling /\
    0 < b_dst cx /\ 0 <= b_dlen cx /\ b_dlen cx < 134217728 /\ b_dst cx + b_dlen cx <= alloc_ceiling /\
    0 < a_fb A /\ a_fb A + 64 <= alloc_ceiling /\ 2147450880 <= a_shf A /\ a_shf A + 8 <= 17594333495296 /\
    0 <= b_n cx <= 9 /\ 1 <= b_n cx /\
    alloc_ceiling <= a_lo A /\ a_lo A + 256 <= a_P A /\ a_P A + 832 <= a_usp A /\ a_usp A <= a_P A + 848 /\ a_usp A < 18446744073709551616 /\
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
  intros ihi A J d s AOK DP. cbv zeta.
  pose proof (alin_core _ _ AOK) as CORE.
  cps_destruct AOK as (LINB & AL & SEPB & ANS & ANT & ANF & LO2 & LO1 & USP & GEO & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & QS & QSRC & QLEN & QDST & QDLEN & NZF & NZS).
  cbv zeta in LINB. bz_ceil; unfold DSTATE_SIZE, CEILING in *.
  cps_destruct LINB as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & SM01 & N09 & TT & L16 & L4 & IH).
  clear TT L16 L4 NZF NZS SEPB AL ANS ANT ANF.
  pose proof (in_rel_length _ _ (dpureF_in _ _ _ _ _ _ DP)) as IRL.
  unfold dpureF, jk_wf, jk_static, drep in DP. unfold bzs_wf in BWF0.
  decompose [and] DP. decompose [and] BWF0. decompose [and] CORE.
  rewrite <- QLEN, <- QDLEN in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac open_dmemF DM :=
  unfold dmem in DM; dvF_cbn_in DM;
  cps_destruct DM as (HD & NBU & CF & MIDc & SAV & DR & STRM & BLK & PAY & GOT & SEV & RN).

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
      | match goal with H : ro_cells _ m _ [C8 _; C8 _; C8 _; C8 _; C8 _] |- _ => exact H end
      | match goal with H : ro_cells _ m _ [C8 _] |- _ => exact H end
      | match goal with H : u32arr _ m _ rnums_words |- _ => exact H end ]
  end.
