(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export DecCut.   (* [comment removed for export] *)
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
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] /\
    ro_cells segs m (di_stderrp I) [C8 sv] /\
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
    ro_cells segs m (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))] ->
    ro_cells segs m (di_stderrp I) [C8 sv] ->
    u32arr segs m (di_rnums I) rnums_words ->
    dmem cx g1 sv payload m (DV h nbu cf d j1 snb j2 r b k).
  Proof. intros. unfold dmem. cbn. repeat (split; [assumption|]). assumption. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WithImg.

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
  a_cx : bctx; a_h0 : dsh; a_b0 : bzs; a_lo : Z; a_g1 : word; a_sv : word; a_payload : list byte;
  a_P : Z;                          (* [comment removed for export] *)
  a_fb : Z;                         (* [comment removed for export] *)
  a_shs : Z; a_sht : Z; a_shf : Z   (* [comment removed for export] *)
}.
End ACeilS1.


Notation a_usp A := (bv_unsigned (a_sp A)).
Notation a_S A := (b_s (a_cx A)).
Section ACeilS2. Context {ACEIL__ : ACeil}.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition W14 (A : act14) : list ivl :=
  [(b_s (a_cx A), b_s (a_cx A) + DSTATE_SIZE)%Z; (b_strm (a_cx A), b_strm (a_cx A) + 20)%Z; (a_P A - 256, a_usp A)%Z;
   (a_fb A, a_fb A + 56)%Z; (a_shf A, a_shf A + 8)%Z] ++ blk_ivls (a_cx A).

(* [comment removed for export] *)
Definition img_apartA (ihi a n : Z) : Prop := (a + n <= 0x10000 \/ ihi <= a)%Z.

(* [comment removed for export] *)
Definition ctx_alA (A : act14) : Prop :=
  (b_s (a_cx A) mod 16 = 0 /\ b_strm (a_cx A) mod 8 = 0 /\ a_fb A mod 64 = 0 /\ a_P A mod 32 = 0 /\
   b_tt (a_cx A) mod 16 = 0 /\ b_ll16 (a_cx A) mod 16 = 0 /\ b_ll4 (a_cx A) mod 16 = 0)%Z.

(* [comment removed for export] *)
Definition act_sepA (ihi : Z) (A : act14) : Prop :=
  let cx := a_cx A in
  let s := b_s cx in let strm := b_strm cx in let src := b_src cx in let len := b_len cx in
  let dst := b_dst cx in let dlen := b_dlen cx in let n := b_n cx in let fb := a_fb A in let shf := a_shf A in
  (* [comment removed for export] *)
  disj s DSTATE_SIZE strm 80 /\ disj s DSTATE_SIZE src len /\ disj s DSTATE_SIZE dst dlen /\
  disj strm 80 src len /\ disj strm 80 dst dlen /\ disj src len dst dlen /\
  (* [comment removed for export] *)
  disj fb 64 s DSTATE_SIZE /\ disj fb 64 strm 80 /\ disj fb 64 src len /\ disj fb 64 shf 8 /\
  disj shf 8 s DSTATE_SIZE /\ disj shf 8 strm 80 /\ disj shf 8 src len /\
  (* [comment removed for export] *)
  (b_tt cx <> 0 -> disj s DSTATE_SIZE (b_tt cx) (400000 * n) /\ disj strm 80 (b_tt cx) (400000 * n) /\
                   disj src len (b_tt cx) (400000 * n) /\ disj fb 64 (b_tt cx) (400000 * n) /\ disj shf 8 (b_tt cx) (400000 * n)) /\
  (b_ll16 cx <> 0 -> disj s DSTATE_SIZE (b_ll16 cx) (200000 * n) /\ disj strm 80 (b_ll16 cx) (200000 * n) /\
                     disj src len (b_ll16 cx) (200000 * n) /\ disj fb 64 (b_ll16 cx) (200000 * n) /\ disj shf 8 (b_ll16 cx) (200000 * n)) /\
  (b_ll4 cx <> 0 -> disj s DSTATE_SIZE (b_ll4 cx) (50000 * n) /\ disj strm 80 (b_ll4 cx) (50000 * n) /\
                    disj src len (b_ll4 cx) (50000 * n) /\ disj fb 64 (b_ll4 cx) (50000 * n) /\ disj shf 8 (b_ll4 cx) (50000 * n)) /\
  (b_ll16 cx <> 0 -> b_ll4 cx <> 0 -> disj (b_ll16 cx) (200000 * n) (b_ll4 cx) (50000 * n)) /\
  (* [comment removed for export] *)
  img_apartA ihi s DSTATE_SIZE /\ img_apartA ihi strm 80 /\ img_apartA ihi fb 64 /\
  (b_tt cx <> 0 -> img_apartA ihi (b_tt cx) (400000 * n)) /\
  (b_ll16 cx <> 0 -> img_apartA ihi (b_ll16 cx) (200000 * n)) /\
  (b_ll4 cx <> 0 -> img_apartA ihi (b_ll4 cx) (50000 * n)).

(* [comment removed for export] *)
Definition act_ok (ihi : Z) (A : act14) : Prop :=
  let cx := a_cx A in
  (* [comment removed for export] *)
  (0 < b_s cx /\ b_s cx + DSTATE_SIZE <= CEILING /\
   0 < b_strm cx /\ b_strm cx + 80 <= CEILING /\
   0 < b_src cx /\ 0 <= b_len cx /\ b_len cx < 134217728 /\ b_src cx + b_len cx <= CEILING /\
   0 < b_dst cx /\ 0 <= b_dlen cx /\ b_dlen cx < 134217728 /\ b_dst cx + b_dlen cx <= CEILING /\
   0 < a_fb A /\ a_fb A + 64 <= CEILING /\ 2147450880 <= a_shf A /\ a_shf A + 8 <= 17594333495296 /\
   (b_small cx = 0 \/ b_small cx = 1) /\ 1 <= b_n cx <= 9 /\
   (b_tt cx = 0 \/ (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= CEILING)) /\
   (b_ll16 cx = 0 \/ (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= CEILING)) /\
   (b_ll4 cx = 0 \/ (0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= CEILING)) /\
   65536 < ihi <= 0x7fff7000)%Z /\
  ctx_alA A /\ act_sepA ihi A /\
  (* [comment removed for export] *)
  sanchor (b_s cx) (a_shs A) /\ sanchor (b_strm cx) (a_sht A) /\ sanchor (a_fb A) (a_shf A) /\
  (* [comment removed for export] *)
  (CEILING <= a_lo A)%Z /\ (a_lo A + 256 <= a_P A)%Z /\ (a_usp A < 2^64)%Z /\
  (a_P A + 864 <= a_usp A <= a_P A + 880)%Z /\
  (* [comment removed for export] *)
  dsh_wf (a_h0 A) /\ bzs_wf (a_b0 A) /\
  Z.of_nat (length (a_payload A)) = b_len cx /\
  sh_strm (a_h0 A) = b_strm cx /\ sh_n (a_h0 A) = b_n cx /\
  bv_unsigned (sh_small (a_h0 A)) = b_small cx /\
  bs_S (a_b0 A) = b_s cx /\ bs_src (a_b0 A) = b_src cx /\ bs_len (a_b0 A) = b_len cx /\
  bs_dst (a_b0 A) = b_dst cx /\ bs_dlen (a_b0 A) = b_dlen cx /\
  (b_small cx = 0%Z -> b_tt cx <> 0%Z) /\
  (b_small cx = 1%Z -> b_ll16 cx <> 0%Z /\ b_ll4 cx <> 0%Z).

Local Ltac aok_open AOK :=
  let LINB := ident:(LINB) in let SEPB := ident:(SEPB) in
  cps_destruct AOK as (LINB & AL & SEPB & ANS & ANT & ANF & LO2 & LO1 & USP & GEO & HWF0 & BWF0 & PL & HS0 & HN0 & HSM0 & QS & QSRC & QLEN & QDST & QDLEN & NZF & NZS);
  cbv zeta in LINB; bz_ceil; unfold DSTATE_SIZE, CEILING in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ActSeps.
  Variables (ihi : Z) (A : act14).
  Hypothesis AOK : act_ok ihi A.
  Let cx := a_cx A.
  Local Ltac prep :=
    pose proof AOK as X; aok_open X;
    let LINB := ident:(LINB) in let SEPB := ident:(SEPB) in
    cps_destruct LINB as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & SM01 & N09 & TT & L16 & L4 & IH);
    unfold act_sepA in SEPB; cbv zeta in SEPB;
    cps_destruct SEPB as (D_s_strm & D_s_src & D_s_dst & D_strm_src & D_strm_dst & D_src_dst & D_fb_s & D_fb_strm & D_fb_src & D_fb_shf &
                          D_shf_s & D_shf_strm & D_shf_src & D_tt & D_ll16 & D_ll4 & D_ll & I_s & I_strm & I_fb & I_tt & I_ll16 & I_ll4);
    unfold cx, disj, img_apartA, DSTATE_SIZE in *.
  Lemma act_sep_s_strm : (b_s cx + 64144 <= b_strm cx \/ b_strm cx + 80 <= b_s cx)%Z.
  Proof. prep. exact D_s_strm. Qed.
  Lemma act_sep_s_src : (b_s cx + 64144 <= b_src cx \/ b_src cx + b_len cx <= b_s cx)%Z.
  Proof. prep. exact D_s_src. Qed.
  (* [comment removed for export] *)
  Lemma act_sep_strm_src : (b_strm cx + 80 <= b_src cx \/ b_src cx + b_len cx <= b_strm cx)%Z.
  Proof. prep. exact D_strm_src. Qed.
  (* [comment removed for export] *)
  Lemma act_sep_src : (b_s cx + 64144 <= b_src cx \/ b_src cx + b_len cx <= b_s cx)%Z /\ (b_strm cx + 80 <= b_src cx \/ b_src cx + b_len cx <= b_strm cx)%Z.
  Proof. prep. split; [exact D_s_src| exact D_strm_src]. Qed.
  Lemma act_small01 : b_small cx = 0%Z \/ b_small cx = 1%Z.
  Proof. prep. exact SM01. Qed.
  (* [comment removed for export] *)
  Lemma act_img_s : (b_s cx + 64144 <= 65536 \/ ihi <= b_s cx)%Z.
  Proof. prep. exact I_s. Qed.
  Lemma act_img_strm : (b_strm cx + 80 <= 65536 \/ ihi <= b_strm cx)%Z.
  Proof. prep. exact I_strm. Qed.
  Lemma act_img_fb : (a_fb A + 64 <= 65536 \/ ihi <= a_fb A)%Z.
  Proof. prep. exact I_fb. Qed.
  (* [comment removed for export] *)
  Lemma act_img_sb : (b_s cx + 64144 <= 65536 \/ ihi <= b_s cx)%Z /\ (b_strm cx + 80 <= 65536 \/ ihi <= b_strm cx)%Z
                     /\ (b_s cx + 64144 <= b_strm cx \/ b_strm cx + 80 <= b_s cx)%Z /\ (65536 < ihi <= 0x7fff7000)%Z.
  Proof. prep. split; [exact I_s|]. split; [exact I_strm|]. split; [exact D_s_strm| exact IH]. Qed.
  (* [comment removed for export] *)
  Lemma act_sep_fb : (a_fb A + 64 <= b_s cx \/ b_s cx + 64144 <= a_fb A)%Z /\ (a_fb A + 64 <= b_strm cx \/ b_strm cx + 80 <= a_fb A)%Z
                     /\ (a_fb A + 64 <= b_src cx \/ b_src cx + b_len cx <= a_fb A)%Z /\ (a_fb A + 64 <= a_shf A \/ a_shf A + 8 <= a_fb A)%Z.
  Proof. prep. repeat split; assumption. Qed.
  Lemma act_sep_shf : (a_shf A + 8 <= b_s cx \/ b_s cx + 64144 <= a_shf A)%Z /\ (a_shf A + 8 <= b_strm cx \/ b_strm cx + 80 <= a_shf A)%Z
                      /\ (a_shf A + 8 <= b_src cx \/ b_src cx + b_len cx <= a_shf A)%Z.
  Proof. prep. repeat split; assumption. Qed.
  Lemma act_img_tt : b_small cx = 0%Z -> (b_tt cx + 400000 * b_n cx <= 65536 \/ ihi <= b_tt cx)%Z.
  Proof. prep. intros E. exact (I_tt (NZF E)). Qed.
  Lemma act_img_ll : b_small cx = 1%Z ->
    (b_ll16 cx + 200000 * b_n cx <= 65536 \/ ihi <= b_ll16 cx)%Z /\ (b_ll4 cx + 50000 * b_n cx <= 65536 \/ ihi <= b_ll4 cx)%Z.
  Proof. prep. intros E. destruct (NZS E) as [M1 M2]. split; [exact (I_ll16 M1)| exact (I_ll4 M2)]. Qed.
  (* [comment removed for export] *)
  Lemma act_tt : b_small cx = 0%Z ->
    (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_s cx)%Z /\
    (b_strm cx + 80 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_strm cx)%Z /\
    (b_src cx + b_len cx <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_src cx)%Z /\
    (a_fb A + 64 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= a_fb A)%Z /\
    (a_shf A + 8 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= a_shf A)%Z.
  Proof.
    prep. intros E. specialize (NZF E). destruct (D_tt NZF) as (Z1 & Z2 & Z3 & Z4 & Z5).
    destruct TT as [TT|TT]; [exfalso; exact (NZF TT)|].
    split; [exact TT|]. repeat split; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma act_ll : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\
     0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_s cx)%Z /\
    (b_strm cx + 80 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_strm cx)%Z /\
    (b_src cx + b_len cx <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_src cx)%Z /\
    (a_fb A + 64 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= a_fb A)%Z /\
    (a_shf A + 8 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= a_shf A)%Z /\
    (b_s cx + 64144 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_s cx)%Z /\
    (b_strm cx + 80 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_strm cx)%Z /\
    (b_src cx + b_len cx <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_src cx)%Z /\
    (a_fb A + 64 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= a_fb A)%Z /\
    (a_shf A + 8 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= a_shf A)%Z /\
    (b_ll16 cx + 200000 * b_n cx <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_ll16 cx)%Z.
  Proof.
    prep. intros E. destruct (NZS E) as [M1 M2].
    destruct (D_ll16 M1) as (Z1 & Z2 & Z3 & Z4 & Z5). destruct (D_ll4 M2) as (Z6 & Z7 & Z8 & Z9 & Z10). pose proof (D_ll M1 M2) as Z11.
    destruct L16 as [L16|L16]; [exfalso; exact (M1 L16)|]. destruct L4 as [L4|L4]; [exfalso; exact (M2 L4)|].
    split; [split; [exact (proj1 L16)| split; [exact (proj2 L16)| exact L4]]|].
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma act_tt_s : b_small cx = 0%Z ->
    (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_s cx)%Z /\
    (b_strm cx + 80 <= b_tt cx \/ b_tt cx + 400000 * b_n cx <= b_strm cx)%Z.
  Proof. intros E. destruct (act_tt E) as (X1 & X2 & X3 & _). split; [exact X1|]. split; [exact X2| exact X3]. Qed.
  Lemma act_ll_s : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\
     0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z /\
    (b_s cx + 64144 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_s cx)%Z /\
    (b_s cx + 64144 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_s cx)%Z /\
    (b_strm cx + 80 <= b_ll16 cx \/ b_ll16 cx + 200000 * b_n cx <= b_strm cx)%Z /\
    (b_strm cx + 80 <= b_ll4 cx \/ b_ll4 cx + 50000 * b_n cx <= b_strm cx)%Z.
  Proof.
    intros E. destruct (act_ll E) as (X1 & X2 & X3 & _ & _ & _ & X7 & X8 & _).
    split; [exact X1|]. split; [exact X2|]. split; [exact X7|]. split; [exact X3| exact X8].
  Qed.
  (* [comment removed for export] *)
  Lemma alin_core :
    (0 < b_s cx /\ b_s cx + 64144 <= alloc_ceiling /\ alloc_ceiling <= a_lo A /\ a_lo A + 256 <= a_P A /\
     a_usp A < 18446744073709551616 /\ a_P A + 864 <= a_usp A /\ a_usp A <= a_P A + 880 /\
     0 < b_strm cx <= alloc_ceiling - 80 /\ 0 < a_fb A <= alloc_ceiling - 64 /\ 2147450880 <= a_shf A <= 17594333495288 /\
     0 < b_src cx /\ 0 <= b_len cx <= alloc_ceiling - b_src cx /\
     Z.of_nat (length (a_payload A)) = b_len cx /\ 1 <= b_n cx <= 9 /\ 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.
  Proof.
    prep. clear D_s_strm D_s_src D_s_dst D_strm_src D_strm_dst D_src_dst D_fb_s D_fb_strm D_fb_src D_fb_shf D_shf_s D_shf_strm D_shf_src
                D_tt D_ll16 D_ll4 D_ll I_s I_strm I_fb I_tt I_ll16 I_ll4 SM01 TT L16 L4 NZF NZS AL ANS ANT ANF.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
  Lemma alin_tt : b_small cx = 0%Z -> (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= alloc_ceiling)%Z.
  Proof. intros E. exact (proj1 (act_tt E)). Qed.
  Lemma alin_ll : b_small cx = 1%Z ->
    (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= alloc_ceiling /\ 0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= alloc_ceiling)%Z.
  Proof. intros E. exact (proj1 (act_ll E)). Qed.
  (* [comment removed for export] *)
  Lemma act_anchor_s : sanchor (b_s cx) (a_shs A). Proof. prep. exact ANS. Qed.
  Lemma act_anchor_strm : sanchor (b_strm cx) (a_sht A). Proof. prep. exact ANT. Qed.
  Lemma act_anchor_fb : sanchor (a_fb A) (a_shf A). Proof. prep. exact ANF. Qed.
End ActSeps.

Lemma act_ok_al : forall ihi A, act_ok ihi A -> ctx_alA A. Proof. intros ihi A H; exact (proj1 (proj2 H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition act_sh (I : dimg) (A : act14) : Prop :=
  let cx := a_cx A in let W := W14 A in let m0 := a_m0 A in let segs := di_segs I in
  shzW segs W m0 (b_s cx) (b_s cx + 64144) /\
  shzW segs W m0 (b_strm cx) (b_strm cx + 80) /\
  shpW segs W m0 (b_src cx) (b_src cx + b_len cx) /\
  shzW segs W m0 (di_rnums I) (di_rnums I + 2048) /\
  (b_small cx = 0%Z -> shzW segs W m0 (b_tt cx) (b_tt cx + 400000 * b_n cx)) /\
  (b_small cx = 1%Z -> shzW segs W m0 (b_ll16 cx) (b_ll16 cx + 200000 * b_n cx) /\
                       shzW segs W m0 (b_ll4 cx) (b_ll4 cx + 50000 * b_n cx)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS2.

Ltac hide_all_but keep :=
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : ro_cells _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : u32arr _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : u8arr _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : bytes_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : drest_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  | H : blk_at _ _ _ _ |- _ => lazymatch keep with context [H] => fail | _ => hide H end
  end.
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
        | first [ revive_dj_slim AOK (act_img_sb _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_sb _ _ AOK) as Y; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; simpl_sizes; slia ] ]
  | ro_cells ?segs me ?A ?cs =>
      apply (ro_cells_transport segs W me m' A cs) in H; [ | exact MUL
        | first [ revive_dj_slim AOK (act_img_sb _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_sb _ _ AOK) as Y; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; simpl_sizes; slia ] ]
  | u32arr ?segs me ?A ?ws =>
      apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_sb _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_sb _ _ AOK) as Y; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | u8arr ?segs me ?A ?bs =>
      apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_img_sb _ _ AOK)
                | let Y := fresh "IMGs" in pose proof (act_img_sb _ _ AOK) as Y; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ] ]
  | bytes_at ?segs me ?A ?bs =>
      apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL
        | first [ revive_dj_slim AOK (act_sep_src _ _ AOK)
                | let Y := fresh "SEPsrc" in pose proof (act_sep_src _ _ AOK) as Y; pose proof (alin_core _ _ AOK); cbn [disjoint_from]; simpl_sizes; slia ] ]
  | drest_at ?segs me ?S ?r =>
      apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML
        | first [ revive_dj_slim AOK (act_sep_s_strm _ _ AOK) | pose proof (act_sep_s_strm _ _ AOK); pose proof (alin_core _ _ AOK); cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK (act_sep_s_strm _ _ AOK) | pose proof (act_sep_s_strm _ _ AOK); pose proof (alin_core _ _ AOK); cbn [disjoint_from]; slia ]
        | first [ revive_dj_slim AOK (act_sep_s_strm _ _ AOK) | pose proof (act_sep_s_strm _ _ AOK); pose proof (alin_core _ _ AOK); cbn [disjoint_from]; slia ] ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in
          intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          [ cps_pose (act_tt_s _ _ AOK E) as (? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ? & ? & ?)
          | cps_pose (act_ll_s _ _ AOK E) as (? & ? & ? & ? & ?) ];
          first [ revive_dj_slim AOK I | pose proof (alin_core _ _ AOK); cbn [disjoint_from]; slia ] ]
  end end.

(* [comment removed for export] *)
Ltac revive_fb_facts A AOK :=
  lazymatch A with
  | context [b_s _] =>
      let X := fresh "X" in let Y := fresh "Y" in
      pose proof (proj1 (act_sep_fb _ _ AOK)) as X; pose proof (proj1 (act_sep_shf _ _ AOK)) as Y
  | context [b_strm _] =>
      let X := fresh "X" in let Y := fresh "Y" in let Z0 := fresh "Z" in
      pose proof (proj1 (proj2 (act_sep_fb _ _ AOK))) as X; pose proof (proj1 (proj2 (act_sep_shf _ _ AOK))) as Y;
      pose proof (act_sep_s_strm _ _ AOK) as Z0
  | context [b_src _] =>
      let X := fresh "X" in let Y := fresh "Y" in let Z0 := fresh "Z" in
      pose proof (proj1 (proj2 (proj2 (act_sep_fb _ _ AOK)))) as X; pose proof (proj2 (proj2 (act_sep_shf _ _ AOK))) as Y;
      pose proof (act_sep_src _ _ AOK) as Z0
  | context [a_P _] => idtac
  | _ => let X := fresh "X" in let Y := fresh "Y" in pose proof (act_img_sb _ _ AOK) as X; pose proof (act_img_fb _ _ AOK) as Y
  end.
Ltac revive_fb_dj A AOK :=
  revive_slim_ctx;
  pose proof alloc_ceiling_range; pose proof (alin_core _ _ AOK);
  revive_fb_facts A AOK;
  try match goal with DP : dpure _ _ _ _ _ |- _ => pose proof (dpure_cf_len _ _ _ _ _ DP); clear DP end;
  cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia.
Ltac revive_fb H MUL WML AOK :=
  unfold hidden in H;
  lazymatch type of MUL with munch ?W ?me ?m' =>
  lazymatch type of H with
  | rw_cells ?segs me ?A ?cs => apply (rw_cells_transport segs W me m' A cs) in H; [ | exact MUL | exact WML | revive_fb_dj A AOK ]
  | ro_cells ?segs me ?A ?cs => apply (ro_cells_transport segs W me m' A cs) in H; [ | exact MUL | revive_fb_dj A AOK ]
  | u32arr ?segs me ?A ?ws => apply (u32arr_transport segs W me m' A ws) in H; [ | exact MUL | exact WML | revive_fb_dj A AOK ]
  | u8arr ?segs me ?A ?bs => apply (u8arr_transport segs W me m' A bs) in H; [ | exact MUL | exact WML | revive_fb_dj A AOK ]
  | bytes_at ?segs me ?A ?bs => apply (bytes_at_transport segs W me m' A bs) in H; [ | exact MUL | revive_fb_dj A AOK ]
  | drest_at ?segs me ?S ?r => apply (drest_transport segs W me m' S r) in H; [ | exact MUL | exact WML | revive_fb_dj S AOK | revive_fb_dj S AOK | revive_fb_dj S AOK ]
  | blk_at ?segs me ?cx ?k =>
      apply (blk_at_transport segs W me m' cx k) in H;
      [ | exact MUL | exact WML
        | let E := fresh "E" in intros ? ? [(E & -> & ->)|(E & [(-> & ->)|(-> & ->)])];
          revive_slim_ctx; pose proof alloc_ceiling_range; pose proof (alin_core _ _ AOK);
          first [ pose proof (act_ll _ _ AOK E) | pose proof (act_tt _ _ AOK E) ];
          cbn [disjoint_from]; slia ]
  end end.
Ltac revive_all_fb MUL WML AOK :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive_fb H MUL WML AOK | fail 100 "cannot revive (fb)" H ] end.

(* [comment removed for export] *)
Ltac revive_all MUL WML AOK :=
  repeat lazymatch goal with H : hidden _ |- _ => first [ revive H MUL WML AOK | fail 100 "cannot revive" H ] end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac unfold_W14 MU := unfold W14, DSTATE_SIZE in MU; cbn [app] in MU.

(* [comment removed for export] *)
Ltac open_ash ASH AOK :=
  let X := fresh "ASHx" in
  pose proof ASH as X; unfold act_sh in X; cbv zeta in X;
  unfold W14, DSTATE_SIZE in X; cbn [app] in X;
  cps_destruct X as (SHS & SHT & SHP & SHR & SHB);
  pose proof (act_anchor_s _ _ AOK) as ANS; pose proof (act_anchor_strm _ _ AOK) as ANT.
