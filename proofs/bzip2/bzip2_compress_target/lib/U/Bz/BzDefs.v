(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeil ACeilTac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)             (* [comment removed for export] *)
(* [comment removed for export] *)            (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)            (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)     (* [comment removed for export] *)
(* [comment removed for export] *)            (* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)           (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)    (* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)
(* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)        (* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)      (* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DSTATE_SIZE : Z := 64144.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MTFL_SIZE : Z := 16.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bs_bzalloc : Z := 56.
Definition bs_bzfree : Z := 64.
Definition bs_opaque : Z := 72.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BZ_OK : Z := 0.
Definition BZ_STREAM_END : Z := 4.
Definition BZ_SEQUENCE_ERROR : Z := -1.
(* [comment removed for export] *)
Definition BZ_MEM_ERROR : Z := -3.
Definition BZ_DATA_ERROR : Z := -4.
Definition BZ_DATA_ERROR_MAGIC : Z := -5.
Definition BZ_UNEXPECTED_EOF : Z := -7.
Definition BZ_OUTBUFF_FULL : Z := -8.

(* [comment removed for export] *)
Definition BZ_X_OUTPUT : Z := 2.
Definition BZ_X_MAGIC_1 : Z := 10.
Definition BZ_X_BLKHDR_1 : Z := 14.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bctx := BCX {
  b_s    : Z;   (* [comment removed for export] *)
  b_strm : Z;   (* [comment removed for export] *)
  b_src  : Z;   (* [comment removed for export] *)
  b_len  : Z;   (* [comment removed for export] *)
  b_dst  : Z;   (* [comment removed for export] *)
  b_dlen : Z;   (* [comment removed for export] *)
  b_pdl  : Z;   (* [comment removed for export] *)
  b_sp   : Z;   (* [comment removed for export] *)
  b_small: Z;   (* [comment removed for export] *)
  b_n    : Z;   (* [comment removed for export] *)
  b_tt   : Z;   (* [comment removed for export] *)
  b_ll16 : Z;   (* [comment removed for export] *)
  b_ll4  : Z    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition CEILING : Z := alloc_ceiling.
  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STACK_TOP : Z := 140737488355328.    (* [comment removed for export] *)
Definition IMG_HI_MAX : Z := 0x3fb00.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x34000.
Definition img_apart (p k : Z) : Prop := p + k <= 65536 \/ IHI <= p.

(* [comment removed for export] *)
Definition ctx_lin (cx : bctx) : Prop :=
  let s := b_s cx in let src := b_src cx in let len := b_len cx in let dst := b_dst cx in
  let dlen := b_dlen cx in let pdl := b_pdl cx in let sp := b_sp cx in
  0 < s /\ s + DSTATE_SIZE <= CEILING /\
  0 < src /\ 0 <= len /\ len < 134217728 /\ src + len <= CEILING /\
  0 < dst /\ 0 <= dlen /\ dlen < 134217728 /\ dst + dlen <= CEILING /\
  CEILING <= sp /\ sp + 128 + 48 <= STACK_TOP /\ pdl = sp + 128 + 12 /\ b_strm cx = sp /\
  (b_small cx = 0 \/ b_small cx = 1) /\
  0 <= b_n cx <= 9 /\
  (b_tt cx = 0 \/ (0 < b_tt cx /\ b_tt cx + 400000 * b_n cx <= CEILING)) /\
  (b_ll16 cx = 0 \/ (0 < b_ll16 cx /\ b_ll16 cx + 200000 * b_n cx <= CEILING)) /\
  (b_ll4 cx = 0 \/ (0 < b_ll4 cx /\ b_ll4 cx + 50000 * b_n cx <= CEILING)).

(* [comment removed for export] *)
Definition ctx_al (cx : bctx) : Prop :=
  b_s cx mod 16 = 0 /\ b_sp cx mod 16 = 0 /\ b_src cx mod 16 = 0 /\ b_dst cx mod 16 = 0 /\
  b_tt cx mod 16 = 0 /\ b_ll16 cx mod 16 = 0 /\ b_ll4 cx mod 16 = 0.

(* [comment removed for export] *)
Definition disj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
Definition ctx_sep (cx : bctx) : Prop :=
  let s := b_s cx in let src := b_src cx in let len := b_len cx in let dst := b_dst cx in
  let dlen := b_dlen cx in let n := b_n cx in
  disj s DSTATE_SIZE src len /\ disj s DSTATE_SIZE dst dlen /\ disj src len dst dlen /\
  (b_tt cx <> 0 -> disj s DSTATE_SIZE (b_tt cx) (400000 * n) /\ disj src len (b_tt cx) (400000 * n) /\
                   disj dst dlen (b_tt cx) (400000 * n)) /\
  (b_ll16 cx <> 0 -> disj s DSTATE_SIZE (b_ll16 cx) (200000 * n) /\ disj src len (b_ll16 cx) (200000 * n) /\
                     disj dst dlen (b_ll16 cx) (200000 * n)) /\
  (b_ll4 cx <> 0 -> disj s DSTATE_SIZE (b_ll4 cx) (50000 * n) /\ disj src len (b_ll4 cx) (50000 * n) /\
                    disj dst dlen (b_ll4 cx) (50000 * n)) /\
  (b_ll16 cx <> 0 -> b_ll4 cx <> 0 -> disj (b_ll16 cx) (200000 * n) (b_ll4 cx) (50000 * n)) /\
  (* [comment removed for export] *)
  img_apart s DSTATE_SIZE /\ img_apart dst dlen /\
  (b_tt cx <> 0 -> img_apart (b_tt cx) (400000 * n)) /\
  (b_ll16 cx <> 0 -> img_apart (b_ll16 cx) (200000 * n)) /\
  (b_ll4 cx <> 0 -> img_apart (b_ll4 cx) (50000 * n)).

Definition ctx_ok (cx : bctx) : Prop := ctx_lin cx /\ ctx_al cx /\ ctx_sep cx.

Section Sep.
  Variable cx : bctx. Hypothesis SEP : ctx_sep cx.
  Lemma sep_s_src : disj (b_s cx) DSTATE_SIZE (b_src cx) (b_len cx).
  Proof. destruct SEP as (A & _). exact A. Qed.
  Lemma sep_s_dst : disj (b_s cx) DSTATE_SIZE (b_dst cx) (b_dlen cx).
  Proof. cps_destruct SEP as (_ & A & _). exact A. Qed.
  (* [comment removed for export] *)
  Lemma sep_s_tt : b_tt cx <> 0 -> disj (b_s cx) DSTATE_SIZE (b_tt cx) (400000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & A & _). exact (proj1 (A H)). Qed.
  Lemma sep_src_tt : b_tt cx <> 0 -> disj (b_src cx) (b_len cx) (b_tt cx) (400000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & A & _). exact (proj1 (proj2 (A H))). Qed.
  Lemma sep_dst_tt : b_tt cx <> 0 -> disj (b_dst cx) (b_dlen cx) (b_tt cx) (400000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & A & _). exact (proj2 (proj2 (A H))). Qed.
  Lemma sep_s_ll16 : b_ll16 cx <> 0 -> disj (b_s cx) DSTATE_SIZE (b_ll16 cx) (200000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & A & _). exact (proj1 (A H)). Qed.
  Lemma sep_src_ll16 : b_ll16 cx <> 0 -> disj (b_src cx) (b_len cx) (b_ll16 cx) (200000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & A & _). exact (proj1 (proj2 (A H))). Qed.
  Lemma sep_dst_ll16 : b_ll16 cx <> 0 -> disj (b_dst cx) (b_dlen cx) (b_ll16 cx) (200000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & A & _). exact (proj2 (proj2 (A H))). Qed.
  Lemma sep_s_ll4 : b_ll4 cx <> 0 -> disj (b_s cx) DSTATE_SIZE (b_ll4 cx) (50000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & A & _). exact (proj1 (A H)). Qed.
  Lemma sep_src_ll4 : b_ll4 cx <> 0 -> disj (b_src cx) (b_len cx) (b_ll4 cx) (50000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & A & _). exact (proj1 (proj2 (A H))). Qed.
  Lemma sep_dst_ll4 : b_ll4 cx <> 0 -> disj (b_dst cx) (b_dlen cx) (b_ll4 cx) (50000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & A & _). exact (proj2 (proj2 (A H))). Qed.
  Lemma sep_ll16_ll4 : b_ll16 cx <> 0 -> b_ll4 cx <> 0 -> disj (b_ll16 cx) (200000 * b_n cx) (b_ll4 cx) (50000 * b_n cx).
  Proof. intros H1 H2. cps_destruct SEP as (_ & _ & _ & _ & _ & _ & A & _). exact (A H1 H2). Qed.
  (* [comment removed for export] *)
  Lemma sep_img_s : img_apart (b_s cx) DSTATE_SIZE.
  Proof. cps_destruct SEP as (_ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  (* [comment removed for export] *)
  Lemma sep_img_tt : b_tt cx <> 0 -> img_apart (b_tt cx) (400000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A & _). exact (A H). Qed.
  Lemma sep_img_ll16 : b_ll16 cx <> 0 -> img_apart (b_ll16 cx) (200000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A & _). exact (A H). Qed.
  Lemma sep_img_ll4 : b_ll4 cx <> 0 -> img_apart (b_ll4 cx) (50000 * b_n cx).
  Proof. intros H. cps_destruct SEP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A). exact (A H). Qed.
End Sep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record dhead {W : Type} := DHEAD {
  h_strm : W; h_state : W; h_soch : W; h_solen : W; h_brand : W; h_rNToGo : W; h_rTPos : W;
  h_bsBuff : W; h_bsLive : W; h_n100k : W; h_small : W; h_currBlockNo : W; h_verb : W;
  h_origPtr : W; h_tPos : W; h_k0 : W }.
End ACeilS1.

Arguments dhead W : clear implicits.
Arguments DHEAD {W}.
Section ACeilS2. Context {ACEIL__ : ACeil}.


Record dmid {W : Type} := DMID {
  d_tt : W; d_ll16 : W; d_ll4 : W; d_sbcrc : W; d_sccrc : W; d_cbcrc : W; d_cccrc : W; d_nInUse : W }.
End ACeilS2.

Arguments dmid W : clear implicits.
Arguments DMID {W}.

(* [comment removed for export] *)
(* [comment removed for export] *)
