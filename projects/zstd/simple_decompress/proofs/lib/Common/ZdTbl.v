(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Tbl.
Variable segs : list Segment.
Notation fmem := (word -> option byte).
(* [comment removed for export] *)
Variables LLD OFD MLD : Z.
(* [comment removed for export] *)
Variable HUFINV : fmem -> Z -> word -> word -> Prop.

(* [comment removed for export] *)
Definition seq_tbl_at (m : fmem) (k : seq_kind) (T : Z) (t : seq_table) : Prop :=
  bytes_at segs m T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok k t.

(* [comment removed for export] *)
Definition tbl_ptr (DCTX own dflt : Z) (d : seq_table) (T : Z) (t : seq_table) : Prop :=
  T = DCTX + own \/ (T = dflt /\ t = d).

Definition zd_tbl_seq (m : fmem) (DCTX : Z) (llt mlt oft fe : word) : Prop :=
  bv_unsigned fe mod 2^32 <> 0 ->
  exists LLT MLT OFT tLL tOF tML,
    llt = Z_to_bv 64 LLT /\ mlt = Z_to_bv 64 MLT /\ oft = Z_to_bv 64 OFT /\
    tbl_ptr DCTX DCTX_entropy_LLTable LLD LL_defaultDTable LLT tLL /\
    tbl_ptr DCTX DCTX_entropy_OFTable OFD OF_defaultDTable OFT tOF /\
    tbl_ptr DCTX DCTX_entropy_MLTable MLD ML_defaultDTable MLT tML /\
    seq_tbl_at m K_LL LLT tLL /\ seq_tbl_at m K_OF OFT tOF /\ seq_tbl_at m K_ML MLT tML.

Definition zd_tbl (m : fmem) (DCTX : Z) (llt mlt oft huf le fe : word) : Prop :=
  zd_tbl_seq m DCTX llt mlt oft fe /\ HUFINV m DCTX huf le.

(* [comment removed for export] *)
Hypothesis LLD_at : forall m, mem_inv segs m -> bytes_at segs m LLD (map (Z_to_bv 8) (seq_table_bytes LL_defaultDTable)).
Hypothesis OFD_at : forall m, mem_inv segs m -> bytes_at segs m OFD (map (Z_to_bv 8) (seq_table_bytes OF_defaultDTable)).
Hypothesis MLD_at : forall m, mem_inv segs m -> bytes_at segs m MLD (map (Z_to_bv 8) (seq_table_bytes ML_defaultDTable)).

(* [comment removed for export] *)
Lemma seq_tbl_at_LLD : forall m, mem_inv segs m -> seq_tbl_at m K_LL LLD LL_defaultDTable.
Proof. intros m MI. split; [apply LLD_at; exact MI | apply LL_default_ok]. Qed.
Lemma seq_tbl_at_OFD : forall m, mem_inv segs m -> seq_tbl_at m K_OF OFD OF_defaultDTable.
Proof. intros m MI. split; [apply OFD_at; exact MI | apply OF_default_ok]. Qed.
Lemma seq_tbl_at_MLD : forall m, mem_inv segs m -> seq_tbl_at m K_ML MLD ML_defaultDTable.
Proof. intros m MI. split; [apply MLD_at; exact MI | apply ML_default_ok]. Qed.

(* [comment removed for export] *)
Lemma seq_tbl_len : forall k t, seq_table_ok k t ->
  Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) = 8 * (1 + 2^(st_log t)) /\ 0 <= st_log t <= kind_maxLog k.
Proof.
  intros k t OK. destruct OK as (H1 & H2 & _). rewrite length_map.
  pose proof (seq_table_bytes_length t) as L. unfold FseNCount.Zlength in *. split; [lia| exact H1].
Qed.

Lemma seq_tbl_len_le : forall k t, seq_table_ok k t ->
  Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 8 * (1 + 2^(kind_maxLog k)).
Proof.
  intros k t OK. destruct (seq_tbl_len k t OK) as (L & R). rewrite L.
  assert (2^(st_log t) <= 2^(kind_maxLog k)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma zd_tbl_seq_intro : forall m DCTX LLT MLT OFT tLL tOF tML fe,
  tbl_ptr DCTX DCTX_entropy_LLTable LLD LL_defaultDTable LLT tLL ->
  tbl_ptr DCTX DCTX_entropy_OFTable OFD OF_defaultDTable OFT tOF ->
  tbl_ptr DCTX DCTX_entropy_MLTable MLD ML_defaultDTable MLT tML ->
  seq_tbl_at m K_LL LLT tLL -> seq_tbl_at m K_OF OFT tOF -> seq_tbl_at m K_ML MLT tML ->
  zd_tbl_seq m DCTX (Z_to_bv 64 LLT) (Z_to_bv 64 MLT) (Z_to_bv 64 OFT) fe.
Proof. intros. intros _. exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [first [reflexivity | assumption]|]). assumption. Qed.

Lemma zd_tbl_seq_off : forall m DCTX llt mlt oft fe, bv_unsigned fe mod 2^32 = 0 -> zd_tbl_seq m DCTX llt mlt oft fe.
Proof. intros m DCTX llt mlt oft fe Z NZ. contradiction. Qed.

(* [comment removed for export] *)
Lemma zd_tbl_seq_init : forall m DCTX llt mlt oft, zd_tbl_seq m DCTX llt mlt oft (Z_to_bv 64 0).
Proof. intros. apply zd_tbl_seq_off. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bytes_at_munch_in : forall (m m' : fmem) W A bs lo hi,
  bytes_at segs m A bs -> munch W m m' -> (forall x, lo <= x < hi -> outside W x) ->
  lo <= A -> A + Z.of_nat (length bs) <= hi -> bytes_at segs m' A bs.
Proof.
  intros m m' W A bs lo hi (H0 & H1 & H) MU OUT L1 L2. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
  apply OUT. rewrite wa_unsigned by lia. lia.
Qed.

Lemma seq_tbl_at_frame : forall (m m' : fmem) W DCTX k own dflt d T t,
  seq_tbl_at m k T t -> tbl_ptr DCTX own dflt d T t -> seq_tbl_at m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 29888 ->
  seq_tbl_at m' k T t.
Proof.
  intros m m' W DCTX k own dflt d T t (BA & OK) [-> | [-> ->]] DF MU OUT O1 O2.
  - split; [|exact OK]. pose proof (seq_tbl_len_le k t OK) as L.
    eapply (bytes_at_munch_in m m' W _ _ (DCTX + 32) (DCTX + 29888)); [exact BA | exact MU | exact OUT | lia | lia].
  - exact DF.
Qed.

Lemma zd_tbl_seq_frame : forall (m m' : fmem) W DCTX llt mlt oft fe,
  zd_tbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv segs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) ->
  zd_tbl_seq m' DCTX llt mlt oft fe.
Proof.
  intros m m' W DCTX llt mlt oft fe T MU MI' OUT NZ.
  destruct (T NZ) as (LLT & MLT & OFT & tLL & tOF & tML & E1 & E2 & E3 & P1 & P2 & P3 & A1 & A2 & A3).
  exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [assumption|]).
  split; [|split].
  - eapply seq_tbl_at_frame; [exact A1 | exact P1 | apply seq_tbl_at_LLD; exact MI' | exact MU | exact OUT | | ];
      unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; lia.
  - eapply seq_tbl_at_frame; [exact A2 | exact P2 | apply seq_tbl_at_OFD; exact MI' | exact MU | exact OUT | | ];
      unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; lia.
  - eapply seq_tbl_at_frame; [exact A3 | exact P3 | apply seq_tbl_at_MLD; exact MI' | exact MU | exact OUT | | ];
      unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; lia.
Qed.

(* [comment removed for export] *)
Hypothesis huf_init : forall m DCTX,
  bytes_at segs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
  HUFINV m DCTX (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0).
Hypothesis huf_frame : forall m m' W DCTX huf le,
  HUFINV m DCTX huf le -> munch W m m' -> mem_inv segs m -> mem_inv segs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) -> HUFINV m' DCTX huf le.

Lemma zd_tbl_init : forall m DCTX llt mlt oft,
  bytes_at segs m (DCTX + 10296) (le4 (Z_to_bv 64 201326604)) ->
  zd_tbl m DCTX llt mlt oft (Z_to_bv 64 (DCTX + 10296)) (Z_to_bv 64 0) (Z_to_bv 64 0).
Proof. intros m DCTX llt mlt oft H. split; [apply zd_tbl_seq_init | apply huf_init; exact H]. Qed.

Lemma zd_tbl_frame : forall m m' W DCTX llt mlt oft huf le fe,
  zd_tbl m DCTX llt mlt oft huf le fe -> munch W m m' -> mem_inv segs m -> mem_inv segs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 29888 -> outside W x) ->
  zd_tbl m' DCTX llt mlt oft huf le fe.
Proof.
  intros m m' W DCTX llt mlt oft huf le fe (S & H) MU MI MI' OUT. split.
  - eapply zd_tbl_seq_frame; eassumption.
  - eapply huf_frame; eassumption.
Qed.
End Tbl.
