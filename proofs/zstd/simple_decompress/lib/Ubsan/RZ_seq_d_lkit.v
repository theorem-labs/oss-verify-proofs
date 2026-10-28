(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import ZdTbl.

(* [comment removed for export] *)
Ltac sd_static_open ST := pose proof (proj1 ST) as S1; pose proof (proj2 ST) as ST__1; clear ST; pose proof (proj1 ST__1) as S2; pose proof (proj2 ST__1) as ST__2; clear ST__1; pose proof (proj1 ST__2) as S3; pose proof (proj2 ST__2) as ST__3; clear ST__2; pose proof (proj1 ST__3) as S4; pose proof (proj2 ST__3) as ST__4; clear ST__3; pose proof (proj1 ST__4) as S5; pose proof (proj2 ST__4) as ST__5; clear ST__4; pose proof (proj1 ST__5) as S6; pose proof (proj2 ST__5) as ST__6; clear ST__5; pose proof (proj1 ST__6) as S7; pose proof (proj2 ST__6) as ST__7; clear ST__6; pose proof (proj1 ST__7) as S8; pose proof (proj2 ST__7) as ST__8; clear ST__7; pose proof (proj1 ST__8) as S9; pose proof (proj2 ST__8) as ST__9; clear ST__8; pose proof (proj1 ST__9) as S10; pose proof (proj2 ST__9) as ST__10; clear ST__9; pose proof (proj1 ST__10) as S11; pose proof (proj2 ST__10) as ST__11; clear ST__10; pose proof (proj1 ST__11) as S12; pose proof (proj2 ST__11) as ST__12; clear ST__11; pose proof (proj1 ST__12) as S13; pose proof (proj2 ST__12) as ST__13; clear ST__12; pose proof (proj1 ST__13) as S14; pose proof (proj2 ST__13) as ST__14; clear ST__13; pose proof (proj1 ST__14) as S15; pose proof (proj2 ST__14) as ST__15; clear ST__14; pose proof (proj1 ST__15) as S16; pose proof (proj2 ST__15) as ST__16; clear ST__15; pose proof (proj1 ST__16) as S17; pose proof (proj2 ST__16) as ST__17; clear ST__16; pose proof (proj1 ST__17) as S18; pose proof (proj2 ST__17) as ST__18; clear ST__17; pose proof (proj1 ST__18) as S19; pose proof (proj2 ST__18) as ST__19; clear ST__18; pose proof (proj1 ST__19) as S20; pose proof (proj2 ST__19) as ST__20; clear ST__19; pose proof (proj1 ST__20) as S21; pose proof (proj2 ST__20) as ST__21; clear ST__20; pose proof (proj1 ST__21) as S22; pose proof (proj2 ST__21) as ST__22; clear ST__21; pose proof (proj1 ST__22) as S23; pose proof (proj2 ST__22) as ST__23; clear ST__22; pose proof (proj1 ST__23) as S24; pose proof (proj2 ST__23) as ST__24; clear ST__23; pose proof (proj1 ST__24) as S25; pose proof (proj2 ST__24) as ST__25; clear ST__24; pose proof (proj1 ST__25) as S26; pose proof (proj2 ST__25) as ST__26; clear ST__25; pose proof (proj1 ST__26) as S27; pose proof (proj2 ST__26) as ST__27; clear ST__26; pose proof (proj1 ST__27) as S28; pose proof (proj2 ST__27) as ST__28; clear ST__27; pose proof (proj1 ST__28) as S29; pose proof (proj2 ST__28) as ST__29; clear ST__28; pose proof (proj1 ST__29) as S30; pose proof (proj2 ST__29) as ST__30; clear ST__29; pose proof (proj1 ST__30) as S31; pose proof (proj2 ST__30) as ST__31; clear ST__30; pose proof (proj1 ST__31) as S32; pose proof (proj2 ST__31) as ST__32; clear ST__31; pose proof (proj1 ST__32) as S33; pose proof (proj2 ST__32) as ST__33; clear ST__32; pose proof (proj1 ST__33) as S34; pose proof (proj2 ST__33) as ST__34; clear ST__33; pose proof (proj1 ST__34) as S35; pose proof (proj2 ST__34) as ST__35; clear ST__34; pose proof (proj1 ST__35) as OKLL; pose proof (proj2 ST__35) as ST__36; clear ST__35; pose proof (proj1 ST__36) as OKOF; pose proof (proj2 ST__36) as ST__37; clear ST__36; pose proof (proj1 ST__37) as OKML; pose proof (proj2 ST__37) as ST__38; clear ST__37; destruct ST__38 as (ALSP & ALLL & ALOF & ALML); repeat match goal with H : _ \/ _ |- _ => hold H end.

Lemma seqd_linv_mi : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP -> mem_inv usegs m1.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP (_ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

Lemma tbl_len_LL : forall t, seq_table_ok K_LL t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 4104.
Proof. intros t OK. pose proof (seq_tbl_len_le K_LL t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^9)) with 4104 in H. exact H. Qed.
Lemma tbl_len_OF : forall t, seq_table_ok K_OF t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 2056.
Proof. intros t OK. pose proof (seq_tbl_len_le K_OF t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^8)) with 2056 in H. exact H. Qed.
Lemma tbl_len_ML : forall t, seq_table_ok K_ML t -> Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes t))) <= 4104.
Proof. intros t OK. pose proof (seq_tbl_len_le K_ML t OK) as H. cbn [kind_maxLog] in H. change (8 * (1 + 2^9)) with 4104 in H. exact H. Qed.

Lemma seq_pow_le : forall k t, seq_table_ok k t -> 1 <= 2^(st_log t) <= 512.
Proof.
  intros k t OK. pose proof (seq_tl_range k t OK) as R. split; [pose proof (Z.pow_pos_nonneg 2 (st_log t)); lia|].
  change 512 with (2^9). apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Ltac kx_lia ::= kx_bv_ranges; first [ assumption | lia ].

(* [comment removed for export] *)
Ltac sd_is_arith T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | not (@eq Z _ _) => idtac
  | and ?A ?B => sd_is_arith A; sd_is_arith B
  | or ?A ?B => sd_is_arith A; sd_is_arith B
  | ?A -> ?B => sd_is_arith A; sd_is_arith B
  end.
Ltac sd_hold_arith := repeat match goal with H : ?T |- _ => sd_is_arith T; hold H end.

(* [comment removed for export] *)
Lemma seqd_linv_frame : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq,
  munch [(q_SPV P - 352, q_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (q_SPV P + -352) (seqd_frame P OEND LEND cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq) ->
  seqd_linv P OEND LEND m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq MUL WML MI2 FR.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XI).
  split; [exists j0, jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 LLL; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 LOF; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 LML; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18; lia|exact I]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 Hx; lia|exact I]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S18; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Definition seqd_cellfacts (P : sdp) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) : Prop :=
  seqd_next P nLL bLL nOF bOF nML bML /\
  nLL < 512 /\ nOF < 512 /\ nML < 512 /\
  0 <= aLL <= 16 /\ 0 <= aOF <= 31 /\ 0 <= aML <= 16 /\
  0 <= vLL /\ vLL + 2^aLL <= 2^17 /\ 0 <= vML /\ vML + 2^aML <= 2^17 + 3 /\ 0 <= vOF /\ vOF + 2^aOF <= 2^32 - 2 /\
  (aOF = 0 -> vOF = 0) /\ (aOF = 1 -> vOF = 1).

Lemma seqd_linv_cells : forall P OEND LEND BND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND BND OP LP bc ptr sLL sOF sML ->
  exists nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
    (rdn usegs m1 (wa (q_LLT P + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) /\
     rdn usegs m1 (wa (q_LLT P + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) /\
     rdn usegs m1 (wa (q_LLT P + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) /\
     rdn usegs m1 (wa (q_LLT P + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL))) /\
    (rdn usegs m1 (wa (q_OFT P + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) /\
     rdn usegs m1 (wa (q_OFT P + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) /\
     rdn usegs m1 (wa (q_OFT P + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) /\
     rdn usegs m1 (wa (q_OFT P + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF))) /\
    (rdn usegs m1 (wa (q_MLT P + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) /\
     rdn usegs m1 (wa (q_MLT P + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) /\
     rdn usegs m1 (wa (q_MLT P + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) /\
     rdn usegs m1 (wa (q_MLT P + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML))) /\
    seqd_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML.
Proof.
  intros P OEND LEND BND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ST INV LF.
  destruct INV as (_ & TLL & TOF & TML & _). destruct LF as (_ & _ & L3 & L4 & L5 & _).
  assert (OKS : seq_table_ok K_LL (q_tLL P) /\ seq_table_ok K_OF (q_tOF P) /\ seq_table_ok K_ML (q_tML P)).
  { destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *. sd_static_open ST. auto. }
  destruct OKS as (OKLL & OKOF & OKML). clear ST.
  destruct (seq_cell_know usegs m1 _ K_LL _ TLL OKLL sLL L3) as (A0 & A1 & A2 & A3 & (CA1 & CA2 & CA3 & SYA)).
  destruct (seq_cell_know usegs m1 _ K_OF _ TOF OKOF sOF L4) as (B0 & B1 & B2 & B3 & (CB1 & CB2 & CB3 & SYB)).
  destruct (seq_cell_know usegs m1 _ K_ML _ TML OKML sML L5) as (C0 & C1 & C2 & C3 & (CC1 & CC2 & CC3 & SYC)).
  pose proof (sym_ok_kind_bounds K_LL _ SYA) as (YA1 & YA2 & YA3 & _).
  pose proof (sym_ok_kind_bounds K_OF _ SYB) as (YB1 & YB2 & YB3 & YB4 & YB5 & _).
  pose proof (sym_ok_kind_bounds K_ML _ SYC) as (YC1 & YC2 & YC3 & _).
  pose proof (seq_tl_range K_LL _ OKLL) as TA. pose proof (seq_tl_range K_OF _ OKOF) as TB. pose proof (seq_tl_range K_ML _ OKML) as TC.
  assert (PA : 2^(st_log (q_tLL P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PB : 2^(st_log (q_tOF P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PC : 2^(st_log (q_tML P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (QA : 0 < 2^(ss_nbBits (st_cell (q_tLL P) sLL))) by (apply Z.pow_pos_nonneg; lia).
  assert (QB : 0 < 2^(ss_nbBits (st_cell (q_tOF P) sOF))) by (apply Z.pow_pos_nonneg; lia).
  assert (QC : 0 < 2^(ss_nbBits (st_cell (q_tML P) sML))) by (apply Z.pow_pos_nonneg; lia).
  do 12 eexists. split; [repeat split; eassumption|]. split; [repeat split; eassumption|]. split; [repeat split; eassumption|].
  unfold seqd_cellfacts, seqd_next. repeat split; try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma rbf_bound : forall x a, 0 <= x < 2^64 -> 1 <= a <= 63 -> 0 <= x / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2^a.
Proof.
  intros x a Hx Ha.
  assert (E : ((-1 * a) mod 2 ^ 64) mod 64 = 64 - a).
  { replace ((-1 * a) mod 2^64) with (2^64 - a) by (apply Z.mod_unique with (-1); lia).
    symmetry. apply Z.mod_unique with (2^58 - 1); lia. }
  rewrite E. split; [apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  replace (2^64) with (2^(64 - a) * 2^a) in Hx by (rewrite <- Z.pow_add_r by lia; f_equal; lia). lia.
Qed.

Lemma rbf_bound_w : forall (w : word) a, 1 <= a <= 63 -> 0 <= bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2^a.
Proof. intros w a Ha. apply rbf_bound; [|exact Ha]. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. exact R. Qed.

(* [comment removed for export] *)
Ltac sd_rbf :=
  repeat match goal with
  | |- context [bv_unsigned ?w / 2 ^ (((-1 * ?a) mod 2 ^ 64) mod 64)] =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned w / 2 ^ (((-1 * a) mod 2 ^ 64) mod 64) < 2 ^ a |- _ => fail
      | _ => pose proof (rbf_bound_w w a ltac:(lia))
      end
  end.

(* [comment removed for export] *)
Lemma bit_ok_mono : forall S n bc bc' ptr, bit_ok S n bc ptr -> bc <= bc' -> bit_ok S n bc' ptr.
Proof. intros S n bc bc' ptr H L H64. apply H. lia. Qed.

Lemma seqd_lfacts_bc : forall P OEND LEND B B' OP LP bc bc' ptr sLL sOF sML,
  seqd_lfacts P OEND LEND B OP LP bc ptr sLL sOF sML -> bc <= bc' <= B' ->
  seqd_lfacts P OEND LEND B' OP LP bc' ptr sLL sOF sML.
Proof.
  intros P OEND LEND B B' OP LP bc bc' ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) H.
  repeat (split; [assumption|]). split; [lia|]. eapply bit_ok_mono; [exact L7| lia].
Qed.
