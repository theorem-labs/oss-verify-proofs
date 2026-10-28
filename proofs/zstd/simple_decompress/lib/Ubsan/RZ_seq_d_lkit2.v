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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_linv_step : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq D1 D2,
  munch [(D1, D2); (q_SPV P - 352, q_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (q_B0 P) (q_B1 P) -> q_DST P <= D1 -> D2 <= OEND ->
  rw_cells usegs m2 (q_SPV P + -352) (seqd_frame P OEND LEND cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq) ->
  seqd_linv P OEND LEND m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' j0 jpad jseq D1 D2 MUL WML MI2 BUF2 HD1 HD2 FR.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XI).
  split; [exists j0, jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 LLL; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 LOF; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 LML; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18; lia|exact I]]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S12 S1 S2 S3 S4 S5 S6 S8 HD1 HD2 Hx; lia| split; [clear - S26 S18 Hx; lia|exact I]]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [exact BUF2|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S18; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HD1 HD2 S5; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seqd_linv_buf : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 D1 D2,
  munch [(D1, D2)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (q_B0 P) (q_B1 P) -> q_DST P <= D1 -> D2 <= OEND ->
  seqd_linv P OEND LEND m2 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 D1 D2 MUL WML MI2 BUF2 HD1 HD2.
  pose proof INV as ((j0 & jpad & jseq & FR) & _).
  eapply (seqd_linv_step P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq D1 D2); try assumption.
  - eapply munch_weaken; [|exact MUL]. unfold sub_fp; cbn [outside]. intros x Hx. tauto.
  - eapply rw_cells_transport; [exact FR | exact MUL | exact WML |].
    clear - ST HD1 HD2. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static seqd_frame q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *. sd_static_open ST. unfold held in *.
    cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2. lia.
Qed.

(* [comment removed for export] *)
Definition seqd_copy_post (P : sdp) (OEND LEND : Z) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (D : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seqd_linv P OEND LEND m' cw bc ptr sLL sOF sML p0 p1 p2 LP.

Lemma seqd_copy_facts : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  stk usegs m1 (q_B0 P) (q_B1 P) /\ rdbl usegs m1 (q_LITP P) (LEND + 32) /\
  4096 <= q_B0 P /\ q_B0 P <= q_DST P /\ OEND <= q_B1 P /\ q_B1 P < 2^47 /\ 4096 <= q_LITP P /\ LEND + 32 < 2^47.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & LIT & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *. sd_static_open ST.
  destruct XI as (_ & _ & BUF & _). repeat (split; [first [assumption | lia]|]). lia.
Qed.

Lemma seqd_copy_spec : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP (D S n : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seqd_static P OEND LEND -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  q_DST P <= D -> 0 <= n -> D + n <= OEND ->
  ((q_LITP P <= S /\ S + n <= LEND + 32) \/ (q_B0 P <= S /\ S + n <= q_B1 P)) ->
  evt usegs (seqd_copy_post P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35670) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP D S n ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HD Hn HDn SRC.
  pose proof (seqd_linv_buf P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as STEP.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seqd_copy_facts P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as FACTS.
  destruct FACTS as (BUF & LIT & F1 & F2 & F3 & F4 & F5 & F6).
  destruct SRC as [(SL1 & SL2)|(SB1 & SB2)].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (q_B0 P) (q_B1 P) (q_LITP P) (LEND + 32) BUF LIT);
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
  - eapply evt_mono.
    + eapply (memmove_reg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 D S n (q_B0 P) (q_B1 P) (q_B0 P) (q_B1 P) BUF (rdbl_of_stk usegs m1 _ _ BUF));
        [ lia | exact MI | reflexivity | reflexivity | reflexivity ].
    + intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & BUF' & _).
      do 15 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact HD | exact HDn].
Qed.

(* [comment removed for export] *)
Ltac sd_copy_intro INV :=
  let ms' := fresh "ms'" in
  intros ms' (?t0 & ?t1 & ?t2 & ?a1 & ?a2 & ?a3 & ?a4 & ?a5 & ?a6 & ?a7 & ?t3 & ?t4 & ?t5 & ?t6 & ?m' & -> & INV);
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
