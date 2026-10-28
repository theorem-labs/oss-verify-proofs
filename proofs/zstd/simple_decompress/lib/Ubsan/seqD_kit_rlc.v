From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame Exec Mem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf41_kit_reload seqD_kit_reload huf411_kit_rs RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lkit2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_frame_hd : forall P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq,
  seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq =
  CB 8 j0 :: tl (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq).
Proof. intros. destruct P. reflexivity. Qed.

Lemma seqd_frame_c8 : forall P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq m A (w : word),
  rw_cells usegs m A (C8 w :: tl (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq)) ->
  rw_cells usegs m A (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP (le8 w) jpad jseq).
Proof.
  intros P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq m A w H.
  pose proof H as [[WF _] _]. cbn [cells_wf] in WF.
  eapply rw_cells_recell; [exact H | |].
  - rewrite seqd_frame_hd. cbn [cells_wf cell_wf]. split; [apply length_le8 | exact (proj2 WF)].
  - rewrite seqd_frame_hd. reflexivity.
Qed.

Lemma seqd_fsplit : forall P OEND LEND (w cw : word) bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  C8 w :: tl (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq) =
  (C8 w :: tl (firstn 13 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq))) ++
  bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P) ++ skipn 19 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq).
Proof. intros. destruct P. reflexivity. Qed.

Lemma seqd_fpre_size : forall P OEND LEND (w cw : word) bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  Z.of_nat (cells_size (C8 w :: tl (firstn 13 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq)))) = 104.
Proof. intros. destruct P. reflexivity. Qed.

Lemma seqd_bitd_size : forall a b c d e, Z.of_nat (cells_size (bitd_cells a b c d e)) = 40.
Proof. intros. reflexivity. Qed.

Lemma seqd_fpre_eq : forall P OEND LEND cw bc ptr cw' bc' ptr' sLL sOF sML p0 p1 p2 LP jpad jseq,
  firstn 13 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq) =
  firstn 13 (seqd_frame P OEND LEND cw' bc' ptr' sLL sOF sML p0 p1 p2 LP [] jpad jseq).
Proof. intros. destruct P. reflexivity. Qed.

Lemma seqd_frest_eq : forall P OEND LEND cw bc ptr cw' bc' ptr' sLL sOF sML p0 p1 p2 LP jpad jseq,
  skipn 19 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq) =
  skipn 19 (seqd_frame P OEND LEND cw' bc' ptr' sLL sOF sML p0 p1 p2 LP [] jpad jseq).
Proof. intros. destruct P. reflexivity. Qed.

Lemma seqd_xinv_buf : forall P m fe, seqd_xinv P m fe -> stk usegs m (q_B0 P) (q_B1 P).
Proof. intros P m0 fe0 XI. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_xinv q_B0 q_B1] in *. destruct XI as (_ & _ & B & _). exact B. Qed.

Lemma seqd_rl_ranges : forall P OEND LEND, seqd_static P OEND LEND ->
  4096 <= q_SPV P + -248 /\ q_SPV P + -248 + 40 < 2^47 /\ 4096 <= q_SEQ P /\ q_SEQ P + zlen (q_sq P) < 2^47 /\
  (q_SPV P + -248) mod 8 = 0 /\ (q_SPV P + -248 + 40 <= q_SEQ P \/ q_SEQ P + zlen (q_sq P) <= q_SPV P + -248) /\
  q_lo P <= q_SPV P - 352 /\ q_SPV P < 2^47 /\ q_DST P <= OEND /\ (q_B1 P <= q_lo P \/ q_SPV P <= q_B0 P).
Proof.
  intros P OEND LEND ST. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_static q_SPV q_SEQ q_sq q_lo q_DST q_B0 q_B1] in *.
  sd_static_open ST. try unfold held in *. pose proof (rsk_al_e _ _ ALSP) as AL.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [clear - AL; Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Definition seqd_rl_post (P : sdp) (OEND LEND : Z) (w : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (jpad jseq : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 m' cw',
    ms' = MS (mkR ra (Z_to_bv 64 (q_SPV P + -352)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q_SPV P + -248)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seqd_linv P OEND LEND m' cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP
    /\ rw_cells usegs m' (q_SPV P + -352) (C8 w :: tl (seqd_frame P OEND LEND cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP [] jpad jseq)).

Lemma seqd_rl_spec : forall P OEND LEND m0 m1 (w cw : word) bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq
    ra gp tp t0 t1 t2 s0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seqd_static P OEND LEND ->
  seqd_linv P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  munch [(q_SPV P - 352, q_SPV P)] m0 m1 -> wmono usegs m0 m1 -> mem_inv usegs m1 ->
  rw_cells usegs m1 (q_SPV P + -352) (C8 w :: tl (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq)) ->
  a0r = Z_to_bv 64 (q_SPV P + -248) ->
  0 <= bc <= 64 -> q_SEQ P + 8 <= ptr -> ptr <= q_SEQ P + zlen (q_sq P) - 8 ->
  evt usegs (seqd_rl_post P OEND LEND w bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc)
    (MS (mkR ra (Z_to_bv 64 (q_SPV P + -352)) gp tp t0 t1 t2 s0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PZD_RELOADI) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LEND m0 m1 w cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq ra gp tp t0 t1 t2 s0 s1 a0r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    ST INV MU0 WM0 MI1 FRw EA0 HBC HP1 HP2. subst a0r.
  pose proof (seqd_rl_ranges P OEND LEND ST) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  pose proof (seqd_frame_c8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRw) as FRj.
  pose proof (seqd_linv_frame P OEND LEND m0 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m1 cw bc ptr sLL sOF sML p0 p1 p2 LP (le8 w) jpad jseq MU0 WM0 MI1 FRj) as INV1.
  pose proof (seqd_linv_step P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV1) as STEP.
  destruct INV1 as (_ & _ & _ & _ & SQB & _ & XI).
  pose proof (seqd_xinv_buf _ _ _ XI) as BUF.
  rewrite seqd_fsplit in FRw. apply rw_cells_app in FRw. destruct FRw as (F0 & FRw).
  rewrite seqd_fpre_size in FRw. apply rw_cells_app in FRw. destruct FRw as (BDC & F2).
  rewrite seqd_bitd_size in F2.
  replace (q_SPV P + -352 + 104) with (q_SPV P + -248) in BDC, F2 by lia.
  eapply evt_mono.
  - eapply (seqd_reload_proof ra (Z_to_bv 64 (q_SPV P + -352)) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
             (q_SPV P + -248) (q_SEQ P) (zlen (q_sq P)) bc ptr cw jpad (map (Z_to_bv 8) (q_sq P)));
      first [eassumption | (rewrite length_map; reflexivity) | lia].
  - intros ms' (b1 & b2 & b3 & b4 & b5 & b6 & m' & cw' & -> & MU & WM & MI' & BDC').
    unfold seqd_rl_post. exists b1, b2, b3, b4, b5, b6, m', cw'. split; [reflexivity|].
    assert (F0' : rw_cells usegs m' (q_SPV P + -352) (C8 w :: tl (firstn 13 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq)))).
    { eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. rewrite seqd_fpre_size. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (F2' : rw_cells usegs m' (q_SPV P + -248 + 40) (skipn 19 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP [] jpad jseq))).
    { eapply rw_cells_transport; [exact F2 | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | exact I]. }
    assert (FRn : rw_cells usegs m' (q_SPV P + -352) (C8 w :: tl (seqd_frame P OEND LEND cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP [] jpad jseq))).
    { rewrite seqd_fsplit. apply rw_cells_app. split.
      - rewrite (seqd_fpre_eq P OEND LEND cw' (bc mod 8) (ptr - bc / 8) cw bc ptr). exact F0'.
      - rewrite seqd_fpre_size. apply rw_cells_app. split.
        + replace (q_SPV P + -352 + 104) with (q_SPV P + -248) by lia. exact BDC'.
        + rewrite seqd_bitd_size. replace (q_SPV P + -352 + 104) with (q_SPV P + -248) by lia.
          rewrite (seqd_frest_eq P OEND LEND cw' (bc mod 8) (ptr - bc / 8) cw bc ptr). exact F2'. }
    split; [|exact FRn].
    eapply (STEP m' cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP (le8 w) jpad jseq (q_DST P) (q_DST P)).
    + eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [clear - H2; lia | exact I].
    + exact WM.
    + exact MI'.
    + eapply stk_transport_disjoint; [exact BUF | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia | exact I].
    + lia.
    + exact G9.
    + exact (seqd_frame_c8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRn).
Qed.
