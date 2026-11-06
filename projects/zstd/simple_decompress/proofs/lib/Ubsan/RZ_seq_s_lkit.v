(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sd_static_open ST := pose proof (proj1 ST) as S1; pose proof (proj2 ST) as ST__1; clear ST; pose proof (proj1 ST__1) as S2; pose proof (proj2 ST__1) as ST__2; clear ST__1; pose proof (proj1 ST__2) as S3; pose proof (proj2 ST__2) as ST__3; clear ST__2; pose proof (proj1 ST__3) as S4; pose proof (proj2 ST__3) as ST__4; clear ST__3; pose proof (proj1 ST__4) as S5; pose proof (proj2 ST__4) as ST__5; clear ST__4; pose proof (proj1 ST__5) as S6; pose proof (proj2 ST__5) as ST__6; clear ST__5; pose proof (proj1 ST__6) as S7; pose proof (proj2 ST__6) as ST__7; clear ST__6; pose proof (proj1 ST__7) as S8; pose proof (proj2 ST__7) as ST__8; clear ST__7; pose proof (proj1 ST__8) as S9; pose proof (proj2 ST__8) as ST__9; clear ST__8; pose proof (proj1 ST__9) as S10; pose proof (proj2 ST__9) as ST__10; clear ST__9; pose proof (proj1 ST__10) as S11; pose proof (proj2 ST__10) as ST__11; clear ST__10; pose proof (proj1 ST__11) as S12; pose proof (proj2 ST__11) as ST__12; clear ST__11; pose proof (proj1 ST__12) as S13; pose proof (proj2 ST__12) as ST__13; clear ST__12; pose proof (proj1 ST__13) as S14; pose proof (proj2 ST__13) as ST__14; clear ST__13; pose proof (proj1 ST__14) as S15; pose proof (proj2 ST__14) as ST__15; clear ST__14; pose proof (proj1 ST__15) as S16; pose proof (proj2 ST__15) as ST__16; clear ST__15; pose proof (proj1 ST__16) as S17; pose proof (proj2 ST__16) as ST__17; clear ST__16; pose proof (proj1 ST__17) as S18; pose proof (proj2 ST__17) as ST__18; clear ST__17; pose proof (proj1 ST__18) as S19; pose proof (proj2 ST__18) as ST__19; clear ST__18; pose proof (proj1 ST__19) as S20; pose proof (proj2 ST__19) as ST__20; clear ST__19; pose proof (proj1 ST__20) as S21; pose proof (proj2 ST__20) as ST__21; clear ST__20; pose proof (proj1 ST__21) as S22; pose proof (proj2 ST__21) as ST__22; clear ST__21; pose proof (proj1 ST__22) as S23; pose proof (proj2 ST__22) as ST__23; clear ST__22; pose proof (proj1 ST__23) as S24; pose proof (proj2 ST__23) as ST__24; clear ST__23; pose proof (proj1 ST__24) as S25; pose proof (proj2 ST__24) as ST__25; clear ST__24; pose proof (proj1 ST__25) as S26; pose proof (proj2 ST__25) as ST__26; clear ST__25; pose proof (proj1 ST__26) as S27; pose proof (proj2 ST__26) as ST__27; clear ST__26; pose proof (proj1 ST__27) as S28; pose proof (proj2 ST__27) as ST__28; clear ST__27; pose proof (proj1 ST__28) as S29; pose proof (proj2 ST__28) as ST__29; clear ST__28; pose proof (proj1 ST__29) as S30; pose proof (proj2 ST__29) as ST__30; clear ST__29; pose proof (proj1 ST__30) as S31; pose proof (proj2 ST__30) as ST__31; clear ST__30; pose proof (proj1 ST__31) as S32; pose proof (proj2 ST__31) as ST__32; clear ST__31; pose proof (proj1 ST__32) as S33; pose proof (proj2 ST__32) as ST__33; clear ST__32; pose proof (proj1 ST__33) as S34; pose proof (proj2 ST__33) as ST__34; clear ST__33; pose proof (proj1 ST__34) as S35; pose proof (proj2 ST__34) as ST__35; clear ST__34; pose proof (proj1 ST__35) as S36; pose proof (proj2 ST__35) as ST__36; clear ST__35; pose proof (proj1 ST__36) as S37; pose proof (proj2 ST__36) as ST__37; clear ST__36; pose proof (proj1 ST__37) as S38; pose proof (proj2 ST__37) as ST__38; clear ST__37; pose proof (proj1 ST__38) as S39; pose proof (proj2 ST__38) as ST__39; clear ST__38; pose proof (proj1 ST__39) as S40; pose proof (proj2 ST__39) as ST__40; clear ST__39; pose proof (proj1 ST__40) as S41; pose proof (proj2 ST__40) as ST__41; clear ST__40; pose proof (proj1 ST__41) as S42; pose proof (proj2 ST__41) as ST__42; clear ST__41; pose proof (proj1 ST__42) as S43; pose proof (proj2 ST__42) as ST__43; clear ST__42; pose proof (proj1 ST__43) as OKLL; pose proof (proj2 ST__43) as ST__44; clear ST__43; pose proof (proj1 ST__44) as OKOF; pose proof (proj2 ST__44) as ST__45; clear ST__44; rename ST__45 into OKML; destruct S43 as (AL1 & AL2 & AL3 & AL4); repeat match goal with H : _ \/ _ |- _ => hold H end.

Lemma seqs_linv_mi : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP -> mem_inv usegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seqs_linv_frame : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(v_SPV P - 384, v_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (v_SPV P + -384) (seqs_frame P OEND c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq) ->
  seqs_linv P OEND LLO LEND LOCV m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP St Lv
         m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq Mu12 Wm12 Mi2 Fr2.
  set (fr := seqs_frame P OEND c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq) in Fr2.
  assert (Fr_sz : Z.of_nat (cells_size fr) = 384) by (unfold fr; destruct P; reflexivity).
  pose proof (stk_of_rw_cells usegs m2 _ fr Fr2) as Fs2.
  rewrite Fr_sz in Fs2.
  replace (v_SPV P + -384 + 384) with (v_SPV P) in Fs2 by lia.
  replace (v_SPV P + -384) with (v_SPV P - 384) in Fs2 by lia.
  pose proof (rdbl_of_stk usegs m2 _ _ Fs2) as Rs2.
  unfold seqs_linv. split; [exists jpad, jseq; exact Fr2|].
  clear Fr2 Fr_sz fr.
  destruct Lv as (_ & Tll & Tof & Tml & Sqb & Lit & Dxr & View & Xi).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv v_SPV v_lo v_DCTX v_LLT v_OFT v_MLT v_SEQ v_sq v_tLL v_tOF v_tML v_ws] in *.
  destruct St as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lo_rng & _ & _ & _ & _ & _ & _ &
                  Sq_off & _ & Dx_off & Ll_off & Of_off & Ml_off & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Ok_ll & Ok_of & Ok_ml).
  destruct Xi as ((r0' & r1' & r2' & Rep) & Dh3 & Buf & Stk & Mu01 & Wm01 & _).
  (* a cell block that ends below the frame or starts above it keeps its contents *)
  assert (Away : forall A cs, rw_cells usegs m1 A cs ->
                   A + Z.of_nat (cells_size cs) <= SPV - 384 \/ SPV <= A -> rw_cells usegs m2 A cs).
  { intros A cs Rw Sep. apply (rw_cells_transport usegs _ m1 m2 A cs Rw Mu12 Wm12). cbn [disjoint_from]. tauto. }
  pose proof (tbl_len_LL tLL Ok_ll) as Len_ll.
  pose proof (tbl_len_OF tOF Ok_of) as Len_of.
  pose proof (tbl_len_ML tML Ok_ml) as Len_ml.
  assert (Tll2 : bytes_at usegs m2 LLT (map (Z_to_bv 8) (seq_table_bytes tLL))).
  { apply (bytes_at_transport usegs _ m1 m2 _ _ Tll Mu12). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (Tof2 : bytes_at usegs m2 OFT (map (Z_to_bv 8) (seq_table_bytes tOF))).
  { apply (bytes_at_transport usegs _ m1 m2 _ _ Tof Mu12). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (Tml2 : bytes_at usegs m2 MLT (map (Z_to_bv 8) (seq_table_bytes tML))).
  { apply (bytes_at_transport usegs _ m1 m2 _ _ Tml Mu12). cbn [disjoint_from]. split; [lia | exact I]. }
  assert (Sqb2 : bytes_at usegs m2 SEQ (map (Z_to_bv 8) sq)).
  { apply (bytes_at_transport usegs _ m1 m2 _ _ Sqb Mu12). cbn [disjoint_from]. rewrite length_map. split; [lia | exact I]. }
  destruct View as (View_c & View_n).
  assert (View2 : h5_viewed m2 DCTX ws (Z_to_bv 64 LOCV)).
  { split; [|exact View_n]. apply (Away _ _ View_c). cbn [h5_vcells cells_size csize]. lia. }
  assert (Rep2 : rw_cells usegs m2 (DCTX + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']).
  { apply (Away _ _ Rep). cbn [cells_size csize]. unfold DCTX_entropy_rep. lia. }
  unfold dctx_h3 in Dh3 |- *.
  pose proof (Away _ _ Dh3 ltac:(cbn [cells_size csize]; lia)) as Dh3_2.
  split; [exact Tll2|]. split; [exact Tof2|]. split; [exact Tml2|]. split; [exact Sqb2|].
  split; [exact (rdbl_after_sub usegs m1 m2 _ _ _ _ Lit Mu12 Rs2)|].
  split; [exact (rdbl_after_sub usegs m1 m2 _ _ _ _ Dxr Mu12 Rs2)|].
  split; [exact View2|].
  split; [exists r0', r1', r2'; exact Rep2|].
  split; [exact Dh3_2|].
  split; [exact (stk_after_sub usegs m1 m2 B0 B1 _ _ Buf Mu12 Wm12 Fs2)|].
  split; [exact (stk_after_sub usegs m1 m2 lo (SPV + -384) _ _ Stk Mu12 Wm12 Fs2)|].
  split; [|split; [exact (wmono_trans usegs m m1 m2 Wm01 Wm12) | exact Mi2]].
  apply (munch_trans _ m m1 m2 Mu01).
  apply (munch_weaken [(SPV - 384, SPV)]); [|exact Mu12].
  intros x Out0. cbn [outside] in Out0 |- *. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Definition seqs_cellfacts (P : ssp) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) : Prop :=
  seqs_next P nLL bLL nOF bOF nML bML /\
  nLL < 512 /\ nOF < 512 /\ nML < 512 /\
  0 <= aLL <= 16 /\ 0 <= aOF <= 31 /\ 0 <= aML <= 16 /\
  0 <= vLL /\ vLL + 2^aLL <= 2^17 /\ 0 <= vML /\ vML + 2^aML <= 2^17 + 3 /\ 0 <= vOF /\ vOF + 2^aOF <= 2^32 - 2 /\
  (aOF = 0 -> vOF = 0) /\ (aOF = 1 -> vOF = 1).

Lemma seqs_linv_cells : forall P OEND LLO LEND LOCV BND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML ->
  exists nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
    (rdn usegs m1 (wa (v_LLT P + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) /\
     rdn usegs m1 (wa (v_LLT P + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) /\
     rdn usegs m1 (wa (v_LLT P + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) /\
     rdn usegs m1 (wa (v_LLT P + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL))) /\
    (rdn usegs m1 (wa (v_OFT P + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) /\
     rdn usegs m1 (wa (v_OFT P + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) /\
     rdn usegs m1 (wa (v_OFT P + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) /\
     rdn usegs m1 (wa (v_OFT P + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF))) /\
    (rdn usegs m1 (wa (v_MLT P + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) /\
     rdn usegs m1 (wa (v_MLT P + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) /\
     rdn usegs m1 (wa (v_MLT P + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) /\
     rdn usegs m1 (wa (v_MLT P + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML))) /\
    seqs_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML.
Proof.
  intros P OEND LLO LEND LOCV BND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP OP St Lv Lf.
  assert (Oks : seq_table_ok K_LL (v_tLL P) /\ seq_table_ok K_OF (v_tOF P) /\ seq_table_ok K_ML (v_tML P)).
  { clear Lv Lf. destruct P. cbn [seqs_static] in St.
    do 43 destruct St as [_ St]. exact St. }
  destruct Oks as (Ok_ll & Ok_of & Ok_ml).
  destruct Lv as (_ & Tll & Tof & Tml & _).
  destruct Lf as (_ & _ & Ix_ll & Ix_of & Ix_ml & _).
  pose proof (seq_cell_know usegs m1 (v_MLT P) K_ML (v_tML P) Tml Ok_ml sML Ix_ml) as Kn_ml.
  pose proof (seq_cell_know usegs m1 (v_OFT P) K_OF (v_tOF P) Tof Ok_of sOF Ix_of) as Kn_of.
  pose proof (seq_cell_know usegs m1 (v_LLT P) K_LL (v_tLL P) Tll Ok_ll sLL Ix_ll) as Kn_ll.
  cbv zeta in Kn_ml, Kn_of, Kn_ll.
  set (cm := st_cell (v_tML P) sML) in Kn_ml.
  set (co := st_cell (v_tOF P) sOF) in Kn_of.
  set (cl := st_cell (v_tLL P) sLL) in Kn_ll.
  destruct Kn_ml as (Rm_n & Rm_a & Rm_b & Rm_v & Cell_ml).
  destruct Kn_of as (Ro_n & Ro_a & Ro_b & Ro_v & Cell_of).
  destruct Kn_ll as (Rl_n & Rl_a & Rl_b & Rl_v & Cell_ll).
  (* field bounds, from the cell invariant and the symbol tables *)
  destruct Cell_ml as (Bits_ml & Next_ml & Fit_ml & Sym_ml).
  destruct Cell_of as (Bits_of & Next_of & Fit_of & Sym_of).
  destruct Cell_ll as (Bits_ll & Next_ll & Fit_ll & Sym_ll).
  pose proof (sym_ok_kind_bounds K_ML cm Sym_ml) as Kb_ml. cbv iota in Kb_ml.
  pose proof (sym_ok_kind_bounds K_OF co Sym_of) as Kb_of. cbv iota in Kb_of.
  pose proof (sym_ok_kind_bounds K_LL cl Sym_ll) as Kb_ll. cbv iota in Kb_ll.
  destruct Kb_ml as (Add_ml & Base_ml & Top_ml & _).
  destruct Kb_of as (Add_of & Base_of & Top_of & Zero_of & One_of & _).
  destruct Kb_ll as (Add_ll & Base_ll & Top_ll & _).
  pose proof (seq_tl_range K_ML (v_tML P) Ok_ml) as Lg_ml.
  pose proof (seq_tl_range K_OF (v_tOF P) Ok_of) as Lg_of.
  pose proof (seq_tl_range K_LL (v_tLL P) Ok_ll) as Lg_ll.
  pose proof (seq_pow_le K_ML (v_tML P) Ok_ml) as Pw_ml.
  pose proof (seq_pow_le K_OF (v_tOF P) Ok_of) as Pw_of.
  pose proof (seq_pow_le K_LL (v_tLL P) Ok_ll) as Pw_ll.
  assert (Pos_ml : 0 < 2 ^ ss_nbBits cm) by (apply Z.pow_pos_nonneg; lia).
  assert (Pos_of : 0 < 2 ^ ss_nbBits co) by (apply Z.pow_pos_nonneg; lia).
  assert (Pos_ll : 0 < 2 ^ ss_nbBits cl) by (apply Z.pow_pos_nonneg; lia).
  exists (ss_next cl), (ss_nbAdd cl), (ss_nbBits cl), (ss_base cl),
         (ss_next co), (ss_nbAdd co), (ss_nbBits co), (ss_base co),
         (ss_next cm), (ss_nbAdd cm), (ss_nbBits cm), (ss_base cm).
  refine (conj (conj Rl_n (conj Rl_a (conj Rl_b Rl_v)))
         (conj (conj Ro_n (conj Ro_a (conj Ro_b Ro_v)))
         (conj (conj Rm_n (conj Rm_a (conj Rm_b Rm_v))) _))).
  unfold seqs_cellfacts, seqs_next.
  repeat match goal with |- _ /\ _ => split end; first [exact Zero_of | exact One_of | lia].
Qed.

(* [comment removed for export] *)
Lemma seqs_linv_lbe : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP V,
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 V ->
  rdn usegs m1 (wa (v_DCTX P + 30360)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 V)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP V Lv Lbe_w.
  destruct Lv as (_ & _ & _ & _ & _ & _ & _ & View & _).
  exact (h5_lbe_know m1 (v_DCTX P) (v_ws P) (Z_to_bv 64 LOCV) V View Lbe_w).
Qed.

Lemma seqs_lfacts_bc : forall P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML,
  seqs_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> bc <= bc' <= B' ->
  seqs_lfacts P OEND LLO LEND B' OP LP bc' ptr sLL sOF sML.
Proof.
  intros P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) H.
  repeat (split; [assumption|]). split; [lia|]. eapply bit_ok_mono; [exact L7| lia].
Qed.

Lemma seqs_lfacts_lp : forall P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML,
  seqs_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> LLO <= LP' <= LEND ->
  seqs_lfacts P OEND LLO LEND B OP LP' bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML (L1 & L2 & L) H. split; [exact L1|]. split; [exact H| exact L]. Qed.
