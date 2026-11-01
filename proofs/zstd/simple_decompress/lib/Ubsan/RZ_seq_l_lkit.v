(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sd_static_open ST := pose proof (proj1 ST) as S1; pose proof (proj2 ST) as ST__1; clear ST; pose proof (proj1 ST__1) as S2; pose proof (proj2 ST__1) as ST__2; clear ST__1; pose proof (proj1 ST__2) as S3; pose proof (proj2 ST__2) as ST__3; clear ST__2; pose proof (proj1 ST__3) as S4; pose proof (proj2 ST__3) as ST__4; clear ST__3; pose proof (proj1 ST__4) as S5; pose proof (proj2 ST__4) as ST__5; clear ST__4; pose proof (proj1 ST__5) as S6; pose proof (proj2 ST__5) as ST__6; clear ST__5; pose proof (proj1 ST__6) as S7; pose proof (proj2 ST__6) as ST__7; clear ST__6; pose proof (proj1 ST__7) as S8; pose proof (proj2 ST__7) as ST__8; clear ST__7; pose proof (proj1 ST__8) as S9; pose proof (proj2 ST__8) as ST__9; clear ST__8; pose proof (proj1 ST__9) as S10; pose proof (proj2 ST__9) as ST__10; clear ST__9; pose proof (proj1 ST__10) as S11; pose proof (proj2 ST__10) as ST__11; clear ST__10; pose proof (proj1 ST__11) as S12; pose proof (proj2 ST__11) as ST__12; clear ST__11; pose proof (proj1 ST__12) as S13; pose proof (proj2 ST__12) as ST__13; clear ST__12; pose proof (proj1 ST__13) as S14; pose proof (proj2 ST__13) as ST__14; clear ST__13; pose proof (proj1 ST__14) as S15; pose proof (proj2 ST__14) as ST__15; clear ST__14; pose proof (proj1 ST__15) as S16; pose proof (proj2 ST__15) as ST__16; clear ST__15; pose proof (proj1 ST__16) as S17; pose proof (proj2 ST__16) as ST__17; clear ST__16; pose proof (proj1 ST__17) as S18; pose proof (proj2 ST__17) as ST__18; clear ST__17; pose proof (proj1 ST__18) as S19; pose proof (proj2 ST__18) as ST__19; clear ST__18; pose proof (proj1 ST__19) as S20; pose proof (proj2 ST__19) as ST__20; clear ST__19; pose proof (proj1 ST__20) as S21; pose proof (proj2 ST__20) as ST__21; clear ST__20; pose proof (proj1 ST__21) as S22; pose proof (proj2 ST__21) as ST__22; clear ST__21; pose proof (proj1 ST__22) as S23; pose proof (proj2 ST__22) as ST__23; clear ST__22; pose proof (proj1 ST__23) as S24; pose proof (proj2 ST__23) as ST__24; clear ST__23; pose proof (proj1 ST__24) as S25; pose proof (proj2 ST__24) as ST__25; clear ST__24; pose proof (proj1 ST__25) as S26; pose proof (proj2 ST__25) as ST__26; clear ST__25; pose proof (proj1 ST__26) as S27; pose proof (proj2 ST__26) as ST__27; clear ST__26; pose proof (proj1 ST__27) as S28; pose proof (proj2 ST__27) as ST__28; clear ST__27; pose proof (proj1 ST__28) as S29; pose proof (proj2 ST__28) as ST__29; clear ST__28; pose proof (proj1 ST__29) as S30; pose proof (proj2 ST__29) as ST__30; clear ST__29; pose proof (proj1 ST__30) as S31; pose proof (proj2 ST__30) as ST__31; clear ST__30; pose proof (proj1 ST__31) as S32; pose proof (proj2 ST__31) as ST__32; clear ST__31; pose proof (proj1 ST__32) as S33; pose proof (proj2 ST__32) as ST__33; clear ST__32; pose proof (proj1 ST__33) as S34; pose proof (proj2 ST__33) as ST__34; clear ST__33; pose proof (proj1 ST__34) as S35; pose proof (proj2 ST__34) as ST__35; clear ST__34; pose proof (proj1 ST__35) as S36; pose proof (proj2 ST__35) as ST__36; clear ST__35; pose proof (proj1 ST__36) as S37; pose proof (proj2 ST__36) as ST__37; clear ST__36; pose proof (proj1 ST__37) as S38; pose proof (proj2 ST__37) as ST__38; clear ST__37; pose proof (proj1 ST__38) as S39; pose proof (proj2 ST__38) as ST__39; clear ST__38; pose proof (proj1 ST__39) as S40; pose proof (proj2 ST__39) as ST__40; clear ST__39; pose proof (proj1 ST__40) as S41; pose proof (proj2 ST__40) as ST__41; clear ST__40; pose proof (proj1 ST__41) as S42; pose proof (proj2 ST__41) as ST__42; clear ST__41; pose proof (proj1 ST__42) as S43; pose proof (proj2 ST__42) as ST__43; clear ST__42; pose proof (proj1 ST__43) as OKLL; pose proof (proj2 ST__43) as ST__44; clear ST__43; pose proof (proj1 ST__44) as OKOF; pose proof (proj2 ST__44) as ST__45; clear ST__44; rename ST__45 into OKML; destruct S43 as (AL1 & AL2 & AL3 & AL4); repeat match goal with H : _ \/ _ |- _ => hold H end.

Lemma seql_linv_mi : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> mem_inv usegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seql_linv_frame : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq,
  munch [(y_SPV P - 688, y_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (y_SPV P + -688) (seql_frame P OEND c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq) ->
  seql_linv P OEND LLO LEND LOCV m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP Stat Inv1
    m2 c0' c8' c16' c24' c40' c48' c64' c72' c104' c128' c152' c168' c176' c184' c216' c224' c232' c240' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq Shrink Grow MemOk2 Frame2.
  destruct P as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m0 SPV lo DCTX ? ? B0 B1 SEQ ? LLT MLT OFT ? ? ? ? ? sq tLL tOF tML ? ? ? ? ? ? ? ? ? ? ? ? ? ws].
  cbn [seql_static] in Stat.
  do 17 (destruct Stat as [_ Stat]).
  destruct Stat as (LoBelow & _ & _ & _ & _ & _ & OffBuf & OffSeq & OffLit & OffDctx & OffLLT & OffOFT & OffMLT & Stat).
  do 13 (destruct Stat as [_ Stat]).
  destruct Stat as (OkLL & OkOF & OkML).
  pose proof (tbl_len_LL tLL OkLL) as LenLL.
  pose proof (tbl_len_OF tOF OkOF) as LenOF.
  pose proof (tbl_len_ML tML OkML) as LenML.
  unfold seql_linv in Inv1 |- *.
  destruct Inv1 as (_ & ImgLL & ImgOF & ImgML & ImgSeq & LitRd & ExtRd & View & Xinv).
  cbn [y_SPV y_LLT y_OFT y_MLT y_SEQ y_sq y_tLL y_tOF y_tML y_DCTX y_ws seql_xinv] in *.
  destruct Xinv as ((q0 & q1 & q2 & Reps) & Ctl3 & StkBuf & StkLow & Munch0 & Mono0 & _).
  destruct View as (ViewCells & ViewLen).
  unfold dctx_h3 in Ctl3 |- *.
  unfold DCTX_entropy_rep in Reps |- *.
  assert (Away : forall a n, a + n <= SPV - 688 \/ SPV <= a -> disjoint_from [(SPV - 688, SPV)] a n).
  { intros a n Side. split; [exact Side | exact I]. }
  assert (Off : forall x, x < SPV - 688 \/ SPV <= x -> outside [(SPV - 688, SPV)] x).
  { intros x Side. split; [lia | exact I]. }
  eapply bytes_at_transport in ImgLL; [| exact Shrink | apply Away; lia].
  eapply bytes_at_transport in ImgOF; [| exact Shrink | apply Away; lia].
  eapply bytes_at_transport in ImgML; [| exact Shrink | apply Away; lia].
  eapply bytes_at_transport in ImgSeq; [| exact Shrink | apply Away; rewrite length_map; lia].
  eapply rdbl_transport in LitRd; [| exact Shrink | intros x Span; left; apply Off; lia].
  assert (ExtRd2 : LOCV = 2 -> rdbl usegs m2 (DCTX + 30372) (DCTX + 95940)).
  { intros Loc2. eapply rdbl_transport; [exact (ExtRd Loc2) | exact Shrink | intros x Span; left; apply Off; lia]. }
  eapply rw_cells_transport in ViewCells; [| exact Shrink | exact Grow | apply Away; cbn [h5_vcells cells_size csize]; lia].
  eapply rw_cells_transport in Reps; [| exact Shrink | exact Grow | apply Away; cbn [cells_size csize]; lia].
  eapply rw_cells_transport in Ctl3; [| exact Shrink | exact Grow | apply Away; cbn [cells_size csize]; lia].
  eapply stk_transport_disjoint in StkBuf; [| exact Shrink | exact Grow | apply Away; lia].
  eapply stk_transport_disjoint in StkLow; [| exact Shrink | exact Grow | apply Away; lia].
  apply (munch_trans _ m0 m1 m2) in Munch0 as Munch2; [| eapply munch_weaken; [| exact Shrink]].
  2: { intros x Outs. cbn [outside] in Outs |- *. destruct Outs as (_ & _ & _ & _ & OutStack & _). split; [lia | exact I]. }
  pose proof (wmono_trans usegs m0 m1 m2 Mono0 Grow) as Mono2.
  split; [exists jpad, jseq; exact Frame2|].
  do 5 (split; [assumption|]).
  split; [exact ExtRd2|].
  split; [split; assumption|].
  split; [exists q0, q1, q2; exact Reps|].
  do 5 (split; [assumption|]).
  exact MemOk2.
Qed.

(* [comment removed for export] *)
Definition seql_cellfacts (P : slp) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) : Prop :=
  seql_next P nLL bLL nOF bOF nML bML /\
  nLL < 512 /\ nOF < 512 /\ nML < 512 /\
  0 <= aLL <= 16 /\ 0 <= aOF <= 31 /\ 0 <= aML <= 16 /\
  0 <= vLL /\ vLL + 2^aLL <= 2^17 /\ 0 <= vML /\ vML + 2^aML <= 2^17 + 3 /\ 0 <= vOF /\ vOF + 2^aOF <= 2^32 - 2 /\
  (aOF = 0 -> vOF = 0) /\ (aOF = 1 -> vOF = 1).

Lemma seql_linv_cells : forall P OEND LLO LEND LOCV BND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML ->
  exists nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
    (rdn usegs m1 (wa (y_LLT P + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) /\
     rdn usegs m1 (wa (y_LLT P + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) /\
     rdn usegs m1 (wa (y_LLT P + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) /\
     rdn usegs m1 (wa (y_LLT P + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL))) /\
    (rdn usegs m1 (wa (y_OFT P + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) /\
     rdn usegs m1 (wa (y_OFT P + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) /\
     rdn usegs m1 (wa (y_OFT P + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) /\
     rdn usegs m1 (wa (y_OFT P + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF))) /\
    (rdn usegs m1 (wa (y_MLT P + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) /\
     rdn usegs m1 (wa (y_MLT P + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) /\
     rdn usegs m1 (wa (y_MLT P + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) /\
     rdn usegs m1 (wa (y_MLT P + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML))) /\
    seql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML.
Proof.
  intros P OEND LLO LEND LOCV BND m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP Stat Inv1 Facts.
  assert (Oks : seq_table_ok K_LL (y_tLL P) /\ seq_table_ok K_OF (y_tOF P) /\ seq_table_ok K_ML (y_tML P)).
  { clear Inv1 Facts.
    destruct P as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? tLL tOF tML ? ? ? ? ? ? ? ? ? ? ? ? ? ?].
    cbn [seql_static y_tLL y_tOF y_tML] in Stat |- *.
    do 43 (destruct Stat as [_ Stat]).
    exact Stat. }
  destruct Oks as (OkLL & OkOF & OkML).
  destruct Facts as (_ & _ & StLL & StOF & StML & _ & _).
  destruct Inv1 as (_ & ImgLL & ImgOF & ImgML & _).
  destruct (seq_cell_know usegs m1 _ K_LL _ ImgLL OkLL sLL StLL) as (NxLL & AdLL & BtLL & BsLL & CellLL).
  destruct (seq_cell_know usegs m1 _ K_OF _ ImgOF OkOF sOF StOF) as (NxOF & AdOF & BtOF & BsOF & CellOF).
  destruct (seq_cell_know usegs m1 _ K_ML _ ImgML OkML sML StML) as (NxML & AdML & BtML & BsML & CellML).
  set (eLL := st_cell (y_tLL P) sLL) in *.
  set (eOF := st_cell (y_tOF P) sOF) in *.
  set (eML := st_cell (y_tML P) sML) in *.
  exists (ss_next eLL), (ss_nbAdd eLL), (ss_nbBits eLL), (ss_base eLL),
         (ss_next eOF), (ss_nbAdd eOF), (ss_nbBits eOF), (ss_base eOF),
         (ss_next eML), (ss_nbAdd eML), (ss_nbBits eML), (ss_base eML).
  refine (conj (conj NxLL (conj AdLL (conj BtLL BsLL)))
            (conj (conj NxOF (conj AdOF (conj BtOF BsOF)))
              (conj (conj NxML (conj AdML (conj BtML BsML))) _))).
  pose proof (seq_pow_le K_LL _ OkLL) as PowLL.
  pose proof (seq_pow_le K_OF _ OkOF) as PowOF.
  pose proof (seq_pow_le K_ML _ OkML) as PowML.
  destruct CellLL as (BitsLL & NextLL & FitLL & SymLL).
  destruct CellOF as (BitsOF & NextOF & FitOF & SymOF).
  destruct CellML as (BitsML & NextML & FitML & SymML).
  pose proof (sym_ok_kind_bounds K_LL _ SymLL) as (AddLL & BaseLL & TopLL & _).
  pose proof (sym_ok_kind_bounds K_OF _ SymOF) as (AddOF & BaseOF & TopOF & ZeroOF & OneOF & _).
  pose proof (sym_ok_kind_bounds K_ML _ SymML) as (AddML & BaseML & TopML & _).
  pose proof (Z.pow_pos_nonneg 2 (ss_nbBits eLL) ltac:(lia)) as WideLL.
  pose proof (Z.pow_pos_nonneg 2 (ss_nbBits eOF) ltac:(lia)) as WideOF.
  pose proof (Z.pow_pos_nonneg 2 (ss_nbBits eML) ltac:(lia)) as WideML.
  unfold seql_cellfacts, seql_next.
  pose proof (seq_tl_range K_LL _ OkLL) as LogLL.
  pose proof (seq_tl_range K_OF _ OkOF) as LogOF.
  pose proof (seq_tl_range K_ML _ OkML) as LogML.
  lia.
Qed.

(* [comment removed for export] *)
Lemma seql_linv_lbe : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP V,
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> wnth (y_ws P) H5_litBufferEnd = Z_to_bv 64 V ->
  rdn usegs m1 (wa (y_DCTX P + 30360)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 V)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP V Inv1 LbeWord.
  destruct Inv1 as (_ & _ & _ & _ & _ & _ & _ & View & _).
  exact (h5_lbe_know m1 (y_DCTX P) (y_ws P) _ V View LbeWord).
Qed.

Lemma seql_lfacts_bc : forall P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML,
  seql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> bc <= bc' <= B' ->
  seql_lfacts P OEND LLO LEND B' OP LP bc' ptr sLL sOF sML.
Proof.
  intros P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) H.
  repeat (split; [assumption|]). split; [lia|]. eapply bit_ok_mono; [exact L7| lia].
Qed.

Lemma seql_lfacts_lp : forall P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML,
  seql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> LLO <= LP' <= LEND ->
  seql_lfacts P OEND LLO LEND B OP LP' bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML (L1 & L2 & L) H. split; [exact L1|]. split; [exact H| exact L]. Qed.
