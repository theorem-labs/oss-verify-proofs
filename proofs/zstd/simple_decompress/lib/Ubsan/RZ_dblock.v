(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable ZdLit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdDctxRep ZdSeqBuildW6 SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_huf_iface RZ_block_iface RZ_seq_iface RZ_tbl RZ_imgfacts
     RZ_blk_iface3 RZ_blk_iface5 RZ_blk_iface6 RZ_seqhdr RZ_declit RZ_offinfo RZ_hufinv seqH_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.

(* [comment removed for export] *)
Lemma seq_tbl_at_fine : forall (m m' : fmem) W DCTX k own dflt d T t,
  seq_tbl_at usegs m k T t -> tbl_ptr DCTX own dflt d T t -> seq_tbl_at usegs m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
  seq_tbl_at usegs m' k T t.
Proof.
  intros m m' W DCTX k own dflt d T t (BA & OK) [-> | [-> ->]] DF MU OUT O1 O2.
  - split; [|exact OK]. pose proof (seq_tbl_len_le k t OK) as L.
    eapply (bytes_at_munch_in usegs m m' W _ _ (DCTX + 32) (DCTX + 10296)); [exact BA | exact MU | exact OUT | lia | lia].
  - exact DF.
Qed.

Lemma seqhdr_tab_fine : forall (m m' : fmem) W DCTX k own dflt d pv,
  seqhdr_tab m DCTX k own dflt d pv -> seq_tbl_at usegs m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
  seqhdr_tab m' DCTX k own dflt d pv.
Proof.
  intros m m' W DCTX k own dflt d pv (T & t & E & TP & TA) DF MU OUT O1 O2. exists T, t. split; [exact E|]. split; [exact TP|].
  eapply seq_tbl_at_fine; eassumption.
Qed.

Lemma ptbl_seq_fine : forall (m m' : fmem) W DCTX llt mlt oft fe,
  ptbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) -> ptbl_seq m' DCTX llt mlt oft fe.
Proof.
  intros m m' W DCTX llt mlt oft fe T MU MI' OUT NZ.
  destruct (T NZ) as (LLT & MLT & OFT & tLL & tOF & tML & E1 & E2 & E3 & P1 & P2 & P3 & A1 & A2 & A3).
  exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [assumption|]).
  split; [|split].
  - eapply seq_tbl_at_fine; [exact A1 | exact P1 | split; [apply pll_default_at; exact MI' | apply LL_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; lia.
  - eapply seq_tbl_at_fine; [exact A2 | exact P2 | split; [apply pof_default_at; exact MI' | apply OF_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; lia.
  - eapply seq_tbl_at_fine; [exact A3 | exact P3 | split; [apply pml_default_at; exact MI' | apply ML_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; lia.
Qed.
(* [comment removed for export] *)
Definition zd_seq_long_relaxed_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem)
         (SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC : Z)
         (sq : list Z) (tLL tOF tML : seq_table) (huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe : word) (ws : list word),
  (* [comment removed for export] *)
  seq_dctx m DCTX LLT MLT OFT huf r0 r1 r2 pde PFX PFX dend expd pcs dsz bt stg le fe ws -> seq_lit2 ws LITP LBE LITB LOC ->
  4096 <= DCTX -> DCTX + DCTX_SIZEOF < 2^47 -> DCTX mod 8 = 0 ->
  (* [comment removed for export] *)
  bytes_at usegs m SEQ (map (Z_to_bv 8) sq) -> all_bytes sq -> 4096 <= SEQ -> SEQ + zlen sq < 2^47 ->
  0 <= nbSeq <= 98047 ->
  (* [comment removed for export] *)
  (nbSeq <> 0 -> seq_table_at m K_LL LLT tLL /\ seq_table_at m K_OF OFT tOF /\ seq_table_at m K_ML MLT tML /\
                 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47) ->
  (* [comment removed for export] *)
  stk usegs m B0 B1 -> B0 <= DST -> (nbSeq <> 0 -> B0 <= PFX <= DST) -> DST + CAP <= B1 -> 0 <= CAP -> B1 < 2^47 ->
  (DST = 0 -> CAP = 0 /\ nbSeq = 0) -> (DST <> 0 -> 4096 <= B0) ->
  (* [comment removed for export] *)
  (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split) -> 4096 <= LITP -> LITP <= LBE -> LBE + WILDCOPY_OVERLENGTH < 2^47 ->
  rdbl usegs m LITP (LBE + WILDCOPY_OVERLENGTH) ->
  seq_lit_placed m DCTX DST CAP B0 B1 LITP LBE LITB LOC ->
  (* [comment removed for export] *)
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - SEQ_LONG_STACK -> 0 <= SPV < 2^47 ->
  off_stack lo SPV DCTX DCTX_SIZEOF -> off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV SEQ (zlen sq) ->
  off_stack lo SPV LITP (LBE + WILDCOPY_OVERLENGTH - LITP) ->
  (nbSeq <> 0 -> off_stack lo SPV LLT (8 * (1 + 2^9)) /\ off_stack lo SPV OFT (8 * (1 + 2^8)) /\ off_stack lo SPV MLT (8 * (1 + 2^9))) ->
  apart B0 (B1 - B0) DCTX DCTX_SIZEOF -> apart B0 (B1 - B0) SEQ (zlen sq) ->
  (nbSeq <> 0 -> apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ apart B0 (B1 - B0) MLT (8 * (1 + 2^9))) ->
  apart SEQ (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) ->
  (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)) ->
  (nbSeq <> 0 -> apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
                 apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)) ->
  SPV mod 16 = 0 -> (nbSeq <> 0 -> LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SEQ -> a4 = Z_to_bv 64 (zlen sq) ->
  a5 = Z_to_bv 64 nbSeq ->
  evt usegs (zd_seq_split_post SEQ_LONG_STACK ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 nbSeq pcs dsz bt stg le fe ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_SEQ_LONG) fc None m (seg_rom usegs)).



(* [comment removed for export] *)
Definition db_hyps (SPV lo DCTX DST CAP B0 B1 PFX SRC slen ip cbs : Z) : Prop :=
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ DCTX mod 8 = 0 /\ 0 <= ip /\ 0 <= cbs < 2^21 /\ ip + cbs <= slen /\ 4096 <= SRC /\ SRC + slen < 2^47
  /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\ (DST = 0 -> CAP = 0) /\ (DST <> 0 -> 4096 <= B0)
  /\ 4096 <= lo /\ lo <= SPV - 2048 /\ SPV < 2^47
  /\ ((PFX = 0 /\ CAP = 0) \/ B0 <= PFX <= DST)
  /\ (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (B1 <= lo \/ SPV <= B0) /\ (SRC + slen <= lo \/ SPV <= SRC)
  /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\ (B1 <= SRC \/ SRC + slen <= B0) /\ (SRC + slen <= DCTX \/ DCTX + 95992 <= SRC).
Ltac open_dbh HY := pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD);
  (* [comment removed for export] *)
  lazymatch type of B0D with _ <= ?DSTv =>
    lazymatch type of DCB with _ + ?CAPv <= _ =>
      lazymatch type of OFFB with _ <= ?lov \/ ?SPVv <= _ =>
        lazymatch type of BD with _ <= ?DCTXv \/ _ =>
          lazymatch type of BSRC with _ <= ?SRCv \/ _ + ?slenv <= _ =>
            assert (OFFDST : DSTv + CAPv <= lov \/ SPVv <= DSTv) by (clear - OFFB B0D DCB; lia);
            assert (DSTD : DSTv + CAPv <= DCTXv \/ DCTXv + 95992 <= DSTv) by (clear - BD B0D DCB; lia);
            assert (DSTSRC : DSTv + CAPv <= SRCv \/ SRCv + slenv <= DSTv) by (clear - BSRC B0D DCB; lia)
          end end end end end;
  hide_all_disj.

Section DB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DCTX DST CAP B0 B1 PFX SRC : Z) (src : list Z) (ip cbs : Z) (h : frame_header)
            (pde expd pcs dsz bt stg : word) (ws : list word).
  Hypothesis HY : db_hyps SPV lo DCTX DST CAP B0 B1 PFX SRC (Z.of_nat (length src)) ip cbs.
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) src.
  Hypothesis BSM : 0 <= fh_bsmax h <= 131072.
  Hypothesis SPA : SPV mod 16 = 0.
  Notation TBLP := (ptbl HUFINVw).
  Notation POST := (zd_dblock_post TBLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP B0 B1 pcs dsz bt stg ws lo m).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -96)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FOOT := [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940); (SPV - 2048, SPV)].

  (* [comment removed for export] *)
  Definition DBB (p0 p1 p2 huv lev fev : word) (wsv : list word) (m1 : fmem) : Prop :=
    dctx_ptrs usegs m1 DCTX p0 p1 p2 huv
    /\ dctx_h1 usegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd
    /\ rw_cells usegs m1 (DCTX + 29928) (zfh_cells h)
    /\ dctx_h3 usegs m1 DCTX pcs dsz bt stg lev fev
    /\ dctx_h5 usegs m1 DCTX wsv
    /\ stk usegs m1 (DCTX + 32) (DCTX + 10296) /\ stk usegs m1 (DCTX + 10296) (DCTX + 26684) /\ stk usegs m1 (DCTX + 26684) (DCTX + 27324)
    /\ stk usegs m1 (DCTX + 27324) (DCTX + 29884) /\ stk usegs m1 (DCTX + 29884) (DCTX + 29888)
    /\ stk usegs m1 (DCTX + 30372) (DCTX + 95940)
    /\ bytes_at usegs m1 SRC (map (Z_to_bv 8) src)
    /\ stk usegs m1 B0 B1
    /\ stk usegs m1 lo (SPV + -96)
    /\ (exists j, rw_cells usegs m1 (SPV + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ mem_inv usegs m1 /\ munch FOOT m m1 /\ wmono usegs m m1.
  Ltac open_dbb I := destruct I as (PTRS & H1 & FP & H3 & H5 & ESEQ & EHUF & EREP & EWK & EPAD & XB & SRCB & BUF & STK & (j & FR) & MI & MU & WM);
                     unfold dctx_ptrs in PTRS; unfold dctx_h1 in H1; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  (* [comment removed for export] *)
  Lemma db_ret : forall m1 p0 p1 p2 huv lev fev wsv r xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 -> 0 <= r < 2^64 -> xa0 = Z_to_bv 64 r ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    (zd_is_error r = false -> TBLP m1 DCTX p0 p1 p2 huv lev fev) ->
    (zd_is_error r = true \/ r <= CAP) ->
    evt usegs POST (ST 0x17928 m1 xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I HR -> KEEP TB RES. pose proof I as (PTRS' & _ & _ & H3' & H5' & _). open_dbb I. open_dbh HY.
    do 11 zstep. zstep.
    release_frame FR STK SPV.
    zstep. apply evt_done. unfold zd_dblock_post.
    do 14 eexists. exists m1, r, p0, p1, p2, huv, lev, fev, wsv.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|]. split; [exact BUF|].
    split; [exact PTRS'|]. split; [exact H3'|]. split; [exact H5'|]. split; [exact KEEP|].
    split.
    { split; [|exact XB].
      eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [exact ESEQ | exact EHUF | lia] | exact EREP | lia] | exact EWK | lia] | exact EPAD | lia]. }
    split; [exact TB|]. split; [exact HR| exact RES].
  Qed.

  Lemma hufinv_fine : forall (m1 m2 : fmem) W huv lev, HUFINVw m1 DCTX huv lev -> munch W m1 m2 ->
    (forall x, DCTX + 10296 <= x < DCTX + 26684 -> outside W x) -> HUFINVw m2 DCTX huv lev.
  Proof. intros m1 m2 W huv lev H MU OUT. eapply hufw_fine; eassumption. Qed.

  Hypothesis HSD : zd_seq_default_stmt.
  Hypothesis HSS : zd_seq_split_stmt.
  Hypothesis HSL : zd_seq_long_relaxed_stmt.


  (* [comment removed for export] *)
  Definition tab_ready (m1 : fmem) (k : seq_kind) (sz : Z) (pv : word) (T : Z) (t : seq_table) : Prop :=
    pv = Z_to_bv 64 T /\ seq_table_at m1 k T t /\ 4096 <= T < 2^47
    /\ off_stack lo (SPV + -96) T sz /\ apart B0 (B1 - B0) T sz /\ apart T sz (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)
    /\ T mod 4 = 0.

  Lemma db_tab_ready : forall m1 k own dflt d pv sz,
    seqhdr_tab m1 DCTX k own dflt d pv -> sz = 8 * (1 + 2^(kind_maxLog k)) -> 32 <= own -> own + sz <= 10296 ->
    65588 <= dflt -> dflt + sz <= 131072 -> own mod 4 = 0 -> dflt mod 4 = 0 ->
    (SPV + -96 <= 0x10000 \/ 0x36000 <= lo) -> (B1 <= 0x10000 \/ 0x36000 <= B0) -> (DCTX + 95940 <= 0x10000 \/ 0x36000 <= DCTX + 30372) ->
    exists T t, tab_ready m1 k sz pv T t.
  Proof.
    intros m1 k own dflt d pv sz (T & t & E & TP & TA) ESZ O1 O2 D1 D2 OA DA IMGS IMGB IMGX. exists T, t.
    pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD).
    assert (KM : 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (P : 256 <= 2^(kind_maxLog k) <= 512) by (destruct k; cbn; lia).
    unfold tab_ready, off_stack, apart, DCTX_entropy_rep, DCTX_SIZEOF.
    split; [exact E|]. split; [exact TA|].
    destruct TP as [-> | [-> _]].
    - clear IMGS IMGB IMGX WIN OFFSRC BSRC SRCD. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
    - clear WIN OFFSRC BSRC SRCD OFFD OFFB BD. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cb12_as_c4s : forall (m1 : fmem) A jj, rw_cells usegs m1 A [CB 12 jj] -> exists a b c, rw_cells usegs m1 A [C4 a; C4 b; C4 c].
  Proof.
    intros m1 A jj H. pose proof H as [[WF _] _]. cbn in WF. destruct WF as [WFJ _].
    exists (le_bytes_to_word (firstn 4 jj)), (le_bytes_to_word (firstn 4 (skipn 4 jj))), (le_bytes_to_word (skipn 8 jj)).
    eapply rw_cells_recell; [exact H | cbn; auto |].
    cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    rewrite !le4_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia).
    rewrite <- (firstn_skipn 4 jj) at 4. f_equal.
    replace (skipn 8 jj) with (skipn 4 (skipn 4 jj)) by (rewrite skipn_skipn; reflexivity). apply firstn_skipn.
  Qed.

  Lemma src_mid : forall (m1 : fmem) i n, bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length src) ->
    let sq := firstn (Z.to_nat n) (skipn (Z.to_nat i) src) in
    bytes_at usegs m1 (SRC + i) (map (Z_to_bv 8) sq) /\ Z.of_nat (length sq) = n /\ Forall (fun c => 0 <= c < 256) sq.
  Proof.
    intros m1 i n SB Hi Hn HL sq.
    destruct (bytes_at_mid m1 SRC _ i n SB Hi Hn ltac:(rewrite length_map; lia)) as [BA _].
    subst sq. rewrite skipn_map, firstn_map in BA. split; [exact BA|].
    split; [rewrite firstn_length, skipn_length; lia|].
    pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i) src) in FB. apply Forall_app in FB. destruct FB as [_ FB].
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) src)) in FB. apply Forall_app in FB. exact (proj1 FB).
  Qed.

  (* [comment removed for export] *)
  Lemma db_lit_default : forall (m1 : fmem) LITP LITSZ LITB LBE LOC,
    stk usegs m1 (DCTX + 30372) (DCTX + 95940) -> bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> stk usegs m1 B0 B1 ->
    0 <= LITSZ <= 131072 -> LITP <= LBE ->
    (LOC = 0 /\ LBE = LITP + LITSZ /\ (LITP = DCTX + 30372 /\ LITSZ <= 65536 \/ SRC + ip <= LITP /\ LBE + 32 <= SRC + ip + cbs)
     \/ LOC = 1 /\ LBE = LITP + LITSZ /\ LITB = LITP /\ DST <= LITB /\ LBE + 32 <= DST + CAP
     \/ LOC = 2 /\ 65536 < LITSZ /\ LITB = LITP /\ DST <= LITP /\ LBE + 32 <= DST + CAP) ->
    LOC <> 2 ->
    (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst) /\ 0 <= LITSZ < 2^32 /\ 4096 <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH < 2^47
    /\ rdbl usegs m1 LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)
    /\ (LOC = ZSTD_in_dst -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH <= B1)
    /\ (LOC = ZSTD_not_in_dst -> apart LITP (LITSZ + WILDCOPY_OVERLENGTH) B0 (B1 - B0))
    /\ off_stack lo (SPV + -96) LITP (LITSZ + WILDCOPY_OVERLENGTH)
    /\ apart LITP (LITSZ + WILDCOPY_OVERLENGTH) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep).
  Proof.
    intros m1 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC NL2.
    pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD).
    unfold ZSTD_not_in_dst, ZSTD_in_dst, WILDCOPY_OVERLENGTH, off_stack, apart, DCTX_entropy_rep, DCTX_litExtraBuffer.
    pose proof (rdbl_of_stk usegs _ _ _ XB) as RX. pose proof (rdbl_of_stk usegs _ _ _ BUF) as RB.
    pose proof (rdbl_of_bytes_at usegs _ _ _ SRCB) as RS. rewrite length_map in RS.
    destruct PLC as [(-> & -> & [(-> & SM) | (SL & SH)]) | [(-> & -> & -> & DL & DH) | (-> & _)]]; [ | | | contradiction].
    - clear WIN OFFB OFFSRC BSRC SRCD. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RX | lia | lia]|]. split; [intros E; discriminate E|]. split; [intros _; lia|]. split; lia.
    - clear WIN OFFB OFFD BD. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RS | lia | lia]|]. split; [intros E; discriminate E|]. split; [intros _; lia|]. split; lia.
    - clear WIN OFFSRC BSRC SRCD. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|]. split; [intros _; lia|]. split; [intros E; discriminate E|]. split; lia.
  Qed.

  Lemma db_lit_placed : forall (m1 : fmem) LITP LITSZ LITB LBE LOC,
    stk usegs m1 (DCTX + 30372) (DCTX + 95940) -> bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> stk usegs m1 B0 B1 ->
    0 <= LITSZ <= 131072 -> LITP <= LBE ->
    (LOC = 0 /\ LBE = LITP + LITSZ /\ (LITP = DCTX + 30372 /\ LITSZ <= 65536 \/ SRC + ip <= LITP /\ LBE + 32 <= SRC + ip + cbs)
     \/ LOC = 1 /\ LBE = LITP + LITSZ /\ LITB = LITP /\ DST <= LITB /\ LBE + 32 <= DST + CAP
     \/ LOC = 2 /\ 65536 < LITSZ /\ LITB = LITP /\ DST <= LITP /\ LBE + 32 <= DST + CAP) ->
    4096 <= LITP /\ LBE + WILDCOPY_OVERLENGTH < 2^47
    /\ rdbl usegs m1 LITP (LBE + WILDCOPY_OVERLENGTH)
    /\ seq_lit_placed m1 DCTX DST CAP B0 B1 LITP LBE LITB LOC
    /\ off_stack lo (SPV + -96) LITP (LBE + WILDCOPY_OVERLENGTH - LITP)
    /\ (LOC <> ZSTD_split -> apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)).
  Proof.
    intros m1 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC.
    pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD).
    unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, off_stack, apart, DCTX_entropy_rep, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz.
    pose proof (rdbl_of_stk usegs _ _ _ XB) as RX. pose proof (rdbl_of_stk usegs _ _ _ BUF) as RB.
    pose proof (rdbl_of_bytes_at usegs _ _ _ SRCB) as RS. rewrite length_map in RS.
    destruct PLC as [(-> & -> & [(-> & SM) | (SL & SH)]) | [(-> & -> & -> & DL & DH) | (-> & BIG & -> & DL & DH)]].
    - clear WIN OFFB OFFSRC BSRC SRCD. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RX | lia | lia]|]. split; [left; split; [reflexivity | lia]|]. split; [lia|]. intros _. lia.
    - clear WIN OFFB OFFD BD. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RS | lia | lia]|]. split; [left; split; [reflexivity | lia]|]. split; [lia|]. intros _. lia.
    - clear WIN OFFSRC BSRC SRCD. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|]. split; [right; left; repeat split; lia|]. split; [lia|]. intros _. lia.
    - clear WIN OFFSRC BSRC SRCD. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|].
      split; [right; right; split; [reflexivity|]; split; [lia|]; split; [lia|]; replace (DCTX + 30372 + 65568) with (DCTX + 95940) by lia; exact RX|].
      split; [lia|]. intros NE. exfalso. apply NE. reflexivity.
  Qed.

  Notation W3 := [(DCTX + 30204, DCTX + 30208); (DST, DST + CAP); (DCTX + 26684, DCTX + 26696); (DCTX + 30004, DCTX + 30008);
                  (DCTX + 30368, DCTX + 30372); (SPV - 2048, SPV)].

  (* [comment removed for export] *)
  Lemma db_fin : forall m1 m2 p0 p1 p2 huv lev fev fev' wsv' r nbSeq xra x5 x6 x7 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev' wsv' m2 ->
    (forall i, h5_block_owned i = false -> wnth wsv' i = wnth ws i) ->
    munch W3 m1 m2 -> HUFINVw m1 DCTX huv lev ->
    ((nbSeq = 0 /\ ptbl_seq m1 DCTX p0 p1 p2 fev)
     \/ (nbSeq <> 0 /\ seqhdr_tab m1 DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable p0 /\
                       seqhdr_tab m1 DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable p2 /\
                       seqhdr_tab m1 DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable p1)) ->
    fev' = (if nbSeq =? 0 then fev else Z_to_bv 64 1) -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= CAP) ->
    evt usegs POST (ST 0x17928 m2 xra x5 x6 x7 xs0 xs1 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP MU3 HINV TABS EFE RR RES.
    pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD).
    assert (DSTD : DST + CAP <= DCTX \/ DCTX + 95992 <= DST) by (clear - BD B0D DCB; lia).
    assert (OUT1 : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W3 x).
    { intros x Hx. cbn [outside]. clear - Hx DSTD OFFD LOS. repeat split; lia. }
    assert (OUT2 : forall x, DCTX + 10296 <= x < DCTX + 26684 -> outside W3 x).
    { intros x Hx. cbn [outside]. clear - Hx DSTD OFFD LOS. repeat split; lia. }
    assert (MI2 : mem_inv usegs m2) by (destruct I as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _); exact MI).
    clear WIN OFFD OFFB OFFSRC BD BSRC SRCD DSTD.
    eapply (db_ret m2 p0 p1 p2 huv lev fev' wsv' r); [exact I | exact RR | reflexivity | exact KEEP | | exact RES].
    intros _. split; [| exact (hufinv_fine _ _ _ _ _ HINV MU3 OUT2)].
    destruct TABS as [(NZ & TS) | (NNZ & TLL & TOF & TML)].
    - subst nbSeq. cbn in EFE. subst fev'. exact (ptbl_seq_fine _ _ _ _ _ _ _ _ TS MU3 MI2 OUT1).
    - pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TLL (conj (pll_default_at _ MI2) LL_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; cbn; lia))
        as (LLT & tLL & -> & PL & AL).
      pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TOF (conj (pof_default_at _ MI2) OF_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; cbn; lia))
        as (OFT & tOF & -> & PO & AO).
      pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TML (conj (pml_default_at _ MI2) ML_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; cbn; lia))
        as (MLT & tML & -> & PM & AM).
      unfold ptbl_seq. eapply zd_tbl_seq_intro; eassumption.
  Qed.
  Ltac cells_words cs :=
    lazymatch cs with
    | nil => constr:(@nil word)
    | C8 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    | C4 ?w :: ?r => let t := cells_words r in constr:(w :: t)
    end.
  (* [comment removed for export] *)
  Lemma db_seq : forall (lng : bool) pcv m1 mc p0 p1 p2 huv lev fev wsv nbSeq i1 rem1 r2 xra x5 x6 x7 xa0 xa1 xa2 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 x28 x29 x30 x31,
    pcv = (if lng then 0x17918 else 0x179ac) ->
    DBB p0 p1 p2 huv lev fev wsv mc -> munch W3 m1 mc ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX huv lev ->
    0 <= nbSeq <= 98047 -> 0 <= i1 -> 0 <= r2 <= rem1 -> ip <= i1 -> i1 + rem1 <= ip + cbs ->
    ((nbSeq = 0 /\ ptbl_seq m1 DCTX p0 p1 p2 fev)
     \/ (nbSeq <> 0 /\ seqhdr_tab m1 DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable p0 /\
                       seqhdr_tab m1 DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable p2 /\
                       seqhdr_tab m1 DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable p1)) ->
    declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    (nbSeq <> 0 -> DST <> 0 /\ CAP <> 0) ->
    rw_cells usegs mc (SPV + -92) [C4 (Z_to_bv 64 nbSeq)] ->
    (lng = true -> xa5 = Z_to_bv 64 nbSeq) ->
    evt usegs POST (ST pcv mc xra x5 x6 x7 (Z_to_bv 64 CAP) (Z_to_bv 64 DST) xa0 xa1 xa2 (Z_to_bv 64 (SRC + i1 + r2)) (Z_to_bv 64 (rem1 - r2)) xa5 xa6 xa7
                       (Z_to_bv 64 DCTX) xs3 xs4 (Z_to_bv 64 (DCTX + 29904)) xs6 xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros EPC I MU3 KEEP HINV NBR I1 R2R IPI IRC TABS PLACED NZD NBC A5. open_dbb I. open_dbh HY.
    destruct PLACED as (LITP & LITSZ & LITB & LBE & LOC & EP & ES & EB & EE & EL & LSZR & LPLE & PLC).
    destruct H5 as [H5 L5]. h5_open wsv L5.
    lazymatch type of EP with ?x = _ => subst x end. lazymatch type of ES with ?x = _ => subst x end. lazymatch type of EB with ?x = _ => subst x end.
    lazymatch type of EE with ?x = _ => subst x end. lazymatch type of EL with ?x = _ => subst x end.
    unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE, DCTX_litExtraBuffer in PLC.
    assert (LOCR : 0 <= LOC <= 2) by (clear - PLC; lia).
    assert (EREPC : DCTX_entropy_rep = 26684) by reflexivity. assert (EFSE : DCTX_fseEntropy = 30004) by reflexivity.
    assert (ELBL : DCTX_litBufferLocation = 30368) by reflexivity. assert (ESZ : DCTX_SIZEOF = 95992) by reflexivity.
    (* [comment removed for export] *)
    assert (OUT1 : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W3 x).
    { intros x Hx. cbn [outside]. clear - Hx DSTD OFFD LOS. unfold hidden in OFFD, DSTD. repeat split; lia. }
    assert (TR : exists LLT MLT OFT tLL tOF tML, p0 = Z_to_bv 64 LLT /\ p1 = Z_to_bv 64 MLT /\ p2 = Z_to_bv 64 OFT /\
              (nbSeq <> 0 -> tab_ready mc K_LL (8 * (1 + 2^9)) p0 LLT tLL /\ tab_ready mc K_OF (8 * (1 + 2^8)) p2 OFT tOF
                             /\ tab_ready mc K_ML (8 * (1 + 2^9)) p1 MLT tML)).
    { unfold hidden in TABS. destruct TABS as [(NZ & TS) | (NNZ & TLL & TOF & TML)].
      - exists (bv_unsigned p0), (bv_unsigned p1), (bv_unsigned p2), LL_defaultDTable, LL_defaultDTable, LL_defaultDTable.
        rewrite !Z_to_bv_lit_self. repeat (split; [reflexivity|]). intros C. contradiction.
      - destruct (NZD NNZ) as [DN0 CN0].
        pose proof (stk_not_ro mc lo (SPV + -96) MI STK ltac:(lia)) as IMGS.
        pose proof (stk_not_ro mc B0 B1 MI BUF ltac:(lia)) as IMGB.
        pose proof (stk_not_ro mc _ _ MI XB ltac:(lia)) as IMGX.
        pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TLL (conj (pll_default_at _ MI) LL_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; cbn; lia)) as TLLc.
        pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TOF (conj (pof_default_at _ MI) OF_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; cbn; lia)) as TOFc.
        pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TML (conj (pml_default_at _ MI) ML_default_ok) MU3 OUT1 ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; cbn; lia)) as TMLc.
        destruct (db_tab_ready mc K_LL _ _ _ p0 (8 * (1 + 2^9)) TLLc eq_refl ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; lia)
                    ltac:(unfold PZD_LL_DEFAULT; lia) ltac:(unfold PZD_LL_DEFAULT; lia) ltac:(reflexivity) ltac:(reflexivity) IMGS IMGB IMGX) as (LLT & tLL & RL).
        destruct (db_tab_ready mc K_OF _ _ _ p2 (8 * (1 + 2^8)) TOFc eq_refl ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; lia)
                    ltac:(unfold PZD_OF_DEFAULT; lia) ltac:(unfold PZD_OF_DEFAULT; lia) ltac:(reflexivity) ltac:(reflexivity) IMGS IMGB IMGX) as (OFT & tOF & RO).
        destruct (db_tab_ready mc K_ML _ _ _ p1 (8 * (1 + 2^9)) TMLc eq_refl ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; lia)
                    ltac:(unfold PZD_ML_DEFAULT; lia) ltac:(unfold PZD_ML_DEFAULT; lia) ltac:(reflexivity) ltac:(reflexivity) IMGS IMGB IMGX) as (MLT & tML & RM).
        exists LLT, MLT, OFT, tLL, tOF, tML. split; [exact (proj1 RL)|]. split; [exact (proj1 RM)|]. split; [exact (proj1 RO)|]. intros _. auto. }
    destruct TR as (LLT & MLT & OFT & tLL & tOF & tML & -> & -> & -> & TRD).
    (* [comment removed for export] *)
    destruct (src_mid mc (i1 + r2) (rem1 - r2) SRCB ltac:(lia) ltac:(lia) ltac:(lia)) as (SQB & SQL & SQF).
    set (sq := firstn (Z.to_nat (rem1 - r2)) (skipn (Z.to_nat (i1 + r2)) src)) in *.
    destruct (stk_open usegs mc _ _ (DCTX + 26684) 12 EREP ltac:(lia) ltac:(lia)) as (jr & REPC & EREPa & EREPb).
    destruct (cb12_as_c4s mc _ _ REPC) as (rp0 & rp1 & rp2 & REP). clear REPC EREP.
    change (Z.of_nat 12) with 12 in EREPb. replace (DCTX + 26684 + 12) with (DCTX + 26696) in EREPb by lia.
    assert (SDC : forall wsl, rw_cells usegs mc (DCTX + 30096) (h5_cells wsl) -> length wsl = 44%nat ->
              seq_dctx mc DCTX LLT MLT OFT huv rp0 rp1 rp2 pde PFX PFX (Z_to_bv 64 0) expd pcs dsz bt stg lev fev wsl).
    { intros wsl HW LW. split; [exact PTRS|]. split; [exact REP|]. split; [exact H1|]. split; [exact H3|]. split; assumption. }
    destruct lng; cbv beta iota in EPC; subst pcv; swap 1 2.
    - (* [comment removed for export] *)
      zstep. rewrite (sx32w_small LOC) by lia. move NBC at bottom. zstep. rewrite (sx32w_small nbSeq) by lia. zstep. zstep. if_cases KL; zify_cond KL.
      + (* [comment removed for export] *)
        do 3 zstep. zstep.
        destruct (db_lit_default mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC KL) as (LOK & LSZ32 & LP0 & LPH & LRD & LIND & LNOT & LOFF & LAP).
        pose proof HSD as SD. unfold zd_seq_default_stmt, PZD_SEQ_DEFAULT in SD.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply evt_cut; [ eapply SD with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1) (SEQ := SRC + (i1 + r2))
                            (nbSeq := nbSeq) (LLT := LLT) (MLT := MLT) (OFT := OFT) (PFX := PFX) (LITP := LITP) (LITSZ := LITSZ) (LITB := LITB) (LOC := LOC)
                            (sq := sq) (tLL := tLL) (tOF := tOF) (tML := tML) (ws := wl);
            first [ eassumption | reflexivity | lia
                  | (apply SDC; [exact H5 | reflexivity])
                  | (unfold seq_lit; repeat split; reflexivity)
                  | (apply Forall_all_bytes; exact SQF)
                  | (unfold off_stack, apart; sep_solve)
                  | (intros NZq; destruct (TRD NZq) as ((_ & TA1 & TR1 & TO1 & TB1 & TD1 & TM1) & (_ & TA2 & TR2 & TO2 & TB2 & TD2 & TM2) & (_ & TA3 & TR3 & TO3 & TB3 & TD3 & TM3));
                     repeat (split; [first [assumption | lia]|]); first [assumption | lia])
                  | (intros NZq; destruct (NZD NZq); unfold hidden in WIN; lia)
                  | (intros E0; split; [apply DNULL; exact E0 | destruct (Z.eq_dec nbSeq 0) as [Q|Q]; [exact Q | exfalso; destruct (NZD Q); contradiction]])
                  | (f_equal; lia) ]
          | clear SD; post_call usegs mc ] end.
        rename PC into STK. rename PC0 into BUF. rename PC1 into REP. rename PC2 into H3. rename PC3 into RR. rename POST into RES.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
        unfold DCTX_entropy_rep in REP.
        pose proof (stk_close usegs md (DCTX + 26684) (DCTX + 27324) (DCTX + 26684) _ EREPa REP
                      ltac:(cbn [cells_size csize Nat.add]; replace (DCTX + 26684 + Z.of_nat 12) with (DCTX + 26696) by lia; exact EREPb)
                      ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EREP.
        zstep.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (db_fin m1 md _ _ _ huv lev fev _ wl _ nbSeq); [ | | exact MU3 | exact HINV | exact TABS | reflexivity | exact RR | exact RES ] end.
        * split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5 | reflexivity]|].
          split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
          split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        * intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      + (* [comment removed for export] *)
        assert (L2 : LOC = 2) by lia. 
        do 3 zstep. zstep.
        destruct (db_lit_placed mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC) as (LP0 & LPH & LRD & LPL & LOFF & LAP).
        assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); unfold hidden in PLC; clear - PLC L2 E0 DNULL LPLE CAP0; lia). specialize (DNN DN0).
        pose proof HSS as SS. unfold zd_seq_split_stmt, zd_seq_split_stmt_at, PZD_SEQ_SPLIT in SS.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply evt_cut; [ eapply SS with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1) (SEQ := SRC + (i1 + r2))
                            (nbSeq := nbSeq) (LLT := LLT) (MLT := MLT) (OFT := OFT) (PFX := PFX) (LITP := LITP) (LBE := LBE) (LITB := LITB) (LOC := LOC)
                            (sq := sq) (tLL := tLL) (tOF := tOF) (tML := tML) (ws := wl);
            first [ eassumption | reflexivity | lia
                  | (apply SDC; [exact H5 | reflexivity])
                  | (unfold seq_lit2; repeat split; reflexivity)
                  | (apply Forall_all_bytes; exact SQF)
                  | (unfold off_stack, apart; sep_solve)
                  | (intros NZq; destruct (TRD NZq) as ((_ & TA1 & TR1 & TO1 & TB1 & TD1 & TM1) & (_ & TA2 & TR2 & TO2 & TB2 & TD2 & TM2) & (_ & TA3 & TR3 & TO3 & TB3 & TD3 & TM3));
                     repeat (split; [first [assumption | lia]|]); first [assumption | lia])
                  | (intros NZq; destruct (NZD NZq); unfold hidden in WIN; lia)
                  | (f_equal; lia) ]
          | clear SS; post_call usegs mc ] end.
        rename PC into STK. rename PC0 into BUF. rename PC1 into REP. rename PC2 into H3. rename PC3 into H5'. rename PC4 into KEEP'. rename PC5 into RR. rename POST into RES.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
        unfold DCTX_entropy_rep in REP.
        pose proof (stk_close usegs md (DCTX + 26684) (DCTX + 27324) (DCTX + 26684) _ EREPa REP
                      ltac:(cbn [cells_size csize Nat.add]; replace (DCTX + 26684 + Z.of_nat 12) with (DCTX + 26696) by lia; exact EREPb)
                      ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EREP.
        zstep.
        lazymatch type of H5' with dctx_h5 _ _ _ ?wl' =>
          eapply (db_fin m1 md _ _ _ huv lev fev _ wl' _ nbSeq); [ | | exact MU3 | exact HINV | exact TABS | reflexivity | exact RR | exact RES ] end.
        * split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [exact H5'|].
          split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
          split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
        * intros i Hi. rewrite KEEP' by (intros E; subst i; discriminate Hi).
          specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
    - (* [comment removed for export] *)
      specialize (A5 eq_refl). subst xa5. do 3 zstep. zstep.
      destruct (db_lit_placed mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC) as (LP0 & LPH & LRD & LPL & LOFF & LAP).
      pose proof HSL as SS. unfold zd_seq_long_relaxed_stmt, PZD_SEQ_LONG in SS.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
      eapply evt_cut; [ eapply SS with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1) (SEQ := SRC + (i1 + r2))
                          (nbSeq := nbSeq) (LLT := LLT) (MLT := MLT) (OFT := OFT) (PFX := PFX) (LITP := LITP) (LBE := LBE) (LITB := LITB) (LOC := LOC)
                          (sq := sq) (tLL := tLL) (tOF := tOF) (tML := tML) (ws := wl);
          first [ eassumption | reflexivity | lia
                | (apply SDC; [exact H5 | reflexivity])
                | (unfold seq_lit2; repeat split; reflexivity)
                | (apply Forall_all_bytes; exact SQF)
                | (unfold off_stack, apart; sep_solve)
                | (intros NZq; destruct (TRD NZq) as ((_ & TA1 & TR1 & TO1 & TB1 & TD1 & TM1) & (_ & TA2 & TR2 & TO2 & TB2 & TD2 & TM2) & (_ & TA3 & TR3 & TO3 & TB3 & TD3 & TM3));
                   repeat (split; [first [assumption | lia]|]); first [assumption | lia])
                | (intros NZq; destruct (NZD NZq); unfold hidden in WIN; lia)
                | (unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split; lia)
                | (intros E0; split; [apply DNULL; exact E0 | destruct (Z.eq_dec nbSeq 0) as [Q|Q]; [exact Q | exfalso; destruct (NZD Q); contradiction]])
                | (f_equal; lia) ]
        | clear SS; post_call usegs mc ] end.
      rename PC into STK. rename PC0 into BUF. rename PC1 into REP. rename PC2 into H3. rename PC3 into H5'. rename PC4 into KEEP'. rename PC5 into RR. rename POST into RES.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into md end.
      unfold DCTX_entropy_rep in REP.
      pose proof (stk_close usegs md (DCTX + 26684) (DCTX + 27324) (DCTX + 26684) _ EREPa REP
                    ltac:(cbn [cells_size csize Nat.add]; replace (DCTX + 26684 + Z.of_nat 12) with (DCTX + 26696) by lia; exact EREPb)
                    ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)) as EREP.
      lazymatch type of H5' with dctx_h5 _ _ _ ?wl' =>
        eapply (db_fin m1 md _ _ _ huv lev fev _ wl' _ nbSeq); [ | | exact MU3 | exact HINV | exact TABS | reflexivity | exact RR | exact RES ] end.
      + split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [exact H5'|].
        split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
        split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros i Hi. rewrite KEEP' by (intros E; subst i; discriminate Hi).
        specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
  Qed.

  (* [comment removed for export] *)
  Lemma db_frame : forall (m1 : fmem) ja w,
    rw_cells usegs m1 (SPV + -96) [CB 4 ja] -> rw_cells usegs m1 (SPV + -92) [C4 w] ->
    rw_cells usegs m1 (SPV + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    exists jj, rw_cells usegs m1 (SPV + -96) [CB 8 jj; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros m1 ja w FA NB FB.
    assert (ALL : rw_cells usegs m1 (SPV + -96) ([CB 4 ja; C4 w] ++ [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split.
      - change [CB 4 ja; C4 w] with ([CB 4 ja] ++ [C4 w]). apply rw_cells_app. split; [exact FA|].
        cbn [cells_size csize Nat.add]. replace (SPV + -96 + Z.of_nat 4) with (SPV + -92) by lia. exact NB.
      - cbn [cells_size csize Nat.add]. replace (SPV + -96 + Z.of_nat 8) with (SPV + -88) by lia. exact FB. }
    pose proof (rw_cells_merge usegs m1 (SPV + -96) [] _ _ ALL) as M. cbn [app cells_size csize Nat.add] in M. eexists. exact M.
  Qed.

  Notation W4 := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (SPV + -92, SPV + -92 + 4); (SPV + -96 - 544, SPV + -96)].

  (* [comment removed for export] *)
  Lemma db_hdr : forall m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v xra x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs8 xs9 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX huv lev -> ptbl_seq m1 DCTX p0 p1 p2 fev ->
    declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    ip <= i1 -> 0 <= rem1 <= 131072 -> i1 + rem1 <= ip + cbs -> a1v - a0v = rem1 -> 0 <= a0v -> 0 <= a1v < 2^64 ->
    evt usegs POST (ST 0x178a0 m1 xra x5 x6 x7 (Z_to_bv 64 CAP) (Z_to_bv 64 DST) (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 (SRC + i1)) xs4 (Z_to_bv 64 (DCTX + 29904)) (Z_to_bv 64 1) xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP HINV TS PLACED IPI REMR IRC ERM A0R A1R. pose proof I as DBI. open_dbb I. open_dbh HY.
    destruct H5 as [H5 L5]. pose proof (conj H5 L5) as H5F. h5_open wsv L5.
    assert (MU4 : munch W4 m1 m1) by apply munch_refl.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. replace (a1v - a0v) with rem1 by lia.
    (* [comment removed for export] *)
    assert (LJ : length j = 8%nat) by (pose proof FR as [[Hwf _] _]; exact (proj1 Hwf)).
    pose proof (rw_cells_split_CB usegs m1 (SPV + -96) [] 8 j [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [4; 4]%nat FR eq_refl) as FS.
    cbn [app mk_CB_cells] in FS. clear FR.
    set (j4 := firstn 4 (skipn 4 j)) in FS. assert (L4 : length j4 = 4%nat) by (subst j4; rewrite firstn_length, skipn_length; lia).
    lazymatch type of FS with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (c1 :: c2 :: rest) with ([c1] ++ [c2] ++ rest) in FS end.
    apply rw_cells_app in FS. destruct FS as [FRa FS]. cbn [cells_size csize Nat.add] in FS.
    apply rw_cells_app in FS. destruct FS as [NB FRb]. cbn [cells_size csize Nat.add] in FRb.
    replace (SPV + -96 + Z.of_nat 4) with (SPV + -92) in * by lia. replace (SPV + -92 + Z.of_nat 4) with (SPV + -88) in * by lia.
    rewrite <- (le4_of_bytes j4 L4) in NB.
    assert (NB' : rw_cells usegs m1 (SPV + -92) [C4 (le_bytes_to_word j4)]).
    { destruct NB as [[Wf B] R]. split; [split|]; [ split; [exact I | exact (proj2 Wf)] | exact B | exact R ]. }
    clear NB. rename NB' into NB.
    destruct (src_mid m1 i1 rem1 SRCB ltac:(lia) ltac:(lia) ltac:(lia)) as (SQB & SQL & SQF).
    set (sq := firstn (Z.to_nat rem1) (skipn (Z.to_nat i1) src)) in *.
    pose proof zd_seqhdr_proof as SH. unfold zd_seqhdr_stmt, PZD_SEQHDR, RZ_blk_iface.off_stack, RZ_blk_iface.apart in SH.
    lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
    eapply evt_cut; [ eapply SH with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (NBP := SPV + -92) (SRC := SRC + i1) (src := sq) (ws := wl) (fe := fev);
        first [ eassumption | reflexivity | lia | (split; [exact H5 | reflexivity]) | sep_solve | (right; lia) | (f_equal; lia) ]
      | clear SH; post_call usegs m1 ] end.
    rename PC into STK. rename PC0 into PTRS. rename PC1 into ESEQ. rename PC2 into EWK. rename PC3 into NB. rename PC4 into RR. rename POST into RES.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    lazymatch type of RR with 0 <= ?r < _ => rename r into r2 end.
    lazymatch type of PTRS with dctx_ptrs _ _ _ ?a ?b ?c _ => rename a into q0; rename b into q1; rename c into q2 end.
    assert (DSTD' : DST + CAP <= DCTX \/ DCTX + 95992 <= DST) by (unfold hidden in DSTD; exact DSTD).
    assert (OUT2 : forall xx, DCTX + 10296 <= xx < DCTX + 26684 -> outside W4 xx).
    { intros xx Hx. cbn [outside]. clear - Hx OFFD LOS. unfold hidden in OFFD. repeat split; lia. }
    pose proof (hufinv_fine _ _ _ _ _ HINV MU4 OUT2) as HINVc. clear DSTD' MU4.
    assert (DBI2 : forall wl, rw_cells usegs mc (DCTX + 30096) (h5_cells wl) -> length wl = 44%nat -> DBB q0 q1 q2 huv lev fev wl mc).
    { intros wl HW LW. destruct (db_frame mc _ _ FRa NB FRb) as (jj & FR). split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [split; assumption|].
      split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
      split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM]. }
    zstep. zstep. if_cases K; zify_cond K.
    { (* [comment removed for export] *)
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (db_ret mc q0 q1 q2 huv lev fev wl r2); [apply DBI2; [exact H5 | reflexivity] | exact RR | reflexivity | | | left ] end.
      - intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      - intros NE. exfalso. unfold zd_is_error, ZE_maxCode in NE. apply Z.ltb_ge in NE. lia.
      - unfold zd_is_error, ZE_maxCode. apply Z.ltb_lt. lia. }
    destruct RES as [ER | (RL & nbSeq & ENB & NBR & CASES)]; [exfalso; unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia|].
    lazymatch type of ENB with ?v = _ => subst v end.
    zstep. zstep. zstep. uck. zstep. zstep. zstep. zb_fix. uck.
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. rewrite (sx32w_small nbSeq) by lia.
    zstep. zstep. zstep. zstep. zstep.
    assert (EA : Z.land (Z.lor (Z.b2z (DST <? 1)) (Z.b2z (CAP <? 1))) (Z.b2z (9223372036854775808 <? Z.lxor nbSeq 9223372036854775808))
                 = if ((DST <? 1) || (CAP <? 1)) && (0 <? nbSeq) then 1 else 0).
    { change 9223372036854775808 with (2^63). rewrite (zb_lxor_pow2_small nbSeq 63) by lia.
      replace (2 ^ 63 <? nbSeq + 2 ^ 63) with (0 <? nbSeq) by (destruct (Z.ltb_spec 0 nbSeq); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia).
      destruct (DST <? 1); destruct (CAP <? 1); destruct (0 <? nbSeq); reflexivity. }
    rewrite EA. clear EA.
    zstep. if_cases K3; zify_cond K3.
    { (* [comment removed for export] *)
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (db_ret mc q0 q1 q2 huv lev fev wl (2^64 - 70)); [apply DBI2; [exact H5 | reflexivity] | lia | apply bv_eq; reflexivity | | | left; reflexivity ] end.
      - intros i Hi. specialize (KEEP i Hi). do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP.
      - intros NE. exfalso. discriminate NE. }
    assert (NZD : nbSeq <> 0 -> DST <> 0 /\ CAP <> 0).
    { intros NZ. destruct (Z.ltb_spec DST 1); destruct (Z.ltb_spec CAP 1); destruct (Z.ltb_spec 0 nbSeq); cbn in K3; try lia. }
    clear K3.
    assert (R2R : 0 <= r2 <= rem1) by lia.
    assert (TABSc : (nbSeq = 0 /\ ptbl_seq mc DCTX q0 q1 q2 fev)
                    \/ (nbSeq <> 0 /\ seqhdr_tab mc DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable q0 /\
                                      seqhdr_tab mc DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable q2 /\
                                      seqhdr_tab mc DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable q1)).
    { unfold hidden in CASES. destruct CASES as [(NZ & -> & -> & -> & MUT) | (NNZ & T3)]; [left | right; split; [exact NNZ | exact T3]].
      split; [exact NZ|]. eapply (ptbl_seq_fine _ _ _ _ _ _ _ _ TS MUT); [assumption|].
      intros xx Hx. cbn [outside]. clear - Hx OFFD LOS. unfold hidden in OFFD. repeat split; lia. }
    clear CASES TS. unfold dctx_ptrs in PTRS.
    zstep. zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW.
      + (* [comment removed for export] *)
        assert (MUS : munch W3 mc mc) by apply munch_refl. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ms end.
        lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
          eapply (db_seq false _ mc ms q0 q1 q2 huv lev fev wl nbSeq i1 rem1 r2); try eassumption; try lia; try reflexivity;
            try (intros; first [reflexivity | discriminate]);
            first [ (destruct (db_frame ms _ _ FRa NB FRb) as (jj & FR);
                     split; [exact PTRS|]; split; [exact H1|]; split; [exact FP|]; split; [exact H3|]; split; [split; [exact H5 | reflexivity]|];
                     split; [exact ESEQ|]; split; [exact EHUF|]; split; [exact EREP|]; split; [exact EWK|]; split; [exact EPAD|]; split; [exact XB|];
                     split; [exact SRCB|]; split; [exact BUF|]; split; [exact STK|]; split; [eexists; exact FR|]; split; [assumption|]; split; [exact MU| exact WM])
                  | (intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP)
                  | exact PLACED ] end.
      + zstep. zstep. if_cases KN; zify_cond KN.
        * (* [comment removed for export] *)
          assert (MUS : munch W3 mc mc) by apply munch_refl. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ms end.
          lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
            eapply (db_seq false _ mc ms q0 q1 q2 huv lev fev wl nbSeq i1 rem1 r2); try eassumption; try lia; try reflexivity;
              try (intros; first [reflexivity | discriminate]);
              first [ (destruct (db_frame ms _ _ FRa NB FRb) as (jj & FR);
                       split; [exact PTRS|]; split; [exact H1|]; split; [exact FP|]; split; [exact H3|]; split; [split; [exact H5 | reflexivity]|];
                       split; [exact ESEQ|]; split; [exact EHUF|]; split; [exact EREP|]; split; [exact EWK|]; split; [exact EPAD|]; split; [exact XB|];
                       split; [exact SRCB|]; split; [exact BUF|]; split; [exact STK|]; split; [eexists; exact FR|]; split; [assumption|]; split; [exact MU| exact WM])
                    | (intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP)
                    | exact PLACED ] end.
        * (* [comment removed for export] *)
          rewrite (signed_lit nbSeq) in KN by lia.
          assert (NNZ : nbSeq <> 0) by lia.
          unfold hidden in TABSc. destruct TABSc as [(NZ & _) | (_ & TLLc & TOFc & TMLc)]; [exfalso; lia|].
          pose proof TOFc as (OFT & tOF & EOF' & PO & AO).
          subst q2.
          assert (OFR : 4096 <= OFT /\ OFT + 2056 < 2^47).
          { destruct PO as [-> | [-> _]]; [unfold DCTX_entropy_OFTable; lia | unfold PZD_OF_DEFAULT; lia]. }
          assert (OFA : OFT mod 4 = 0).
          { destruct PO as [-> | [-> _]]; [unfold DCTX_entropy_OFTable; lia | unfold PZD_OF_DEFAULT; reflexivity]. }
          assert (MU5 : munch [] mc mc) by apply munch_refl.
          zstep. zstep. zstep. zstep. zstep.
          pose proof zd_offinfo_proof as OI. unfold zd_offinfo_stmt, PZD_OFFINFO in OI.
          eapply evt_cut; [ eapply OI with (SPV := SPV + -96) (OFT := OFT) (t := tOF); first [ eassumption | reflexivity | lia ]
            | clear OI; post_call usegs mc ].
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mo end.
          assert (OUTN : forall A B xx, A <= xx < B -> outside [] xx) by (intros; exact I).
          assert (MIo : mem_inv usegs mo) by assumption.
          pose proof (hufinv_fine _ _ _ _ _ HINVc MU5 (OUTN _ _)) as HINVo.
          pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TLLc (conj (pll_default_at _ MIo) LL_default_ok) MU5 (OUTN _ _) ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; cbn; lia)) as TLLo.
          pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TOFc (conj (pof_default_at _ MIo) OF_default_ok) MU5 (OUTN _ _) ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; cbn; lia)) as TOFo.
          pose proof (seqhdr_tab_fine _ _ _ _ _ _ _ _ _ TMLc (conj (pml_default_at _ MIo) ML_default_ok) MU5 (OUTN _ _) ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; cbn; lia)) as TMLo.
          clear MU5. do 4 zstep. assert (MUS : munch W3 mo mo) by apply munch_refl. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ms end.
          zstep. if_cases KO; zify_cond KO.
          -- lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
               eapply (db_seq false _ mo ms q0 q1 (Z_to_bv 64 OFT) huv lev fev wl nbSeq i1 rem1 r2); try eassumption; try lia; try reflexivity;
                 try (intros; first [reflexivity | discriminate]);
                 first [ (destruct (db_frame ms _ _ FRa NB FRb) as (jj & FR);
                          split; [exact PTRS|]; split; [exact H1|]; split; [exact FP|]; split; [exact H3|]; split; [split; [exact H5 | reflexivity]|];
                          split; [exact ESEQ|]; split; [exact EHUF|]; split; [exact EREP|]; split; [exact EWK|]; split; [exact EPAD|]; split; [exact XB|];
                          split; [exact SRCB|]; split; [exact BUF|]; split; [exact STK|]; split; [eexists; exact FR|]; split; [assumption|]; split; [exact MU| exact WM])
                       | (intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP)
                       | (right; split; [assumption|]; split; [assumption|]; split; assumption)
                       | exact PLACED ] end.
          -- zstep. rewrite (sx32w_small nbSeq) by lia. zstep.
             lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
               eapply (db_seq true _ mo ms q0 q1 (Z_to_bv 64 OFT) huv lev fev wl nbSeq i1 rem1 r2); try eassumption; try lia; try reflexivity;
                 try (intros; first [reflexivity | discriminate]);
                 first [ (destruct (db_frame ms _ _ FRa NB FRb) as (jj & FR);
                          split; [exact PTRS|]; split; [exact H1|]; split; [exact FP|]; split; [exact H3|]; split; [split; [exact H5 | reflexivity]|];
                          split; [exact ESEQ|]; split; [exact EHUF|]; split; [exact EREP|]; split; [exact EWK|]; split; [exact EPAD|]; split; [exact XB|];
                          split; [exact SRCB|]; split; [exact BUF|]; split; [exact STK|]; split; [eexists; exact FR|]; split; [assumption|]; split; [exact MU| exact WM])
                       | (intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP)
                       | (right; split; [assumption|]; split; [assumption|]; split; assumption)
                       | exact PLACED ] end.
    - assert (MUS : munch W3 mc mc) by apply munch_refl. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ms end.
      lazymatch type of H5 with rw_cells _ _ _ ?cs => let wl := cells_words cs in
        eapply (db_seq true _ mc ms q0 q1 q2 huv lev fev wl nbSeq i1 rem1 r2); try eassumption; try lia; try reflexivity;
          try (intros; first [reflexivity | discriminate]);
          first [ (destruct (db_frame ms _ _ FRa NB FRb) as (jj & FR);
                   split; [exact PTRS|]; split; [exact H1|]; split; [exact FP|]; split; [exact H3|]; split; [split; [exact H5 | reflexivity]|];
                   split; [exact ESEQ|]; split; [exact EHUF|]; split; [exact EREP|]; split; [exact EWK|]; split; [exact EPAD|]; split; [exact XB|];
                   split; [exact SRCB|]; split; [exact BUF|]; split; [exact STK|]; split; [eexists; exact FR|]; split; [assumption|]; split; [exact MU| exact WM])
                | (intros i Hi; specialize (KEEP i Hi); do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]); exact KEEP)
                | exact PLACED ] end.
  Qed.

  Lemma db_bsm : forall m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v bsm xra x5 x6 x7 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs8 xs9 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX huv lev -> ptbl_seq m1 DCTX p0 p1 p2 fev ->
    declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    ip <= i1 -> 0 <= rem1 <= 131072 -> i1 + rem1 <= ip + cbs -> a1v - a0v = rem1 -> 0 <= a0v -> 0 <= a1v < 2^64 ->
    0 <= bsm <= CAP -> bsm <= 131072 ->
    evt usegs POST (ST 0x17884 m1 xra x5 x6 x7 (Z_to_bv 64 CAP) (Z_to_bv 64 DST) (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) (Z_to_bv 64 bsm) xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 (SRC + i1)) xs4 (Z_to_bv 64 (DCTX + 29904)) (Z_to_bv 64 1) xs7 xs8 xs9 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I KEEP HINV TS PLACED IPI REMR IRC ERM A0R A1R BS1 BS2.
    pose proof HY as (DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH
                      & WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD).
    zstep. zstep. zstep. if_cases KZ; zify_cond KZ.
    - eapply db_hdr; eassumption.
    - zstep. zstep. uck. zstep. uck. zstep. uck. eapply db_hdr; eassumption.
  Qed.

  Hypothesis H1X : huf_1x_stmt.
  Hypothesis H4X : huf_4x_stmt.
  Hypothesis H1W : huf_1x1_wksp_stmt.
  Hypothesis H4W : huf_4x_wksp_stmt.

  Notation W6 := [(DST, DST + CAP); (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884);
                  (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPV + -96 - 1184, SPV + -96)].

  (* [comment removed for export] *)
  Lemma db_main : forall (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) llt mlt oft huf le fe,
    dctx_ptrs usegs m DCTX llt mlt oft huf ->
    dctx_h1 usegs m DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd ->
    rw_cells usegs m (DCTX + 29928) (zfh_cells h) ->
    dctx_h3 usegs m DCTX pcs dsz bt stg le fe ->
    dctx_h5 usegs m DCTX ws -> wnth ws H5_isFrameDecompression = Z_to_bv 64 1 ->
    dctx_owned usegs m DCTX ->
    TBLP m DCTX llt mlt oft huf le fe ->
    bytes_at usegs m SRC (map (Z_to_bv 8) src) -> stk usegs m B0 B1 -> stk usegs m lo SPV -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 (SRC + ip)) (Z_to_bv 64 cbs)
               (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1779c) fc None m (seg_rom usegs)).
  Proof.
    intros until fe. intros PTRS H1 FP H3 H5 ISF (EALL & XB) (TS & HINV) SRCB BUF STK MI. open_dbh HY.
    assert (MU : munch FOOT m m) by apply munch_refl. assert (WM : wmono usegs m m) by apply wmono_refl.
    assert (MU0 : munch [(SPV - 2048, SPV)] m m) by apply munch_refl.
    assert (KEEP : forall i, h5_block_owned i = false -> wnth ws i = wnth ws i) by reflexivity.
    destruct (stk_split usegs m _ (DCTX + 10296) _ EALL ltac:(lia)) as [ESEQ E2]. destruct (stk_split usegs m _ (DCTX + 26684) _ E2 ltac:(lia)) as [EHUF E3].
    destruct (stk_split usegs m _ (DCTX + 27324) _ E3 ltac:(lia)) as [EREP E4]. destruct (stk_split usegs m _ (DCTX + 29884) _ E4 ltac:(lia)) as [EWK EPAD].
    clear EALL E2 E3 E4.
    pose proof (h5_isf_cell _ _ _ H5) as ISFC. rewrite ISF in ISFC.
    unfold zfh_cells in FP. unfold dctx_ptrs in PTRS. unfold dctx_h1 in H1. unfold dctx_h3 in H3. destruct H5 as [H5 L5].
    assert (H5SZ : Z.of_nat (cells_size (h5_cells ws)) = 276) by (rewrite (h5_cells_size ws L5); reflexivity).
    zstep. carve_frame 96%nat STK.
    do 11 zstep.
    zstep. uck. zstep. zstep. zstep. uck. do 5 zstep. zstep. rewrite (sx32w_small 1) by lia. zstep. if_false.
    zstep. rewrite (zx32w_small (fh_bsmax h)) by lia. zstep. if_cases KB; zify_cond KB.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
      assert (OUTA : forall A B, DCTX <= A -> B <= DCTX + 95992 -> forall xx, A <= xx < B -> outside [(SPV - 2048, SPV)] xx).
      { intros A B HA HB xx Hx. cbn [outside]. clear - HA HB Hx OFFD LOS. unfold hidden in OFFD. repeat split; lia. }
      pose proof (ptbl_seq_fine _ _ _ _ _ _ _ _ TS MU0 ltac:(assumption) (OUTA (DCTX + 32) (DCTX + 10296) ltac:(lia) ltac:(lia))) as TSp.
      pose proof (hufinv_fine _ _ _ _ _ HINV MU0 (OUTA (DCTX + 10296) (DCTX + 26684) ltac:(lia) ltac:(lia))) as HINVp.
      clear MU0 TS HINV OUTA.
      assert (MU6 : munch W6 mp mp) by apply munch_refl.
      do 7 zstep. zstep.
      destruct (src_mid mp ip cbs SRCB ltac:(lia) ltac:(lia) ltac:(lia)) as (LSB & LSL & LSF).
      set (lsrc := firstn (Z.to_nat cbs) (skipn (Z.to_nat ip) src)) in *.
      pose proof (zd_declit_proof H1X H4X H1W H4W) as DL. unfold zd_declit_stmt, PZD_DECLIT in DL.
      eapply evt_cut; [ eapply DL with (SPV := SPV + -96) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1) (LSRC := SRC + ip)
                          (src := lsrc) (h := h) (ws := ws) (le := le);
          first [ eassumption | reflexivity | lia | (split; [exact H5 | exact L5]) | sep_solve | (f_equal; lia) ]
        | clear DL; post_call usegs mp ].
      rename PC into STK. rename PC0 into BUF. rename PC1 into PTRS. rename PC2 into EHUF. rename PC3 into EWK. rename PC4 into H3. rename PC5 into H5'.
      rename PC6 into KEEP'. rename PC7 into XB. rename PC8 into RR. rename POST into RES.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into ml end.
      lazymatch type of RR with 0 <= ?r < _ => rename r into r1 end.
      lazymatch type of PTRS with dctx_ptrs _ _ _ _ _ _ ?hv => rename hv into huf' end.
      lazymatch type of H3 with dctx_h3 _ _ _ _ _ _ _ ?lv _ => rename lv into le' end.
      lazymatch type of H5' with dctx_h5 _ _ _ ?wv => rename wv into ws' end.
      assert (OUT1 : forall xx, DCTX + 32 <= xx < DCTX + 10296 -> outside W6 xx).
      { intros xx Hx. cbn [outside]. clear - Hx DSTD OFFD LOS. unfold hidden in OFFD, DSTD. repeat split; lia. }
      pose proof (ptbl_seq_fine _ _ _ _ _ _ _ _ TSp MU6 ltac:(assumption) OUT1) as TSl. clear TSp OUT1 MU6.
      assert (DBI : DBB llt mlt oft huf' le' fe ws' ml).
      { split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [exact H5'|].
        split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
        split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM]. }
      zstep. zstep. if_cases K; zify_cond K.
      { (* [comment removed for export] *)
        eapply (db_ret ml llt mlt oft huf' le' fe ws' r1); [exact DBI | exact RR | reflexivity | exact KEEP' | | left ].
        - intros NE. exfalso. unfold zd_is_error, ZE_maxCode in NE. apply Z.ltb_ge in NE. lia.
        - unfold zd_is_error, ZE_maxCode. apply Z.ltb_lt. lia. }
      destruct RES as [ER | (R1R & HINVl & PLACED)]; [exfalso; unfold zd_is_error, ZE_maxCode in ER; apply Z.ltb_lt in ER; lia|].
      rewrite LSL in PLACED.
      pose proof (h5_isf_cell _ _ _ H5') as ISFC. rewrite (KEEP' H5_isFrameDecompression eq_refl), ISF in ISFC.
      unfold dctx_h3 in H3. unfold dctx_ptrs in PTRS.
      zstep. zstep. zstep. uck. zstep. zstep. zstep. zstep. zb_fix. uck. zstep. rewrite (sx32w_small 1) by lia. zstep. zstep. if_false.
      zstep. rewrite (zx32w_small (fh_bsmax h)) by lia. zstep. zstep. if_cases KM; zify_cond KM.
      + replace (r1 + (SRC + ip)) with (SRC + (ip + r1)) by lia.
        eapply (db_bsm ml llt mlt oft huf' le' fe ws' (ip + r1) (cbs - r1) r1 cbs); try eassumption; try lia.
      + zstep. zstep. replace (r1 + (SRC + ip)) with (SRC + (ip + r1)) by lia.
        eapply (db_bsm ml llt mlt oft huf' le' fe ws' (ip + r1) (cbs - r1) r1 cbs); try eassumption; try lia.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mp end.
      assert (OUTA : forall A B, DCTX <= A -> B <= DCTX + 95992 -> forall xx, A <= xx < B -> outside [(SPV - 2048, SPV)] xx).
      { intros A B HA HB xx Hx. cbn [outside]. clear - HA HB Hx OFFD LOS. unfold hidden in OFFD. repeat split; lia. }
      pose proof (ptbl_seq_fine _ _ _ _ _ _ _ _ TS MU0 ltac:(assumption) (OUTA (DCTX + 32) (DCTX + 10296) ltac:(lia) ltac:(lia))) as TSp.
      pose proof (hufinv_fine _ _ _ _ _ HINV MU0 (OUTA (DCTX + 10296) (DCTX + 26684) ltac:(lia) ltac:(lia))) as HINVp.
      zstep. zstep.
      eapply (db_ret mp llt mlt oft huf le fe ws (2^64 - 72)); [ | lia | apply bv_eq; reflexivity | exact KEEP | | left; reflexivity ].
      + split; [exact PTRS|]. split; [exact H1|]. split; [exact FP|]. split; [exact H3|]. split; [split; [exact H5 | exact L5]|].
        split; [exact ESEQ|]. split; [exact EHUF|]. split; [exact EREP|]. split; [exact EWK|]. split; [exact EPAD|]. split; [exact XB|].
        split; [exact SRCB|]. split; [exact BUF|]. split; [exact STK|]. split; [eexists; exact FR|]. split; [assumption|]. split; [exact MU| exact WM].
      + intros NE. discriminate NE.
  Qed.
End DB.

Theorem zd_dblock_proof :
  huf_1x_stmt -> huf_4x_stmt -> huf_1x1_wksp_stmt -> huf_4x_wksp_stmt ->
  zd_seq_default_stmt -> zd_seq_split_stmt -> zd_seq_long_relaxed_stmt ->
  zd_dblock_stmt (ptbl HUFINVw).
Proof.
  intros H1X H4X H1W H4W HSD HSS HSL. unfold zd_dblock_stmt, PZD_DBLOCK. intros until ws.
  intros PTRS H1 FP BSM WINR H3 H5 ISF OWN TB DCL DCH DCA SRCB AB IP0 CBSR IPC SRCL SRCH BUF B0D DCB CAP0 B1H WIN DNULL DNN STK LO0 LOS SPH
         OFFD OFFB OFFSRC BD BSRC SRCD SPA MI -> -> -> -> -> ->.
  assert (HY : db_hyps SPV lo DCTX DST CAP B0 B1 PFX SRC (Z.of_nat (length src)) ip cbs).
  { unfold db_hyps. repeat (split; [first [assumption | lia]|]). assumption. }
  eapply (db_main ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws HY
            (all_bytes_Forall _ AB) BSM SPA HSD HSS HSL H1X H4X H1W H4W); eassumption.
Qed.

(* [comment removed for export] *)
Theorem zd_dblock_closed :
  huf_1x_stmt -> huf_4x_stmt -> huf_1x1_wksp_stmt -> huf_4x_wksp_stmt ->
  zd_seq_default_stmt -> zd_seq_split_stmt -> zd_seq_long_stmt ->
  zd_dblock_stmt (ptbl HUFINVw).
Proof.
  intros H1X H4X H1W H4W HSD HSS HSL. apply zd_dblock_proof; assumption.
Qed.
