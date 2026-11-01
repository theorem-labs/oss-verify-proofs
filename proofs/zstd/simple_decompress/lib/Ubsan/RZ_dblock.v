(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  intros m m' W DCTX k own dflt d T t OLD WHERE NEWDFL KEEP AWAY OWN_LO OWN_HI.
  destruct WHERE as [INDCTX | [ISDFL ISD]].
  2: { subst T t. exact NEWDFL. }
  destruct OLD as [(TLO & THI & READS) SHAPE].
  pose proof (seq_tbl_len_le k t SHAPE) as SPAN.
  set (S := 8 * (1 + 2 ^ kind_maxLog k)) in *.
  split; [| exact SHAPE].
  split; [lia|]. split; [lia|].
  intros i IDX. specialize (READS i IDX). unfold mrd in *.
  rewrite KEEP; [exact READS|].
  rewrite wa_unsigned by lia. apply AWAY. lia.
Qed.

Lemma seqhdr_tab_fine : forall (m m' : fmem) W DCTX k own dflt d pv,
  seqhdr_tab m DCTX k own dflt d pv -> seq_tbl_at usegs m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
  seqhdr_tab m' DCTX k own dflt d pv.
Proof.
  intros m m' W DCTX k own dflt d pv (T & t & PV & WHERE & OLD) NEWDFL KEEP AWAY OWN_LO OWN_HI.
  exists T, t. refine (conj PV (conj WHERE _)).
  exact (seq_tbl_at_fine m m' W DCTX k own dflt d T t OLD WHERE NEWDFL KEEP AWAY OWN_LO OWN_HI).
Qed.

Lemma ptbl_seq_fine : forall (m m' : fmem) W DCTX llt mlt oft fe,
  ptbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv usegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) -> ptbl_seq m' DCTX llt mlt oft fe.
Proof.
  intros m m' W DCTX llt mlt oft fe TABS KEEP MINV AWAY FESET.
  destruct (TABS FESET) as (LLT & MLT & OFT & tLL & tOF & tML & ELL & EML & EOF & WLL & WOF & WML & ALL & AOF & AML).
  exists LLT, MLT, OFT, tLL, tOF, tML.
  do 6 (split; [assumption|]).
  unfold DCTX_entropy_LLTable, DCTX_entropy_OFTable, DCTX_entropy_MLTable in *.
  split; [| split].
  - eapply seq_tbl_at_fine; [exact ALL | exact WLL | apply (seq_tbl_at_LLD usegs _ pll_default_at _ MINV) | exact KEEP | exact AWAY | lia | cbn; lia].
  - eapply seq_tbl_at_fine; [exact AOF | exact WOF | apply (seq_tbl_at_OFD usegs _ pof_default_at _ MINV) | exact KEEP | exact AWAY | lia | cbn; lia].
  - eapply seq_tbl_at_fine; [exact AML | exact WML | apply (seq_tbl_at_MLD usegs _ pml_default_at _ MINV) | exact KEEP | exact AWAY | lia | cbn; lia].
Qed.
(* [comment removed for export] *)
Definition zd_seq_long_relaxed_stmt : Prop :=
  zd_seq_long_stmt_at PZD_SEQ_LONG 896 (fun LOC => LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split).



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
    dctx_ptrs usegs m1 DCTX p0 p1 p2 huv /\
    dctx_h1 usegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd /\
    rw_cells usegs m1 (DCTX + 29928) (zfh_cells h) /\
    dctx_h3 usegs m1 DCTX pcs dsz bt stg lev fev /\
    dctx_h5 usegs m1 DCTX wsv /\
    stk usegs m1 (DCTX + 32) (DCTX + 10296) /\
    stk usegs m1 (DCTX + 10296) (DCTX + 26684) /\
    stk usegs m1 (DCTX + 26684) (DCTX + 27324) /\
    stk usegs m1 (DCTX + 27324) (DCTX + 29884) /\
    stk usegs m1 (DCTX + 29884) (DCTX + 29888) /\
    stk usegs m1 (DCTX + 30372) (DCTX + 95940) /\
    bytes_at usegs m1 SRC (map (Z_to_bv 8) src) /\
    stk usegs m1 B0 B1 /\
    stk usegs m1 lo (SPV + -96) /\
    (exists j, rw_cells usegs m1 (SPV + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
    mem_inv usegs m1 /\ munch FOOT m m1 /\ wmono usegs m m1.
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
    pv = Z_to_bv 64 T /\ seq_tbl_at usegs m1 k T t /\ 4096 <= T /\ T + sz < 2^47 /\ T mod 4 = 0 /\
    off_stack lo (SPV + -96) T sz /\ apart B0 (B1 - B0) T sz /\
    apart T sz (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep).

  Lemma db_tab_ready : forall m1 k own dflt d pv sz,
    seqhdr_tab m1 DCTX k own dflt d pv -> sz = 8 * (1 + 2^(kind_maxLog k)) -> 32 <= own -> own + sz <= 10296 ->
    65588 <= dflt -> dflt + sz <= 131072 -> own mod 4 = 0 -> dflt mod 4 = 0 ->
    (SPV + -96 <= 0x10000 \/ 0x36000 <= lo) -> (B1 <= 0x10000 \/ 0x36000 <= B0) -> (DCTX + 95940 <= 0x10000 \/ 0x36000 <= DCTX + 30372) ->
    exists T t, tab_ready m1 k sz pv T t.
  Proof using HY SPA.
    intros m1 k own dflt d pv sz (T & t & PV & WHERE & AT) SZ OWN_LO OWN_HI DFL_LO DFL_HI OWN4 DFL4 STKROM BUFROM DCTXROM.
    pose proof HY as (CTX_LO & CTX_HI & CTX_AL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & CTX_STK & _ & _ & CTX_BUF & _ & _).
    assert (SZPOS : 2056 <= sz <= 4104) by (subst sz; destruct k; cbn; lia).
    clear SZ.
    exists T, t. unfold tab_ready, off_stack, apart, DCTX_SIZEOF, DCTX_entropy_rep.
    split; [exact PV|]. split; [exact AT|].
    destruct WHERE as [INDCTX | [ISDFL _]]; subst T.
    - clear STKROM BUFROM DCTXROM DFL_LO DFL_HI DFL4.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [destruct CTX_STK; lia|]. split; [destruct CTX_BUF; lia|]. lia.
    - clear CTX_STK CTX_BUF OWN_LO OWN_HI OWN4.
      split; [lia|]. split; [lia|]. split; [exact DFL4|].
      split; [destruct STKROM; lia|]. split; [destruct BUFROM; lia|]. destruct DCTXROM; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cb12_as_c4s : forall (m1 : fmem) A jj, rw_cells usegs m1 A [CB 12 jj] -> exists a b c, rw_cells usegs m1 A [C4 a; C4 b; C4 c].
  Proof using SPV.
    intros m1 A jj WHOLE.
    pose proof (rw_cells_split_CB usegs m1 A [] 12 jj [] [4%nat; 8%nat] WHOLE eq_refl) as AS48.
    pose proof (rw_cells_split_CB usegs m1 A [] 12 jj [] [8%nat; 4%nat] WHOLE eq_refl) as AS84.
    cbn [app mk_CB_cells] in AS48, AS84.
    destruct (proj1 (rw_cells_app usegs m1 A [CB 4 (firstn 4 jj)] [CB 8 (firstn 8 (skipn 4 jj))]) AS48) as [_ UPPER].
    destruct (proj1 (rw_cells_app usegs m1 A [CB 8 (firstn 8 jj)] [CB 4 (firstn 4 (skipn 8 jj))]) AS84) as [LOWER _].
    cbn [cells_size csize Nat.add Z.of_nat] in UPPER.
    destruct (cb8_as_c4s usegs m1 _ _ UPPER) as (w1 & w2 & HI2).
    destruct (cb8_as_c4s usegs m1 _ _ LOWER) as (w0 & wdrop & LO2).
    destruct (proj1 (rw_cells_app usegs m1 A [C4 w0] [C4 wdrop]) LO2) as [FIRST _].
    exists w0, w1, w2.
    apply (proj2 (rw_cells_app usegs m1 A [C4 w0] [C4 w1; C4 w2])).
    split; [exact FIRST|]. exact HI2.
  Qed.

  Lemma src_mid : forall (m1 : fmem) i n, bytes_at usegs m1 SRC (map (Z_to_bv 8) src) -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length src) ->
    let sq := firstn (Z.to_nat n) (skipn (Z.to_nat i) src) in
    bytes_at usegs m1 (SRC + i) (map (Z_to_bv 8) sq) /\ Z.of_nat (length sq) = n /\ Forall (fun c => 0 <= c < 256) sq.
  Proof using SPV FBY.
    intros m1 i n WHOLE ILO NLO FITS sq.
    assert (MAPLEN : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    destruct (bytes_at_mid m1 SRC (map (Z_to_bv 8) src) i n WHOLE ILO NLO ltac:(lia)) as [PIECE PLEN].
    rewrite skipn_map, firstn_map in PIECE, PLEN. rewrite length_map in PLEN.
    split; [exact PIECE|]. split; [exact PLEN|].
    pose proof FBY as ALLB.
    rewrite <- (firstn_skipn (Z.to_nat i) src) in ALLB. apply Forall_app in ALLB as [_ TAILB].
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) src)) in TAILB. apply Forall_app in TAILB as [HEADB _].
    exact HEADB.
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
  Proof using HY SPA.
    intros m1 LITP LITSZ LITB LBE LOC XBUF SRCB BUFS SZR ORD PLACE NOT2.
    pose proof HY as (CTX_LO & CTX_HI & _ & IP_LO & CBS_R & IP_FIT & SRC_LO & SRC_HI & DST_LO & DST_FIT & CAP_LO & BUF_HI
                      & NULL_CAP & NN_BUF & _ & _ & _ & _ & CTX_STK & BUF_STK & SRC_STK & CTX_BUF & SRC_BUF & SRC_CTX).
    pose proof (rdbl_of_bytes_at usegs m1 SRC _ SRCB) as SRCRD. rewrite length_map in SRCRD.
    pose proof (rdbl_of_stk usegs m1 _ _ XBUF) as XRD.
    pose proof (rdbl_of_stk usegs m1 _ _ BUFS) as BRD.
    clear XBUF SRCB BUFS.
    unfold ZSTD_not_in_dst, ZSTD_in_dst, WILDCOPY_OVERLENGTH, off_stack, apart, DCTX_entropy_rep, DCTX_litExtraBuffer.
    destruct PLACE as [(L0 & EBE & [(EP & SMALL) | (INSRC & FITSRC)]) | [(L1 & EBE & EB & DLO & FITD) | (L2 & _)]].
    - subst LOC LBE LITP. clear SRCRD BRD SRC_STK SRC_BUF SRC_CTX BUF_STK NULL_CAP NN_BUF.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ XRD); lia|].
      split; [intros CONTRA; discriminate CONTRA|].
      split; [intros _; destruct CTX_BUF; lia|].
      split; [destruct CTX_STK; lia|]. lia.
    - subst LOC LBE. clear XRD BRD CTX_STK BUF_STK CTX_BUF NULL_CAP NN_BUF.
      split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ SRCRD); lia|].
      split; [intros CONTRA; discriminate CONTRA|].
      split; [intros _; destruct SRC_BUF; lia|].
      split; [destruct SRC_STK; lia|]. destruct SRC_CTX; lia.
    - subst LOC LBE LITB.
      assert (DSTNZ : DST <> 0) by (intros DZ; specialize (NULL_CAP DZ); lia).
      specialize (NN_BUF DSTNZ). clear XRD SRCRD SRC_STK SRC_BUF SRC_CTX NULL_CAP.
      split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ BRD); lia|].
      split; [intros _; lia|].
      split; [intros CONTRA; discriminate CONTRA|].
      split; [destruct BUF_STK; lia|]. destruct CTX_BUF; lia.
    - exfalso. exact (NOT2 L2).
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
  Proof using HY SPA.
    intros m1 LITP LITSZ LITB LBE LOC XBUF SRCB BUFS SZR ORD PLACE.
    pose proof HY as (CTX_LO & CTX_HI & _ & IP_LO & CBS_R & IP_FIT & SRC_LO & SRC_HI & DST_LO & DST_FIT & CAP_LO & BUF_HI
                      & NULL_CAP & NN_BUF & _ & _ & _ & _ & CTX_STK & BUF_STK & SRC_STK & CTX_BUF & SRC_BUF & SRC_CTX).
    pose proof (rdbl_of_bytes_at usegs m1 SRC _ SRCB) as SRCRD. rewrite length_map in SRCRD.
    pose proof (rdbl_of_stk usegs m1 _ _ XBUF) as XRD.
    pose proof (rdbl_of_stk usegs m1 _ _ BUFS) as BRD.
    clear XBUF SRCB BUFS.
    unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, off_stack, apart,
      DCTX_entropy_rep, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz.
    destruct PLACE as [(L0 & EBE & [(EP & SMALL) | (INSRC & FITSRC)]) | [(L1 & EBE & EB & DLO & FITD) | (L2 & BIG & EB & DLO & FITD)]].
    - subst LOC LBE LITP. clear SRCRD BRD SRC_STK SRC_BUF SRC_CTX BUF_STK NULL_CAP NN_BUF.
      split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ XRD); lia|].
      split; [left; split; [reflexivity|]; destruct CTX_BUF; lia|].
      split; [destruct CTX_STK; lia|]. intros _; lia.
    - subst LOC LBE. clear XRD BRD CTX_STK BUF_STK CTX_BUF NULL_CAP NN_BUF.
      split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ SRCRD); lia|].
      split; [left; split; [reflexivity|]; destruct SRC_BUF; lia|].
      split; [destruct SRC_STK; lia|]. intros _; destruct SRC_CTX; lia.
    - subst LOC LBE LITB.
      assert (DSTNZ : DST <> 0) by (intros DZ; specialize (NULL_CAP DZ); lia).
      specialize (NN_BUF DSTNZ). clear XRD SRCRD SRC_STK SRC_BUF SRC_CTX NULL_CAP.
      split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ BRD); lia|].
      split; [right; left; lia|].
      split; [destruct BUF_STK; lia|]. intros _; destruct CTX_BUF; lia.
    - subst LOC LITB.
      assert (DSTNZ : DST <> 0) by (intros DZ; specialize (NULL_CAP DZ); lia).
      specialize (NN_BUF DSTNZ). clear SRCRD SRC_STK SRC_BUF SRC_CTX NULL_CAP CTX_BUF.
      split; [lia|]. split; [lia|].
      split; [apply (rdbl_sub usegs m1 _ _ _ _ BRD); lia|].
      split.
      { right; right. split; [reflexivity|]. split; [lia|]. split; [lia|].
        apply (rdbl_sub usegs m1 _ _ _ _ XRD); lia. }
      split; [destruct BUF_STK; lia|]. intros WRONG; exfalso; exact (WRONG eq_refl).
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
  Proof using HY FBY SPA HSD HSS HSL.
    intros lng pcv m1 mc p0 p1 p2 huv lev fev wsv nbSeq i1 rem1 r2 xra x5 x6 x7 xa0 xa1 xa2 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs8 xs9 x28 x29 x30 x31
           PCV BLK W3MU KEEPH5 HINV NBR I1LO R2R IPI1 FITI1 TABS LITS NZ NBCELL LNGA5.
    pose proof TABS as TABS1.
    pose proof LITS as (LITP & LITSZ & LITB & LBE & LOC & ELP & ELS & ELB & ELBE & ELOC & LSZR & LORD & LPLACE).
    unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_litExtraBuffer, ZSTD_LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in LPLACE.
    assert (LOCR : 0 <= LOC <= 2) by (clear - LPLACE; lia).
    open_dbb BLK. open_dbh HY.
    (* the remaining source bytes handed to the sequence decoder *)
    destruct (src_mid mc (i1 + r2) (rem1 - r2) SRCB ltac:(lia) ltac:(lia) ltac:(lia)) as (SQB & SQLEN & SQOK).
    set (sq := firstn (Z.to_nat (rem1 - r2)) (skipn (Z.to_nat (i1 + r2)) src)) in *.
    replace (SRC + (i1 + r2)) with (SRC + i1 + r2) in SQB by lia.
    pose proof (Forall_all_bytes sq SQOK) as SQALL.
    assert (EA4 : Z_to_bv 64 (rem1 - r2) = Z_to_bv 64 (zlen sq)) by (rewrite SQLEN; reflexivity).
    (* the repeat-offset cells *)
    destruct (stk_open usegs mc (DCTX + 26684) (DCTX + 27324) (DCTX + 26684) 12 EREP ltac:(lia) ltac:(cbn; lia))
      as (jrep & REPCB & REPNIL & REPHI).
    clear REPNIL EREP.
    destruct (cb12_as_c4s mc (DCTX + 26684) jrep REPCB) as (rp0 & rp1 & rp2 & REPC). clear REPCB.
    replace (DCTX + 26684 + Z.of_nat 12) with (DCTX + 26696) in REPHI by (cbn; lia).
    (* the three decoding tables, ready for the decoder when there are sequences *)
    assert (TABR : exists LLT MLT OFT tLL tOF tML,
               p0 = Z_to_bv 64 LLT /\ p1 = Z_to_bv 64 MLT /\ p2 = Z_to_bv 64 OFT /\
               (nbSeq <> 0 -> tab_ready mc K_LL 4104 p0 LLT tLL /\ tab_ready mc K_OF 2056 p2 OFT tOF /\
                              tab_ready mc K_ML 4104 p1 MLT tML)).
    { unfold hidden in TABS. destruct TABS as [(NB0 & _) | (NBNZ & TLL & TOF & TML)].
      - exists (bv_unsigned p0), (bv_unsigned p1), (bv_unsigned p2), LL_defaultDTable, OF_defaultDTable, ML_defaultDTable.
        rewrite !Z_to_bv_lit_self. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        intros NOTZ; exfalso; exact (NOTZ NB0).
      - destruct (NZ NBNZ) as [DSTNZ CAPNZ].
        assert (AWAY : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W3 x).
        { intros x XR. unfold hidden in DSTD, OFFD. cbn [outside]. clear - XR DSTD OFFD LOS.
          repeat split; lia. }
        pose proof (stk_not_ro mc lo (SPV + -96) MI STK ltac:(clear - LOS; lia)) as ROMSTK.
        pose proof (stk_not_ro mc B0 B1 MI BUF ltac:(clear - CAPNZ CAP0 B0D DCB; lia)) as ROMBUF.
        pose proof (stk_not_ro mc (DCTX + 30372) (DCTX + 95940) MI XB ltac:(clear - DCL; lia)) as ROMCTX.
        pose proof (seqhdr_tab_fine m1 mc W3 DCTX K_LL _ _ _ p0 TLL (seq_tbl_at_LLD usegs _ pll_default_at mc MI) W3MU AWAY
                      ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as TLLc.
        pose proof (seqhdr_tab_fine m1 mc W3 DCTX K_OF _ _ _ p2 TOF (seq_tbl_at_OFD usegs _ pof_default_at mc MI) W3MU AWAY
                      ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as TOFc.
        pose proof (seqhdr_tab_fine m1 mc W3 DCTX K_ML _ _ _ p1 TML (seq_tbl_at_MLD usegs _ pml_default_at mc MI) W3MU AWAY
                      ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as TMLc.
        destruct (db_tab_ready mc K_LL _ _ _ p0 4104 TLLc eq_refl
                    ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)
                    ltac:(apply Z.leb_le; reflexivity) ltac:(reflexivity) ltac:(reflexivity) ROMSTK ROMBUF ROMCTX) as (LLT & tLL & RLL).
        destruct (db_tab_ready mc K_OF _ _ _ p2 2056 TOFc eq_refl
                    ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)
                    ltac:(apply Z.leb_le; reflexivity) ltac:(reflexivity) ltac:(reflexivity) ROMSTK ROMBUF ROMCTX) as (OFT & tOF & ROF).
        destruct (db_tab_ready mc K_ML _ _ _ p1 4104 TMLc eq_refl
                    ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)
                    ltac:(apply Z.leb_le; reflexivity) ltac:(reflexivity) ltac:(reflexivity) ROMSTK ROMBUF ROMCTX) as (MLT & tML & RML).
        exists LLT, MLT, OFT, tLL, tOF, tML.
        split; [exact (proj1 RLL)|]. split; [exact (proj1 RML)|]. split; [exact (proj1 ROF)|].
        intros _. exact (conj RLL (conj ROF RML)). }
    destruct TABR as (LLT & MLT & OFT & tLL & tOF & tML & EP0 & EP1 & EP2 & TREADY).
    subst p0 p1 p2.
    (* the decoder's preconditions, in the shape its statement asks for *)
    assert (P_DCTX : seq_dctx mc DCTX LLT MLT OFT huv rp0 rp1 rp2 pde PFX PFX (Z_to_bv 64 0) expd pcs dsz bt stg lev fev wsv)
      by exact (conj PTRS (conj REPC (conj H1 (conj H3 H5)))).
    assert (P_LIT : seq_lit wsv LITP LITSZ LITB LOC) by exact (conj ELP (conj ELS (conj ELB ELOC))).
    assert (P_CTXHI : DCTX + DCTX_SIZEOF < 2 ^ 47) by (unfold DCTX_SIZEOF; lia).
    assert (P_SEQLO : 4096 <= SRC + i1 + r2) by lia.
    assert (P_SEQHI : SRC + i1 + r2 + zlen sq < 2 ^ 47) by lia.
    assert (P_TAB : nbSeq <> 0 -> seq_table_at mc K_LL LLT tLL /\ seq_table_at mc K_OF OFT tOF /\ seq_table_at mc K_ML MLT tML /\
                                 4096 <= LLT < 2 ^ 47 /\ 4096 <= OFT < 2 ^ 47 /\ 4096 <= MLT < 2 ^ 47).
    { intros NBNZ. destruct (TREADY NBNZ) as [(_ & AL & LL0 & LL1 & _) [(_ & AO & OL0 & OL1 & _) (_ & AM & ML0 & ML1 & _)]].
      split; [exact AL|]. split; [exact AO|]. split; [exact AM|]. lia. }
    assert (P_PFX : nbSeq <> 0 -> B0 <= PFX <= DST).
    { intros NBNZ. destruct (NZ NBNZ) as [_ CAPNZ]. unfold hidden in WIN. clear - WIN CAPNZ. lia. }
    assert (P_NULL : DST = 0 -> CAP = 0 /\ nbSeq = 0).
    { intros DZ. split; [exact (DNULL DZ)|]. destruct (Z.eq_dec nbSeq 0) as [NB0|NBNZ]; [exact NB0|].
      destruct (NZ NBNZ) as [DSTNZ _]. contradiction. }
    assert (P_SPV : 0 <= SPV + -96 < 2 ^ 47) by lia.
    assert (P_SPA : (SPV + -96) mod 16 = 0) by (clear - SPA; lia).
    assert (P_CSTK : off_stack lo (SPV + -96) DCTX DCTX_SIZEOF)
      by (unfold off_stack, DCTX_SIZEOF; unfold hidden in OFFD; clear - OFFD; lia).
    assert (P_BSTK : off_stack lo (SPV + -96) B0 (B1 - B0)) by (unfold off_stack; unfold hidden in OFFB; clear - OFFB; lia).
    assert (P_SSTK : off_stack lo (SPV + -96) (SRC + i1 + r2) (zlen sq))
      by (unfold off_stack; unfold hidden in OFFSRC; clear - OFFSRC SQLEN FITI1 IPC IPI1 I1LO R2R; lia).
    assert (P_BCTX : apart B0 (B1 - B0) DCTX DCTX_SIZEOF) by (unfold apart, DCTX_SIZEOF; unfold hidden in BD; clear - BD; lia).
    assert (P_BSEQ : apart B0 (B1 - B0) (SRC + i1 + r2) (zlen sq))
      by (unfold apart; unfold hidden in BSRC; clear - BSRC SQLEN FITI1 IPC IPI1 I1LO R2R IP0; lia).
    assert (P_SEQREP : apart (SRC + i1 + r2) (zlen sq) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep))
      by (unfold apart, DCTX_SIZEOF, DCTX_entropy_rep; unfold hidden in SRCD; clear - SRCD SQLEN FITI1 IPC IPI1 I1LO R2R IP0; lia).
    assert (P_TSTK : nbSeq <> 0 -> off_stack lo (SPV + -96) LLT (8 * (1 + 2 ^ 9)) /\ off_stack lo (SPV + -96) OFT (8 * (1 + 2 ^ 8)) /\
                                  off_stack lo (SPV + -96) MLT (8 * (1 + 2 ^ 9))).
    { intros NBNZ. destruct (TREADY NBNZ) as [(_ & _ & _ & _ & _ & SL & _) [(_ & _ & _ & _ & _ & SO & _) (_ & _ & _ & _ & _ & SM & _)]].
      exact (conj SL (conj SO SM)). }
    assert (P_TBUF : nbSeq <> 0 -> apart B0 (B1 - B0) LLT (8 * (1 + 2 ^ 9)) /\ apart B0 (B1 - B0) OFT (8 * (1 + 2 ^ 8)) /\
                                  apart B0 (B1 - B0) MLT (8 * (1 + 2 ^ 9))).
    { intros NBNZ. destruct (TREADY NBNZ) as [(_ & _ & _ & _ & _ & _ & BL & _) [(_ & _ & _ & _ & _ & _ & BO & _) (_ & _ & _ & _ & _ & _ & BM & _)]].
      exact (conj BL (conj BO BM)). }
    assert (P_TREP : nbSeq <> 0 ->
              apart LLT (8 * (1 + 2 ^ 9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
              apart OFT (8 * (1 + 2 ^ 8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
              apart MLT (8 * (1 + 2 ^ 9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)).
    { intros NBNZ. destruct (TREADY NBNZ) as [(_ & _ & _ & _ & _ & _ & _ & RL) [(_ & _ & _ & _ & _ & _ & _ & RO) (_ & _ & _ & _ & _ & _ & _ & RM)]].
      exact (conj RL (conj RO RM)). }
    assert (P_TAL : nbSeq <> 0 -> LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0).
    { intros NBNZ. destruct (TREADY NBNZ) as [(_ & _ & _ & _ & AL & _) [(_ & _ & _ & _ & AO & _) (_ & _ & _ & _ & AM & _)]].
      exact (conj AL (conj AO AM)). }
    clear TREADY.
    assert (P_LO544 : lo <= SPV + -96 - 544) by lia.
    assert (P_LO592 : lo <= SPV + -96 - 592) by lia.
    assert (P_LO896 : lo <= SPV + -96 - 896) by lia.
    unfold hidden in LPLACE.
    destruct lng; subst pcv.
    - specialize (LNGA5 eq_refl). subst xa5.
      destruct (db_lit_placed mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LORD LPLACE)
        as (Q_LO & Q_HI & Q_RD & Q_PL & Q_STK & Q_REP).
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply HSL.
        all: try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity end).
        all: try (lazymatch goal with |- _ <= DST => exact B0D end).
        all: try (lazymatch goal with |- DST + CAP <= _ => exact DCB end).
        all: try (lazymatch goal with |- stk usegs _ _ (SPV + -96) => exact STK end).
        all: try first [ eassumption | reflexivity
                       | lazymatch goal with |- seq_lit2 _ _ _ _ _ => repeat split; eassumption end
                       | (unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split; clear - LOCR; lia) ].
      }
      intros ms' LPOST. hnf in LPOST. try unfold DCTX_entropy_rep in LPOST. try unfold DCTX_fseEntropy in LPOST.
      try unfold DCTX_litBufferLocation in LPOST.
      clear P_DCTX P_LIT P_CTXHI P_SEQLO P_SEQHI P_TAB P_PFX P_NULL P_SPV P_SPA P_CSTK P_BSTK P_SSTK P_BCTX P_BSEQ P_SEQREP
            P_TSTK P_TBUF P_TREP P_TAL P_LO544 P_LO592 P_LO896 EA4 SQB SQALL SQOK SQLEN Q_LO Q_HI Q_RD Q_PL Q_STK Q_REP.
      hide NZ. hide DNULL. hide DNN.
      revert ms' LPOST. post_call usegs mc.
      unfold hidden in TABS1.
      lazymatch goal with HR : forall i : nat, i <> H5_litBufferLocation -> wnth ?w' i = _ |- _ =>
        assert (KEEP2 : forall i, h5_block_owned i = false -> wnth w' i = wnth ws i)
          by (intros i OWN; rewrite HR by (intros EI; subst i; vm_compute in OWN; discriminate OWN); exact (KEEPH5 i OWN));
        eapply (db_fin m1 _ (Z_to_bv 64 LLT) (Z_to_bv 64 MLT) (Z_to_bv 64 OFT) huv lev fev
                  (if nbSeq =? 0 then fev else Z_to_bv 64 1) w' _ nbSeq) end.
      2: exact KEEP2.
      2: eassumption.
      2: exact HINV.
      2: exact TABS1.
      2: reflexivity.
      2: eassumption.
      2: eassumption.
      lazymatch goal with RC : rw_cells usegs ?mm (DCTX + 26684) [C4 _; C4 _; C4 _] |- _ =>
        pose proof (stk_of_rw_cells usegs mm _ _ RC) as REPLO end.
      replace (DCTX + 26684 + Z.of_nat (cells_size [C4 _; C4 _; C4 _])) with (DCTX + 26696) in REPLO by (cbn; lia).
      unfold DBB.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|].
      split; [eassumption|]. split; [eassumption|].
      split; [eapply stk_merge; [exact REPLO | eassumption | lia]|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|].
      split; [eexists; eassumption|].
      split; [eassumption|]. split; eassumption.
    - pose proof H5 as [H5C H5LEN]. clear H5. h5_open wsv H5LEN.
      rewrite ELOC in *.
      zstep. zstep. zstep. zstep.
      rewrite (sx32w_small nbSeq), (sx32w_small LOC) by lia.
      if_cases BR; zify_cond BR.
      + (* not a split literal buffer: the plain decoder *)
        destruct (db_lit_default mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LORD LPLACE ltac:(lia))
          as (D_LOC & D_SZ & D_LO & D_HI & D_RD & D_IN & D_NOT & D_STK & D_REP).
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply (HSD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      (SPV + -96) lo DCTX DST CAP B0 B1 (SRC + i1 + r2) nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC).
          all: first [eassumption | reflexivity]. }
        intros ms' DPOST. unfold zd_seq_default_post, DCTX_entropy_rep, DCTX_fseEntropy in DPOST.
        clear P_DCTX P_LIT P_CTXHI P_SEQLO P_SEQHI P_TAB P_PFX P_NULL P_SPV P_SPA P_CSTK P_BSTK P_SSTK P_BCTX P_BSEQ P_SEQREP
              P_TSTK P_TBUF P_TREP P_TAL P_LO544 P_LO592 P_LO896 EA4 SQB SQALL SQOK SQLEN
              D_LOC D_SZ D_LO D_HI D_RD D_IN D_NOT D_STK D_REP.
        hide NZ. hide DNULL. hide DNN.
        revert ms' DPOST. post_call usegs mc.
        zstep.
        unfold hidden in TABS1.
        let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
        eapply (db_fin m1 _ (Z_to_bv 64 LLT) (Z_to_bv 64 MLT) (Z_to_bv 64 OFT) huv lev fev
                  (if nbSeq =? 0 then fev else Z_to_bv 64 1) wl _ nbSeq).
        2: intros i OWN; exact (KEEPH5 i OWN).
        2: eassumption.
        2: exact HINV.
        2: exact TABS1.
        2: reflexivity.
        2: eassumption.
        2: eassumption.
        lazymatch goal with RC : rw_cells usegs ?mm (DCTX + 26684) [C4 _; C4 _; C4 _] |- _ =>
          pose proof (stk_of_rw_cells usegs mm _ _ RC) as REPLO end.
        replace (DCTX + 26684 + Z.of_nat (cells_size [C4 _; C4 _; C4 _])) with (DCTX + 26696) in REPLO by (cbn; lia).
        unfold DBB.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [split; [eassumption | reflexivity]|].
        split; [eassumption|]. split; [eassumption|].
        split; [eapply stk_merge; [exact REPLO | eassumption | lia]|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|]. split; [eassumption|].
        split; [eexists; eassumption|].
        split; [eassumption|]. split; eassumption.
      + destruct (db_lit_placed mc LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LORD LPLACE)
          as (Q_LO & Q_HI & Q_RD & Q_PL & Q_STK & Q_REP).
        assert (CAPPOS : 0 < CAP) by (clear - LPLACE BR LSZR LORD; lia).
        assert (B0HI : 4096 <= B0) by (apply DNN; intros DZ; specialize (DNULL DZ); clear - DNULL CAPPOS; lia).
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply HSS.
          all: try (lazymatch goal with |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity end).
          all: try (lazymatch goal with |- _ <= DST => exact B0D end).
          all: try (lazymatch goal with |- DST + CAP <= _ => exact DCB end).
          all: try (lazymatch goal with |- stk usegs _ _ (SPV + -96) => exact STK end).
          all: try first [ eassumption | reflexivity
                         | lazymatch goal with |- seq_lit2 _ _ _ _ _ => repeat split; eassumption end
                         | unfold ZSTD_split; exact BR ].
          }
        intros ms' SPOST. hnf in SPOST. try unfold DCTX_entropy_rep in SPOST. try unfold DCTX_fseEntropy in SPOST.
        try unfold DCTX_litBufferLocation in SPOST.
        clear P_DCTX P_LIT P_CTXHI P_SEQLO P_SEQHI P_TAB P_PFX P_NULL P_SPV P_SPA P_CSTK P_BSTK P_SSTK P_BCTX P_BSEQ P_SEQREP
              P_TSTK P_TBUF P_TREP P_TAL P_LO544 P_LO592 P_LO896 EA4 SQB SQALL SQOK SQLEN Q_LO Q_HI Q_RD Q_PL Q_STK Q_REP
              CAPPOS B0HI.
        hide NZ. hide DNULL. hide DNN.
        revert ms' SPOST. post_call usegs mc.
        zstep.
        unfold hidden in TABS1.
        lazymatch goal with HR : forall i : nat, i <> H5_litBufferLocation -> wnth ?w' i = _ |- _ =>
          assert (KEEP2 : forall i, h5_block_owned i = false -> wnth w' i = wnth ws i)
            by (intros i OWN; rewrite HR by (intros EI; subst i; vm_compute in OWN; discriminate OWN); exact (KEEPH5 i OWN));
          eapply (db_fin m1 _ (Z_to_bv 64 LLT) (Z_to_bv 64 MLT) (Z_to_bv 64 OFT) huv lev fev
                    (if nbSeq =? 0 then fev else Z_to_bv 64 1) w' _ nbSeq) end.
        2: exact KEEP2.
        2: eassumption.
        2: exact HINV.
        2: exact TABS1.
        2: reflexivity.
        2: eassumption.
        2: eassumption.
        lazymatch goal with RC : rw_cells usegs ?mm (DCTX + 26684) [C4 _; C4 _; C4 _] |- _ =>
          pose proof (stk_of_rw_cells usegs mm _ _ RC) as REPLO end.
        replace (DCTX + 26684 + Z.of_nat (cells_size [C4 _; C4 _; C4 _])) with (DCTX + 26696) in REPLO by (cbn; lia).
        unfold DBB.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|].
        split; [eassumption|]. split; [eassumption|].
        split; [eapply stk_merge; [exact REPLO | eassumption | lia]|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|]. split; [eassumption|].
        split; [eexists; eassumption|].
        split; [eassumption|]. split; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma db_frame : forall (m1 : fmem) ja w,
    rw_cells usegs m1 (SPV + -96) [CB 4 ja] -> rw_cells usegs m1 (SPV + -92) [C4 w] ->
    rw_cells usegs m1 (SPV + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    exists jj, rw_cells usegs m1 (SPV + -96) [CB 8 jj; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros m1 ja w PAD NBCELL SAVED.
    set (SAVEDCS := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in *.
    assert (LOW8 : rw_cells usegs m1 (SPV + -96) ([CB 4 ja] ++ [C4 w])).
    { apply (proj2 (rw_cells_app usegs m1 (SPV + -96) [CB 4 ja] [C4 w])). split; [exact PAD|].
      replace (SPV + -96 + Z.of_nat (cells_size [CB 4 ja])) with (SPV + -92) by (cbn; lia). exact NBCELL. }
    assert (ALL : rw_cells usegs m1 (SPV + -96) ([] ++ [CB 4 ja; C4 w] ++ SAVEDCS)).
    { apply (proj2 (rw_cells_app usegs m1 (SPV + -96) [CB 4 ja; C4 w] SAVEDCS)). split; [exact LOW8|].
      replace (SPV + -96 + Z.of_nat (cells_size [CB 4 ja; C4 w])) with (SPV + -88) by (cbn; lia). exact SAVED. }
    exists (cells_bytes [CB 4 ja; C4 w]).
    exact (rw_cells_merge usegs m1 (SPV + -96) [] [CB 4 ja; C4 w] SAVEDCS ALL).
  Qed.

  Notation W4 := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (DCTX + 30204, DCTX + 30208);
                  (SPV - 2048, SPV)].

  (* [comment removed for export] *)
  Lemma db_hdr : forall m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v xra x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs8 xs9 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m1 DCTX huv lev -> ptbl_seq m1 DCTX p0 p1 p2 fev ->
    declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    ip <= i1 -> 0 <= rem1 <= 131072 -> i1 + rem1 <= ip + cbs -> a1v - a0v = rem1 -> 0 <= a0v -> 0 <= a1v < 2^64 ->
    evt usegs POST (ST 0x178a0 m1 xra x5 x6 x7 (Z_to_bv 64 CAP) (Z_to_bv 64 DST) (Z_to_bv 64 a0v) (Z_to_bv 64 a1v) xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 DCTX) (Z_to_bv 64 (SRC + i1)) xs4 (Z_to_bv 64 (DCTX + 29904)) (Z_to_bv 64 1) xs7 xs8 xs9 x28 x29 x30 x31).
  Proof using HY FBY SPA HSD HSS HSL.
    intros m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v xra x5 x6 x7 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs8 xs9 x28 x29 x30 x31
           BLK KEEPH5 HINV PTS LITS IPI1 REMR FIT ADIFF A0LO A1R.
    open_dbb BLK. open_dbh HY.
    pose proof H5 as P_H5. destruct H5 as [H5C H5LEN]. h5_open wsv H5LEN.
    (* split the saved frame so that the nbSeq cell stands on its own *)
    destruct (proj1 (rw_cells_app usegs m1 (SPV + -96) [CB 8 j]
                       [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) FR) as [FRLO FRHI].
    replace (SPV + -96 + Z.of_nat (cells_size [CB 8 j])) with (SPV + -88) in FRHI by (cbn; lia).
    destruct (cb8_as_c4s usegs m1 _ _ FRLO) as (wpad & wnb & FR2). clear FRLO FR.
    destruct (proj1 (rw_cells_app usegs m1 (SPV + -96) [C4 wpad] [C4 wnb]) FR2) as [PADC NBC]. clear FR2.
    replace (SPV + -96 + Z.of_nat (cells_size [C4 wpad])) with (SPV + -92) in NBC by (cbn; lia).
    (* the source bytes left after the literals section *)
    destruct (src_mid m1 i1 rem1 SRCB ltac:(lia) ltac:(lia) ltac:(lia)) as (HB & HLEN & HOK).
    set (hs := firstn (Z.to_nat rem1) (skipn (Z.to_nat i1) src)) in *.
    assert (S_NBLO : 4096 <= SPV + -92) by lia.
    assert (S_NBHI : SPV + -92 + 4 < 2 ^ 47) by lia.
    assert (S_LEN : Z.of_nat (length hs) <= 1048576) by lia.
    assert (S_SRCLO : 4096 <= SRC + i1) by lia.
    assert (S_SRCHI : SRC + i1 + Z.of_nat (length hs) < 2 ^ 47) by lia.
    assert (S_LO544 : lo <= SPV + -96 - 544) by lia.
    assert (S_SPHI : SPV + -96 < 2 ^ 47) by lia.
    assert (S_OSD : RZ_blk_iface.off_stack lo (SPV + -96) DCTX 95992)
      by (unfold RZ_blk_iface.off_stack; unfold hidden in OFFD; clear - OFFD; lia).
    assert (S_OSN : RZ_blk_iface.off_stack lo (SPV + -96) (SPV + -92) 4) by (unfold RZ_blk_iface.off_stack; lia).
    assert (S_OSS : RZ_blk_iface.off_stack lo (SPV + -96) (SRC + i1) (Z.of_nat (length hs)))
      by (unfold RZ_blk_iface.off_stack; unfold hidden in OFFSRC; clear - OFFSRC HLEN FIT IPC IPI1 IP0; lia).
    assert (S_ADN : RZ_blk_iface.apart DCTX 95992 (SPV + -92) 4)
      by (unfold RZ_blk_iface.apart; unfold hidden in OFFD; clear - OFFD LOS; lia).
    assert (S_ADS : RZ_blk_iface.apart DCTX 95992 (SRC + i1) (Z.of_nat (length hs)))
      by (unfold RZ_blk_iface.apart; unfold hidden in SRCD; clear - SRCD HLEN FIT IPC IPI1 IP0; lia).
    assert (S_ANS : RZ_blk_iface.apart (SPV + -92) 4 (SRC + i1) (Z.of_nat (length hs)))
      by (unfold RZ_blk_iface.apart; unfold hidden in OFFSRC; clear - OFFSRC HLEN FIT IPC IPI1 IP0 LOS; lia).
    assert (S_NBAL : (SPV + -92) mod 4 = 0) by (clear - SPA; lia).
    assert (S_SPA : (SPV + -96) mod 16 = 0) by (clear - SPA; lia).
    assert (S_A3 : Z_to_bv 64 rem1 = Z_to_bv 64 (Z.of_nat (length hs))) by (rewrite HLEN; reflexivity).
    pose proof (munch_refl W4 m1) as MTRK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    try rewrite ADIFF.
    eapply evt_cut.
    { eapply (zd_seqhdr_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
                (SPV + -96) lo DCTX (SPV + -92) (SRC + i1) hs p0 p1 p2 huv pcs dsz bt stg lev fev wnb).
      all: first [ eassumption | reflexivity | (f_equal; lia) ]. }
    intros ms' HPOST. unfold zd_seqhdr_post in HPOST.
    destruct HPOST as (t0h & t1h & t2h & a1h & a2h & a3h & a4h & a5h & a6h & a7h & t3h & t4h & t5h & t6h & m2 & r & llt2 & mlt2 & oft2 & nbw
                       & EMS & MUH & WMH & MI2 & STK2 & PTRS2 & ESEQ2 & EWK2 & NBC2 & RR & RES).
    subst ms'.
    clear S_NBLO S_NBHI S_LEN S_SRCLO S_SRCHI S_LO544 S_SPHI S_OSD S_OSN S_OSS S_ADN S_ADS S_ANS S_NBAL S_SPA S_A3 P_H5 HB HOK.
    hide DNULL. hide DNN.
    transport_after_call usegs m1 m2 MUH WMH.
    clear MUH WMH MI.
    unfold dctx_ptrs in PTRS2.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    assert (HINV2 : HUFINVw m2 DCTX huv lev).
    { eapply hufinv_fine; [exact HINV | exact MTRK |].
      intros x XR. cbn [outside]. unfold hidden in OFFD. clear - XR OFFD LOS. repeat split; lia. }
    clear MTRK.
    destruct (rw_cells_forget usegs _ _ _ PADC) as (jpad & PADB). cbn [cells_size csize Nat.add] in PADB. clear PADC.
    zstep. zstep.
    if_cases SERR; zify_cond SERR.
    - (* the header decoder reported an error: hand it back *)
      destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
      let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
      eapply (db_ret m2 llt2 mlt2 oft2 huv lev fev wl r).
      2: exact RR.
      2: reflexivity.
      2: intros i OWN; exact (KEEPH5 i OWN).
      2: intros NE; exfalso; apply zd_is_error_false_iff in NE; clear - NE SERR RR; lia.
      2: left; apply zd_is_error_true_iff; clear - SERR RR; lia.
      unfold DBB.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [split; [eassumption | reflexivity]|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [exists jfr; exact FRN|].
      split; [eassumption|]. split; eassumption.
    - assert (RNE : zd_is_error r = false) by (apply zd_is_error_false_iff; clear - SERR RR; lia).
      unfold hidden in RES.
      destruct RES as [ISERR | (RLE & nbSeq & ENB & NBR & TABS2)]; [rewrite RNE in ISERR; discriminate ISERR|].
      subst nbw. rewrite HLEN in RLE.
      assert (TABS3 : (nbSeq = 0 /\ ptbl_seq m2 DCTX llt2 mlt2 oft2 fev) \/
                      (nbSeq <> 0 /\ seqhdr_tab m2 DCTX K_LL DCTX_entropy_LLTable PZD_LL_DEFAULT LL_defaultDTable llt2 /\
                                     seqhdr_tab m2 DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable oft2 /\
                                     seqhdr_tab m2 DCTX K_ML DCTX_entropy_MLTable PZD_ML_DEFAULT ML_defaultDTable mlt2)).
      { destruct TABS2 as [(NB0 & EL & EM & EO & KEPT) | NEWT]; [left | right; exact NEWT].
        subst llt2 mlt2 oft2. split; [exact NB0|].
        eapply ptbl_seq_fine; [exact PTS | exact KEPT | exact MI2 |].
        intros x XR. cbn [outside]. unfold hidden in OFFD. clear - XR OFFD LOS. repeat split; lia. }
      clear TABS2.
      zstep. zstep. zstep.
      if_cases WRAP; zify_cond WRAP; [exfalso; clear - WRAP RR RLE SRCL SRCH FIT IPC IPI1 IP0 REMR; lia|].
      zstep. zstep. zstep.
      if_cases ZNUL.
      1: exfalso; replace (SRC + i1 + r <? 1) with false in ZNUL
           by (symmetry; apply Z.ltb_ge; clear - SRCL WRAP IPI1 IP0 RR; lia);
         vm_compute in ZNUL; discriminate ZNUL.
      assert (DSTR : 0 <= DST < 2 ^ 47) by (unfold hidden in DNULL, DNN; clear - DNULL DNN B0D DCB B1H CAP0; lia).
      assert (CAPR : 0 <= CAP < 2 ^ 47) by (clear - DSTR DCB B1H CAP0; lia).
      zstep. zstep. zstep. zstep.
      if_cases DBIG.
      1: exfalso; zify_cond DBIG; clear - DBIG DSTR; lia.
      zstep.
      rewrite (sx32w_small nbSeq) by (clear - NBR; lia).
      zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases DZERR.
      + (* sequences but no room to write them *)
        destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
        let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
        eapply (db_ret m2 llt2 mlt2 oft2 huv lev fev wl (2 ^ 64 - 70)).
        2: clear - RR; lia.
        2: apply bv_eq; vm_compute; reflexivity.
        2: intros i OWN; exact (KEEPH5 i OWN).
        2: intros NE; exfalso; apply zd_is_error_false_iff in NE; clear - NE; lia.
        2: left; apply zd_is_error_true_iff; clear - RR; lia.
        unfold DBB.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [split; [eassumption | reflexivity]|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [exists jfr; exact FRN|].
        split; [eassumption|]. split; eassumption.
      + assert (NZ2 : nbSeq <> 0 -> DST <> 0 /\ CAP <> 0).
        { intros NBNZ.
          assert (LD : Z.land DST 18446744073709551615 = DST).
          { change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear - DSTR; lia). apply Z.mod_small. clear - DSTR; lia. }
          assert (LC : Z.land CAP 18446744073709551615 = CAP).
          { change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear - CAPR; lia). apply Z.mod_small. clear - CAPR; lia. }
          assert (LN : Z.lxor nbSeq 9223372036854775808 = nbSeq + 9223372036854775808).
          { change 9223372036854775808 with (2 ^ 63). apply zb_lxor_pow2_small; clear - NBR; lia. }
          rewrite ?LD, ?LC, ?LN in DZERR.
          clear LD LC LN.
          split; intros ZERO; rewrite ZERO in DZERR;
            repeat match type of DZERR with
                   | context [?x <? ?y] =>
                       first [ replace (x <? y) with true in DZERR by (symmetry; apply Z.ltb_lt; clear - NBNZ NBR; lia)
                             | replace (x <? y) with false in DZERR by (symmetry; apply Z.ltb_ge; clear - NBNZ NBR; lia)
                             | destruct (x <? y) ]
                   end;
            vm_compute in DZERR; discriminate DZERR. }
        clear DZERR.
        pose proof (munch_refl W3 m2) as MW3.
        zstep. zstep.
        if_cases COLD.
        * (* ddictIsCold is zero: three tests, and the long decoder is taken only if all pass: dst + min(capacity, block size max) lies more than 16 MiB past the virtual start, there are at least 9 sequences, and the long-offset share (low 32 bits of the offset-info result, after sext.w) is at least 7; if any fails, the short path at 0x179ac *)
          zstep. zstep. zstep. zstep.
          if_cases HIST.
          -- zstep.
             destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
             let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
             eapply (db_seq false 0x179ac m2 _ llt2 mlt2 oft2 huv lev fev wl nbSeq i1 rem1 r).
             1: reflexivity.
             2: eassumption.
             2: { intros i OWN.
                  do 17 (destruct i as [|i]; [exact (KEEPH5 _ OWN)|]).
                  destruct i as [|i]; [vm_compute in OWN; discriminate OWN|].
                  exact (KEEPH5 _ OWN). }
             2: exact HINV2.
             2: exact NBR.
             2: clear - IPI1 IP0; lia.
             2: clear - RR RLE; lia.
             2: exact IPI1.
             2: exact FIT.
             2: exact TABS3.
             2: exact LITS.
             2: exact NZ2.
             2: eassumption.
             2: intros NOTL; discriminate NOTL.
             unfold DBB.
             split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
             split; [split; [eassumption | reflexivity]|].
             split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
             split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
             split; [exists jfr; exact FRN|].
             split; [eassumption|]. split; eassumption.
          -- zstep. zstep.
             if_cases FEW.
             ++ zstep.
                destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
                let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
                eapply (db_seq false 0x179ac m2 _ llt2 mlt2 oft2 huv lev fev wl nbSeq i1 rem1 r).
                1: reflexivity.
                2: eassumption.
                2: { intros i OWN.
                     do 17 (destruct i as [|i]; [exact (KEEPH5 _ OWN)|]).
                     destruct i as [|i]; [vm_compute in OWN; discriminate OWN|].
                     exact (KEEPH5 _ OWN). }
                2: exact HINV2.
                2: exact NBR.
                2: clear - IPI1 IP0; lia.
                2: clear - RR RLE; lia.
                2: exact IPI1.
                2: exact FIT.
                2: exact TABS3.
                2: exact LITS.
                2: exact NZ2.
                2: eassumption.
                2: intros NOTL; discriminate NOTL.
                unfold DBB.
                split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                split; [split; [eassumption | reflexivity]|].
                split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                split; [exists jfr; exact FRN|].
                split; [eassumption|]. split; eassumption.
             ++ assert (NNZ : nbSeq <> 0) by (intros N0; rewrite N0 in FEW; vm_compute in FEW; discriminate FEW).
                destruct (NZ2 NNZ) as [DSTNZ CAPNZ].
                zstep. zstep. zstep. zstep. zstep.
                assert (TOF2 : seqhdr_tab m2 DCTX K_OF DCTX_entropy_OFTable PZD_OF_DEFAULT OF_defaultDTable oft2).
                { destruct TABS3 as [(NB0 & _) | (_ & _ & TO & _)]; [contradiction | exact TO]. }
                pose proof (stk_not_ro m2 lo (SPV + -96) MI2 STK2 ltac:(clear - LOS; lia)) as ROMSTK.
                pose proof (stk_not_ro m2 B0 B1 MI2 BUF ltac:(clear - CAPNZ CAP0 B0D DCB; lia)) as ROMBUF.
                pose proof (stk_not_ro m2 (DCTX + 30372) (DCTX + 95940) MI2 XB ltac:(clear - DCL; lia)) as ROMCTX.
                destruct (db_tab_ready m2 K_OF _ _ _ oft2 2056 TOF2 eq_refl
                            ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)
                            ltac:(apply Z.leb_le; reflexivity) ltac:(reflexivity) ltac:(reflexivity) ROMSTK ROMBUF ROMCTX)
                  as (TOF & tOF & EOF & ATOF & TOFLO & TOFHI & TOFAL & _).
                clear ROMSTK ROMBUF ROMCTX.
                eapply evt_cut.
                { eapply (zd_offinfo_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (SPV + -96) TOF tOF).
                  all: first [ eassumption | (clear - LO0 LOS SPH; lia) ]. }
                post_call usegs m2.
                zstep. zstep. zstep. zstep. zstep. zstep.
                if_cases SHARE.
                ** destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
                   let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
                   eapply (db_seq false 0x179ac m2 _ llt2 mlt2 oft2 huv lev fev wl nbSeq i1 rem1 r).
                   1: reflexivity.
                   2: eassumption.
                   2: { intros i OWN.
                        do 17 (destruct i as [|i]; [exact (KEEPH5 _ OWN)|]).
                        destruct i as [|i]; [vm_compute in OWN; discriminate OWN|].
                        exact (KEEPH5 _ OWN). }
                   2: exact HINV2.
                   2: exact NBR.
                   2: clear - IPI1 IP0; lia.
                   2: clear - RR RLE; lia.
                   2: exact IPI1.
                   2: exact FIT.
                   2: exact TABS3.
                   2: exact LITS.
                   2: exact NZ2.
                   2: eassumption.
                   2: intros NOTL; discriminate NOTL.
                   unfold DBB.
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [split; [eassumption | reflexivity]|].
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [exists jfr; exact FRN|].
                   split; [eassumption|]. split; eassumption.
                ** zstep.
                   rewrite (sx32w_small nbSeq) by lia.
                   zstep.
                   destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
                   let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
                   eapply (db_seq true 0x17918 m2 _ llt2 mlt2 oft2 huv lev fev wl nbSeq i1 rem1 r).
                   1: reflexivity.
                   2: eassumption.
                   2: { intros i OWN.
                        do 17 (destruct i as [|i]; [exact (KEEPH5 _ OWN)|]).
                        destruct i as [|i]; [vm_compute in OWN; discriminate OWN|].
                        exact (KEEPH5 _ OWN). }
                   2: exact HINV2.
                   2: exact NBR.
                   2: clear - IPI1 IP0; lia.
                   2: clear - RR RLE; lia.
                   2: exact IPI1.
                   2: exact FIT.
                   2: exact TABS3.
                   2: exact LITS.
                   2: exact NZ2.
                   2: eassumption.
                   2: intros _; reflexivity.
                   unfold DBB.
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [split; [eassumption | reflexivity]|].
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
                   split; [exists jfr; exact FRN|].
                   split; [eassumption|]. split; eassumption.
        * (* cold dictionary: always the prefetching decoder *)
          zstep.
          destruct (db_frame _ jpad _ PADB NBC2 FRHI) as (jfr & FRN).
          let wl := lazymatch type of H5C with rw_cells _ _ _ ?cs => cells_words cs end in
          eapply (db_seq true 0x17918 m2 _ llt2 mlt2 oft2 huv lev fev wl nbSeq i1 rem1 r).
          1: reflexivity.
          2: eassumption.
          2: { intros i OWN.
               do 17 (destruct i as [|i]; [exact (KEEPH5 _ OWN)|]).
               destruct i as [|i]; [vm_compute in OWN; discriminate OWN|].
               exact (KEEPH5 _ OWN). }
          2: exact HINV2.
          2: exact NBR.
          2: clear - IPI1 IP0; lia.
          2: clear - RR RLE; lia.
          2: exact IPI1.
          2: exact FIT.
          2: exact TABS3.
          2: exact LITS.
          2: exact NZ2.
          2: eassumption.
          2: intros _; reflexivity.
          unfold DBB.
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [split; [eassumption | reflexivity]|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [exists jfr; exact FRN|].
          split; [eassumption|]. split; eassumption.
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
  Proof using HY FBY SPA HSD HSS HSL.
    intros m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v bsm xra x5 x6 x7 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xs8 xs9 x28 x29 x30 x31
           BLK KEEPH5 HINV PTS LITS IPI1 REMR FIT ADIFF A0LO A1R BSMCAP BSMHI.
    pose proof HY as (_ & _ & _ & _ & _ & _ & _ & _ & DSTLO & DSTFIT & _ & BUFHI & NULLCAP & NNBUF & _).
    zstep. zstep. zstep.
    if_cases BZERO; zify_cond BZERO.
    - eapply (db_hdr m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v); eassumption.
    - assert (DSTNZ : DST <> 0) by (intros DZ; specialize (NULLCAP DZ); clear - NULLCAP BZERO BSMCAP; lia).
      specialize (NNBUF DSTNZ).
      zstep. zstep.
      if_cases WRAP; zify_cond WRAP; [exfalso; clear - WRAP BSMCAP DSTFIT BUFHI DSTLO NNBUF; lia|].
      zstep.
      if_cases DNUL; zify_cond DNUL; [exfalso; clear - DNUL DSTNZ DSTLO BUFHI DSTFIT NNBUF; lia|].
      zstep.
      if_cases ENUL; zify_cond ENUL; [exfalso; clear - ENUL DSTNZ DSTLO BUFHI DSTFIT BSMCAP NNBUF; lia|].
      eapply (db_hdr m1 p0 p1 p2 huv lev fev wsv i1 rem1 a0v a1v); eassumption.
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
  Proof using HY FBY BSM SPA HSD HSS HSL H1X H4X H1W H4W.
    intros t0 t1 t2 a6 a7 t3 t4 t5 t6 llt mlt oft huf le fe PTRS0 HD1 FP0 HD3 HD5 ISF OWN TB SRCB0 BUF0 STK0 MI0.
    open_dbh HY.
    hide DNULL. hide DNN.
    pose proof (munch_refl FOOT m) as MUF.
    pose proof (wmono_refl usegs m) as WMF.
    pose proof (munch_refl [(SPV - 2048, SPV)] m) as MSTK.
    unfold ptbl, zd_tbl in TB. destruct TB as [TBS TBH].
    change (ptbl_seq m DCTX llt mlt oft fe) in TBS.
    destruct OWN as [OWNA XB0].
    destruct (stk_split usegs m _ (DCTX + 10296) _ OWNA ltac:(lia)) as [ESEQ0 REST1].
    destruct (stk_split usegs m _ (DCTX + 26684) _ REST1 ltac:(lia)) as [EHUF0 REST2].
    destruct (stk_split usegs m _ (DCTX + 27324) _ REST2 ltac:(lia)) as [EREP0 REST3].
    destruct (stk_split usegs m _ (DCTX + 29884) _ REST3 ltac:(lia)) as [EWK0 EPAD0].
    clear OWNA REST1 REST2 REST3.
    pose proof (h5_isf_cell m DCTX ws HD5) as ISFC. rewrite ISF in ISFC.
    unfold dctx_ptrs in PTRS0. unfold dctx_h1 in HD1. unfold dctx_h3 in HD3. unfold zfh_cells in FP0.
    carve_frame 96%nat STK0.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mp := mm) in *; clearbody mp end.
    (* what the prologue left untouched *)
    assert (OUTSTK : forall x, DCTX + 32 <= x < DCTX + 29888 -> outside [(SPV - 2048, SPV)] x).
    { intros x XR. cbn [outside]. unfold hidden in OFFD. clear - XR OFFD LOS. repeat split; lia. }
    destruct HD5 as [H5C H5L].
    assert (H5P : rw_cells usegs mp (DCTX + 30096) (h5_cells ws)).
    { eapply rw_cells_transport; [exact H5C | exact MSTK | exact WMF |].
      rewrite (h5_cells_size ws H5L). cbn [disjoint_from]. unfold hidden in OFFD.
      clear - OFFD LOS. split; [lia | exact I]. }
    clear H5C.
    assert (TBSP : ptbl_seq mp DCTX llt mlt oft fe)
      by (eapply ptbl_seq_fine; [exact TBS | exact MSTK | exact MI0 | intros x XR; apply OUTSTK; lia]).
    assert (TBHP : HUFINVw mp DCTX huf le)
      by (eapply hufinv_fine; [exact TBH | exact MSTK | intros x XR; apply OUTSTK; lia]).
    clear TBS TBH OUTSTK MSTK.
    zstep.
    if_cases CTX0.
    1: exfalso; zify_cond CTX0; clear - CTX0 DCL DCH; lia.
    zstep. zstep. zstep.
    if_cases MISAL.
    1: exfalso; zify_cond MISAL; uck_norm MISAL; clear - MISAL DCA DCL DCH; lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (sx32w_small 1) by lia.
    zstep.
    if_cases NOTF.
    1: exfalso; vm_compute in NOTF; discriminate NOTF.
    zstep. rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia). zstep.
    if_cases BSZ; zify_cond BSZ.
    2: { (* the block is larger than the frame allows *)
         zstep. zstep.
         eapply (db_ret mp llt mlt oft huf le fe ws (2 ^ 64 - 72)).
         2: clear - SPA; lia.
         2: apply bv_eq; vm_compute; reflexivity.
         2: intros i OWN; reflexivity.
         2: intros NE; exfalso; apply zd_is_error_false_iff in NE; clear - NE; lia.
         2: left; apply zd_is_error_true_iff; clear - SPA; lia.
         unfold DBB.
         split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
         split; [split; eassumption|].
         split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
         split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
         split; [eexists; eassumption|].
         split; [eassumption|]. split; eassumption. }
    (* decode the literals section *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    destruct (src_mid mp ip cbs SRCB0 ltac:(lia) ltac:(lia) ltac:(lia)) as (DSB & DSLEN & DSOK).
    set (ds := firstn (Z.to_nat cbs) (skipn (Z.to_nat ip) src)) in *.
    unfold hidden in DNULL, DNN.
    assert (CAPR : 0 <= CAP < 2 ^ 47) by (clear - DNULL DNN B0D DCB B1H CAP0; lia).
    assert (D_LEN : Z.of_nat (length ds) <= 131072) by (clear - DSLEN BSZ BSM; lia).
    assert (D_SRCLO : 4096 <= SRC + ip) by (clear - SRCL IP0; lia).
    assert (D_SRCHI : SRC + ip + Z.of_nat (length ds) < 2 ^ 47) by (clear - DSLEN SRCH IPC; lia).
    assert (D_LO : lo <= SPV + -96 - 1184) by (clear - LOS; lia).
    assert (D_SPHI : SPV + -96 < 2 ^ 47) by (clear - SPH; lia).
    assert (D_OD : DCTX + 95992 <= lo \/ SPV + -96 <= DCTX) by (unfold hidden in OFFD; clear - OFFD; lia).
    assert (D_OB : B1 <= lo \/ SPV + -96 <= B0) by (unfold hidden in OFFB; clear - OFFB; lia).
    assert (D_OS : SRC + ip + Z.of_nat (length ds) <= lo \/ SPV + -96 <= SRC + ip)
      by (unfold hidden in OFFSRC; clear - OFFSRC DSLEN IPC IP0; lia).
    assert (D_BD : B1 <= DCTX \/ DCTX + 95992 <= B0) by (unfold hidden in BD; exact BD).
    assert (D_BS : B1 <= SRC + ip \/ SRC + ip + Z.of_nat (length ds) <= B0)
      by (unfold hidden in BSRC; clear - BSRC DSLEN IPC IP0; lia).
    assert (D_SD : SRC + ip + Z.of_nat (length ds) <= DCTX \/ DCTX + 95992 <= SRC + ip)
      by (unfold hidden in SRCD; clear - SRCD DSLEN IPC IP0; lia).
    assert (D_SPA : (SPV + -96) mod 16 = 0) by (clear - SPA; lia).
    assert (D_A2 : Z_to_bv 64 cbs = Z_to_bv 64 (Z.of_nat (length ds))) by (rewrite DSLEN; reflexivity).
    assert (D_H5 : dctx_h5 usegs mp DCTX ws) by (split; assumption).
    pose proof (munch_refl W6 mp) as MW6.
    eapply evt_cut.
    { eapply (zd_declit_proof H1X H4X H1W H4W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mp
                (SPV + -96) lo DCTX DST CAP B0 B1 (SRC + ip) ds h llt mlt oft huf pcs dsz bt stg le fe ws).
      all: first [ eassumption | reflexivity ]. }
    intros ms' DLPOST. unfold zd_declit_post in DLPOST.
    destruct DLPOST as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & md & r & hufd & led & wsd
                        & EMS & MUD & WMD & MID & STKD & BUFD & PTRSD & EHUFD & EWKD & H3D & H5D & KEEPD & XBD & RR & RES).
    subst ms'.
    clear D_LEN D_SRCLO D_SRCHI D_LO D_SPHI D_OD D_OB D_OS D_BD D_BS D_SD D_SPA D_A2 D_H5 DSB DSOK H5P.
    hide DNULL. hide DNN.
    transport_after_call usegs mp md MUD WMD.
    clear MUD WMD MI0.
    unfold dctx_ptrs in PTRSD.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    assert (TBSD : ptbl_seq md DCTX llt mlt oft fe).
    { eapply ptbl_seq_fine; [exact TBSP | exact MW6 | exact MID |].
      intros x XR. cbn [outside]. unfold hidden in DSTD, OFFD. clear - XR DSTD OFFD LOS. repeat split; lia. }
    clear TBSP MW6 TBHP.
    zstep. zstep.
    if_cases DERR; zify_cond DERR.
    - (* the literals decoder reported an error *)
      eapply (db_ret md llt mlt oft hufd led fe wsd r).
      2: exact RR.
      2: reflexivity.
      2: exact KEEPD.
      2: intros NE; exfalso; apply zd_is_error_false_iff in NE; clear - NE DERR RR; lia.
      2: left; apply zd_is_error_true_iff; clear - DERR RR; lia.
      unfold DBB.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eexists; eassumption|].
      split; [eassumption|]. split; eassumption.
    - assert (RNE : zd_is_error r = false) by (apply zd_is_error_false_iff; clear - DERR RR; lia).
      destruct RES as [ISERR | (RLO & HINVD & LITD)]; [rewrite RNE in ISERR; discriminate ISERR|].
      rewrite DSLEN in RLO, LITD.
      pose proof (h5_isf_cell md DCTX wsd H5D) as ISFD.
      rewrite (KEEPD H5_isFrameDecompression eq_refl), ISF in ISFD.
      zstep. zstep. zstep.
      if_cases SWRAP; zify_cond SWRAP.
      1: exfalso; clear - SWRAP RR RLO IPC SRCH IP0 SRCL; lia.
      zstep. zstep. zstep. zstep.
      repeat match goal with
             | |- context [?x <? ?y] =>
                 first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; clear - SRCL IP0 RR RLO; lia)
                       | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; clear - SRCL IP0 RR RLO; lia) ]
             end.
      cbn [Z.b2z].
      if_cases ANUL.
      1: exfalso; vm_compute in ANUL; discriminate ANUL.
      zstep. rewrite (sx32w_small 1) by lia. zstep. zstep.
      if_cases NOTF2.
      1: exfalso; vm_compute in NOTF2; discriminate NOTF2.
      zstep. rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia). zstep. zstep.
      replace (r + (SRC + ip)) with (SRC + (ip + r)) by lia.
      if_cases CAPLT; zify_cond CAPLT.
      + (* the output capacity is the tighter bound *)
        eapply (db_bsm md llt mlt oft hufd led fe wsd (ip + r) (cbs - r) r cbs CAP).
        2: exact KEEPD.
        2: exact HINVD.
        2: exact TBSD.
        2: exact LITD.
        2: clear - RLO; lia.
        2: clear - RLO BSZ BSM; lia.
        2: clear - RLO; lia.
        2: reflexivity.
        2: clear - RLO; lia.
        2: clear - CBSR; lia.
        2: clear - CAP0; lia.
        2: clear - CAPLT BSM CAPR; lia.
        unfold DBB.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eexists; eassumption|].
        split; [eassumption|]. split; eassumption.
      + zstep. zstep.
        eapply (db_bsm md llt mlt oft hufd led fe wsd (ip + r) (cbs - r) r cbs (fh_bsmax h)).
        2: exact KEEPD.
        2: exact HINVD.
        2: exact TBSD.
        2: exact LITD.
        2: clear - RLO; lia.
        2: clear - RLO BSZ BSM; lia.
        2: clear - RLO; lia.
        2: reflexivity.
        2: clear - RLO; lia.
        2: clear - CBSR; lia.
        2: clear - CAPLT BSM CAPR; lia.
        2: clear - BSM; lia.
        unfold DBB.
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
        split; [eexists; eassumption|].
        split; [eassumption|]. split; eassumption.
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
