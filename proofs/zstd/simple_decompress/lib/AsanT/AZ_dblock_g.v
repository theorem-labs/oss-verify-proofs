(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep ZdTbl MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface3 AZ_blk_iface5 AZ_blk_iface6 AZ_seq_iface AZ_libc_iface
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a AZ_dblock_b AZ_dblock_c AZ_dblock_d AZ_dblock_e AZ_dblock_f.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF5 := (Z_to_bv 8 18446744073709551605).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B04 := (Z_to_bv 8 4).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.

Section DB.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
            (SPV SPA lo DCTX DST CAP B0 B1 PFX SRC : Z) (src : list Z) (ip cbs : Z) (h : frame_header)
            (pde expd pcs dsz bt stg : word) (ws : list word) (FF SHF FLG : Z).

  Hypothesis CTX : AZ_dblock_a.DBCTX fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FRL : fake_release_law AI fflag.

  Ltac db_open C :=
    pose proof C as ((DCL & DCH & DCA & IP0 & CBSR & IPC & SRCL & SRCH & B0D & DCB & CAP0 & B1H & DNULL & DNN & LO0 & LOS & SPH)
                     & (WIN & OFFD & OFFB & OFFSRC & BD & BSRC & SRCD)
                     & (FBY & BSM & WND & ISF & WL44)
                     & (G1 & G2 & G3 & G4 & G5 & G6 & KLO)
                     & (D1 & D4 & D5)
                     & (S1 & S4 & S5)
                     & OUTB
                     & (F1 & F2 & F3 & F4 & F5 & F6)
                     & (L0 & L1 & L2 & L3 & L4)
                     & (RSTK & RI & R_src & RD1 & RD2 & R_out & RF1 & RF2 & RF3)
                     & (LBH & ASH & RFS & SPT & RSTKT & TP) & DNB);
    pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR;
    pose proof (fk_ablk_lits _ _ F1) as FL; pose proof (fk_ablk_lits _ _ L1) as LL; pose proof (fk_ablk_lits _ _ D1) as DL;
    assert (ESHF : SHF = SHB + FF / 8) by (rewrite F4, shad_div; reflexivity);
    assert (GS : SHB + 805376 <= SHF /\ SHF + 8 <= 17594333495296) by (rewrite ESHF; clear - FL ATR; Z.div_mod_to_equations; lia);
    assert (FFSH : FF + 64 <= SHF \/ SHF + 8 <= FF) by (clear - FL GS ATR; lia);
    assert (FLSH : FLG + 1 <= SHF \/ SHF + 8 <= FLG) by (clear - LL GS ATR; lia);
    assert (DCSH : DCTX + 95992 <= SHF \/ SHF + 8 <= DCTX) by (clear - DL GS ATR; lia).

  Notation WR := [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940)].
  Notation FOOT := [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940); (SPV - 6384, SPV)].
  Notation TBLA := (atbl HUFINVw).
  Notation POST := (zd_dblock_postA AI TBLA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DCTX DST CAP B0 B1 pcs dsz bt stg ws lo m0).
  Notation SAVED := (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 FF) xs3 (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 (DCTX + 29904)) xs7 xs8 xs9 xs10 (Z_to_bv 64 FF) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation DBB := (AZ_dblock_a.DBB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src h pde expd pcs dsz bt stg FF).
  Ltac open_dbb I :=
    unfold AZ_dblock_a.DBB in I;
    destruct I as (PTRS & H1 & FP & H3 & H5 & ESEQ & EHUF & EREP & EWK & EPAD & XB & SRCB & BUF & STL & SAV & STG & MI & AH & FFR & MU & WM
                   & UD & US & UB & ARO & AZS & AHD & AHS & AHB);
    unfold dctx_ptrs in PTRS; unfold dctx_h1 in H1; unfold dctx_h3 in H3; unfold zfh_cells in FP.
  Notation dbb_keep := (AZ_dblock_a.dbb_keep AI fflag rng_fs L RNG st LB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws FF SHF FLG CTX FHL).
  Notation p_ret := (AZ_dblock_a.p_ret AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws FF SHF FLG CTX FFLAG FRL).
  Notation p_exit1 := (AZ_dblock_a.p_exit1 AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws FF SHF FLG CTX FHL FFLAG FRL).
  Ltac hlia := unfold fk_held in *; lia.
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Ltac cells_words cs := lazymatch cs with nil => constr:(@nil word) | C8 ?w :: ?r => let t := cells_words r in constr:(w :: t) | C4 ?w :: ?r => let t := cells_words r in constr:(w :: t) end.
  Ltac csz := cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length BSH0 BSH4 FSAVED zfh_cells].

  (* [comment removed for export] *)
  Ltac db_chk mm p UDx RDSx DG :=
    let RDz := fresh "RDz" in let RTz := fresh "RTz" in
    pose proof (db_sh_rd0s mm DCTX 95992 p UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
    pose proof (db_sh_rng1 RNG DCTX p RDSx (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz;
    zstep; clear RDz RTz;
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity; try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity;
    zstep; if_false.

  (* [comment removed for export] *)
  Local Ltac acc_hint ::= lazymatch goal with
    | |- acc_in ?R (Z_to_bv 64 (SPA + _), _) => match goal with H : rng R lo (SPV - lo) |- _ => solve_acc_with H end
    | |- acc_in ?R (Z_to_bv 64 SPA, _) => match goal with H : rng R lo (SPV - lo) |- _ => solve_acc_with H end
    end.

  (* [comment removed for export] *)
  Lemma db_seqhdr_tab_fcall : forall LB' (mq m m' : amem) W k own dflt d pv,
    AHEAP AI L RNG st LB' mq -> ainblk LB' DCTX 95992 -> disjoint_from W (DCTX + 32) 10264 ->
    munch (W ++ fake_area L) m m' -> ffr_pres W LB' m m' -> seq_tbl_at bsegs m' k dflt d ->
    32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
    seqhdr_tab m DCTX k own dflt d pv -> seqhdr_tab m' DCTX k own dflt d pv.
  Proof.
    intros LB' mq m m' W k own dflt d pv AHq IB DJ MUq FFRq DF O1 O2 (T & t & E & TPT & TA). exists T, t. split; [exact E|]. split; [exact TPT|].
    destruct TA as [BA OK]. destruct TPT as [-> | [-> ->]]; [| exact DF]. split; [| exact OK]. pose proof (seq_tbl_len_le k t OK) as LEN.
    eapply (fcall_bytes_pres AI FHL); [exact AHq| | | exact MUq| exact FFRq| exact BA].
    - destruct IB as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hb1 Hb2 O1 O2 LEN; lia].
    - eapply disjoint_from_sub1; [exact DJ| clear - O1; lia| clear - O2 LEN; lia].
  Qed.

  Hypothesis SEQL : zd_seq_long_stmtA AI rng_fs.
  Notation tab_readyA := (AZ_dblock_f.tab_readyA RNG LB SPA lo DCTX B0 B1 FF).

  Lemma p_long : forall m4 p0 p1 p2 huv lev fev wsv r r2 nbSeq jA jB w0 MXD
                          (xra x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m4 ->
    rw_cells bsegs m4 SPA [CB 16 jA; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 MXD); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 DCTX);
                           C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m4 FF [C8 w0] -> rw_cells bsegs m4 (FF + 32) [C4 (Z_to_bv 64 nbSeq)] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m4 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) -> wnth wsv H5_ddictIsCold = Z_to_bv 64 0 ->
    HUFINVw m4 DCTX huv lev -> cbs <= fh_bsmax h -> MXD = Z.min CAP (fh_bsmax h) ->
    1 <= r <= cbs -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    0 <= r2 <= cbs - r -> 0 <= nbSeq <= 98047 -> (nbSeq <> 0 -> DST <> 0 /\ CAP <> 0) ->
    ((nbSeq = 0 /\ atbl_seq m4 DCTX p0 p1 p2 fev)
     \/ (nbSeq <> 0 /\ seqhdr_tab m4 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                       seqhdr_tab m4 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                       seqhdr_tab m4 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)) ->
    evtF bsegs RNG POST (ST 0x89628 m4 xra x5 x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (SRC + ip + r + r2)) (Z_to_bv 64 (cbs - r - r2)) xa5 (Z_to_bv 64 DCTX) xa7
                           xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31).

  Proof.
    intros until x31. intros I FRA XM XN XP XS KEEP W17 HINV KB EMXD RL PLACED R2R NBR NZD TABS. db_open CTX. pose proof I as DBI. open_dbb I.
    unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    (* [comment removed for export] *)
    assert (TR : exists LLT MLT OFT tLL tOF tML, p0 = Z_to_bv 64 LLT /\ p1 = Z_to_bv 64 MLT /\ p2 = Z_to_bv 64 OFT /\
              (nbSeq <> 0 -> tab_readyA m4 K_LL (8 * (1 + 2^9)) p0 LLT tLL /\ tab_readyA m4 K_OF (8 * (1 + 2^8)) p2 OFT tOF /\ tab_readyA m4 K_ML (8 * (1 + 2^9)) p1 MLT tML)).
    { destruct TABS as [(NZ & TS) | (NNZ & TLL & TOF & TML)].
      - exists (bv_unsigned p0), (bv_unsigned p1), (bv_unsigned p2), LL_defaultDTable, LL_defaultDTable, LL_defaultDTable.
        rewrite !Z_to_bv_bv_unsigned. repeat (split; [reflexivity|]). intros C. contradiction.
      - destruct (NZD NNZ) as [DN0 CN0]. assert (HBB : B0 < B1) by (exact (DNB DN0)).
        destruct (AZ_dblock_f.db_tab_ready fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX
                    m4 K_LL _ _ _ p0 (8 * (1 + 2^9)) TLL eq_refl ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; lia) ltac:(unfold DCTX_entropy_LLTable; reflexivity)
                    ltac:(left; repeat split; reflexivity) UD ARO HBB) as (LLT & tLL & RL1).
        destruct (AZ_dblock_f.db_tab_ready fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX
                    m4 K_OF _ _ _ p2 (8 * (1 + 2^8)) TOF eq_refl ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; reflexivity)
                    ltac:(right; left; repeat split; reflexivity) UD ARO HBB) as (OFT & tOF & RO1).
        destruct (AZ_dblock_f.db_tab_ready fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX
                    m4 K_ML _ _ _ p1 (8 * (1 + 2^9)) TML eq_refl ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; lia) ltac:(unfold DCTX_entropy_MLTable; reflexivity)
                    ltac:(right; right; repeat split; reflexivity) UD ARO HBB) as (MLT & tML & RM1).
        exists LLT, MLT, OFT, tLL, tOF, tML. split; [exact (proj1 RL1)|]. split; [exact (proj1 RM1)|]. split; [exact (proj1 RO1)|]. intros _. split; [exact RL1| split; [exact RO1| exact RM1]]. }
    destruct TR as (LLT & MLT & OFT & tLL & tOF & tML & EP0 & EP1 & EP2 & TRD).
    (* [comment removed for export] *)
    destruct (db_src_mid m4 SRC src (ip + r + r2) (cbs - r - r2) SRCB FBY ltac:(clear - IP0 RL R2R; lia) ltac:(clear - R2R; lia) ltac:(clear - IPC RL R2R; lia)) as (SQB & SQL & SQF).
    set (sq := firstn (Z.to_nat (cbs - r - r2)) (skipn (Z.to_nat (ip + r + r2)) src)) in *.
    destruct (stk_open bsegs m4 _ _ (DCTX + 26684) 12 EREP ltac:(clear; lia) ltac:(clear; lia)) as (jr & REPC & EREPa & EREPb).
    destruct (db_cb12_as_c4s m4 _ _ REPC) as (rp0 & rp1 & rp2 & REP). clear REPC.
    change (Z.of_nat 12) with 12 in EREPb. replace (DCTX + 26684 + 12) with (DCTX + 26696) in EREPb by (clear; lia).
    destruct PLACED as (LITP & LITSZ & LITB & LBE & LOC & ELP & ELS & ELB & ELE & ELL & LSZR & LPLE & PLC).
    unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, ZSTD_LITBUFFEREXTRASIZE, DCTX_litExtraBuffer in PLC.
    destruct (AZ_dblock_f.db_lit_placed fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX m4 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC)
      as (LP0 & LPH & LRD & LPL & LOFF & LAP).
    (* [comment removed for export] *)
    assert (ARD : areg RNG m4 DCTX 95992) by (intros _; split; [exact D1| split; [exact UD| split; [exact RD1| exact RD2]]]).
    assert (ARS4 : areg RNG m4 SRC (zlen src)) by (intros NZ; split; [exact (S1 NZ)| split; [exact (US NZ)| exact (R_src NZ)]]).
    assert (ARB4 : B0 < B1 -> areg RNG m4 B0 (B1 - B0)).
    { intros HB. intros _. pose proof (OUTB HB) as (OB1 & OB2 & OB3). unfold aregU. replace (B0 + (B1 - B0)) with B1 by (clear; lia). split; [exact OB1| split; [exact (UB HB)| exact (R_out HB)]]. }
    assert (LITA : areg RNG m4 LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\ ahull RNG m4 LITP (LBE + WILDCOPY_OVERLENGTH - LITP) /\ ainblk (FB0 FF :: LB) LITP (LBE + WILDCOPY_OVERLENGTH - LITP)).
    { unfold WILDCOPY_OVERLENGTH.
      destruct PLC as [(QL & QE & [(QX & QM) | (QS & QH)]) | [(QL & QE & QB & QDL & QDH) | (QL & QG & QB & QDL & QDH & QEE)]].
      - split; [eapply areg_sub; [exact ARD| clear - QX; lia| clear - LPLE; lia| clear - QX QM QE LSZR; lia]|].
        split; [eapply db_ahull_sub; [exact AHD| clear - QX; lia| clear - QX QM QE LSZR; lia]|].
        apply INCONS. eapply db_inblk_sub; [exact D4| clear - QX; lia| clear - QX QM QE LSZR; lia].
      - assert (NZ : 0 < zlen src) by (clear - IPC IP0 RL; lia).
        split; [eapply areg_sub; [exact ARS4| clear - QS IP0; lia| clear - LPLE; lia| clear - QH IPC; lia]|].
        split; [eapply db_ahull_sub; [exact (AHS NZ)| clear - QS IP0; lia| clear - QH IPC; lia]|].
        apply INCONS. eapply db_inblk_sub; [exact (S4 NZ)| clear - QS IP0; lia| clear - QH IPC; lia].
      - assert (HB : B0 < B1) by (clear - QDL QDH QB LPLE B0D DCB; lia). pose proof (OUTB HB) as (_ & OB2 & _).
        split; [eapply areg_sub; [exact (ARB4 HB)| clear - QDL QB B0D; lia| clear - LPLE; lia| clear - QDH DCB; lia]|].
        split; [eapply db_ahull_sub; [exact (AHB HB)| clear - QDL QB B0D; lia| clear - QDH DCB; lia]|].
        apply INCONS. eapply db_inblk_sub; [exact OB2| clear - QDL QB B0D; lia| clear - QDH DCB; lia].
      - assert (HB : B0 < B1) by (clear - QDL QDH LPLE B0D DCB; lia). pose proof (OUTB HB) as (_ & OB2 & _).
        split; [eapply areg_sub; [exact (ARB4 HB)| clear - QDL B0D; lia| clear - LPLE; lia| clear - QDH DCB; lia]|].
        split; [eapply db_ahull_sub; [exact (AHB HB)| clear - QDL B0D; lia| clear - QDH DCB; lia]|].
        apply INCONS. eapply db_inblk_sub; [exact OB2| clear - QDL B0D; lia| clear - QDH DCB; lia]. }
    destruct LITA as (LAR & LAH & LAI).
    assert (LOCS : LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst \/ LOC = ZSTD_split).
    { unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split. destruct PLC as [(QL & _) | [(QL & _) | (QL & _)]]; [left | right; left | right; right]; exact QL. }
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (AFP4 : afpre AI rng_fs L RNG st (FB0 FF :: LB) m4 lo SPA 1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & RA & RB & RC & RD & RE & RF & RG & _).
      unfold afpre, astk. split; [exact AH|]. split; [eapply ashort_mono; [eapply (ashort_push _ _ 5); [exact ASH| clear; lia]| clear; lia]|].
      split; [unfold art; split; [exact RA|]; split; [exact RB|]; split; [exact RD|]; split; [exact RF|]; split; [exact RG| exact RC]|].
      split; [split; [unfold KHIGH; exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    (* [comment removed for export] *)
    assert (TT : nbSeq <> 0 ->
       (seq_table_at m4 K_LL LLT tLL /\ seq_table_at m4 K_OF OFT tOF /\ seq_table_at m4 K_ML MLT tML /\ 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47)
       /\ (AZ_seq_iface.off_stack lo SPA LLT (8 * (1 + 2^9)) /\ AZ_seq_iface.off_stack lo SPA OFT (8 * (1 + 2^8)) /\ AZ_seq_iface.off_stack lo SPA MLT (8 * (1 + 2^9)))
       /\ (AZ_seq_iface.apart B0 (B1 - B0) LLT (8 * (1 + 2^9)) /\ AZ_seq_iface.apart B0 (B1 - B0) OFT (8 * (1 + 2^8)) /\ AZ_seq_iface.apart B0 (B1 - B0) MLT (8 * (1 + 2^9)))
       /\ (AZ_seq_iface.apart LLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
           AZ_seq_iface.apart OFT (8 * (1 + 2^8)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep) /\
           AZ_seq_iface.apart MLT (8 * (1 + 2^9)) (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep))
       /\ ((ainblk (FB0 FF :: LB) LLT (8 * (1 + 2^9)) \/ LLT + 8 * (1 + 2^9) <= AIMG_HI) /\ (ainblk (FB0 FF :: LB) OFT (8 * (1 + 2^8)) \/ OFT + 8 * (1 + 2^8) <= AIMG_HI) /\ (ainblk (FB0 FF :: LB) MLT (8 * (1 + 2^9)) \/ MLT + 8 * (1 + 2^9) <= AIMG_HI))
       /\ (aro RNG m4 LLT (8 * (1 + 2 ^ st_log tLL)) /\ aro RNG m4 OFT (8 * (1 + 2 ^ st_log tOF)) /\ aro RNG m4 MLT (8 * (1 + 2 ^ st_log tML)))
       /\ (LLT mod 8 = 0 /\ OFT mod 8 = 0 /\ MLT mod 8 = 0)).
    { intros NZ. destruct (TRD NZ) as ((_ & La & Lb & Lc & Ld & Le & Lf & Lg & Lh) & (_ & Oa & Ob & Oc & Od & Oe & Of & Og & Oh) & (_ & Ma & Mb & Mc & Md & Me & Mf & Mg & Mh)).
      split; [exact (conj La (conj Oa (conj Ma (conj Lb (conj Ob Mb)))))|]. split; [exact (conj Lc (conj Oc Mc))|]. split; [exact (conj Ld (conj Od Md))|].
      split; [exact (conj Le (conj Oe Me))|]. split; [exact (conj Lg (conj Og Mg))|]. split; [exact (conj Lf (conj Of Mf))| exact (conj Lh (conj Oh Mh))]. }
    fk_hold DBI. fk_hold SEQL. fk_hold KEEP. fk_hold W17. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold TRD. fk_hold TT. fk_hold XM. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    fk_hold SQB. fk_hold SQF. fk_hold EREPa. fk_hold EREPb. fk_hold REP. fk_hold LRD. fk_hold LPL. fk_hold LOFF. fk_hold LAP. fk_hold LAR. fk_hold LAH. fk_hold LAI.
    fk_hold ARD. fk_hold ARS4. fk_hold ARB4. fk_hold AFP4. fk_hold LBH'. fk_hold INCONS. fk_hold LOCS. fk_hold PLC.
    clearbody sq.
    zstep.                                                     (* [comment removed for export] *)
    unfold fk_held in RF1.
    zstep. try rewrite (sx32w_small nbSeq) by (clear - NBR; lia).   (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    gf_unhold.
    zstep.                                                     (* [comment removed for export] *)
    unfold zd_seq_long_stmtA, zd_seq_long_stmtA_at, APZD_SEQ_LONG in SEQL.
    eapply evtF_cut.
    { eapply (SEQL L RNG st (FB0 FF :: LB)) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1)
          (SEQ := SRC + ip + r + r2) (nbSeq := nbSeq) (LLT := LLT) (MLT := MLT) (OFT := OFT) (PFX := PFX) (LITP := LITP) (LBE := LBE) (LITB := LITB) (LOC := LOC)
          (sq := sq) (tLL := tLL) (tOF := tOF) (tML := tML) (huf := huv) (r0 := rp0) (r1 := rp1) (r2 := rp2) (pde := pde) (dend := Z_to_bv 64 0) (expd := expd)
          (pcs := pcs) (dsz := dsz) (bt := bt) (stg := stg) (le := lev) (fe := fev) (ws := wsv);
      lazymatch goal with
      | |- seq_dctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold seq_dctx; rewrite <- EP0, <- EP1, <- EP2; split; [exact PTRS| split; [exact REP| split; [exact H1| split; [exact H3| exact H5]]]]
      | |- seq_lit2 _ _ _ _ _ => unfold seq_lit2; split; [exact ELP| split; [exact ELE| split; [exact ELB| exact ELL]]]
      | |- 4096 <= DCTX => exact DCL
      | |- DCTX + DCTX_SIZEOF < _ => unfold DCTX_SIZEOF; exact DCH
      | |- DCTX mod 8 = 0 => exact DCA
      | |- bytes_at _ _ _ _ => replace (SRC + ip + r + r2) with (SRC + (ip + r + r2)) by (clear; lia); exact SQB
      | |- all_bytes sq => apply Forall_all_bytes; exact SQF
      | |- 4096 <= SRC + _ + _ + _ => clear - SRCL IP0 RL R2R; lia
      | |- SRC + _ + _ + _ + zlen sq < _ => rewrite SQL; clear - SRCH IPC IP0 RL R2R; lia
      | |- 0 <= nbSeq <= _ => exact NBR
      | |- nbSeq <> 0 -> seq_table_at _ _ _ _ /\ _ => intros NZ; exact (proj1 (TT NZ))
      | |- stk _ _ B0 B1 => exact BUF
      | |- B0 <= DST => exact B0D
      | |- nbSeq <> 0 -> B0 <= PFX <= DST => intros NZ; destruct (NZD NZ) as [_ CN0]; destruct WIN as [[_ C0]|WW]; [exfalso; exact (CN0 C0)| exact WW]
      | |- DST + CAP <= B1 => exact DCB
      | |- 0 <= CAP => exact CAP0
      | |- B1 < _ => exact B1H
      | |- DST = 0 -> _ => intros E0; split; [exact (DNULL E0)| destruct (Z.eq_dec nbSeq 0) as [Q|Q]; [exact Q| exfalso; exact (proj1 (NZD Q) E0)]]
      | |- DST <> 0 -> 4096 <= B0 => exact DNN
      | |- LOC = _ \/ _ => exact LOCS
      | |- 4096 <= LITP => exact LP0
      | |- LITP <= LBE => exact LPLE
      | |- LBE - LITP < _ => clear - PLC LSZR; lia
      | |- LBE + _ < _ => exact LPH
      | |- rdbl _ _ _ _ => exact LRD
      | |- seq_lit_placed _ _ _ _ _ _ _ _ _ _ => exact LPL
      | |- stk _ _ lo SPA => exact STL
      | |- 4096 <= lo => exact LO0
      | |- lo <= SPA - _ => clear - G2; lia
      | |- 0 <= SPA < _ => clear - G2 G3 SPH LO0; lia
      | |- AZ_seq_iface.off_stack _ _ DCTX _ => unfold AZ_seq_iface.off_stack, DCTX_SIZEOF; clear - OFFD G3; lia
      | |- AZ_seq_iface.off_stack _ _ B0 _ => unfold AZ_seq_iface.off_stack; clear - OFFB G3; lia
      | |- AZ_seq_iface.off_stack _ _ (SRC + _ + _ + _) _ => unfold AZ_seq_iface.off_stack; rewrite SQL; clear - OFFSRC G3 IPC IP0 RL R2R; lia
      | |- AZ_seq_iface.off_stack _ _ LITP _ => exact LOFF
      | |- nbSeq <> 0 -> AZ_seq_iface.off_stack _ _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (TT NZ)))
      | |- AZ_seq_iface.apart B0 _ DCTX _ => unfold AZ_seq_iface.apart, DCTX_SIZEOF; clear - BD; lia
      | |- AZ_seq_iface.apart B0 _ (SRC + _ + _ + _) _ => unfold AZ_seq_iface.apart; rewrite SQL; clear - BSRC IPC IP0 RL R2R; lia
      | |- nbSeq <> 0 -> AZ_seq_iface.apart B0 _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (proj2 (TT NZ))))
      | |- AZ_seq_iface.apart (SRC + _ + _ + _) _ _ _ => unfold AZ_seq_iface.apart, DCTX_SIZEOF, DCTX_entropy_rep; rewrite SQL; clear - SRCD IPC IP0 RL R2R; lia
      | |- LOC <> _ -> _ => exact LAP
      | |- nbSeq <> 0 -> AZ_seq_iface.apart LLT _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (proj2 (proj2 (TT NZ)))))
      | |- DST <> 0 -> B0 < B1 => exact DNB
      | |- nbSeq <> 0 -> 0 < CAP => intros NZ; destruct (NZD NZ) as [_ CN0]; clear - CN0 CAP0; lia
      | |- afpre _ _ _ _ _ _ _ _ _ _ => exact AFP4
      | |- tp = _ => exact TP
      | |- azstk _ _ _ _ => eapply azstk_sub; [exact AZS| clear; lia| clear - G2; lia| clear - G3; lia]
      | |- areg _ _ DCTX _ => unfold DCTX_SIZEOF; exact ARD
      | |- ahull _ _ DCTX _ => unfold DCTX_SIZEOF; exact AHD
      | |- ainblk _ DCTX _ => unfold DCTX_SIZEOF; apply INCONS; exact D4
      | |- areg _ _ (SRC + _ + _ + _) _ => rewrite SQL; eapply areg_sub; [exact ARS4| clear - IP0 RL R2R; lia| clear - R2R; lia| clear - IPC RL R2R; lia]
      | |- 0 < _ -> ainblk _ (SRC + _ + _ + _) _ => rewrite SQL; intros NZ'; apply INCONS; eapply db_inblk_sub; [exact (S4 ltac:(clear - NZ' IPC IP0 RL R2R; lia))| clear - IP0 RL R2R; lia| clear - IPC RL R2R; lia]
      | |- nbSeq <> 0 -> (ainblk _ _ _ \/ _) /\ _ => intros NZ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (TT NZ))))))
      | |- nbSeq <> 0 -> aro _ _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (TT NZ)))))))
      | |- aro_client _ _ => exact ARO
      | |- nbSeq <> 0 -> LLT mod 8 = 0 /\ _ => intros NZ; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (TT NZ)))))))
      | |- B0 < B1 -> _ => intros HB; pose proof (OUTB HB) as (_ & OB2 & _); split; [exact (ARB4 HB)| split; [exact (AHB HB)| apply INCONS; exact OB2]]
      | |- areg _ _ LITP _ => exact LAR
      | |- ahull _ _ LITP _ => exact LAH
      | |- ainblk _ LITP _ => exact LAI
      | |- mem_inv _ _ => exact MI
      | |- (fun _ => _) _ => cbv beta; exact LOCS
      | |- _ = _ => first [reflexivity | rewrite SQL; reflexivity]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m5 & rq & rq0 & rq1 & rq2 & ws5
                    & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & BUF5 & REP5 & H35 & H55 & KEEP5 & RR5 & RES5).
    rd_retlit.
    unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in MU5, FFR5, REP5.
    (* [comment removed for export] *)
    set (IVD := if 0 <? CAP then (DST, DST + CAP) else (DCTX + 26684, DCTX + 26684)).
    assert (IVDP : (0 < CAP /\ IVD = (DST, DST + CAP) /\ B0 < B1) \/ (CAP = 0 /\ IVD = (DCTX + 26684, DCTX + 26684))).
    { subst IVD. destruct (Z.ltb_spec 0 CAP) as [Hc|Hc]; [left; split; [exact Hc| split; [reflexivity| clear - Hc B0D DCB; lia]]| right; split; [clear - Hc CAP0; lia| reflexivity]]. }
    clearbody IVD.
    set (W5 := [IVD; (DCTX + 26684, DCTX + 26696); (DCTX + 30004, DCTX + 30008); (DCTX + 30368, DCTX + 30372); (SPA - 5056, SPA)]).
    assert (MU5' : munch (W5 ++ fake_area L) m4 m5).
    { eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp; cbn [outside app]. intros x Hx.
      destruct IVDP as [(Hc & -> & _)|(Hc & ->)]; cbn [fst snd] in Hx; destruct Hx as (Hx1 & Hx2 & Hx3 & Hx4 & Hx);
        (split; [clear - Hx1 Hc; lia| split; [clear - Hx2; lia| split; [clear - Hx3; lia| split; [clear - Hx4; lia| exact Hx]]]]). }
    assert (FFR5' : ffr_pres W5 (FB0 FF :: LB) m4 m5).
    { eapply db_ffr_pres_weaken; [exact FFR5|]. subst W5. unfold sub_fp; cbn [outside]; intros x Hx.
      destruct IVDP as [(Hc & -> & _)|(Hc & ->)]; cbn [fst snd] in Hx; destruct Hx as (Hx1 & Hx2 & Hx3 & Hx4 & Hx5); cbn;
        (split; [clear - Hx1 Hc; lia| split; [clear - Hx2; lia| split; [clear - Hx3; lia| split; [clear - Hx4; lia| exact I]]]]). }
    clear MU5. rename MU5' into MU5.
    assert (AW5 : aappW W5).
    { subst W5. unfold aappW, KLOW, KHIGH. pose proof (ablk_disj_band _ _ D1) as DBD. unfold KLS in DBD.
      apply Forall_cons; [destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [fst snd];
        [pose proof (OUTB HB) as (OB1 & _); pose proof (ablk_disj_band _ _ OB1) as OBD; pose proof (fk_ablk_lits _ _ OB1) as OBL; unfold KLS in OBD; clear - OBD OBL B0D DCB CAP0; lia
        | clear - DBD DL; lia]|].
      repeat (apply Forall_cons; [cbn [fst snd]; clear - DBD DL KLO G2 G3; lia|]). apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k A1 A2 Hk. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from app fake_area]; rewrite !shad_div; unfold FAKESZ, ASHOFF in *;
        (split; [first [clear - A1 A2 Hk OFFB B0D DCB G2 G3 HB; lia| clear - A1 A2 Hk OFFD G2 G3; lia]|]);
        clear - A1 A2 Hk FABL OFFD G1 G2 G3 ATR KLO; repeat split; Z.div_mod_to_equations; lia. }
    assert (DJF : forall X k, FF <= X -> X + k <= FF + 64 -> 0 <= k -> disjoint_from W5 X k).
    { intros X k A1 A2 Hk. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
        (split; [first [pose proof (OUTB HB) as (_ & _ & OB3); clear - OB3 A1 A2 Hk B0D DCB; lia| clear - A1 A2 Hk D5; lia]|]);
        clear - A1 A2 Hk D5 F3 G1 G2; repeat split; lia. }
    assert (PFF : forall X k a, FF <= X -> X + k <= FF + 64 -> 0 <= k -> X <= a < X + k ->
              (in_fake (FB0 FF :: LB) a /\ outside W5 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros X k a A1 A2 Hk Ha. left. split; [exists 0, FF, 64; split; [left; reflexivity| clear - A1 A2 Ha; lia]|].
      eapply disjoint_outside; [exact (DJF X k A1 A2 Hk)| exact Ha]. }
    assert (PSF : forall a, SHF <= a < SHF + 8 -> (in_fake (FB0 FF :: LB) a /\ outside W5 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 0, FF, 64; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DSTK; [clear - G3; lia| csz; clear; lia| clear; lia])) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DSTK; [clear; lia| csz; clear - G3; lia| clear; lia])) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as STG5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5' XM ltac:(csz; intros a Ha; apply (PFF FF 8 a); clear - Ha; lia)) as XM5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5' XP ltac:(csz; intros a Ha; apply (PFF (FF + 56) 8 a); clear - Ha; lia)) as XP5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5' XS ltac:(csz; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    assert (DIN : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> ainblk (FB0 FF :: LB) X k)
      by (intros X k A1 A2; destruct D4 as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| clear - A1 A2 Hb1 Hb2; lia]).
    assert (DDJ : forall X k, DCTX <= X -> (X + k <= DCTX + 26684 \/ (DCTX + 26696 <= X /\ X + k <= DCTX + 30004) \/ (DCTX + 30008 <= X /\ X + k <= DCTX + 30368) \/ (DCTX + 30372 <= X /\ X + k <= DCTX + 95992)) -> 0 <= k ->
                  disjoint_from W5 X k).
    { intros X k A1 A2 Hk. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
        (split; [first [clear - BD A1 A2 Hk B0D DCB HB; lia| clear - A1 A2 Hk; lia]|]);
        clear - A1 A2 Hk OFFD G2 G3; repeat split; lia. }
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ DCTX [C8 p0; C8 p1; C8 p2; C8 huv] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' PTRS) as PTRS5.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' H1) as H15.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29928) (zfh_cells h) AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' FP) as FP5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 32) (DCTX + 10296) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' ESEQ) as ESEQ5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 10296) (DCTX + 26684) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' EHUF) as EHUF5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 26696) (DCTX + 27324) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' EREPb) as EREPb5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 27324) (DCTX + 29884) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' EWK) as EWK5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29884) (DCTX + 29888) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' EPAD) as EPAD5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 30372) (DCTX + 95940) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' XB) as XB5.
    assert (EREP5 : stk bsegs m5 (DCTX + 26684) (DCTX + 27324)).
    { eapply (stk_close bsegs m5 _ _ (DCTX + 26684) [C4 rq0; C4 rq1; C4 rq2]);
        [apply (stk_empty bsegs); clear - DCL DCH; lia| exact REP5| csz; replace (DCTX + 26684 + Z.of_nat 12) with (DCTX + 26696) by (clear; lia); exact EREPb5| clear; lia| csz; clear; lia]. }
    assert (SB5 : bytes_at bsegs m5 SRC (map (Z_to_bv 8) src)).
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [Hz|Hz].
      - pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
        eapply (fcall_bytes_pres AI FHL); [exact AH| rewrite length_map; apply INCONS; exact (S4 Hz)| | exact MU5| exact FFR5'| exact SRCB].
        rewrite length_map. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
          (split; [first [clear - BSRC Hz B0D DCB HB; lia| clear - SRCD Hz; lia]|]);
          clear - Hz SRCD OFFSRC G2 G3; repeat split; lia.
      - destruct SRCB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    assert (UD5 : unpoisoned m5 DCTX (DCTX + 95992)).
    { eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact D4| clear; lia| unfold KEND; clear - DL ATR; lia| exact AW5| exact MU5| exact FFR5'| exact UD]. }
    assert (US5 : 0 < zlen src -> unpoisoned m5 SRC (SRC + zlen src)).
    { intros Hz. pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact (S4 Hz)| exact Hz| unfold KEND; clear - SL ATR; lia| exact AW5| exact MU5| exact FFR5'| exact (US Hz)]. }
    assert (UB5 : B0 < B1 -> unpoisoned m5 B0 B1).
    { intros Hz. pose proof (OUTB Hz) as (OB1 & OB2 & _). pose proof (fk_ablk_lits _ _ OB1) as BL. replace B1 with (B0 + (B1 - B0)) by (clear; lia).
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact OB2| clear - Hz; lia| unfold KEND; clear - BL ATR; lia| exact AW5| exact MU5| exact FFR5'|].
      replace (B0 + (B1 - B0)) with B1 by (clear; lia). exact (UB Hz). }
    assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO| exact MU5| exact WM5| exact AW5| exact FAB]).
    assert (AZS5 : azstk RNG m5 lo SPV).
    { eapply azstk_transport_F; [exact AZS| exact MU5| exact WM5| exact AW5| exact FAB| clear; unfold al_fake; Z.div_mod_to_equations; lia
                               | destruct LY5 as (_ & _ & FA1 & FA2); unfold FAKESZ; clear - FA2 G1; lia| clear - G2 G3; lia]. }
    pose proof (db_ahull_wmono _ _ _ _ _ AHD WM5) as AHD5.
    assert (HINV5 : HUFINVw m5 DCTX huv lev).
    { eapply (AZ_dblock_c.db_hufinv_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5); [exact AH| apply INCONS; exact D4| apply DDJ; clear; lia| exact MU5| exact FFR5'| exact HINV]. }
    (* [comment removed for export] *)
    assert (FFR05 : ffr_pres WR LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR|].
      eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
      - left. cbn [outside] in HO |- *. destruct HO as (O1 & O2 & O3 & O4 & _).
        split; [exists c, A, k; split; [right; exact Hb| exact Ha]| clear - O1 O2 O3 O4; repeat split; lia].
      - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (MU05 : munch (FOOT ++ fake_area L) m0 m5).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [fst snd]; destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6);
        (split; [first [exact X1| clear - X2; lia]|]); clear - X2 X3 X4 X5 X6 G3; repeat split; try lia; tauto. }
    assert (WM05 : wmono bsegs m0 m5) by exact (wmono_trans _ _ _ _ WM WM5).
    assert (DB5 : DBB p0 p1 p2 huv lev (if nbSeq =? 0 then fev else Z_to_bv 64 1) ws5 m5).
    { split; [exact PTRS5|]. split; [exact H15|]. split; [exact FP5|]. split; [exact H35|]. split; [exact H55|].
      split; [exact ESEQ5|]. split; [exact EHUF5|]. split; [exact EREP5|]. split; [exact EWK5|]. split; [exact EPAD5|]. split; [exact XB5|].
      split; [exact SB5|]. split; [exact BUF5|]. split; [exact ST5|]. split; [exact SAV5|]. split; [exact STG5|]. split; [exact MI5|].
      split; [exact AH5|]. split; [exact FFR05|]. split; [exact MU05|]. split; [exact WM05|].
      split; [exact UD5|]. split; [exact US5|]. split; [exact UB5|]. split; [exact ARO5|]. split; [exact AZS5|]. split; [exact AHD5|].
      split; [intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHS Hz) WM5)| intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHB Hz) WM5)]. }
    assert (KEEP5' : forall i, h5_block_owned i = false -> wnth ws5 i = wnth ws i).
    { intros i Hi. assert (NE : i <> H5_litBufferLocation) by (intros ->; discriminate Hi). rewrite (KEEP5 i NE). exact (KEEP i Hi). }
    (* [comment removed for export] *)
    assert (TB5 : zd_is_error rq = false -> atbl HUFINVw m5 DCTX p0 p1 p2 huv lev (if nbSeq =? 0 then fev else Z_to_bv 64 1)).
    { intros _. destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)].
      - rewrite (proj2 (Z.eqb_eq nbSeq 0) NZ0). split; [| exact HINV5].
        exact (AZ_dblock_b.db_atbl_seq_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5 _ _ _ _ AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' MI5 T0).
      - rewrite (proj2 (Z.eqb_neq nbSeq 0) NZ1). split; [| exact HINV5].
        destruct (db_seqhdr_tab_fcall (FB0 FF :: LB) m4 m4 m5 W5 K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (all_default_at _ MI5) LL_default_ok) ltac:(unfold DCTX_entropy_LLTable; clear; lia) ltac:(unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; clear; lia) T1) as (T1' & t1' & EQ1 & P1 & A1).
        destruct (db_seqhdr_tab_fcall (FB0 FF :: LB) m4 m4 m5 W5 K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (aof_default_at _ MI5) OF_default_ok) ltac:(unfold DCTX_entropy_OFTable; clear; lia) ltac:(unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; clear; lia) T2) as (T2' & t2' & EQ2 & P2 & A2).
        destruct (db_seqhdr_tab_fcall (FB0 FF :: LB) m4 m4 m5 W5 K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (aml_default_at _ MI5) ML_default_ok) ltac:(unfold DCTX_entropy_MLTable; clear; lia) ltac:(unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia) T3) as (T3' & t3' & EQ3 & P3 & A3).
        rewrite EQ1, EQ2, EQ3. eapply zd_tbl_seq_intro; eassumption. }
    destruct (rw_cells_forget bsegs _ _ _ FRA5) as [jA' FRA']. cbn [cells_size csize Nat.add length] in FRA'.
    eapply (p_exit1 m5 p0 p1 p2 huv lev _ ws5 rq jA' w0 BSH4);
      [exact DB5| exact FRA'| exact XM5| exact XP5| exact XS5| reflexivity| exact RR5| exact KEEP5'| exact TB5| exact RES5].
  Qed.
End DB.
End CANSEC1.
