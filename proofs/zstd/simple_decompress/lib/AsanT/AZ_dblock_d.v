(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_globals AZ_globalsR AZ_frame_iface AZ_huf_iface AZ_block_iface AZ_blk_iface3 AZ_blk_iface5 AZ_blk_iface6 AZ_seq_iface AZ_libc_iface
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a AZ_dblock_b AZ_dblock_c.
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
  (* [comment removed for export] *)
  Ltac b2z_norm G :=
    repeat match type of G with
           | context [Z.ltb ?a ?b] =>
               first [ replace (Z.ltb a b) with true in G by (symmetry; apply Z.ltb_lt; lia)
                     | replace (Z.ltb a b) with false in G by (symmetry; apply Z.ltb_ge; lia) ]
           | context [Z.eqb ?a ?b] =>
               first [ replace (Z.eqb a b) with true in G by (symmetry; apply Z.eqb_eq; lia)
                     | replace (Z.eqb a b) with false in G by (symmetry; apply Z.eqb_neq; lia) ]
           end; cbn [Z.b2z] in G.
  Ltac grdb := let G := fresh "G" in if_cases G; zify_cond G; [ exfalso; b2z_norm G; first [ congruence | lia | vm_compute in G; first [ congruence | lia | apply G; reflexivity ] ] | clear G ].
  Ltac gf_unhold := unfold fk_held in *.
  (* [comment removed for export] *)
  Ltac csz := cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length BSH0 BSH4 FSAVED zfh_cells].

  (* [comment removed for export] *)
  Ltac db_chk mm p UDx RDSx DG :=
    let RDz := fresh "RDz" in let RTz := fresh "RTz" in
    pose proof (db_sh_rd0s mm DCTX 95992 p UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
    pose proof (db_sh_rng1 RNG DCTX p RDSx (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz;
    zstep; clear RDz RTz;
    try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity; try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity;
    zstep; if_false.

  Hypothesis OFFINFO : zd_offinfo_stmtA.
  Hypothesis SEQD : zd_seq_default_stmtA AI rng_fs.
  Hypothesis SEQS : zd_seq_split_stmtA AI rng_fs.
  Hypothesis SEQL : zd_seq_long_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Hypothesis POK : forall m3 p0 p1 p2 huv lev fev wsv r r2 nbSeq jA jB w0 MXD
                          (xra x5 x6 x7 xa0 xa2 xa4 xa5 xa6 xa7 xs8 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m3 ->
    rw_cells bsegs m3 SPA [CB 16 jA; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 MXD); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 DCTX);
                           C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m3 FF [C8 w0] -> rw_cells bsegs m3 (FF + 32) [C4 (Z_to_bv 64 nbSeq)] -> rw_cells bsegs m3 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m3 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m3 DCTX huv lev -> cbs <= fh_bsmax h -> MXD = Z.min CAP (fh_bsmax h) ->
    1 <= r <= cbs -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    0 <= r2 <= cbs - r -> 0 <= nbSeq <= 98047 -> (nbSeq <> 0 -> DST <> 0 /\ CAP <> 0) ->
    ((nbSeq = 0 /\ atbl_seq m3 DCTX p0 p1 p2 fev)
     \/ (nbSeq <> 0 /\ seqhdr_tab m3 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                       seqhdr_tab m3 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                       seqhdr_tab m3 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)) ->
    evtF bsegs RNG POST (ST 0x89610 m3 xra x5 x6 x7 xa0 (Z_to_bv 64 r2) xa2 (Z_to_bv 64 (SRC + ip + r + r2)) xa4 xa5 xa6 xa7
                           (Mem.sx32 (wnth wsv H5_ddictIsCold)) (Z_to_bv 64 (cbs - r)) xs8 (Z_to_bv 64 (DCTX + 30204)) (Z_to_bv 64 (Z.shiftr (DCTX + 30204) 3 + SHB)) x28 x29 x30 x31).

  Lemma p_seq : forall m3 p0 p1 p2 huv lev fev wsv r r2 jA jB w0 nbw MXD
                          (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m3 ->
    rw_cells bsegs m3 SPA [CB 16 jA; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 MXD); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 DCTX);
                           C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m3 FF [C8 w0] -> rw_cells bsegs m3 (FF + 32) [C4 nbw] -> rw_cells bsegs m3 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m3 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m3 DCTX huv lev -> cbs <= fh_bsmax h -> MXD = Z.min CAP (fh_bsmax h) ->
    1 <= r <= cbs -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    0 <= r2 < 2^64 ->
    (zd_is_error r2 = true
     \/ (r2 <= cbs - r /\ exists nbSeq, nbw = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
         ((nbSeq = 0 /\ atbl_seq m3 DCTX p0 p1 p2 fev)
          \/ (nbSeq <> 0 /\ seqhdr_tab m3 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                            seqhdr_tab m3 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                            seqhdr_tab m3 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)))) ->
    evtF bsegs RNG POST (ST 0x895b8 m3 xra x5 x6 x7 (Z_to_bv 64 r2) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           (Mem.sx32 (wnth wsv H5_ddictIsCold)) (Z_to_bv 64 (cbs - r)) (Z_to_bv 64 (SRC + ip + r)) (Z_to_bv 64 (DCTX + 30204)) (Z_to_bv 64 (Z.shiftr (DCTX + 30204) 3 + SHB)) x28 x29 x30 x31).

  Proof.
    intros until x31. intros I FRA XM XN XP XS KEEP HINV KB EMXD RL PLACED RR RES. db_open CTX. pose proof I as DBI. open_dbb I.
    unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    assert (CAPH : 0 <= CAP < 2^47) by (clear - DNN DNULL B0D DCB B1H CAP0; destruct (Z.eq_dec DST 0); lia).
    assert (DSTH : 0 <= DST < 2^47) by (clear - DNN DNULL B0D DCB B1H CAP0; destruct (Z.eq_dec DST 0); lia).
    fk_hold DBI. fk_hold OFFINFO. fk_hold SEQD. fk_hold SEQS. fk_hold SEQL. fk_hold INCONS. fk_hold KEEP. fk_hold PLACED. fk_hold HINV. fk_hold RES. fk_hold XM. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_cases KE; zify_cond KE.                          (* [comment removed for export] *)
    { unfold fk_held in *.
      destruct (rw_cells_forget bsegs _ _ _ FRA) as [jA' FRA']. cbn [cells_size csize Nat.add length] in FRA'.
      eapply (p_exit1 m3 p0 p1 p2 huv lev fev wsv r2 jA' w0 BSH4);
        [exact DBI| exact FRA'| exact XM| exact XP| exact XS| reflexivity| exact RR| exact KEEP| | left; apply (proj2 (zd_is_error_true_iff r2)); clear - KE; lia].
      intros NE. exfalso. apply (proj2 (zd_is_error_true_iff r2)) in KE. rewrite KE in NE. discriminate NE. }
    unfold fk_held in RES. destruct RES as [ER | (R2L & nbSeq & ENB & NBR & TABS)]; [exfalso; apply (proj1 (zd_is_error_true_iff r2)) in ER; clear - ER KE; lia|].
    subst nbw. fk_hold TABS.
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
                                                               (* [comment removed for export] *)
                                                               (* [comment removed for export] *)
                                                               (* [comment removed for export] *)
    try replace (SRC + ip + r + r2) with (SRC + ip + r + r2) by reflexivity.
                                                               (* [comment removed for export] *)
    unfold fk_held in RF1.
    zstep; if_cases KD; zify_cond KD;                          (* [comment removed for export] *)
      [| zstep; zstep; if_cases KC; zify_cond KC].             (* [comment removed for export] *)
    1,2: zstep; zstep; zstep; zstep;                           (* [comment removed for export] *)
         (zstep; if_cases KX; zify_cond KX; [exfalso; clear - KX DSTH; lia|]);   (* [comment removed for export] *)
         zstep; zstep; try rewrite (sx32w_small nbSeq) by (clear - NBR; lia);   (* [comment removed for export] *)
         (zstep; if_cases KN; zify_cond KN).                   (* [comment removed for export] *)
    1,3: replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 (2^64 - 70)) by (apply Z_to_bv_eqm; reflexivity).
    1,2: unfold fk_held in DBI, XM, XP, XS, KEEP; destruct (rw_cells_forget bsegs _ _ _ FRA) as [jA' FRA']; cbn [cells_size csize Nat.add length] in FRA';
         eapply (p_exit1 m3 p0 p1 p2 huv lev fev wsv (2^64 - 70) jA' w0 BSH4);
         [exact DBI| exact FRA'| exact XM| exact XP| exact XS| reflexivity| clear; lia| exact KEEP
         | intros NE; exfalso; rewrite (proj2 (zd_is_error_true_iff (2^64 - 70)) ltac:(clear; lia)) in NE; discriminate NE| left; apply (proj2 (zd_is_error_true_iff _)); clear; lia].
    3: zstep; zstep; zstep;                                    (* [comment removed for export] *)
       (zstep; if_cases KY; zify_cond KY; [| exfalso; clear - KY DSTH; lia]).   (* [comment removed for export] *)
    all: zstep; unfold fk_held in *.
    all: eapply (POK m3 p0 p1 p2 huv lev fev wsv r r2 nbSeq jA jB w0 MXD);
      [exact DBI| exact FRA| exact XM| exact XN| exact XP| exact XS| exact KEEP| exact HINV| exact KB| exact EMXD| exact RL| exact PLACED
      | clear - RR R2L; lia| exact NBR| | exact TABS].
    all: intros NZ; match goal with
         | K : (0 <? ?n) && _ = false, B : 0 <= ?n <= 98047 |- _ => exfalso; apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; clear - K NZ B; lia
         | |- _ => split; assumption
         end.
  Qed.
End DB.
End CANSEC1.
