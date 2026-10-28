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
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a AZ_dblock_b.
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

Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma bsh4_unp : forall (m : amem) FF, rw_cells bsegs m (shad FF) BSH4 -> FF mod 8 = 0 -> 6443008 <= FF -> FF + 64 <= 2^47 ->
  unpoisoned m (FF + 32) (FF + 36).
Proof.
  intros m FF H F8 F0 FH. unfold BSH4 in H. rewrite shad_div in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 BF1; C1 BF1; C1 BF1; C1 BF1] _)) in H.
  destruct H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
  apply (proj1 (rw_cells_app bsegs _ _ [C1 B04] _)) in H. destruct H as [H4 _].
  pose proof (fk_byte_of_c1 m _ _ H4 ltac:(unfold ASHOFF; lia)) as R4.
  split; [lia|]. split; [lia|]. intros G HG Ha Hb.
  assert (E : G = FF / 8 + 4) by (Z.div_mod_to_equations; lia). subst G.
  exists B04. split; [rewrite <- R4; f_equal; f_equal; unfold ASHOFF; lia| right]. change (sval B04) with 4. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma db_h5_cold_cell : forall (m1 : amem) D wsq, dctx_h5 bsegs m1 D wsq -> rw_cells bsegs m1 (D + 30204) [C4 (wnth wsq H5_ddictIsCold)].
Proof.
  intros m1 D wsq (C & L). h5_open wsq L.
  lazymatch type of C with rw_cells _ _ _ ?cs =>
    change cs with (firstn 17 cs ++ [nth 17 cs (C1 (Z_to_bv 8 0))] ++ skipn 18 cs) in C end.
  cbn [firstn skipn nth] in C.
  apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
  cbn [cells_size csize Nat.add] in C. replace (D + 30096 + Z.of_nat 108) with (D + 30204) in C by lia. exact C.
Qed.

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

  (* [comment removed for export] *)
  Lemma db_hufinv_fcall : forall LB' (mq m m' : amem) W huf le,
    AHEAP AI L RNG st LB' mq -> ainblk LB' DCTX 95992 -> disjoint_from W (DCTX + 10296) 16388 ->
    munch (W ++ fake_area L) m m' -> ffr_pres W LB' m m' -> HUFINVw m DCTX huf le -> HUFINVw m' DCTX huf le.
  Proof.
    intros LB' mq m m' W huf le AHq IB DJ MUq FFRq (E & (h4 & B4 & L4 & N4) & TOK). split; [exact E|]. split.
    - exists h4. split; [| split; assumption].
      eapply (fcall_bytes_pres AI FHL); [exact AHq| | | exact MUq| exact FFRq| exact B4].
      + destruct IB as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| rewrite L4; clear - Hb1 Hb2; cbn; lia].
      + eapply disjoint_from_sub1; [exact DJ| clear; lia| rewrite L4; clear; cbn; lia].
    - intros NZ. destruct (TOK NZ) as (dtb & BA & OK). exists dtb. split; [|exact OK].
      assert (LD : zlen dtb = 16388) by (destruct OK as [[LD _] _]; exact LD).
      eapply (fcall_bytes_pres AI FHL); [exact AHq| | | exact MUq| exact FFRq| exact BA].
      + destruct IB as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| rewrite LD; clear - Hb1 Hb2; lia].
      + eapply disjoint_from_sub1; [exact DJ| clear; lia| rewrite LD; clear; lia].
  Qed.

  Hypothesis SEQHDR : zd_seqhdr_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Hypothesis PSH : forall m3 p0 p1 p2 huv lev fev wsv r r2 jA jB w0 nbw MXD
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

  (* [comment removed for export] *)
  Definition PMX_T : Prop := forall m2 p0 p1 p2 huv lev fev wsv r jA jB w0 nbw MXD (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa7 xs3 xs9 xs10 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m2 ->
    rw_cells bsegs m2 SPA [CB 40 jA; C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m2 FF [C8 w0] -> rw_cells bsegs m2 (FF + 32) [C4 nbw] -> rw_cells bsegs m2 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m2 SHF BSH0 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    atbl_seq m2 DCTX p0 p1 p2 fev -> cbs <= fh_bsmax h ->
    1 <= r <= cbs -> HUFINVw m2 DCTX huv lev -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv -> MXD = Z.min CAP (fh_bsmax h) ->
    evtF bsegs RNG POST (ST 0x8955c m2 xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 (Z_to_bv 64 DCTX) (Z_to_bv 64 MXD) xa7
                           xs3 (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + ip)) xs9 xs10 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_mx : PMX_T.
  Proof.
    intros m2 p0 p1 p2 huv lev fev wsv r jA jB w0 nbw MXD xra x5 x6 x7 xa1 xa2 xa3 xa4 xa7 xs3 xs9 xs10 x28 x29 x30 x31 I FRA XM XN XP XS KEEP TBS KB RL HINV PLACED EMXD.
    db_open CTX. pose proof I as DBI. open_dbb I. unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    pose proof (db_h5_cold_cell _ _ _ H5) as COLDC. fk_hold COLDC.
    pose proof (munch_refl [(SPA + 8, SPA + 48); (SHF + 4, SHF + 5)] m2) as MU23. pose proof (wmono_refl bsegs m2) as WM23.
    pose proof (munch_refl [(SPA + 8, SPA + 48)] m2) as MUa.
    assert (UDSH : disjoint_from [(SPA + 8, SPA + 48); (SHF + 4, SHF + 5)] (shad DCTX) (shad (DCTX + 95992 - 1) + 1 - shad DCTX)).
    { cbn [disjoint_from]. rewrite !shad_div. rewrite ESHF. unfold ASHOFF. clear - KLO G2 G3 DL D5 F2 ATR. split; [|split; [|exact I]]; Z.div_mod_to_equations; lia. }
    fk_hold DBI. fk_hold TBS. fk_hold PSH. fk_hold SEQHDR. fk_hold INCONS. fk_hold KEEP. fk_hold PLACED. fk_hold HINV. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold UDSH. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    zstep. zstep.                                              (* [comment removed for export] *)
    db_chk m2 (DCTX + 29904) UD RD2 DG.                        (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (UDx : unpoisoned mx DCTX (DCTX + 95992)) by (eapply unpoisoned_munch; [exact UD| exact MU23| unfold fk_held in UDSH; eapply disjoint_from_sub1; [exact UDSH| clear; lia| clear; lia]]);
      pose proof (db_sh_rd0s mx DCTX 95992 (DCTX + 30204) UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
      pose proof (db_sh_rng1 RNG DCTX (DCTX + 30204) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz; clear UDx end.
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (H1x : rw_cells bsegs mx (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd])
        by (unfold fk_held in H1; eapply rw_cells_transport; [exact H1| exact MU23| exact WM23| csz; cbn [disjoint_from]; unfold fk_held in OFFD, DCSH; clear - OFFD G2 G3 DCSH; repeat split; lia]) end.
    zstep. clear H1x.                                          (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_false.                                           (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (COLDx : rw_cells bsegs mx (DCTX + 30204) [C4 (wnth wsv H5_ddictIsCold)])
        by (unfold fk_held in COLDC; eapply rw_cells_transport; [exact COLDC| exact MU23| exact WM23| csz; cbn [disjoint_from]; unfold fk_held in OFFD, DCSH; clear - OFFD G2 G3 DCSH; repeat split; lia]) end.
    zstep. clear COLDx.                                        (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    unfold fk_held in ESHF.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (XSx : rw_cells bsegs mx SHF BSH0)
        by (unfold fk_held in XS; eapply rw_cells_transport; [exact XS| exact MUa| exact WM23| csz; cbn [disjoint_from]; clear - GS KLO G2 G3; repeat split; lia]) end.
    unfold BSH0 in XSx. clear MUa.
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                                (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    clear COLDC.
    idtac "C1".
    (* [comment removed for export] *)
    gf_unhold.
    assert (H54 : dctx_h5 bsegs m4 DCTX wsv).
    { destruct H5 as [H5C WL']. split; [| exact WL']. eapply rw_cells_transport; [exact H5C| exact MU23| exact WM23| rewrite (h5_cells_size _ WL'); cbn [disjoint_from]].
      clear - OFFD G2 G3 DCSH. repeat split; lia. }
    assert (DB4 : DBB p0 p1 p2 huv lev fev wsv m4).
    { eapply (dbb_keep p0 p1 p2 huv lev fev wsv wsv m2 m4); [exact DBI| exact MU23| exact WM23| exact MI| exact H54|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| left; clear; lia]|]. apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; left; clear; lia]| apply Forall_nil]. }
    assert (HINV4 : HUFINVw m4 DCTX huv lev).
    { eapply hufw_fine; [exact HINV| exact MU23|]. intros x Hx. cbn [outside]. clear - Hx OFFD G2 G3 DCSH. repeat split; lia. }
    assert (TBS4 : atbl_seq m4 DCTX p0 p1 p2 fev).
    { eapply db_atbl_seq_fine; [exact TBS| exact MU23| exact MI|]. intros x Hx. cbn [outside]. clear - Hx OFFD G2 G3 DCSH. repeat split; lia. }
    assert (XM4 : rw_cells bsegs m4 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU23| exact WM23| csz; cbn [disjoint_from]; clear - F3 G1 G2 FFSH; repeat split; lia]).
    assert (XN4 : rw_cells bsegs m4 (FF + 32) [C4 nbw]) by (eapply rw_cells_transport; [exact XN| exact MU23| exact WM23| csz; cbn [disjoint_from]; clear - F3 G1 G2 FFSH; repeat split; lia]).
    assert (XP4 : rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU23| exact WM23| csz; cbn [disjoint_from]; clear - F3 G1 G2 FFSH; repeat split; lia]).
    fold BSH4 in XSx. clear XS. rename XSx into XS.
    clear DBI H5 H54 HINV TBS PTRS FP UD H1 H3 ESEQ EHUF EREP EWK EPAD XB SRCB BUF STL SAV STG AH FFR MU WM US UB ARO AZS AHD AHS AHB MI XM XN XP MU23 WM23 UDSH.
    pose proof DB4 as DBI. open_dbb DB4.
    (* [comment removed for export] *)
    destruct (db_src_mid m4 SRC src (ip + r) (cbs - r) SRCB FBY ltac:(clear - IP0 RL; lia) ltac:(clear - RL; lia) ltac:(clear - IPC RL; lia)) as (SQB & SQL & SQF).
    set (sq := firstn (Z.to_nat (cbs - r)) (skipn (Z.to_nat (ip + r)) src)) in *.
    replace (SRC + ip + r) with (SRC + (ip + r)) by (clear; lia).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (AFP4 : afpre AI rng_fs L RNG st (FB0 FF :: LB) m4 lo SPA 3).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & RA & RB & RC & RD & RE & RF & RG & _).
      unfold afpre, astk. split; [exact AH|]. split; [eapply ashort_mono; [eapply (ashort_push _ _ 5); [exact ASH| clear; lia]| clear; lia]|].
      split; [unfold art; split; [exact RA|]; split; [exact RB|]; split; [exact RD|]; split; [exact RF|]; split; [exact RG| exact RC]|].
      split; [split; [unfold KHIGH; exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    assert (ARS4 : areg RNG m4 SRC (zlen src)) by (intros NZ; split; [exact (S1 NZ)| split; [exact (US NZ)| exact (R_src NZ)]]).
    assert (F8 : FF mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    assert (UNB : unpoisoned m4 (FF + 32) (FF + 36)) by (apply bsh4_unp; [rewrite <- F4; exact XS| exact F8| clear - FL; lia| clear - FL ATR; lia]).
    idtac "C2".
    zstep.                                                     (* [comment removed for export] *)
    unfold zd_seqhdr_stmtA, APZD_SEQHDR in SEQHDR.
    eapply evtF_cut.
    { eapply (SEQHDR L RNG st (FB0 FF :: LB)) with (lo := lo) (DCTX := DCTX) (NBP := FF + 32) (SRC := SRC + (ip + r)) (src := sq) (SPV := SPA)
                                              (llt := p0) (mlt := p1) (oft := p2) (huf := huv) (le := lev) (fe := fev) (pcs := pcs) (dsz := dsz) (bt := bt) (stg := stg) (ws := wsv);
      lazymatch goal with
      | |- dctx_ptrs _ _ _ _ _ _ _ => exact PTRS
      | |- stk _ _ (DCTX + 32) _ => exact ESEQ
      | |- stk _ _ (DCTX + 27324) _ => exact EWK
      | |- dctx_h3 _ _ _ _ _ _ _ _ _ => exact H3
      | |- dctx_h5 _ _ _ _ => exact H5
      | |- atbl_seq _ _ _ _ _ _ => exact TBS4
      | |- 4096 <= DCTX => exact DCL
      | |- DCTX + 95992 < _ => exact DCH
      | |- rw_cells _ _ (FF + 32) _ => exact XN4
      | |- 4096 <= FF + 32 => clear - FL; lia
      | |- FF + 32 + 4 < _ => clear - FL ATR; lia
      | |- bytes_at _ _ _ _ => exact SQB
      | |- Forall _ _ => exact SQF
      | |- zlen sq <= _ => rewrite SQL; clear - KB BSM RL; lia
      | |- 4096 <= SRC + _ => clear - SRCL IP0 RL; lia
      | |- SRC + _ + zlen sq < _ => rewrite SQL; clear - SRCH IPC IP0 RL; lia
      | |- stk _ _ lo SPA => exact STL
      | |- 4096 <= lo => exact LO0
      | |- lo <= SPA - _ => clear - G2; lia
      | |- SPA < _ => clear - G3 SPH; lia
      | |- AZ_blk_iface.off_stack _ _ DCTX _ => unfold AZ_blk_iface.off_stack; clear - OFFD G3; lia
      | |- AZ_blk_iface.off_stack _ _ (FF + 32) _ => unfold AZ_blk_iface.off_stack; clear - F3 G1 G2; lia
      | |- AZ_blk_iface.off_stack _ _ (SRC + _) _ => unfold AZ_blk_iface.off_stack; rewrite SQL; clear - OFFSRC G3 IPC IP0 RL; lia
      | |- AZ_blk_iface.apart DCTX _ (FF + 32) _ => unfold AZ_blk_iface.apart; clear - D5; lia
      | |- AZ_blk_iface.apart DCTX _ (SRC + _) _ => unfold AZ_blk_iface.apart; rewrite SQL; clear - SRCD IPC IP0 RL; lia
      | |- AZ_blk_iface.apart (FF + 32) _ (SRC + _) _ => unfold AZ_blk_iface.apart; rewrite SQL; pose proof (S5 ltac:(clear - IPC IP0 RL; lia)) as S5'; clear - S5' IPC IP0 RL; lia
      | |- afpre _ _ _ _ _ _ _ _ _ _ => exact AFP4
      | |- tp = _ => exact TP
      | |- aro_client _ _ => exact ARO
      | |- DCTX mod 8 = 0 => exact DCA
      | |- areg _ _ DCTX _ => intros _; split; [exact D1| split; [exact UD| split; [exact RD1| exact RD2]]]
      | |- ainblk _ DCTX _ => apply INCONS; exact D4
      | |- areg _ _ (FF + 32) _ => intros _; split; [eapply ablk_sub; [exact F1| clear; lia| clear; lia]| split; [replace (FF + 32 + 4) with (FF + 36) by (clear; lia); exact UNB| split; [eapply rng_sub'; [exact RF1| clear; lia]| eapply rng_sub'; [exact RF2| rewrite F4; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - F8; Z.div_mod_to_equations; lia]]]]
      | |- ainblk _ (FF + 32) _ => exists (FB0 FF); split; [left; reflexivity| cbn; clear; lia]
      | |- areg _ _ (SRC + _) _ => rewrite SQL; eapply areg_sub; [exact ARS4| clear - IP0 RL; lia| clear - RL; lia| clear - IPC RL; lia]
      | |- 0 < _ -> ainimg _ (SRC + _) _ => rewrite SQL; intros NZ'; left; apply INCONS; eapply db_inblk_sub; [exact (S4 ltac:(clear - NZ' IPC IP0 RL; lia))| clear - IP0 RL; lia| clear - IPC RL; lia]
      | |- 0 < _ -> ahull _ _ (SRC + _) _ => rewrite SQL; intros NZ'; eapply db_ahull_sub; [exact (AHS ltac:(clear - NZ' IPC IP0 RL; lia))| clear - IP0 RL; lia| clear - IPC RL; lia]
      | |- mem_inv _ _ => exact MI
      | |- (FF + 32) mod 4 = 0 => clear - F2; Z.div_mod_to_equations; lia      (* [comment removed for export] *)
      | |- _ = _ => first [reflexivity | rewrite SQL; reflexivity]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m5 & r2 & llt' & mlt' & oft' & nbw'
                    & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & PTRS5 & ESEQ5 & EWK5 & NB5 & RR2 & RES2).
    rd_retlit.
    idtac "C3".
    (* [comment removed for export] *)
    pose proof (db_ffr_pres_weaken _ [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (FF + 32, FF + 32 + 4); (SPA - 5248, SPA)] _ _ _ FFR5
                  ltac:(unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; repeat split; first [lia | exact I])) as FFR5w.
    set (W5 := [(DCTX, DCTX + 24); (DCTX + 32, DCTX + 10296); (DCTX + 27324, DCTX + 29884); (FF + 32, FF + 32 + 4); (SPA - 5248, SPA)]) in MU5, FFR5w.
    assert (AW5 : aappW W5).
    { subst W5. unfold aappW, KLOW, KHIGH. pose proof (ablk_disj_band _ _ D1) as DBD. pose proof (ablk_disj_band _ _ F1) as FBD. unfold KLS in DBD, FBD.
      repeat (apply Forall_cons; [cbn [fst snd]; clear - DBD DL FBD FL KLO G2 G3; lia|]). apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k A1 A2 Hk. subst W5. cbn [disjoint_from app fake_area]; rewrite !shad_div; unfold FAKESZ, ASHOFF in *.
      clear - A1 A2 Hk FABL OFFD F3 G1 G2 G3 ATR KLO; repeat split; Z.div_mod_to_equations; lia. }
    assert (DJF : forall X k, FF <= X -> X + k <= FF + 64 -> 0 <= k -> (X + k <= FF + 32 \/ FF + 36 <= X) -> disjoint_from W5 X k).
    { intros X k A1 A2 Hk A3. subst W5. cbn [disjoint_from]. clear - A1 A2 Hk A3 D5 F3 G1 G2; repeat split; first [lia | exact I]. }
    assert (PFF : forall X k a, FF <= X -> X + k <= FF + 64 -> 0 <= k -> (X + k <= FF + 32 \/ FF + 36 <= X) -> X <= a < X + k ->
              (in_fake (FB0 FF :: LB) a /\ outside W5 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros X k a A1 A2 Hk A3 Ha. left. split; [exists 0, FF, 64; split; [left; reflexivity| clear - A1 A2 Ha; lia]|].
      eapply disjoint_outside; [exact (DJF X k A1 A2 Hk A3)| exact Ha]. }
    assert (PSF : forall a, SHF <= a < SHF + 8 -> (in_fake (FB0 FF :: LB) a /\ outside W5 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 0, FF, 64; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU5 WM5 ltac:(apply DSTK; [clear - G3; lia| csz; clear; lia| clear; lia])) as SAV5.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU5 WM5 ltac:(apply DSTK; [clear; lia| csz; clear - G3; lia| clear; lia])) as FRA5.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU5 WM5 ltac:(apply DSTK; clear - G3; lia)) as STG5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5w XM4 ltac:(csz; intros a Ha; apply (PFF FF 8 a); clear - Ha; lia)) as XM5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5w XP4 ltac:(csz; intros a Ha; apply (PFF (FF + 56) 8 a); clear - Ha; lia)) as XP5.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR5w XS ltac:(csz; intros a Ha; apply PSF; clear - Ha; lia)) as XS5.
    assert (DIN : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> ainblk (FB0 FF :: LB) X k)
      by (intros X k A1 A2; destruct D4 as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| clear - A1 A2 Hb1 Hb2; lia]).
    assert (DDJ : forall X k, ((DCTX + 10296 <= X /\ X + k <= DCTX + 27324) \/ DCTX + 29884 <= X) -> X + k <= DCTX + 95992 -> 0 <= k -> disjoint_from W5 X k).
    { intros X k A1 A2 Hk. subst W5. cbn [disjoint_from]. clear - A1 A2 Hk OFFD G2 G3 D5; repeat split; first [lia | exact I]. }
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5w H1) as H15.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29928) (zfh_cells h) AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5w FP) as FP5.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 lev; C4 fev] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5w H3) as H35.
    assert (H55 : dctx_h5 bsegs m5 DCTX wsv).
    { destruct H5 as [H5C WL']. split; [| exact WL'].
      exact (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 30096) (h5_cells wsv) AH ltac:(rewrite (h5_cells_size _ WL'); apply DIN; clear; lia) ltac:(rewrite (h5_cells_size _ WL'); apply DDJ; clear; lia) MU5 WM5 FFR5w H5C). }
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 10296) (DCTX + 26684) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5w EHUF) as EHUF5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 26684) (DCTX + 27324) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5w EREP) as EREP5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29884) (DCTX + 29888) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5w EPAD) as EPAD5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 30372) (DCTX + 95940) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5w XB) as XB5.
    assert (SB5 : bytes_at bsegs m5 SRC (map (Z_to_bv 8) src)).
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [Hz|Hz].
      - pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
        eapply (fcall_bytes_pres AI FHL); [exact AH| rewrite length_map; apply INCONS; exact (S4 Hz)| | exact MU5| exact FFR5w| exact SRCB].
        rewrite length_map. subst W5. cbn [disjoint_from]. pose proof (S5 Hz) as S5'. clear - Hz SRCD OFFSRC S5' G2 G3. repeat split; first [lia | exact I].
      - destruct SRCB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    assert (BUF5 : stk bsegs m5 B0 B1).
    { destruct (Z_lt_ge_dec B0 B1) as [Hz|Hz].
      - pose proof (OUTB Hz) as (OB1 & OB2 & OB3). replace B1 with (B0 + (B1 - B0)) by (clear; lia).
        eapply (fcall_stk_pres AI FHL); [exact AH| apply INCONS; replace (B0 + (B1 - B0) - B0) with (B1 - B0) by (clear; lia); exact OB2| | exact MU5| exact WM5| exact FFR5w| replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact BUF].
        subst W5. cbn [disjoint_from]. clear - Hz BD OFFB OB3 G2 G3. repeat split; first [lia | exact I].
      - pose proof BUF as (B00 & _). replace B1 with B0 by (clear - Hz B0D DCB CAP0; lia). apply (stk_empty bsegs). clear - B00 B0D DCB CAP0 B1H. lia. }
    assert (UD5 : unpoisoned m5 DCTX (DCTX + 95992)).
    { eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact D4| clear; lia| unfold KEND; clear - DL ATR; lia| exact AW5| exact MU5| exact FFR5w| exact UD]. }
    assert (US5 : 0 < zlen src -> unpoisoned m5 SRC (SRC + zlen src)).
    { intros Hz. pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact (S4 Hz)| exact Hz| unfold KEND; clear - SL ATR; lia| exact AW5| exact MU5| exact FFR5w| exact (US Hz)]. }
    assert (UB5 : B0 < B1 -> unpoisoned m5 B0 B1).
    { intros Hz. pose proof (OUTB Hz) as (OB1 & OB2 & _). pose proof (fk_ablk_lits _ _ OB1) as BL. replace B1 with (B0 + (B1 - B0)) by (clear; lia).
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact OB2| clear - Hz; lia| unfold KEND; clear - BL ATR; lia| exact AW5| exact MU5| exact FFR5w|].
      replace (B0 + (B1 - B0)) with B1 by (clear; lia). exact (UB Hz). }
    assert (ARO5 : aro_client RNG m5) by (eapply aro_client_transport_F; [exact ARO| exact MU5| exact WM5| exact AW5| exact FAB]).
    assert (AZS5 : azstk RNG m5 lo SPV).
    { eapply azstk_transport_F; [exact AZS| exact MU5| exact WM5| exact AW5| exact FAB| clear; unfold al_fake; Z.div_mod_to_equations; lia
                               | destruct LY5 as (_ & _ & FA1 & FA2); unfold FAKESZ; clear - FA2 G1; lia| clear - G2 G3; lia]. }
    pose proof (db_ahull_wmono _ _ _ _ _ AHD WM5) as AHD5.
    assert (HINV5 : HUFINVw m5 DCTX huv lev).
    { eapply (db_hufinv_fcall (FB0 FF :: LB) m4 m4 m5 W5); [exact AH| apply INCONS; exact D4| apply DDJ; clear; lia| exact MU5| exact FFR5w| exact HINV4]. }
    (* [comment removed for export] *)
    assert (FFR05 : ffr_pres WR LB m0 m5).
    { eapply ffr_pres_trans; [exact FFR|].
      eapply magree_mono; [exact FFR5|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
      - left. cbn [outside] in HO |- *. destruct HO as (O1 & O2 & O3 & O4 & _).
        pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH _ Hb) as HB. cbn [ab_addr ab_size] in HB.
        split; [exists c, A, k; split; [right; exact Hb| exact Ha]| clear - O1 O2 O3 O4 HB Ha; repeat split; first [lia | exact I]].
      - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (MU05 : munch (FOOT ++ fake_area L) m0 m5).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU5]. subst W5. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _). clear - X1 X2 X3 X4 X5 X6 X7 G3 F5 F6. repeat split; try lia; exact I. }
    assert (WM05 : wmono bsegs m0 m5) by exact (wmono_trans _ _ _ _ WM WM5).
    assert (DB5 : DBB llt' mlt' oft' huv lev fev wsv m5).
    { split; [exact PTRS5|]. split; [exact H15|]. split; [exact FP5|]. split; [exact H35|]. split; [exact H55|].
      split; [exact ESEQ5|]. split; [exact EHUF5|]. split; [exact EREP5|]. split; [exact EWK5|]. split; [exact EPAD5|]. split; [exact XB5|].
      split; [exact SB5|]. split; [exact BUF5|]. split; [exact ST5|]. split; [exact SAV5|]. split; [exact STG5|]. split; [exact MI5|].
      split; [exact AH5|]. split; [exact FFR05|]. split; [exact MU05|]. split; [exact WM05|].
      split; [exact UD5|]. split; [exact US5|]. split; [exact UB5|]. split; [exact ARO5|]. split; [exact AZS5|]. split; [exact AHD5|].
      split; [intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHS Hz) WM5)| intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHB Hz) WM5)]. }
    (* [comment removed for export] *)
    assert (RESD : zd_is_error r2 = true
                   \/ (r2 <= cbs - r /\ exists nbSeq, nbw' = Z_to_bv 64 nbSeq /\ 0 <= nbSeq <= 98047 /\
                       ((nbSeq = 0 /\ atbl_seq m5 DCTX llt' mlt' oft' fev)
                        \/ (nbSeq <> 0 /\ seqhdr_tab m5 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable llt' /\
                                          seqhdr_tab m5 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable oft' /\
                                          seqhdr_tab m5 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable mlt')))).
    { destruct RES2 as [ER|(RLE & nbSeq & ENB & NBR & CASES)]; [left; exact ER| right]. rewrite SQL in RLE. split; [exact RLE|].
      exists nbSeq. split; [exact ENB|]. split; [exact NBR|].
      destruct CASES as [(NZ0 & -> & -> & -> & MUq)|(NZ1 & T1 & T2 & T3)]; [left| right; split; [exact NZ1| split; [exact T1| split; [exact T2| exact T3]]]].
      split; [exact NZ0|]. eapply db_atbl_seq_fine; [exact TBS4| exact MUq| exact MI5|]. intros x Hx. cbn [outside]. clear - Hx D5 OFFD G2 G3. repeat split; first [lia | exact I]. }
    replace (SRC + (ip + r)) with (SRC + ip + r) by (clear; lia).
    eapply (PSH m5 llt' mlt' oft' huv lev fev wsv r r2 _ _ w0 nbw' MXD);
      [exact DB5| exact FRA5| exact XM5| exact NB5| exact XP5| exact XS5| exact KEEP| exact HINV5| exact KB| exact EMXD| exact RL| exact PLACED| exact RR2| exact RESD].
  Qed.

  (* [comment removed for export] *)
  Lemma p_lit : forall m2 p0 p1 p2 huv lev fev wsv r jA jB w0 nbw (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m2 ->
    rw_cells bsegs m2 SPA [CB 40 jA; C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m2 FF [C8 w0] -> rw_cells bsegs m2 (FF + 32) [C4 nbw] -> rw_cells bsegs m2 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m2 SHF BSH0 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    atbl_seq m2 DCTX p0 p1 p2 fev -> cbs <= fh_bsmax h -> 0 <= r < 2^64 ->
    (zd_is_error r = true \/ (1 <= r <= cbs /\ HUFINVw m2 DCTX huv lev /\ declit_placed DCTX DST CAP (SRC + ip) cbs wsv)) ->
    evtF bsegs RNG POST (ST 0x894f8 m2 xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 (Z.shiftr (DCTX + 30176) 3 + SHB)) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + ip)) xs9 (Z_to_bv 64 (DCTX + 30176)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XN XP XS KEEP TBS KB RR RES. db_open CTX. pose proof I as DBI. open_dbb I.
    unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    pose proof (db_h5_isf_cell _ _ _ H5) as ISFC. rewrite (KEEP H5_isFrameDecompression eq_refl), ISF in ISFC.
    assert (CAPH : 0 <= CAP < 2^47) by (clear - DNN DNULL B0D DCB B1H CAP0; destruct (Z.eq_dec DST 0); lia).
    fk_hold DBI. fk_hold TBS. fk_hold PSH. fk_hold SEQHDR. fk_hold KEEP. fk_hold RES. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    unfold fk_held in FP.
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_cases KE; zify_cond KE.                          (* [comment removed for export] *)
    { unfold fk_held in *.
      destruct (rw_cells_forget bsegs _ _ _ FRA) as [jA' FRA']. cbn [cells_size csize Nat.add length] in FRA'.
      destruct (rw_cells_forget bsegs _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add BSH0 length] in XS'.
      eapply (p_ret m2 p0 p1 p2 huv lev fev wsv r jA' w0 shb);
        [exact DBI| exact FRA'| exact XM| exact XP| exact XS'| exact RR| exact KEEP| | left; apply (proj2 (zd_is_error_true_iff r)); clear - KE; lia].
      intros NE. exfalso. apply (proj2 (zd_is_error_true_iff r)) in KE. rewrite KE in NE. discriminate NE. }
    unfold fk_held in RES. destruct RES as [ER | (RL & HINV & PLACED)]; [exfalso; apply (proj1 (zd_is_error_true_iff r)) in ER; clear - ER KE; lia|].
    fk_hold HINV. fk_hold PLACED.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (db_sh_rd0s m2 DCTX 95992 (DCTX + 30176) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz.
    pose proof (db_sh_rng1 RNG DCTX (DCTX + 30176) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz.
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
    zstep; if_false.                                           (* [comment removed for export] *)
    zstep. try rewrite (sx32w_small 1) by (clear; lia).        (* [comment removed for export] *)
    zstep. zstep; if_cases KI; zify_cond KI; [exfalso; clear - KI; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    db_chk m2 (DCTX + 29944) UD RD2 DG.                        (* [comment removed for export] *)
    zstep. rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia).   (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_cases KM; zify_cond KM;                          (* [comment removed for export] *)
      [| pose proof (db_sh_rd0s m2 DCTX 95992 (DCTX + 29944) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
         pose proof (db_sh_rng1 RNG DCTX (DCTX + 29944) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz;
         zstep; clear RDz RTz; try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity;
         zstep; if_false; zstep; rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia); zstep ].
    all: try replace (r + (SRC + ip)) with (SRC + ip + r) by (clear; lia).
    all: unfold fk_held in *; eapply (p_mx m2 p0 p1 p2 huv lev fev wsv r jA jB w0 nbw);
      [exact DBI| exact FRA| exact XM| exact XN| exact XP| exact XS| exact KEEP| exact TBS| exact KB| exact RL| exact HINV| exact PLACED| clear - KM; lia].
  Qed.
End DB.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
