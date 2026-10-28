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
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a.
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

(* [comment removed for export] *)
Lemma db_h5_isf_cell : forall (m1 : amem) D wsq, dctx_h5 bsegs m1 D wsq -> rw_cells bsegs m1 (D + 30176) [C4 (wnth wsq H5_isFrameDecompression)].
Proof.
  intros m1 D wsq (C & L). h5_open wsq L.
  lazymatch type of C with rw_cells _ _ _ ?cs =>
    change cs with (firstn 12 cs ++ [nth 12 cs (C1 (Z_to_bv 8 0))] ++ skipn 13 cs) in C end.
  cbn [firstn skipn nth] in C.
  apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
  cbn [cells_size csize Nat.add] in C. replace (D + 30096 + Z.of_nat 80) with (D + 30176) in C by lia. exact C.
Qed.

(* [comment removed for export] *)
Lemma db_src_mid : forall (m1 : amem) SRC (src : list Z) i n, bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  0 <= i -> 0 <= n -> i + n <= zlen src ->
  let sq := firstn (Z.to_nat n) (skipn (Z.to_nat i) src) in
  bytes_at bsegs m1 (SRC + i) (map (Z_to_bv 8) sq) /\ zlen sq = n /\ Forall (fun c => 0 <= c < 256) sq.
Proof.
  intros m1 SRC src i n SB FBY Hi Hn HL sq.
  pose proof (zd_src_skipn bsegs m1 SRC src i SB ltac:(lia)) as B.
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) src)) in B. rewrite map_app in B.
  apply bytes_at_app in B. destruct B as [B _]. subst sq.
  split; [exact B|]. split; [rewrite firstn_length, skipn_length; lia|].
  pose proof FBY as FB. rewrite <- (firstn_skipn (Z.to_nat i) src) in FB. apply Forall_app in FB. destruct FB as [_ FB].
  rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) src)) in FB. apply Forall_app in FB. exact (proj1 FB).
Qed.

(* [comment removed for export] *)
Lemma db_sh_rd0s : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n -> 0 <= X -> X + n <= 2^47 ->
  ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr p 3 + SHB)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m X n p U H1 H2 H3 H4.
  pose proof (unp_shadow_zero m X n p U H1 H2) as B.
  assert (C : rw_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)]).
  { apply rw_cells_C1_of_byte; [| | exact B]; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia. }
  pose proof (rw_cells_read bsegs m (shad p) [C1 (Z_to_bv 8 0)] 0 (C1 (Z_to_bv 8 0)) C eq_refl) as RD.
  rewrite Z.add_0_r in RD. unfold shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.
(* [comment removed for export] *)
Lemma db_sh_rng1 : forall RNG DCTX p, rng RNG (shad DCTX) (shspan DCTX 95992) -> DCTX mod 8 = 0 -> DCTX <= p -> p + 8 <= DCTX + 95992 ->
  rng RNG (Z.shiftr p 3 + SHB) 1.
Proof.
  intros RNG DCTX p R A H1 H2. eapply rng_sub'; [exact R|]. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  unfold shspan. rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma db_seq_tbl_at_fine : forall (m m' : amem) W DCTX k own dflt d T t,
  seq_tbl_at bsegs m k T t -> tbl_ptr DCTX own dflt d T t -> seq_tbl_at bsegs m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
  seq_tbl_at bsegs m' k T t.
Proof.
  intros m m' W DCTX k own dflt d T t (BA & OK) [-> | [-> ->]] DF MU OUT O1 O2.
  - split; [|exact OK]. pose proof (seq_tbl_len_le k t OK) as L.
    eapply (bytes_at_munch_in bsegs m m' W _ _ (DCTX + 32) (DCTX + 10296)); [exact BA | exact MU | exact OUT | lia | lia].
  - exact DF.
Qed.
Lemma db_seqhdr_tab_fine : forall (m m' : amem) W DCTX k own dflt d pv,
  seqhdr_tab m DCTX k own dflt d pv -> seq_tbl_at bsegs m' k dflt d ->
  munch W m m' -> (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) ->
  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 ->
  seqhdr_tab m' DCTX k own dflt d pv.
Proof.
  intros m m' W DCTX k own dflt d pv (T & t & E & TP & TA) DF MU OUT O1 O2. exists T, t. split; [exact E|]. split; [exact TP|].
  eapply db_seq_tbl_at_fine; eassumption.
Qed.
Lemma db_atbl_seq_fine : forall (m m' : amem) W DCTX llt mlt oft fe,
  atbl_seq m DCTX llt mlt oft fe -> munch W m m' -> mem_inv bsegs m' ->
  (forall x, DCTX + 32 <= x < DCTX + 10296 -> outside W x) -> atbl_seq m' DCTX llt mlt oft fe.
Proof.
  intros m m' W DCTX llt mlt oft fe T MU MI' OUT NZ.
  destruct (T NZ) as (LLT & MLT & OFT & tLL & tOF & tML & E1 & E2 & E3 & P1 & P2 & P3 & A1 & A2 & A3).
  exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [assumption|]).
  split; [|split].
  - eapply db_seq_tbl_at_fine; [exact A1 | exact P1 | split; [apply all_default_at; exact MI' | apply LL_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; lia.
  - eapply db_seq_tbl_at_fine; [exact A2 | exact P2 | split; [apply aof_default_at; exact MI' | apply OF_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; lia.
  - eapply db_seq_tbl_at_fine; [exact A3 | exact P3 | split; [apply aml_default_at; exact MI' | apply ML_default_ok] | exact MU | exact OUT | | ];
      unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; lia.
Qed.

Lemma db_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & A1 & A2 & A3 & A4 & A5 & A6 & W & R) H1 H2. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.
Lemma db_inblk_sub : forall LB' X n X' n', ainblk LB' X n -> X <= X' -> X' + n' <= X + n -> ainblk LB' X' n'.
Proof. intros LB' X n X' n' (bb & Hb & H1 & H2) A B. exists bb. split; [exact Hb| clear - H1 H2 A B; lia]. Qed.

Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

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
  Lemma db_atbl_seq_fcall : forall LB' (mq m m' : amem) W llt mlt oft fe,
    AHEAP AI L RNG st LB' mq -> ainblk LB' DCTX 95992 -> disjoint_from W (DCTX + 32) 10264 ->
    munch (W ++ fake_area L) m m' -> ffr_pres W LB' m m' -> mem_inv bsegs m' ->
    atbl_seq m DCTX llt mlt oft fe -> atbl_seq m' DCTX llt mlt oft fe.
  Proof.
    intros LB' mq m m' W llt mlt oft fe AHq IB DJ MUq FFRq MIq TS NZ.
    destruct (TS NZ) as (LLT & MLT & OFT & tLL & tOF & tML & E1 & E2 & E3 & P1 & P2 & P3 & A1 & A2 & A3).
    exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [assumption|]).
    assert (OWN : forall k T t own dflt d, seq_tbl_at bsegs m k T t -> tbl_ptr DCTX own dflt d T t -> seq_tbl_at bsegs m' k dflt d ->
                  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 -> seq_tbl_at bsegs m' k T t).
    { intros k T t own dflt d (BA & OK) [-> | [-> ->]] DF O1 O2; [| exact DF]. split; [| exact OK]. pose proof (seq_tbl_len_le k t OK) as LEN.
      eapply (fcall_bytes_pres AI FHL); [exact AHq| | | exact MUq| exact FFRq| exact BA].
      - destruct IB as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hb1 Hb2 O1 O2 LEN; lia].
      - eapply disjoint_from_sub1; [exact DJ| clear - O1; lia| clear - O2 LEN; lia]. }
    split; [| split].
    - eapply (OWN K_LL); [exact A1| exact P1| split; [apply all_default_at; exact MIq| apply LL_default_ok]| unfold DCTX_entropy_LLTable; clear; lia| unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; clear; lia].
    - eapply (OWN K_OF); [exact A2| exact P2| split; [apply aof_default_at; exact MIq| apply OF_default_ok]| unfold DCTX_entropy_OFTable; clear; lia| unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; clear; lia].
    - eapply (OWN K_ML); [exact A3| exact P3| split; [apply aml_default_at; exact MIq| apply ML_default_ok]| unfold DCTX_entropy_MLTable; clear; lia| unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia].
  Qed.

  Hypothesis DECLIT : zd_declit_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Hypothesis PDL : forall m2 p0 p1 p2 huv lev fev wsv r jA jB w0 nbw (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m2 ->
    rw_cells bsegs m2 SPA [CB 40 jA; C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m2 FF [C8 w0] -> rw_cells bsegs m2 (FF + 32) [C4 nbw] -> rw_cells bsegs m2 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m2 SHF BSH0 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    atbl_seq m2 DCTX p0 p1 p2 fev -> cbs <= fh_bsmax h -> 0 <= r < 2^64 ->
    (zd_is_error r = true \/ (1 <= r <= cbs /\ HUFINVw m2 DCTX huv lev /\ declit_placed DCTX DST CAP (SRC + ip) cbs wsv)) ->
    evtF bsegs RNG POST (ST 0x894f8 m2 xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                           (Z_to_bv 64 (Z.shiftr (DCTX + 30176) 3 + SHB)) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + ip)) xs9 (Z_to_bv 64 (DCTX + 30176)) x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma p_top : forall m1 p0 p1 p2 huv lev fev jA jB w0 nbw xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa7 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev ws m1 ->
    rw_cells bsegs m1 SPA [CB 48 jA; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 32) [C4 nbw] -> rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 SHF BSH0 ->
    TBLA m1 DCTX p0 p1 p2 huv lev fev ->
    evtF bsegs RNG POST (ST 0x894a4 m1 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 (Z_to_bv 64 DCTX) xa7
                           (Z_to_bv 64 (Z.shiftr (DCTX + 30176) 3 + SHB)) (Z_to_bv 64 cbs) (Z_to_bv 64 (SRC + ip)) (Z_to_bv 64 0) (Z_to_bv 64 (DCTX + 30176)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XN XP XS TB. db_open CTX. pose proof I as DBI. open_dbb I.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    pose proof (db_h5_isf_cell _ _ _ H5) as ISFC. rewrite ISF in ISFC.
    pose proof TB as [TBS HINV]. unfold atbl_seq in TBS |- *.
    unfold KHIGH in KLO.
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    fk_hold DBI. fk_hold TB. fk_hold TBS. fk_hold HINV. fk_hold PDL. fk_hold DECLIT. fk_hold INCONS.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB.
    fk_hold DL. fk_hold FL. fk_hold LL. fk_hold FFSH. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF2. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT. fk_hold ESHF.
    zstep. try rewrite (sx32w_small 1) by (clear; lia).        (* [comment removed for export] *)
    zstep; if_cases KI; zify_cond KI; [exfalso; clear - KI; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    db_chk m1 (DCTX + 29944) UD RD2 DG.                        (* [comment removed for export] *)
    zstep. rewrite (zx32w_small (fh_bsmax h)) by (clear - BSM; lia).   (* [comment removed for export] *)
    zstep; if_cases KB; zify_cond KB.                          (* [comment removed for export] *)
    2:{ (* [comment removed for export] *)
        zstep. zstep. replace (Z_to_bv 64 (-72)) with (Z_to_bv 64 (2^64 - 72)) by (apply Z_to_bv_eqm; reflexivity).
        unfold fk_held in *.
        destruct (rw_cells_forget bsegs _ _ _ FRA) as [jA' FRA']. cbn [cells_size csize Nat.add] in FRA'.
        destruct (rw_cells_forget bsegs _ _ _ XS) as [shb XS']. cbn [cells_size csize Nat.add BSH0 length] in XS'.
        eapply (p_ret m1 p0 p1 p2 huv lev fev ws (2^64 - 72) jA' w0 shb);
          [exact DBI| exact FRA'| exact XM| exact XP| exact XS'| clear; lia| intros i _; reflexivity| intros NE; exact TB| left; reflexivity]. }
    clear ISFC. fk_hold PTRS. fk_hold FP. fk_hold UD. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPA + 40, SPA + 48)] m1) as MU12. pose proof (wmono_refl bsegs m1) as WM12.
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    rename m into m2.
    (* [comment removed for export] *)
    unfold fk_held in H5, DBI, HINV, TBS.
    assert (DJ12 : forall X k, (X + k <= lo \/ SPV <= X) -> 0 <= k -> disjoint_from [(SPA + 40, SPA + 48)] X k)
      by (intros X k A B; cbn [disjoint_from]; clear - A B G2 G3; split; [lia| exact I]).
    assert (H52 : dctx_h5 bsegs m2 DCTX ws).
    { destruct H5 as [H5C WL']. split; [| exact WL']. eapply rw_cells_transport; [exact H5C| exact MU12| exact WM12| rewrite (h5_cells_size _ WL'); apply DJ12; [| clear; lia]].
      unfold fk_held in OFFD. clear - OFFD. lia. }
    assert (DB2 : DBB p0 p1 p2 huv lev fev ws m2).
    { eapply (dbb_keep p0 p1 p2 huv lev fev ws ws m1 m2); [exact DBI| exact MU12| exact WM12| exact MI| exact H52|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| left; clear; lia]| apply Forall_nil]. }
    assert (HINV2 : HUFINVw m2 DCTX huv lev).
    { eapply hufw_fine; [exact HINV| exact MU12|]. intros x Hx. cbn [outside]. unfold fk_held in OFFD. clear - Hx OFFD G2 G3 DL. split; [lia| exact I]. }
    assert (TBS2 : atbl_seq m2 DCTX p0 p1 p2 fev).
    { eapply db_atbl_seq_fine; [exact TBS| exact MU12| exact MI|]. intros x Hx. cbn [outside]. unfold fk_held in OFFD. clear - Hx OFFD G2 G3 DL. split; [lia| exact I]. }
    unfold fk_held in XM, XN, XP, XS.
    assert (XM2 : rw_cells bsegs m2 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU12| exact WM12| csz; cbn [disjoint_from]; clear - F3 G1 G2; split; [lia| exact I]]).
    assert (XN2 : rw_cells bsegs m2 (FF + 32) [C4 nbw]) by (eapply rw_cells_transport; [exact XN| exact MU12| exact WM12| csz; cbn [disjoint_from]; clear - F3 G1 G2; split; [lia| exact I]]).
    assert (XP2 : rw_cells bsegs m2 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU12| exact WM12| csz; cbn [disjoint_from]; clear - F3 G1 G2; split; [lia| exact I]]).
    assert (XS2 : rw_cells bsegs m2 SHF BSH0) by (eapply rw_cells_transport; [exact XS| exact MU12| exact WM12| csz; cbn [disjoint_from]; clear - GS KLO G2; split; [lia| exact I]]).
    clear DBI H5 H52 HINV TBS PTRS FP UD H1 H3 ESEQ EHUF EREP EWK EPAD XB SRCB BUF STL SAV STG AH FFR MU WM US UB ARO AZS AHD AHS AHB MI XM XN XP XS.
    pose proof DB2 as DBI. open_dbb DB2.
    gf_unhold.
    (* [comment removed for export] *)
    destruct (db_src_mid m2 SRC src ip cbs SRCB FBY IP0 ltac:(clear - CBSR; lia) IPC) as (BLK & BLKL & BLKF).
    set (blk := firstn (Z.to_nat cbs) (skipn (Z.to_nat ip) src)) in *.
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    assert (ASH' : ashort (FB0 FF :: LB) 4) by (eapply ashort_mono; [eapply (ashort_push _ _ 5); [exact ASH| clear; lia]| clear; lia]).
    assert (ART2 : art m2).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C]. }
    assert (AFP2 : afpre AI rng_fs L RNG st (FB0 FF :: LB) m2 lo SPA 4).
    { unfold afpre, astk. split; [exact AH|]. split; [exact ASH'|]. split; [exact ART2|].
      split; [split; [unfold KHIGH; exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]|].
      split; [exact RFS|]. split; [exact G1|]. split; [clear - G3 SPT; lia|]. split; [clear - G4; Z.div_mod_to_equations; lia|]. split; [exact RSTKT| exact LBH']. }
    assert (ARS2 : areg RNG m2 SRC (zlen src)) by (intros NZ; split; [exact (S1 NZ)| split; [exact (US NZ)| exact (R_src NZ)]]).
    clear ART2 ASH' MU12 WM12 DJ12.
    idtac "B2".
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    unfold zd_declit_stmtA, APZD_DECLIT in DECLIT.
    eapply evtF_cut.
    { eapply (DECLIT L RNG st (FB0 FF :: LB)) with (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1) (LSRC := SRC + ip) (src := blk)
                                              (h := h) (ws := ws) (SPV := SPA) (llt := p0) (mlt := p1) (oft := p2) (huf := huv) (le := lev) (fe := fev)
                                              (pcs := pcs) (dsz := dsz) (bt := bt) (stg := stg);
      lazymatch goal with
      | |- dctx_ptrs _ _ _ _ _ _ _ => exact PTRS
      | |- stk _ _ (DCTX + 10296) _ => exact EHUF
      | |- HUFINVw _ _ _ _ => exact HINV2
      | |- stk _ _ (DCTX + 27324) _ => exact EWK
      | |- rw_cells _ _ (DCTX + 29928) _ => exact FP
      | |- 0 <= fh_bsmax h <= _ => exact BSM
      | |- dctx_h3 _ _ _ _ _ _ _ _ _ => exact H3
      | |- dctx_h5 _ _ _ _ => exact H5
      | |- wnth _ _ = _ => exact ISF
      | |- stk _ _ (DCTX + 30372) _ => exact XB
      | |- 4096 <= DCTX => exact DCL
      | |- DCTX + 95992 < _ => exact DCH
      | |- DCTX mod 8 = 0 => exact DCA
      | |- bytes_at _ _ _ _ => exact BLK
      | |- Forall _ _ => exact BLKF
      | |- zlen blk <= _ => rewrite BLKL; clear - KB BSM; lia
      | |- 4096 <= SRC + ip => clear - SRCL IP0; lia
      | |- SRC + ip + zlen blk < _ => rewrite BLKL; clear - SRCH IPC IP0 CBSR; lia
      | |- stk _ _ B0 B1 => exact BUF
      | |- B0 <= DST => exact B0D
      | |- DST + CAP <= B1 => exact DCB
      | |- 0 <= CAP => exact CAP0
      | |- B1 < _ => exact B1H
      | |- DST = 0 -> _ => exact DNULL
      | |- DST <> 0 -> _ => exact DNN
      | |- stk _ _ lo SPA => exact STL
      | |- 4096 <= lo => exact LO0
      | |- lo <= SPA - _ => exact G2
      | |- SPA < _ => clear - G3 SPH; lia
      | |- DCTX + 95992 <= lo \/ SPA <= DCTX => clear - OFFD G3; lia
      | |- B1 <= lo \/ SPA <= B0 => clear - OFFB G3; lia
      | |- SRC + ip + zlen blk <= lo \/ SPA <= SRC + ip => rewrite BLKL; clear - OFFSRC G3 IPC IP0 CBSR; lia
      | |- B1 <= DCTX \/ _ => exact BD
      | |- B1 <= SRC + ip \/ _ => rewrite BLKL; clear - BSRC IPC IP0 CBSR; lia
      | |- SRC + ip + zlen blk <= DCTX \/ _ => rewrite BLKL; clear - SRCD IPC IP0 CBSR; lia
      | |- afpre _ _ _ _ _ _ _ _ _ _ => exact AFP2
      | |- tp = _ => exact TP
      | |- azstk _ _ _ _ => eapply azstk_sub; [exact AZS| clear; lia| clear - G2; lia| clear - G3; lia]
      | |- aro_client _ _ => exact ARO
      | |- areg _ _ DCTX _ => intros _; split; [exact D1| split; [exact UD| split; [exact RD1| exact RD2]]]
      | |- ahull _ _ DCTX _ => exact AHD
      | |- ainblk _ DCTX _ => apply INCONS; exact D4
      | |- areg _ _ (SRC + ip) _ => rewrite BLKL; eapply areg_sub; [exact ARS2| clear - IP0; lia| clear - CBSR; lia| clear - IPC; lia]
      | |- 0 < _ -> ahull _ _ (SRC + ip) _ => rewrite BLKL; intros NZ'; eapply db_ahull_sub; [exact (AHS ltac:(clear - NZ' IPC IP0; lia))| clear - IP0; lia| clear - IPC; lia]
      | |- 0 < _ -> ainimg _ (SRC + ip) _ => rewrite BLKL; intros NZ'; left; apply INCONS; eapply db_inblk_sub; [exact (S4 ltac:(clear - NZ' IPC IP0; lia))| clear - IP0; lia| clear - IPC; lia]
      | |- B0 < B1 -> _ => intros HB; pose proof (OUTB HB) as (OB1 & OB2 & OB3); split; [intros _; split; [replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact OB1| split; [replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact (UB HB)| exact (R_out HB)]]| split; [exact (AHB HB)| apply INCONS; exact OB2]]
      | |- mem_inv _ _ => exact MI
      | |- _ = _ => first [reflexivity | rewrite BLKL; reflexivity]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m3 & r & huf' & le' & ws'
                    & -> & MU3 & WM3 & MI3 & ST3 & FFR3 & AH3 & BUF3 & PTRS3 & EHUF3 & EWK3 & H33 & H53 & KEEP3 & XB3 & RR & RES).
    rd_retlit.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (IVD := if 0 <? CAP then (DST, DST + CAP) else (DCTX + 24, DCTX + 24)).
    assert (IVDP : (0 < CAP /\ IVD = (DST, DST + CAP) /\ B0 < B1) \/ (CAP = 0 /\ IVD = (DCTX + 24, DCTX + 24))).
    { subst IVD. destruct (Z.ltb_spec 0 CAP) as [Hc|Hc]; [left; split; [exact Hc| split; [reflexivity| clear - Hc B0D DCB; lia]]| right; split; [clear - Hc CAP0; lia| reflexivity]]. }
    clearbody IVD.
    set (W7 := [IVD; (DCTX + 24, DCTX + 32); (DCTX + 10296, DCTX + 26684); (DCTX + 27324, DCTX + 29884); (DCTX + 30000, DCTX + 30004); (DCTX + 30096, DCTX + 95940); (SPA - 6096, SPA)]).
    assert (MU3' : munch (W7 ++ fake_area L) m2 m3).
    { eapply munch_weaken; [| exact MU3]. subst W7. unfold sub_fp; cbn [outside app]. intros x Hx.
      destruct IVDP as [(Hc & -> & _)|(Hc & ->)]; cbn [fst snd] in Hx; destruct Hx as [Hx1 Hx]; (split; [clear - Hx1 Hc; lia| exact Hx]). }
    assert (FFR3' : ffr_pres W7 (FB0 FF :: LB) m2 m3).
    { eapply db_ffr_pres_weaken; [exact FFR3|]. subst W7. unfold sub_fp; cbn [outside]; intros x Hx.
      destruct IVDP as [(Hc & -> & _)|(Hc & ->)]; cbn [fst snd] in Hx; destruct Hx as [Hx1 Hx]; cbn; (split; [clear - Hx1 Hc; lia| clear - Hx; tauto]). }
    clear MU3. rename MU3' into MU3.
    assert (AW7 : aappW W7).
    { subst W7. unfold aappW, KLOW, KHIGH. pose proof (ablk_disj_band _ _ D1) as DBD. unfold KLS in DBD.
      apply Forall_cons; [destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [fst snd];
        [pose proof (OUTB HB) as (OB1 & _); pose proof (ablk_disj_band _ _ OB1) as OBD; pose proof (fk_ablk_lits _ _ OB1) as OBL; unfold KLS in OBD; clear - OBD OBL B0D DCB CAP0; lia
        | clear - DBD DL; lia]|].
      repeat (apply Forall_cons; [cbn [fst snd]; clear - DBD DL KLO G2 G3; lia|]). apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W7 ++ fake_area L) X k).
    { intros X k A1 A2 Hk. subst W7. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from app fake_area]; rewrite !shad_div; unfold FAKESZ, ASHOFF in *;
        (split; [first [clear - A1 A2 Hk OFFB B0D DCB G2 G3 HB; lia| clear - A1 A2 Hk OFFD G2 G3; lia]|]);
        clear - A1 A2 Hk FABL OFFD G1 G2 G3 ATR KLO; repeat split; Z.div_mod_to_equations; lia. }
    assert (DJF : forall X k, FF <= X -> X + k <= FF + 64 -> 0 <= k -> disjoint_from W7 X k).
    { intros X k A1 A2 Hk. subst W7. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
        (split; [first [pose proof (OUTB HB) as (_ & _ & OB3); clear - OB3 A1 A2 Hk B0D DCB; lia| clear - A1 A2 Hk D5; lia]|]);
        clear - A1 A2 Hk D5 F3 G1 G2; repeat split; lia. }
    assert (PFF : forall X k a, FF <= X -> X + k <= FF + 64 -> 0 <= k -> X <= a < X + k ->
              (in_fake (FB0 FF :: LB) a /\ outside W7 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros X k a A1 A2 Hk Ha. left. split; [exists 0, FF, 64; split; [left; reflexivity| clear - A1 A2 Ha; lia]|].
      eapply disjoint_outside; [exact (DJF X k A1 A2 Hk)| exact Ha]. }
    assert (PSF : forall a, SHF <= a < SHF + 8 -> (in_fake (FB0 FF :: LB) a /\ outside W7 a) \/ (exists a', in_fake (FB0 FF :: LB) a' /\ a = shad a')).
    { intros a Ha. right. exists (8 * (a - SHB)). rewrite ESHF in Ha.
      split; [exists 0, FF, 64; split; [left; reflexivity| clear - Ha F2; Z.div_mod_to_equations; lia]|].
      rewrite shad_div. unfold ASHOFF. clear - Ha. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ SAV MU3 WM3 ltac:(apply DSTK; [clear - G3; lia| csz; clear; lia| clear; lia])) as SAV3.
    pose proof (rw_cells_transport _ _ _ _ _ _ FRA MU3 WM3 ltac:(apply DSTK; [clear; lia| csz; clear - G3; lia| clear; lia])) as FRA3.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ STG MU3 WM3 ltac:(apply DSTK; clear - G3; lia)) as STG3.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR3' XM2 ltac:(csz; intros a Ha; apply (PFF FF 8 a); clear - Ha; lia)) as XM3.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR3' XN2 ltac:(csz; intros a Ha; apply (PFF (FF + 32) 4 a); clear - Ha; lia)) as XN3.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR3' XP2 ltac:(csz; intros a Ha; apply (PFF (FF + 56) 8 a); clear - Ha; lia)) as XP3.
    pose proof (rw_cells_magree _ _ _ _ _ _ FFR3' XS2 ltac:(csz; intros a Ha; apply PSF; clear - Ha; lia)) as XS3.
    assert (DIN : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> ainblk (FB0 FF :: LB) X k)
      by (intros X k A1 A2; destruct D4 as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| clear - A1 A2 Hb1 Hb2; lia]).
    assert (DDJ : forall X k, DCTX + 32 <= X -> X + k <= DCTX + 10296 \/ (DCTX + 26684 <= X /\ X + k <= DCTX + 27324) \/ (DCTX + 29884 <= X /\ X + k <= DCTX + 30000) -> 0 <= k ->
                  disjoint_from W7 X k).
    { intros X k A1 A2 Hk. subst W7. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
        (split; [first [clear - BD A1 A2 Hk B0D DCB HB; lia| clear - A1 Hk; lia]|]);
        clear - A1 A2 Hk OFFD G2 G3; repeat split; lia. }
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU3 WM3 FFR3' H1) as H13.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29928) (zfh_cells h) AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU3 WM3 FFR3' FP) as FP3.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 32) (DCTX + 10296) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU3 WM3 FFR3' ESEQ) as ESEQ3.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 26684) (DCTX + 27324) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU3 WM3 FFR3' EREP) as EREP3.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29884) (DCTX + 29888) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU3 WM3 FFR3' EPAD) as EPAD3.
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src)).
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [Hz|Hz].
      - pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
        eapply (fcall_bytes_pres AI FHL); [exact AH| rewrite length_map; apply INCONS; exact (S4 Hz)| | exact MU3| exact FFR3'| exact SRCB].
        rewrite length_map. subst W7. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
          (split; [first [clear - BSRC Hz B0D DCB HB; lia| clear - SRCD Hz; lia]|]);
          clear - Hz SRCD OFFSRC G2 G3; repeat split; lia.
      - destruct SRCB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)).
    { eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact D4| clear; lia| unfold KEND; clear - DL ATR; lia| exact AW7| exact MU3| exact FFR3'| exact UD]. }
    assert (US3 : 0 < zlen src -> unpoisoned m3 SRC (SRC + zlen src)).
    { intros Hz. pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact (S4 Hz)| exact Hz| unfold KEND; clear - SL ATR; lia| exact AW7| exact MU3| exact FFR3'| exact (US Hz)]. }
    assert (UB3 : B0 < B1 -> unpoisoned m3 B0 B1).
    { intros Hz. pose proof (OUTB Hz) as (OB1 & OB2 & _). pose proof (fk_ablk_lits _ _ OB1) as BL. replace B1 with (B0 + (B1 - B0)) by (clear; lia).
      eapply (fcall_unp_pres AI FHL); [exact AH| apply INCONS; exact OB2| clear - Hz; lia| unfold KEND; clear - BL ATR; lia| exact AW7| exact MU3| exact FFR3'|].
      replace (B0 + (B1 - B0)) with B1 by (clear; lia). exact (UB Hz). }
    assert (ARO3 : aro_client RNG m3) by (eapply aro_client_transport_F; [exact ARO| exact MU3| exact WM3| exact AW7| exact FAB]).
    assert (AZS3 : azstk RNG m3 lo SPV).
    { eapply azstk_transport_F; [exact AZS| exact MU3| exact WM3| exact AW7| exact FAB| clear; unfold al_fake; Z.div_mod_to_equations; lia
                               | destruct LY5 as (_ & _ & FA1 & FA2); unfold FAKESZ; clear - FA2 G1; lia| clear - G2 G3; lia]. }
    pose proof (db_ahull_wmono _ _ _ _ _ AHD WM3) as AHD3.
    assert (TBS3 : atbl_seq m3 DCTX p0 p1 p2 fev).
    { eapply (db_atbl_seq_fcall (FB0 FF :: LB) m2 m2 m3 W7); [exact AH| apply INCONS; exact D4| apply DDJ; clear; lia| exact MU3| exact FFR3'| exact MI3| exact TBS2]. }
    (* [comment removed for export] *)
    assert (FFR03 : ffr_pres WR LB m0 m3).
    { eapply ffr_pres_trans; [exact FFR|].
      eapply magree_mono; [exact FFR3|]. intros a [[(c & A & k & Hb & Ha) HO]|(a' & (c & A & k & Hb & Ha) & ->)].
      - left. cbn [outside] in HO |- *. destruct HO as (O1 & O2 & O3 & O4 & _).
        split; [exists c, A, k; split; [right; exact Hb| exact Ha]| clear - O1 O2 O3 O4; repeat split; lia].
      - right. exists a'. split; [exists c, A, k; split; [right; exact Hb| exact Ha]| reflexivity]. }
    assert (MU03 : munch (FOOT ++ fake_area L) m0 m3).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU3]. subst W7. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [fst snd]; destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6);
        (split; [first [exact X1| clear - X2; lia]|]); clear - X2 X3 X4 X5 X6 G3; repeat split; try lia; tauto. }
    assert (WM03 : wmono bsegs m0 m3) by exact (wmono_trans _ _ _ _ WM WM3).
    assert (DB3 : DBB p0 p1 p2 huf' le' fev ws' m3).
    { split; [exact PTRS3|]. split; [exact H13|]. split; [exact FP3|]. split; [exact H33|]. split; [exact H53|].
      split; [exact ESEQ3|]. split; [exact EHUF3|]. split; [exact EREP3|]. split; [exact EWK3|]. split; [exact EPAD3|]. split; [exact XB3|].
      split; [exact SB3|]. split; [exact BUF3|]. split; [exact ST3|]. split; [exact SAV3|]. split; [exact STG3|]. split; [exact MI3|].
      split; [exact AH3|]. split; [exact FFR03|]. split; [exact MU03|]. split; [exact WM03|].
      split; [exact UD3|]. split; [exact US3|]. split; [exact UB3|]. split; [exact ARO3|]. split; [exact AZS3|]. split; [exact AHD3|].
      split; [intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHS Hz) WM3)| intros Hz; exact (db_ahull_wmono _ _ _ _ _ (AHB Hz) WM3)]. }
    rewrite BLKL in RES.
    eapply (PDL m3 p0 p1 p2 huf' le' fev ws' r _ _ w0 nbw);
      [exact DB3| exact FRA3| exact XM3| exact XN3| exact XP3| exact XS3| exact KEEP3| exact TBS3| exact KB| exact RR| exact RES].
  Qed.
End DB.
End CANSEC1.
