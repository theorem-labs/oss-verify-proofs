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
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a AZ_dblock_b AZ_dblock_c AZ_dblock_d AZ_dblock_e.
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

Lemma db_le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with 4294967296 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma db_cb12_as_c4s : forall (m1 : amem) A jj, rw_cells bsegs m1 A [CB 12 jj] -> exists a b c, rw_cells bsegs m1 A [C4 a; C4 b; C4 c].
Proof.
  intros m1 A jj H. pose proof H as [[WF _] _]. cbn in WF. destruct WF as [WFJ _].
  exists (le_bytes_to_word (firstn 4 jj)), (le_bytes_to_word (firstn 4 (skipn 4 jj))), (le_bytes_to_word (skipn 8 jj)).
  eapply rw_cells_recell; [exact H | cbn; auto |].
  cbn [cells_bytes cbytes]. rewrite !app_nil_r.
  rewrite !db_le4_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia).
  rewrite <- (firstn_skipn 4 jj) at 4. f_equal.
  replace (skipn 8 jj) with (skipn 4 (skipn 4 jj)) by (rewrite skipn_skipn; reflexivity). apply firstn_skipn.
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
  Definition tab_readyA (m1 : amem) (k : seq_kind) (sz : Z) (pv : word) (T : Z) (t : seq_table) : Prop :=
    pv = Z_to_bv 64 T /\ seq_tbl_at bsegs m1 k T t /\ 4096 <= T < 2^47
    /\ AZ_seq_iface.off_stack lo SPA T sz /\ AZ_seq_iface.apart B0 (B1 - B0) T sz /\ AZ_seq_iface.apart T sz (DCTX + DCTX_entropy_rep) (DCTX_SIZEOF - DCTX_entropy_rep)
    /\ aro RNG m1 T (8 * (1 + 2 ^ st_log t)) /\ (ainblk (FB0 FF :: LB) T sz \/ T + sz <= AIMG_HI) /\ T mod 8 = 0.

  Lemma db_tab_ready : forall m1 k own dflt d pv sz,
    seqhdr_tab m1 DCTX k own dflt d pv -> sz = 8 * (1 + 2^(kind_maxLog k)) -> 32 <= own -> own + sz <= 10296 -> own mod 8 = 0 ->
    (dflt = APZD_LL_DEFAULT /\ d = LL_defaultDTable /\ k = K_LL) \/ (dflt = APZD_OF_DEFAULT /\ d = OF_defaultDTable /\ k = K_OF) \/ (dflt = APZD_ML_DEFAULT /\ d = ML_defaultDTable /\ k = K_ML) ->
    unpoisoned m1 DCTX (DCTX + 95992) -> aro_client RNG m1 -> B0 < B1 ->
    exists T t, tab_readyA m1 k sz pv T t.
  Proof.
    intros m1 k own dflt d pv sz (T & t & E & TPT & TA) ESZ O1 O2 O8 DFL UD ARO HBB. exists T, t. db_open CTX. unfold KHIGH in KLO.
    assert (KM : 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (P : 256 <= 2^(kind_maxLog k) <= 512) by (destruct k; cbn; lia).
    pose proof TA as [_ OK]. destruct (seq_tbl_len k t OK) as [LEN LR].
    assert (PL : 2 ^ st_log t <= 2 ^ kind_maxLog k) by (apply Z.pow_le_mono_r; clear - LR; lia).
    assert (PL0 : 1 <= 2 ^ st_log t) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; clear - LR; lia).
    unfold tab_readyA, AZ_seq_iface.off_stack, AZ_seq_iface.apart, DCTX_entropy_rep, DCTX_SIZEOF.
    split; [exact E|]. split; [exact TA|].
    destruct TPT as [-> | [-> ->]].
    - (* [comment removed for export] *)
      split; [clear - DCL DCH O1 O2 ESZ P; lia|]. split; [clear - OFFD G3 O1 O2 ESZ P; lia|]. split; [clear - BD O1 O2 ESZ P; lia|]. split; [clear - O1 O2 ESZ P; lia|].
      split; [split; [eapply unpoisoned_sub; [exact UD| clear - O1; lia| clear - O2 ESZ P PL; lia]
                    | split; [eapply rng_sub'; [exact RD1| clear - O1 O2 ESZ P PL PL0; lia]
                            | eapply rng_sub; [exact RD2| |]; pose proof (shspan_sub DCTX 95992 (DCTX + own) (8 * (1 + 2 ^ st_log t)) ltac:(clear - O1; lia) ltac:(clear - PL0; lia) ltac:(clear - O2 ESZ P PL; lia)) as [S1' S2']; [exact S1'| exact S2']]]|].
      split; [left; destruct D4 as (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| clear - Hb1 Hb2 O1 O2 ESZ P; lia]|]. clear - DCA O8; Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      destruct ARO as [AR _].
      destruct DFL as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; unfold APZD_LL_DEFAULT, APZD_OF_DEFAULT, APZD_ML_DEFAULT, AIMG_HI in *; subst sz; cbn [kind_maxLog Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in *;
        (split; [clear; lia|]); (split; [clear - KLO G2; lia|]); (split; [pose proof (fk_ablk_lits _ _ (proj1 (OUTB HBB))) as BL; clear - BL; lia|]);
        (split; [clear - DL; lia|]); (split; [apply AR; cbn [ACLIENT_RO In]; repeat (first [left; apply f_equal2; reflexivity | right])|]); (split; [right; clear; lia| reflexivity]).
  Qed.
  (* [comment removed for export] *)
  Lemma db_lit_default : forall (m1 : amem) LITP LITSZ LITB LBE LOC,
    stk bsegs m1 (DCTX + 30372) (DCTX + 95940) -> bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> stk bsegs m1 B0 B1 ->
    0 <= LITSZ <= 131072 -> LITP <= LBE ->
    (LOC = 0 /\ LBE = LITP + LITSZ /\ (LITP = DCTX + 30372 /\ LITSZ <= 65536 \/ SRC + ip <= LITP /\ LBE + 32 <= SRC + ip + cbs)
     \/ LOC = 1 /\ LBE = LITP + LITSZ /\ LITB = LITP /\ DST <= LITB /\ LBE + 32 <= DST + CAP
     \/ LOC = 2 /\ 65536 < LITSZ /\ LITB = LITP /\ DST <= LITP /\ LBE + 32 <= DST + CAP /\ LBE = LITP + LITSZ - 65536) ->
    LOC <> 2 ->
    (LOC = ZSTD_not_in_dst \/ LOC = ZSTD_in_dst) /\ 0 <= LITSZ < 2^32 /\ 4096 <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH < 2^47
    /\ rdbl bsegs m1 LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)
    /\ (LOC = ZSTD_in_dst -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LITP + LITSZ + WILDCOPY_OVERLENGTH <= B1)
    /\ (LOC = ZSTD_not_in_dst -> AZ_seq_iface.apart LITP (LITSZ + WILDCOPY_OVERLENGTH) B0 (B1 - B0))
    /\ AZ_seq_iface.off_stack lo SPA LITP (LITSZ + WILDCOPY_OVERLENGTH)
    /\ AZ_seq_iface.apart LITP (LITSZ + WILDCOPY_OVERLENGTH) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep).
  Proof.
    intros m1 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC NL2.
    db_open CTX. unfold KHIGH in KLO.
    clear G1 G4 G5 G6 D1 D4 D5 S1 S4 S5 OUTB F1 F2 F3 F4 F5 F6 L0 L1 L2 L3 L4 RSTK RI R_src RD1 RD2 R_out RF1 RF2 RF3 LBH ASH RFS SPT RSTKT TP ATR FL LL DL ESHF GS FFSH FLSH DCSH DNB WL44 ISF WND BSM FBY.
    unfold ZSTD_not_in_dst, ZSTD_in_dst, WILDCOPY_OVERLENGTH, AZ_seq_iface.off_stack, AZ_seq_iface.apart, DCTX_entropy_rep, DCTX_litExtraBuffer.
    pose proof (rdbl_of_stk bsegs _ _ _ XB) as RX. pose proof (rdbl_of_stk bsegs _ _ _ BUF) as RB.
    pose proof (rdbl_of_bytes_at bsegs _ _ _ SRCB) as RS. rewrite length_map in RS.
    destruct PLC as [(-> & -> & [(-> & SM) | (SL & SH)]) | [(-> & -> & -> & DLo & DHi) | (-> & _)]]; [ | | | contradiction].
    - clear WIN OFFB OFFSRC BSRC SRCD. unfold KHIGH in KLO. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RX | lia | lia]|]. split; [intros E; discriminate E|]. split; [intros _; lia|]. split; lia.
    - clear WIN OFFB OFFD BD. unfold KHIGH in KLO. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RS | lia | lia]|]. split; [intros E; discriminate E|]. split; [intros _; lia|]. split; lia.
    - clear WIN OFFSRC BSRC SRCD. unfold KHIGH in KLO. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|]. split; [intros _; lia|]. split; [intros E; discriminate E|]. split; lia.
  Qed.

  Lemma db_lit_placed : forall (m1 : amem) LITP LITSZ LITB LBE LOC,
    stk bsegs m1 (DCTX + 30372) (DCTX + 95940) -> bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> stk bsegs m1 B0 B1 ->
    0 <= LITSZ <= 131072 -> LITP <= LBE ->
    (LOC = 0 /\ LBE = LITP + LITSZ /\ (LITP = DCTX + 30372 /\ LITSZ <= 65536 \/ SRC + ip <= LITP /\ LBE + 32 <= SRC + ip + cbs)
     \/ LOC = 1 /\ LBE = LITP + LITSZ /\ LITB = LITP /\ DST <= LITB /\ LBE + 32 <= DST + CAP
     \/ LOC = 2 /\ 65536 < LITSZ /\ LITB = LITP /\ DST <= LITP /\ LBE + 32 <= DST + CAP /\ LBE = LITP + LITSZ - 65536) ->
    4096 <= LITP /\ LBE + WILDCOPY_OVERLENGTH < 2^47
    /\ rdbl bsegs m1 LITP (LBE + WILDCOPY_OVERLENGTH)
    /\ seq_lit_placed m1 DCTX DST CAP B0 B1 LITP LBE LITB LOC
    /\ AZ_seq_iface.off_stack lo SPA LITP (LBE + WILDCOPY_OVERLENGTH - LITP)
    /\ (LOC <> ZSTD_split -> AZ_seq_iface.apart LITP (LBE + WILDCOPY_OVERLENGTH - LITP) (DCTX + DCTX_entropy_rep) (DCTX_litExtraBuffer - DCTX_entropy_rep)).
  Proof.
    intros m1 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC.
    db_open CTX. unfold KHIGH in KLO.
    clear G1 G4 G5 G6 D1 D4 D5 S1 S4 S5 OUTB F1 F2 F3 F4 F5 F6 L0 L1 L2 L3 L4 RSTK RI R_src RD1 RD2 R_out RF1 RF2 RF3 LBH ASH RFS SPT RSTKT TP ATR FL LL DL ESHF GS FFSH FLSH DCSH DNB WL44 ISF WND BSM FBY.
    unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, AZ_seq_iface.off_stack, AZ_seq_iface.apart, DCTX_entropy_rep, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz.
    pose proof (rdbl_of_stk bsegs _ _ _ XB) as RX. pose proof (rdbl_of_stk bsegs _ _ _ BUF) as RB.
    pose proof (rdbl_of_bytes_at bsegs _ _ _ SRCB) as RS. rewrite length_map in RS.
    destruct PLC as [(-> & -> & [(-> & SM) | (SL & SH)]) | [(-> & -> & -> & DLo & DHi) | (-> & BIG & -> & DLo & DHi & ELBE)]].
    - clear WIN OFFB OFFSRC BSRC SRCD. unfold KHIGH in KLO. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RX | lia | lia]|]. split; [left; split; [reflexivity | lia]|]. split; [lia|]. intros _. lia.
    - clear WIN OFFB OFFD BD. unfold KHIGH in KLO. split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RS | lia | lia]|]. split; [left; split; [reflexivity | lia]|]. split; [lia|]. intros _. lia.
    - clear WIN OFFSRC BSRC SRCD. unfold KHIGH in KLO. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|]. split; [right; left; repeat split; lia|]. split; [lia|]. intros _. lia.
    - clear WIN OFFSRC BSRC SRCD. unfold KHIGH in KLO. assert (DN0 : DST <> 0) by (intros E0; specialize (DNULL E0); lia). specialize (DNN DN0).
      split; [lia|]. split; [lia|].
      split; [eapply rdbl_sub; [exact RB | lia | lia]|].
      split; [right; right; split; [reflexivity|]; split; [lia|]; split; [lia|]; replace (DCTX + 30372 + 65568) with (DCTX + 95940) by lia; exact RX|].
      split; [lia|]. intros NE. exfalso. apply NE. reflexivity.
  Qed.

End DB.
End CANSEC1.
