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
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c.
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
Definition BSH0 : list cell := [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 BF8; C1 BF3; C1 BF3; C1 BF3].
Definition BSH4 : list cell := [C1 BF1; C1 BF1; C1 BF1; C1 BF1; C1 B04; C1 BF3; C1 BF3; C1 BF3].

Lemma db_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W | exact WM] | exact R].
Qed.

Lemma db_ffr_pres_weaken : forall W W' LB (m m' : amem), ffr_pres W LB m m' -> sub_fp W W' -> ffr_pres W' LB m m'.
Proof.
  intros W W' LB m m' H HS. unfold ffr_pres in *. eapply magree_mono; [exact H|].
  intros a [[HF HO]|HX]; [left; split; [exact HF| apply HS; exact HO]| right; exact HX].
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

  (* [comment removed for export] *)
  Definition DBCTX : Prop :=
    (* [comment removed for export] *)
    (4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ DCTX mod 8 = 0 /\ 0 <= ip /\ 0 <= cbs < 2^21 /\ ip + cbs <= zlen src /\ 4096 <= SRC /\ SRC + zlen src < 2^47
     /\ B0 <= DST /\ DST + CAP <= B1 /\ 0 <= CAP /\ B1 < 2^47 /\ (DST = 0 -> CAP = 0) /\ (DST <> 0 -> 4096 <= B0)
     /\ 4096 <= lo /\ lo <= SPV - 6384 /\ SPV < 2^47)
    /\ (((PFX = 0 /\ CAP = 0) \/ B0 <= PFX <= DST)
        /\ (DCTX + 95992 <= lo \/ SPV <= DCTX) /\ (B1 <= lo \/ SPV <= B0) /\ (SRC + zlen src <= lo \/ SPV <= SRC)
        /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\ (B1 <= SRC \/ SRC + zlen src <= B0) /\ (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC))
    /\ (Forall (fun c => 0 <= c < 256) src /\ 0 <= fh_bsmax h <= 131072 /\ 0 <= fh_window h < 2^64 /\ wnth ws H5_isFrameDecompression = Z_to_bv 64 1
        /\ length ws = 44%nat)
    (* [comment removed for export] *)
    /\ (ATOP + 4096 <= lo /\ lo <= SPA - 6096 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0 /\ KHIGH <= lo)
    /\ (ablk DCTX (DCTX + 95992) /\ ainblk LB DCTX 95992 /\ (DCTX + 95992 <= FF \/ FF + 64 <= DCTX))
    /\ ((0 < zlen src -> ablk SRC (SRC + zlen src)) /\ (0 < zlen src -> ainblk LB SRC (zlen src)) /\ (0 < zlen src -> SRC + zlen src <= FF \/ FF + 64 <= SRC))
    /\ (B0 < B1 -> ablk B0 B1 /\ ainblk LB B0 (B1 - B0) /\ (B1 <= FF \/ FF + 64 <= B0))
    /\ (ablk FF (FF + 64) /\ FF mod 64 = 0 /\ FF + 64 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 64 <= al_fake L + FAKESZ)
    /\ (FLG = fflag L 0 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
        /\ (forall b, In b (FB0 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG))
    (* [comment removed for export] *)
    /\ (rng RNG lo (SPV - lo) /\ rng_aimg RNG /\ (0 < zlen src -> rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)))
        /\ rng RNG DCTX 95992 /\ rng RNG (shad DCTX) (shspan DCTX 95992)
        /\ (B0 < B1 -> rng RNG B0 (B1 - B0) /\ rng RNG (shad B0) (shspan B0 (B1 - B0)))
        /\ rng RNG FF 64 /\ rng RNG SHF 8 /\ rng RNG FLG 1)
    (* [comment removed for export] *)
    /\ (ablkLB LB /\ ashort LB 6 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ tp = Z_to_bv 64 ATP)
    /\ (DST <> 0 -> B0 < B1).

  Hypothesis CTX : DBCTX.
  Hypothesis FHL : fake_heap_law AI.

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
  (* [comment removed for export] *)
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 FF) xs3 (Z_to_bv 64 SHF) (Z_to_bv 64 SHB) (Z_to_bv 64 (DCTX + 29904)) xs7 xs8 xs9 xs10 (Z_to_bv 64 FF) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition DBB (p0 p1 p2 huv lev fev : word) (wsv : list word) (m1 : amem) : Prop :=
    dctx_ptrs bsegs m1 DCTX p0 p1 p2 huv
    /\ dctx_h1 bsegs m1 DCTX pde (Z_to_bv 64 PFX) (Z_to_bv 64 PFX) (Z_to_bv 64 0) expd
    /\ rw_cells bsegs m1 (DCTX + 29928) (zfh_cells h)
    /\ dctx_h3 bsegs m1 DCTX pcs dsz bt stg lev fev
    /\ dctx_h5 bsegs m1 DCTX wsv
    /\ stk bsegs m1 (DCTX + 32) (DCTX + 10296) /\ stk bsegs m1 (DCTX + 10296) (DCTX + 26684) /\ stk bsegs m1 (DCTX + 26684) (DCTX + 27324)
    /\ stk bsegs m1 (DCTX + 27324) (DCTX + 29884) /\ stk bsegs m1 (DCTX + 29884) (DCTX + 29888)
    /\ stk bsegs m1 (DCTX + 30372) (DCTX + 95940)
    /\ bytes_at bsegs m1 SRC (map (Z_to_bv 8) src)
    /\ stk bsegs m1 B0 B1
    /\ stk bsegs m1 lo SPA /\ rw_cells bsegs m1 (SPV + -104) SAVED /\ stk bsegs m1 (SPA + 88) (SPV + -104)
    /\ mem_inv bsegs m1
    /\ AHEAP AI L RNG st (FB0 FF :: LB) m1 /\ ffr_pres WR LB m0 m1 /\ munch (FOOT ++ fake_area L) m0 m1 /\ wmono bsegs m0 m1
    /\ unpoisoned m1 DCTX (DCTX + 95992) /\ (0 < zlen src -> unpoisoned m1 SRC (SRC + zlen src)) /\ (B0 < B1 -> unpoisoned m1 B0 B1)
    /\ aro_client RNG m1 /\ azstk RNG m1 lo SPV /\ ahull RNG m1 DCTX 95992 /\ (0 < zlen src -> ahull RNG m1 SRC (zlen src))
    /\ (B0 < B1 -> ahull RNG m1 B0 (B1 - B0)).
  Ltac open_dbb I :=
    destruct I as (PTRS & H1 & FP & H3 & H5 & ESEQ & EHUF & EREP & EWK & EPAD & XB & SRCB & BUF & STL & SAV & STG & MI & AH & FFR & MU & WM
                   & UD & US & UB & ARO & AZS & AHD & AHS & AHB);
    unfold dctx_ptrs in PTRS; unfold dctx_h1 in H1; unfold dctx_h3 in H3; unfold zfh_cells in FP.

  (* [comment removed for export] *)
  Lemma dbb_keep : forall p0 p1 p2 huv lev fev ws1 ws2 (ma mb : amem) W,
    DBB p0 p1 p2 huv lev fev ws1 ma ->
    munch W ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb -> dctx_h5 bsegs mb DCTX ws2 ->
    Forall (fun iv => fst iv <= snd iv /\ ((SPA <= fst iv /\ snd iv <= SPA + 88) \/ (FF <= fst iv /\ snd iv <= FF + 56) \/ (SHF <= fst iv /\ snd iv <= SHF + 8)
                                           \/ (DCTX + 30096 <= fst iv /\ snd iv <= DCTX + 30372))) W ->
    DBB p0 p1 p2 huv lev fev ws2 mb.
  Proof.
    intros p0 p1 p2 huv lev fev ws1 ws2 ma mb W I MUx WMx MIx H5x HW. db_open CTX. open_dbb I.
    unfold KHIGH in KLO.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (DJ : forall X n, 0 <= n -> (X + n <= SPA \/ SPA + 88 <= X) -> (X + n <= FF \/ FF + 56 <= X) -> (X + n <= SHF \/ SHF + 8 <= X) ->
                 (X + n <= DCTX + 30096 \/ DCTX + 30372 <= X) -> disjoint_from W X n).
    { intros X n Hn A B C D. clear - HW Hn A B C D. induction HW as [|[x y] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [lia| exact IH]. }
    assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 64 <= X) ->
                  ((6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP)) ->
                  disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C E BND. rewrite !shad_div. unfold ASHOFF. apply DJ; rewrite ?ESHF; clear - A B C E BND DL FL G1 G2 G3 ATR GS F2; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    assert (MUF : munch ([(SPA, SPA + 88); (DCTX + 30096, DCTX + 30372)] ++ fake_area L) ma mb).
    { eapply munch_weaken; [| exact MUx]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      rewrite ESHF, shad_div in *. unfold ASHOFF, FAKESZ in *.
      clear - Hx HW F5 F6 F2 FA8. induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [| exact IH].
      Z.div_mod_to_equations. lia. }
    assert (AW : aappW [(SPA, SPA + 88); (DCTX + 30096, DCTX + 30372)]).
    { unfold aappW, KLOW, KHIGH. apply Forall_cons; [cbn [fst snd]; clear - KLO G2; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DL ATR; lia| apply Forall_nil]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, zfh_cells.
    split; [eapply rw_cells_transport; [exact PTRS| exact MUx| exact WMx| apply DJ; cbn; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply rw_cells_transport; [exact H1| exact MUx| exact WMx| apply DJ; cbn; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply rw_cells_transport; [exact H3| exact MUx| exact WMx| apply DJ; cbn; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [exact H5x|].
    split; [eapply stk_transport_disjoint; [exact ESEQ| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply stk_transport_disjoint; [exact EREP| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply stk_transport_disjoint; [exact EPAD| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split; [eapply stk_transport_disjoint; [exact XB| exact MUx| exact WMx| apply DJ; clear - DL G1 G2 G3 OFFD D5 DCSH; lia]|].
    split.
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [Hz|Hz].
      - pose proof (fk_ablk_lits _ _ (S1 Hz)) as SL.
        eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; [clear - SBL| clear - OFFSRC G1 G2 G3| clear - S5 Hz| clear - SL SBL GS ATR SRCH Hz| clear - SRCD]; lia].
      - destruct SRCB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    pose proof BUF as (B00 & B11 & _).
    split.
    { destruct (Z_lt_ge_dec B0 B1) as [Hz|Hz].
      - pose proof (OUTB Hz) as (OB1 & _ & OB3). pose proof (fk_ablk_lits _ _ OB1) as BL.
        eapply stk_transport_disjoint; [exact BUF| exact MUx| exact WMx| apply DJ; [clear - Hz| clear - OFFB G1 G2 G3| clear - OB3 Hz| clear - BL Hz GS ATR B1H| clear - BD]; lia].
      - replace B1 with B0 by (clear - Hz B0D DCB CAP0; lia). apply (stk_empty bsegs). clear - B00 B0D DCB CAP0 B1H. lia. }
    split; [eapply stk_transport_disjoint; [exact STL| exact MUx| exact WMx| apply DJ; clear - G1 G2 G3 LO0 FL GS ATR OFFD DL KLO; lia]|].
    split; [eapply rw_cells_transport; [exact SAV| exact MUx| exact WMx| apply DJ; unfold FSAVED; cbn; clear - G1 G2 G3 LO0 FL GS ATR OFFD DL KLO; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MUx| exact WMx| apply DJ; clear - G1 G2 G3 LO0 FL GS ATR OFFD DL KLO; lia]|].
    split; [exact MIx|].
    split.
    { eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|]. clear - HW D4 G1 G2 G3 SPH LOS F1 F2 F4 FL. induction HW as [|[x y] W [Hle Hc] HW IH]; [apply Forall_nil|].
      apply Forall_cons; [| exact IH]. cbn [fst snd] in *. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
      - eapply fk_acr_stack; [exact G1| clear - Hc G2; lia| clear - Hc Hle G3 SPH; lia].
      - eapply fk_acr_frame; [left; reflexivity| clear - Hc; lia| cbn; clear - Hc Hle; lia].
      - set (nn := y - x) in *. set (kk := x - shad FF) in *.
        assert (Ek : x = shad (FF + 8 * kk)) by (subst kk; rewrite !shad_div; unfold ASHOFF; clear - F2; Z.div_mod_to_equations; lia).
        rewrite Ek. rewrite F4 in Hc. eapply (fk_acr_fshadow AI _ 0 FF 64); [left; reflexivity| subst kk; clear - Hc; lia| subst nn kk; clear - Hc Hle; lia| clear - F2; Z.div_mod_to_equations; lia| subst kk; clear - FL Hc; lia].
      - apply fk_acr_inblk. destruct D4 as (bb & Hb & Hb1 & Hb2). exists bb. split; [right; exact Hb| cbn; clear - Hle Hc Hb1 Hb2; lia]. }
    split.
    { eapply ffr_pres_trans; [exact FFR|].
      eapply (db_ffr_pres_weaken [(DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940)]); [| unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia].
      eapply (fk_ffr_fin AI L RNG st LB ma ma mb 0 FF 64 SHF 8 _ [(SPA, SPA + 88); (FF, FF + 56)]);
        [exact AH| exact LBH| exact F1| clear - F2; Z.div_mod_to_equations; lia| exact F4| clear; lia| clear; lia| | | apply ffr_pres_refl| | exact WMx].
      - apply Forall_cons; [cbn [fst snd]; split; [clear; lia| left; clear - G1 G2 G3 SPH; lia]|].
        apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH b Hb) as HB; clear - HB; lia
                                                                      | exists FF, (FF + 64); split; [exact F1| clear; lia]]]| apply Forall_nil].
      - apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]|].
        apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]|].
        apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]| apply Forall_nil].
      - cbn [app]. eapply munch_weaken; [| exact MUx]. unfold sub_fp; cbn [outside]; intros x Hx.
        clear - Hx HW. induction HW as [|[u v] W [Hle Hc] HW IH]; cbn; [exact I|]. cbn in Hle, Hc. split; [lia| exact IH]. }
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUF]]; unfold sub_fp, fake_area; cbn [outside app]; intros x Hx; clear - Hx G3; lia|].
    split; [exact (wmono_trans _ _ _ _ WM WMx)|].
    split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; [clear - DL| clear| clear - DL ATR| exact D5| exact DL]; lia]|].
    split; [intros NZ; eapply unpoisoned_munch; [exact (US NZ)| exact MUx| pose proof (fk_ablk_lits _ _ (S1 NZ)) as SL; apply DJS; [clear - SL| clear - NZ| clear - SL ATR| exact (S5 NZ)| exact SL]; lia]|].
    split; [intros NZ; pose proof (OUTB NZ) as (OB1 & _ & OB3); pose proof (fk_ablk_lits _ _ OB1) as BL; eapply unpoisoned_munch; [exact (UB NZ)| exact MUx|
            replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; [clear - BL| clear - NZ| clear - BL ATR| clear - OB3; lia| clear - BL; lia]; lia]|].
    split; [eapply aro_client_transport_F; [exact ARO| exact MUF| exact WMx| exact AW| exact FAB]|].
    split; [eapply azstk_transport_F; [exact AZS| exact MUF| exact WMx| exact AW| exact FAB| exact FA8| destruct LY5 as (_ & _ & FA1 & FA2); unfold FAKESZ; clear - FA2 G1; lia| clear - G2 G3; lia]|].
    split; [exact (db_ahull_wmono _ _ _ _ _ AHD WMx)|].
    split; [intros NZ; exact (db_ahull_wmono _ _ _ _ _ (AHS NZ) WMx)|].
    intros NZ; exact (db_ahull_wmono _ _ _ _ _ (AHB NZ) WMx).
  Qed.

  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FRL : fake_release_law AI fflag.

  (* [comment removed for export] *)
  Lemma p_ret : forall m1 p0 p1 p2 huv lev fev wsv r jA w0 shb xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 ->
    rw_cells bsegs m1 SPA [CB 88 jA] ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 SHF [CB 8 shb] ->
    0 <= r < 2^64 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    (zd_is_error r = false -> TBLA m1 DCTX p0 p1 p2 huv lev fev) ->
    (zd_is_error r = true \/ r <= CAP) ->
    evtF bsegs RNG POST (ST 0x89648 m1 xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XP XS RR KEEP TB RES. db_open CTX. pose proof I as I'. open_dbb I.
    pose proof (L4 _ ltac:(left; reflexivity)) as FLA. cbn [ab_addr ab_size] in FLA.
    assert (F0' : 6443008 <= FF) by (clear - FL; lia).
    assert (L0' : 6443008 <= FLG) by (clear - LL; lia).
    assert (FLD : FLG + 1 <= DCTX \/ DCTX + 95992 <= FLG).
    { destruct D4 as (b & Hb & Hb1 & Hb2). pose proof (L4 b (or_intror Hb)) as X. clear - X Hb1 Hb2. lia. }
    destruct (FFLAG _ _ _ _ _ 0 FF 64 AH ltac:(left; reflexivity)) as (XL & _). rewrite <- L0 in XL.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells bsegs _ _ _ FRA) as FRAS. cbn [cells_size csize Nat.add length] in FRAS.
    assert (STH : stk bsegs m1 SPA (SPV + -104)).
    { eapply stk_merge with (mid := SPA + 88); [| exact STG | clear - G3; lia]. replace (SPA + 88) with (SPA + Z.of_nat 88) by (clear; lia). exact FRAS. }
    clear FRA FRAS STG.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [1;1;1;1;1;1;1;1]%nat) in XS; [| reflexivity]. cbn [mk_CB_cells app] in XS.
    pose proof (munch_refl [(FF, FF + 8); (SHF, SHF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    destruct H5 as [H5C WL']. pose proof MI as MI1. fk_hold MI1.
    fk_hold I'. fk_hold MU. fk_hold WM. fk_hold FFR. fk_hold RI. fk_hold KEEP. fk_hold TB. fk_hold RES. fk_hold D4. fk_hold D1. fk_hold D5. fk_hold L3. fk_hold L4. fk_hold LBH.
    fk_hold F1. fk_hold F5. fk_hold F6. fk_hold OUTB. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold R_src. fk_hold R_out. fk_hold US. fk_hold UB. fk_hold AHS. fk_hold AHB. fk_hold ASH.
    fk_hold PTRS. fk_hold H1. fk_hold FP. fk_hold H3. fk_hold H5C. fk_hold WL'. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF.
    fk_hold UD. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold FLA. fk_hold XP. fk_hold STL. fk_hold STH. fk_hold SAV. fk_hold XL. fk_hold AH.
    fk_hold DL. fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold FLD. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold RD1. fk_hold RD2. fk_hold RSTK. fk_hold RSTKT. fk_hold ESHF.
    zstep. zstep.                                          (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; [exfalso; clear - K0 F0'; lia|].   (* [comment removed for export] *)
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-11)) with (Z_to_bv 64 18446744073709551605) by (apply Z_to_bv_eqm; reflexivity).
    do 8 zstep.                                            (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    clear XM XS.
    unfold fk_held in FLA, XP, AH.
    assert (XPA : rw_cells bsegs mA (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MUL| exact WML| cbn; clear - FFSH; lia]). clear XP.
    zstep.                                                 (* [comment removed for export] *)
    assert (AHA : AHEAP AI L RNG st (FB0 FF :: LB) mA).
    { eapply (AI_frame AI); [exact AH | exact MUL | exact WML |].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia] |].
      constructor; [cbn [fst snd] | constructor].
      rewrite F4. replace (shad FF + 8 - shad FF) with 8 by (clear; lia).
      eapply (fk_acr_fshadow AI _ 0 FF 64 FF 8); [left; reflexivity | clear; lia | clear; lia | clear - F2; Z.div_mod_to_equations; lia | clear - F0'; lia]. }
    (* [comment removed for export] *)
    pose proof (munch_refl [(FLG, FLG + 1)] mA) as MU2.
    unfold fk_held in XL, FLSH.
    assert (XLA : rw_cells bsegs mA FLG [C1 (Z_to_bv 8 1)]) by (eapply rw_cells_transport; [exact XL| exact MUL| exact WML| cbn; clear - FLSH FLA; lia]). clear XL XPA.
    fk_hold AHA. fk_hold MUL. fk_hold FLSH. fk_hold FLA. fk_hold FFSH. fk_hold AH.
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    unfold fk_held in AHA.
    assert (AHB' : AHEAP AI L RNG st LB mB).
    { rewrite L0 in MU2, XLA. eapply (fk_release AI fflag L RNG st LB mA mB 0 FF 64 FRL AHA); [rewrite <- L0; clear - L0'; lia | rewrite <- L0; clear - L2 ATR; lia | rewrite <- L0; clear - L0'; lia | exact MU2 | exact XLA]. }
    clear AHA. unfold fk_held in MUL.
    assert (MUX : munch [(FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)] m1 mB)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    clear MUL MU2 XLA.
    assert (DJK : forall X k, lo <= X -> X + k <= SPV -> 0 <= k -> disjoint_from [(FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)] X k).
    { intros X k A B C. cbn [disjoint_from]. unfold KHIGH in KLO. clear - A B C F3 G1 GS KLO L2 ATR. repeat split; lia. }
    unfold fk_held in SAV, STL, STH.
    assert (SAVB : rw_cells bsegs mB (SPV + -104) SAVED) by (eapply rw_cells_transport; [exact SAV| exact MUX| exact WML| apply DJK; unfold FSAVED; cbn; clear - G2 G3; lia]).
    assert (STLB : stk bsegs mB lo SPA) by (eapply stk_transport_disjoint; [exact STL| exact MUX| exact WML| apply DJK; clear - G2 G3 LO0; lia]).
    assert (STHB : stk bsegs mB SPA (SPV + -104)) by (eapply stk_transport_disjoint; [exact STH| exact MUX| exact WML| apply DJK; clear - G2 G3; lia]).
    clear SAV STL STH.
    fk_hold STLB. fk_hold STHB. unfold fk_held in RSTK.
    (* [comment removed for export] *)
    zstep.
    zstep.                                                 (* [comment removed for export] *)
    unfold FSAVED in SAVB.
    do 13 zstep.                                           (* [comment removed for export] *)
    zstep. zstep.                                          (* [comment removed for export] *)
    apply evtF_done. unfold zd_dblock_postA.
    unfold fk_held in *.
    do 14 eexists. exists mB, r, p0, p1, p2, huv, lev, fev, wsv. split; [reflexivity|].
    pose proof (stk_of_rw_cells bsegs _ _ _ SAVB) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (DJD : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> 0 <= k -> disjoint_from [(FF, FF + 8); (SHF, SHF + 8); (FLG, FLG + 1)] X k)
      by (intros X k A B C; cbn [disjoint_from]; clear - A B C D5 DCSH FLD; repeat split; lia).
    assert (MIB : mem_inv bsegs mB) by assumption.
    split.
    { (* [comment removed for export] *)
      eapply munch_trans; [exact MU|].
      eapply munch_weaken; [| exact MUX]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      destruct L3 as [L3a L3b]. rewrite shad_div in Hx. rewrite ESHF. unfold ASHOFF, FAKESZ in *. clear - Hx F5 F6 L3a L3b FA8 F2. Z.div_mod_to_equations. lia. }
    split; [exact (wmono_trans _ _ _ _ WM WML)|].
    split; [exact MIB|].
    split.
    { eapply stk_merge; [exact STLB | | clear - G2 G3; lia].
      eapply stk_merge with (mid := SPV + -104); [exact STHB | | clear - G3; lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
    split.
    { (* [comment removed for export] *)
      eapply ffr_pres_trans; [exact FFR|].
      eapply (db_ffr_pres_weaken [(DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940)]); [| unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia].
      eapply (fk_ffr_fin AI L RNG st LB m1 m1 mB 0 FF 64 SHF 8 _ [(FF, FF + 8); (FLG, FLG + 1)]);
        [exact AH | exact LBH | exact F1 | clear - F2; Z.div_mod_to_equations; lia | exact F4 | clear; lia | clear; lia | | | apply ffr_pres_refl | | exact WML].
      - constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH b Hb) as HB; clear - HB; lia
                                                            | exists FF, (FF + 64); split; [exact F1 | clear; lia]]] |].
        constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; exact (L4 b (or_intror Hb)) | exists FLG, (FLG + 1); split; [exact L1 | clear; lia]]] | constructor].
      - apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]|].
        apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]|].
        apply Forall_cons; [cbn [fst snd]; split; [exists DCTX, (DCTX + 95992); split; [exact D1| clear; lia]| clear; lia]| apply Forall_nil].
      - cbn [app]. eapply munch_weaken; [| exact MUX]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    split; [exact AHB'|].
    split.
    { destruct (Z_lt_ge_dec B0 B1) as [Hz|Hz].
      - pose proof (OUTB Hz) as (OB1 & (b & Hb & Hb1 & Hb2) & OB3). pose proof (fk_ablk_lits _ _ OB1) as BL.
        pose proof (L4 b (or_intror Hb)) as FLB.
        eapply stk_transport_disjoint; [exact BUF | exact MUX | exact WML |]. cbn [disjoint_from]. clear - OB3 BL GS ATR FLB Hb1 Hb2 Hz B1H. repeat split; lia.
      - pose proof BUF as (B00 & _). replace B1 with B0 by (clear - Hz B0D DCB CAP0; lia). apply (stk_empty bsegs). clear - B00 B0D DCB CAP0 B1H. lia. }
    split; [eapply rw_cells_transport; [exact PTRS | exact MUX | exact WML | apply DJD; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact H3 | exact MUX | exact WML | apply DJD; cbn; clear; lia]|].
    split; [split; [eapply rw_cells_transport; [exact H5C | exact MUX | exact WML | rewrite (h5_cells_size _ WL'); apply DJD; clear; lia] | exact WL']|].
    split; [exact KEEP|].
    split.
    { split; [| eapply stk_transport_disjoint; [exact XB | exact MUX | exact WML | apply DJD; clear; lia]].
      assert (ESEQ' : stk bsegs mB (DCTX + 32) (DCTX + 10296)) by (eapply stk_transport_disjoint; [exact ESEQ| exact MUX| exact WML| apply DJD; clear; lia]).
      assert (EHUF' : stk bsegs mB (DCTX + 10296) (DCTX + 26684)) by (eapply stk_transport_disjoint; [exact EHUF| exact MUX| exact WML| apply DJD; clear; lia]).
      assert (EREP' : stk bsegs mB (DCTX + 26684) (DCTX + 27324)) by (eapply stk_transport_disjoint; [exact EREP| exact MUX| exact WML| apply DJD; clear; lia]).
      assert (EWK' : stk bsegs mB (DCTX + 27324) (DCTX + 29884)) by (eapply stk_transport_disjoint; [exact EWK| exact MUX| exact WML| apply DJD; clear; lia]).
      assert (EPAD' : stk bsegs mB (DCTX + 29884) (DCTX + 29888)) by (eapply stk_transport_disjoint; [exact EPAD| exact MUX| exact WML| apply DJD; clear; lia]).
      eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [exact ESEQ' | exact EHUF' | clear; lia] | exact EREP' | clear; lia] | exact EWK' | clear; lia] | exact EPAD' | clear; lia]. }
    split.
    { intros NE. eapply (atbl_frame HUFINVw hufw_frame); [exact (TB NE) | exact MUX | exact MI1 | exact MIB |].
      intros x Hx. cbn [outside]. clear - Hx D5 DCSH FLD. repeat split; lia. }
    split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma p_exit1 : forall m1 p0 p1 p2 huv lev fev wsv r jA w0 shc xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31,
    DBB p0 p1 p2 huv lev fev wsv m1 ->
    rw_cells bsegs m1 SPA [CB 88 jA] ->
    rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m1 SHF shc -> cells_size shc = 8%nat ->
    0 <= r < 2^64 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    (zd_is_error r = false -> TBLA m1 DCTX p0 p1 p2 huv lev fev) ->
    (zd_is_error r = true \/ r <= CAP) ->
    evtF bsegs RNG POST (ST 0x89640 m1 xra x5 x6 x7 (Z_to_bv 64 r) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XP XS XSZ RR KEEP TB RES. db_open CTX.
    assert (F0' : 6443008 <= FF) by (clear - FL; lia).
    destruct (rw_cells_forget bsegs _ _ _ XS) as [shb XS8]. rewrite XSZ in XS8. clear XS.
    apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [4;1;3]%nat) in XS8; [| reflexivity]. cbn [mk_CB_cells app] in XS8.
    pose proof (munch_refl [(SHF, SHF + 8)] m1) as MUL. pose proof (wmono_refl bsegs m1) as WML.
    pose proof I as I2. open_dbb I2. rename H5 into H5x.
    clear PTRS H1 FP H3 ESEQ EHUF EREP EWK EPAD XB SRCB BUF STL SAV STG AH FFR MU WM UD US UB ARO AZS AHD AHS AHB. pose proof MI as MI1.
    fk_hold I. fk_hold FRA. fk_hold MI1. fk_hold XM. fk_hold XP. fk_hold KEEP. fk_hold TB. fk_hold RES. fk_hold CTX.
    zstep.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    zstep.                                                 (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    unfold fk_held in *.
    destruct (rw_cells_forget bsegs _ _ _ XS8) as [shb2 XS2]. cbn [cells_size csize Nat.add length] in XS2.
    assert (H52 : dctx_h5 bsegs m2 DCTX wsv).
    { destruct H5x as [H5C WL']. split; [| exact WL']. eapply rw_cells_transport; [exact H5C| exact MUL| exact WML| rewrite (h5_cells_size _ WL'); cbn [disjoint_from]; clear - DCSH; split; [lia| exact I]]. }
    eapply (p_ret m2 p0 p1 p2 huv lev fev wsv r jA w0 shb2);
      [ eapply (dbb_keep p0 p1 p2 huv lev fev wsv wsv m1 m2); [exact I| exact MUL| exact WML| assumption| exact H52| apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; left; clear; lia]| apply Forall_nil]]
      | eapply rw_cells_transport; [exact FRA| exact MUL| exact WML| cbn; unfold KHIGH in KLO; clear - GS KLO G2; split; [lia| exact I]]
      | eapply rw_cells_transport; [exact XM| exact MUL| exact WML| cbn; clear - FFSH; split; [lia| exact I]]
      | eapply rw_cells_transport; [exact XP| exact MUL| exact WML| cbn; clear - FFSH; split; [lia| exact I]]
      | exact XS2 | exact RR | exact KEEP | | exact RES ].
    intros NE. eapply (atbl_frame HUFINVw hufw_frame); [exact (TB NE) | exact MUL | exact MI1 | exact MI |].
    intros x Hx. cbn [outside]. clear - Hx DCSH. split; [lia| exact I].
  Qed.
End DB.
End CANSEC1.
