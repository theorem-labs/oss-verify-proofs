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
     AZ_hufinv AZ_tbl AZ_kx AZ_findfsi_a AZ_findfsi_c AZ_dblock_a AZ_dblock_b AZ_dblock_c AZ_dblock_d AZ_dblock_e AZ_dblock_f AZ_dblock_g.
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

  Notation tab_readyA := (AZ_dblock_f.tab_readyA RNG LB SPA lo DCTX B0 B1 FF).

  (* [comment removed for export] *)
  Lemma dbb_keep_stk : forall p0 p1 p2 huv lev fev ws1 (ma mb : amem),
    DBB p0 p1 p2 huv lev fev ws1 ma -> munch [(SPA - 16, SPA)] ma mb -> wmono bsegs ma mb -> mem_inv bsegs mb -> stk bsegs mb lo SPA ->
    DBB p0 p1 p2 huv lev fev ws1 mb.
  Proof.
    intros p0 p1 p2 huv lev fev ws1 ma mb I MUx WMx MIx STx. db_open CTX. open_dbb I.
    unfold KHIGH in KLO.
    pose proof (bytes_at_bound _ _ _ _ SRCB) as SBL. rewrite length_map in SBL.
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (DJ : forall X n, (X + n <= SPA - 16 \/ SPA <= X) -> disjoint_from [(SPA - 16, SPA)] X n) by (intros X n A; cbn; split; [exact A| exact I]).
    assert (DJS : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPA - 16, SPA)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. rewrite !shad_div. unfold ASHOFF. apply DJ. left. clear - A B C KLO G2 ATR. Z.div_mod_to_equations. lia. }
    assert (MUF : munch ([(SPA - 16, SPA)] ++ fake_area L) ma mb).
    { eapply munch_weaken; [| exact MUx]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. destruct Hx as [Hx _]. split; [exact Hx| exact I]. }
    assert (AW : aappW [(SPA - 16, SPA)]).
    { unfold aappW, KLOW, KHIGH. apply Forall_cons; [cbn [fst snd]; clear - KLO G2 G3 SPH; lia| apply Forall_nil]. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, zfh_cells.
    split; [eapply rw_cells_transport; [exact PTRS| exact MUx| exact WMx| apply DJ; cbn; clear - G2 G3 OFFD; lia]|].
    split; [eapply rw_cells_transport; [exact H1| exact MUx| exact WMx| apply DJ; cbn; clear - G2 G3 OFFD; lia]|].
    split; [eapply rw_cells_transport; [exact FP| exact MUx| exact WMx| apply DJ; cbn; clear - G2 G3 OFFD; lia]|].
    split; [eapply rw_cells_transport; [exact H3| exact MUx| exact WMx| apply DJ; cbn; clear - G2 G3 OFFD; lia]|].
    split; [destruct H5 as [H5C WL']; split; [| exact WL']; eapply rw_cells_transport; [exact H5C| exact MUx| exact WMx| rewrite (h5_cells_size _ WL'); apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact ESEQ| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EHUF| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EREP| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EWK| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact EPAD| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split; [eapply stk_transport_disjoint; [exact XB| exact MUx| exact WMx| apply DJ; clear - G2 G3 OFFD; lia]|].
    split.
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [Hz|Hz].
      - eapply bytes_at_transport; [exact SRCB| exact MUx| rewrite length_map; apply DJ; clear - OFFSRC G2 G3; lia].
      - destruct SRCB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    pose proof BUF as (B00 & B11 & _).
    split.
    { destruct (Z_lt_ge_dec B0 B1) as [Hz|Hz].
      - eapply stk_transport_disjoint; [exact BUF| exact MUx| exact WMx| apply DJ; clear - OFFB G2 G3 Hz; lia].
      - replace B1 with B0 by (clear - Hz B0D DCB CAP0; lia). apply (stk_empty bsegs). clear - B00 B0D DCB CAP0 B1H. lia. }
    split; [exact STx|].
    split; [eapply rw_cells_transport; [exact SAV| exact MUx| exact WMx| apply DJ; unfold FSAVED; cbn; clear - G3; lia]|].
    split; [eapply stk_transport_disjoint; [exact STG| exact MUx| exact WMx| apply DJ; clear - G3; lia]|].
    split; [exact MIx|].
    split.
    { eapply (AI_frame AI); [exact AH| exact MUx| exact WMx|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      eapply fk_acr_stack; [exact G1| clear - G2; lia| clear - G3 SPH; lia]. }
    split.
    { eapply ffr_pres_trans; [exact FFR|].
      eapply (db_ffr_pres_weaken []); [| unfold sub_fp; cbn [outside]; intros x Hx; exact I].
      eapply (fk_ffr_fin AI L RNG st LB ma ma mb 0 FF 64 SHF 0 [] [(SPA - 16, SPA)]);
        [exact AH| exact LBH| exact F1| clear - F2; Z.div_mod_to_equations; lia| exact F4| clear; lia| clear; lia| | apply Forall_nil| apply ffr_pres_refl| | exact WMx].
      - apply Forall_cons; [cbn [fst snd]; split; [clear; lia| left; clear - G1 G2 G3 SPH; lia]| apply Forall_nil].
      - cbn [app]. eapply munch_weaken; [| exact MUx]. unfold sub_fp; cbn [outside]; intros x Hx. destruct Hx as [Hx _]. split; [exact Hx| exact I]. }
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUF]]; unfold sub_fp, fake_area; cbn [outside app]; intros x Hx; clear - Hx G2 G3; lia|].
    split; [exact (wmono_trans _ _ _ _ WM WMx)|].
    split; [eapply unpoisoned_munch; [exact UD| exact MUx| apply DJS; clear - DL ATR; lia]|].
    split; [intros NZ; eapply unpoisoned_munch; [exact (US NZ)| exact MUx| pose proof (fk_ablk_lits _ _ (S1 NZ)) as SL; apply DJS; clear - SL NZ ATR; lia]|].
    split; [intros NZ; pose proof (OUTB NZ) as (OB1 & _ & OB3); pose proof (fk_ablk_lits _ _ OB1) as BL; eapply unpoisoned_munch; [exact (UB NZ)| exact MUx|
            replace B1 with (B0 + (B1 - B0)) at 1 by (clear; lia); apply DJS; clear - BL NZ ATR; lia]|].
    split; [eapply aro_client_transport_F; [exact ARO| exact MUF| exact WMx| exact AW| exact FAB]|].
    split; [eapply azstk_transport_F; [exact AZS| exact MUF| exact WMx| exact AW| exact FAB| exact FA8| destruct LY5 as (_ & _ & FA1 & FA2); unfold FAKESZ; clear - FA2 G1; lia| clear - G2 G3; lia]|].
    split; [exact (db_ahull_wmono _ _ _ _ _ AHD WMx)|].
    split; [intros NZ; exact (db_ahull_wmono _ _ _ _ _ (AHS NZ) WMx)|].
    intros NZ; exact (db_ahull_wmono _ _ _ _ _ (AHB NZ) WMx).
  Qed.

  Notation TABSX mm p0 p1 p2 fev nbSeq :=
    ((nbSeq = 0 /\ atbl_seq mm DCTX p0 p1 p2 fev)
     \/ (nbSeq <> 0 /\ seqhdr_tab mm DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                       seqhdr_tab mm DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                       seqhdr_tab mm DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)) (only parsing).
  Notation FRAME9 mm jA jB MXD := (rw_cells bsegs mm SPA [CB 16 jA; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 MXD); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 DCTX);
                           C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 CAP); CB 16 jB; C8 (Z_to_bv 64 FF)]) (only parsing).

  (* [comment removed for export] *)
  Lemma p_post : forall STACK m4 m5 p0 p1 p2 huv lev fev wsv nbSeq jA jB w0 (MXD : Z) rq rq0 rq1 rq2 ws5
                        (xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m4 -> FRAME9 m4 jA jB MXD ->
    rw_cells bsegs m4 FF [C8 w0] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m4 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m4 DCTX huv lev -> 0 <= nbSeq <= 98047 -> TABSX m4 p0 p1 p2 fev nbSeq ->
    0 <= STACK <= 6096 ->
    munch ([(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPA - STACK, SPA)] ++ fake_area L) m4 m5 ->
    wmono bsegs m4 m5 -> mem_inv bsegs m5 -> stk bsegs m5 lo SPA ->
    ffr_pres [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4)] (FB0 FF :: LB) m4 m5 ->
    AHEAP AI L RNG st (FB0 FF :: LB) m5 -> stk bsegs m5 B0 B1 -> rw_cells bsegs m5 (DCTX + 26684) [C4 rq0; C4 rq1; C4 rq2] ->
    dctx_h3 bsegs m5 DCTX pcs dsz bt stg lev (if nbSeq =? 0 then fev else Z_to_bv 64 1) ->
    dctx_h5 bsegs m5 DCTX ws5 -> (forall i, i <> H5_litBufferLocation -> wnth ws5 i = wnth wsv i) ->
    0 <= rq < 2^64 -> (zd_is_error rq = true \/ rq <= CAP) ->
    evtF bsegs RNG POST (ST 0x89640 m5 xra x5 x6 x7 (Z_to_bv 64 rq) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XP XS KEEP HINV NBR TABS HS MU5 WM5 MI5 ST5 FFR5 AH5 BUF5 REP5 H35 H55 KEEP5 RR5 RES5.
    db_open CTX. pose proof I as DBI. open_dbb I. unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    assert (LBH' : ablkLB (FB0 FF :: LB)) by (apply ablkLB_cons; [exact F1| exact LBH]).
    set (IVD := if 0 <? CAP then (DST, DST + CAP) else (DCTX + 26684, DCTX + 26684)).
    assert (IVDP : (0 < CAP /\ IVD = (DST, DST + CAP) /\ B0 < B1) \/ (CAP = 0 /\ IVD = (DCTX + 26684, DCTX + 26684))).
    { subst IVD. destruct (Z.ltb_spec 0 CAP) as [Hc|Hc]; [left; split; [exact Hc| split; [reflexivity| clear - Hc B0D DCB; lia]]| right; split; [clear - Hc CAP0; lia| reflexivity]]. }
    clearbody IVD.
    set (W5 := [IVD; (DCTX + 26684, DCTX + 26696); (DCTX + 30004, DCTX + 30008); (DCTX + 30368, DCTX + 30372); (SPA - STACK, SPA)]).
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
      repeat (apply Forall_cons; [cbn [fst snd]; clear - DBD DL KLO G2 G3 HS; lia|]). apply Forall_nil. }
    assert (DSTK : forall X k, SPA <= X -> X + k <= SPV -> 0 <= k -> disjoint_from (W5 ++ fake_area L) X k).
    { intros X k A1 A2 Hk. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from app fake_area]; rewrite !shad_div; unfold FAKESZ, ASHOFF in *;
        (split; [first [clear - A1 A2 Hk OFFB B0D DCB G2 G3 HB; lia| clear - A1 A2 Hk OFFD G2 G3; lia]|]);
        clear - A1 A2 Hk FABL OFFD G1 G2 G3 ATR KLO HS; repeat split; Z.div_mod_to_equations; lia. }
    assert (DJF : forall X k, FF <= X -> X + k <= FF + 64 -> 0 <= k -> disjoint_from W5 X k).
    { intros X k A1 A2 Hk. subst W5. destruct IVDP as [(Hc & -> & HB)|(Hc & ->)]; cbn [disjoint_from];
        (split; [first [pose proof (OUTB HB) as (_ & _ & OB3); clear - OB3 A1 A2 Hk B0D DCB; lia| clear - A1 A2 Hk D5; lia]|]);
        clear - A1 A2 Hk D5 F3 G1 G2 HS; repeat split; lia. }
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
        clear - A1 A2 Hk OFFD G2 G3 HS; repeat split; lia. }
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ DCTX [C8 p0; C8 p1; C8 p2; C8 huv] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' PTRS) as PTRS5.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd] AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' H1) as H15.
    pose proof (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 29928) (zfh_cells h) AH ltac:(apply DIN; csz; clear; lia) ltac:(apply DDJ; csz; clear; lia) MU5 WM5 FFR5' FP) as FP5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 32) (DCTX + 10296) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' ESEQ) as ESEQ5.
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 10296) (DCTX + 26684) AH ltac:(apply DIN; clear; lia) ltac:(apply DDJ; clear; lia) MU5 WM5 FFR5' EHUF) as EHUF5.
    destruct (stk_split bsegs m4 (DCTX + 26684) (DCTX + 26696) (DCTX + 27324) EREP ltac:(clear; lia)) as [_ EREPb].
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
          clear - Hz SRCD OFFSRC G2 G3 HS; repeat split; lia.
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
        (split; [first [exact X1| clear - X2; lia]|]); clear - X2 X3 X4 X5 X6 G3 HS; repeat split; try lia; tauto. }
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
    idtac "G3".
    assert (TB5 : zd_is_error rq = false -> atbl HUFINVw m5 DCTX p0 p1 p2 huv lev (if nbSeq =? 0 then fev else Z_to_bv 64 1)).
    { intros _. destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)].
      - rewrite (proj2 (Z.eqb_eq nbSeq 0) NZ0). split; [| exact HINV5].
        exact (AZ_dblock_b.db_atbl_seq_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5 _ _ _ _ AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' MI5 T0).
      - rewrite (proj2 (Z.eqb_neq nbSeq 0) NZ1). split; [| exact HINV5].
        destruct (AZ_dblock_g.db_seqhdr_tab_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5 K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (all_default_at _ MI5) LL_default_ok) ltac:(unfold DCTX_entropy_LLTable; clear; lia) ltac:(unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; clear; lia) T1) as (T1' & t1' & EQ1 & P1 & A1).
        destruct (AZ_dblock_g.db_seqhdr_tab_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5 K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (aof_default_at _ MI5) OF_default_ok) ltac:(unfold DCTX_entropy_OFTable; clear; lia) ltac:(unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; clear; lia) T2) as (T2' & t2' & EQ2 & P2 & A2).
        destruct (AZ_dblock_g.db_seqhdr_tab_fcall AI L RNG st DCTX FHL (FB0 FF :: LB) m4 m4 m5 W5 K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1 AH ltac:(apply INCONS; exact D4) ltac:(apply DDJ; clear; lia) MU5 FFR5' (conj (aml_default_at _ MI5) ML_default_ok) ltac:(unfold DCTX_entropy_MLTable; clear; lia) ltac:(unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia) T3) as (T3' & t3' & EQ3 & P3 & A3).
        rewrite EQ1, EQ2, EQ3. eapply zd_tbl_seq_intro; eassumption. }
    destruct (rw_cells_forget bsegs _ _ _ FRA5) as [jA' FRA']. cbn [cells_size csize Nat.add length] in FRA'.
    eapply (p_exit1 m5 p0 p1 p2 huv lev _ ws5 rq jA' w0 BSH4);
      [exact DB5| exact FRA'| exact XM5| exact XP5| exact XS5| reflexivity| exact RR5| exact KEEP5'| exact TB5| exact RES5].
  Qed.

  Hypothesis SEQD : zd_seq_default_stmtA AI rng_fs.
  Hypothesis SEQS : zd_seq_split_stmtA AI rng_fs.

  (* [comment removed for export] *)
  Lemma db_h5_loc_cell : forall (m1 : amem) D wsq, dctx_h5 bsegs m1 D wsq -> rw_cells bsegs m1 (D + 30368) [C4 (wnth wsq H5_litBufferLocation)].
  Proof.
    intros m1 D wsq [C WL]. h5_open wsq WL.
    lazymatch type of C with rw_cells _ _ _ ?cs =>
      change cs with (firstn 43 cs ++ [nth 43 cs (C1 (Z_to_bv 8 0))] ++ skipn 44 cs) in C end.
    cbn [firstn skipn nth] in C.
    apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
    cbn [cells_size csize Nat.add] in C. replace (D + 30096 + Z.of_nat 272) with (D + 30368) in C by lia. exact C.
  Qed.

  (* [comment removed for export] *)
  Lemma p_mid : forall m4 p0 p1 p2 huv lev fev wsv r r2 nbSeq jA jB w0 (MXD : Z)
                         (xra x5 x6 x7 xa0 xa1 xa2 xa5 xa7 xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m4 -> FRAME9 m4 jA jB MXD ->
    rw_cells bsegs m4 FF [C8 w0] -> rw_cells bsegs m4 (FF + 32) [C4 (Z_to_bv 64 nbSeq)] -> rw_cells bsegs m4 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m4 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) ->
    HUFINVw m4 DCTX huv lev -> cbs <= fh_bsmax h ->
    1 <= r <= cbs -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    0 <= r2 <= cbs - r -> 0 <= nbSeq <= 98047 -> (nbSeq <> 0 -> DST <> 0 /\ CAP <> 0) ->
    TABSX m4 p0 p1 p2 fev nbSeq ->
    evtF bsegs RNG POST (ST 0x89774 m4 xra x5 x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (SRC + ip + r + r2)) (Z_to_bv 64 (cbs - r - r2)) xa5 (Z_to_bv 64 DCTX) xa7
                           xs3 xs7 xs8 xs9 xs10 x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XN XP XS KEEP HINV KB RL PLACED R2R NBR NZD TABS. db_open CTX. pose proof I as DBI. open_dbb I.
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
    pose proof (db_h5_loc_cell _ _ _ H5) as LOCC.
    clearbody sq.
    fk_hold DBI. fk_hold SEQD. fk_hold SEQS. fk_hold KEEP. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold TRD. fk_hold TT. fk_hold XM. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    fk_hold SQB. fk_hold SQF. fk_hold EREPa. fk_hold EREPb. fk_hold REP. fk_hold LRD. fk_hold LPL. fk_hold LOFF. fk_hold LAP. fk_hold LAR. fk_hold LAH. fk_hold LAI.
    fk_hold ARD. fk_hold ARS4. fk_hold ARB4. fk_hold AFP4. fk_hold LBH'. fk_hold INCONS. fk_hold LOCS. fk_hold PLC.
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    db_chk m4 (DCTX + 30368) UD RD2 DG.                        (* [comment removed for export] *)
    zstep. clear LOCC.                                         (* [comment removed for export] *)
    rewrite ELL. rewrite (sx32w_small LOC) by (clear - LOCS; unfold fk_held, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in LOCS; lia).
    zstep.                                                     (* [comment removed for export] *)
    unfold fk_held in RF1.
    zstep. try rewrite (sx32w_small nbSeq) by (clear - NBR; lia).   (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_cases KL.                                        (* [comment removed for export] *)
    { (* [comment removed for export] *)
      assert (NL2 : LOC <> 2) by (clear - KL LOCS; unfold fk_held in LOCS; unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in LOCS; zify_cond KL; lia).
      gf_unhold.
      destruct (AZ_dblock_f.db_lit_default fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX m4 LITP LITSZ LITB LBE LOC XB SRCB BUF LSZR LPLE PLC NL2)
        as (DLOC & DSZ & DP0 & DPH & DRD & DIN' & DND & DOFF & DAP).
      assert (ESZ : LITSZ + WILDCOPY_OVERLENGTH = LBE + WILDCOPY_OVERLENGTH - LITP) by (clear - PLC NL2; lia).
    fk_hold DBI. fk_hold SEQD. fk_hold SEQS. fk_hold KEEP. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold TRD. fk_hold TT. fk_hold XM. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold H1. fk_hold H3. fk_hold H5. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    fk_hold SQB. fk_hold SQF. fk_hold EREPa. fk_hold EREPb. fk_hold REP. fk_hold LRD. fk_hold LPL. fk_hold LOFF. fk_hold LAP. fk_hold LAR. fk_hold LAH. fk_hold LAI.
    fk_hold ARD. fk_hold ARS4. fk_hold ARB4. fk_hold AFP4. fk_hold LBH'. fk_hold INCONS. fk_hold LOCS. fk_hold PLC. fk_hold DLOC. fk_hold DRD. fk_hold DIN'. fk_hold DND. fk_hold DOFF. fk_hold DAP.
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    gf_unhold.
    zstep.                                                     (* [comment removed for export] *)
    unfold zd_seq_default_stmtA, APZD_SEQ_DEFAULT in SEQD.
    eapply evtF_cut.
    { eapply (SEQD L RNG st (FB0 FF :: LB)) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1)
          (SEQ := SRC + ip + r + r2) (nbSeq := nbSeq) (LLT := LLT) (MLT := MLT) (OFT := OFT) (PFX := PFX) (LITP := LITP) (LITSZ := LITSZ) (LITB := LITB) (LOC := LOC)
          (sq := sq) (tLL := tLL) (tOF := tOF) (tML := tML) (huf := huv) (r0 := rp0) (r1 := rp1) (r2 := rp2) (pde := pde) (dend := Z_to_bv 64 0) (expd := expd)
          (pcs := pcs) (dsz := dsz) (bt := bt) (stg := stg) (le := lev) (fe := fev) (ws := wsv);
      lazymatch goal with
      | |- seq_dctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold seq_dctx; rewrite <- EP0, <- EP1, <- EP2; split; [exact PTRS| split; [exact REP| split; [exact H1| split; [exact H3| exact H5]]]]
      | |- seq_lit _ _ _ _ _ => unfold seq_lit; split; [exact ELP| split; [exact ELS| split; [exact ELB| exact ELL]]]
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
      | |- LOC = _ \/ _ => exact DLOC
      | |- 0 <= LITSZ < _ => exact DSZ
      | |- LITP + LITSZ + _ < _ => exact DPH
      | |- LOC = ZSTD_in_dst -> _ => exact DIN'
      | |- LOC = ZSTD_not_in_dst -> _ => exact DND
      | |- 4096 <= LITP => exact LP0
      | |- rdbl _ _ _ _ => exact DRD
      | |- stk _ _ lo SPA => exact STL
      | |- 4096 <= lo => exact LO0
      | |- lo <= SPA - _ => clear - G2; lia
      | |- 0 <= SPA < _ => clear - G2 G3 SPH LO0; lia
      | |- AZ_seq_iface.off_stack _ _ DCTX _ => unfold AZ_seq_iface.off_stack, DCTX_SIZEOF; clear - OFFD G3; lia
      | |- AZ_seq_iface.off_stack _ _ B0 _ => unfold AZ_seq_iface.off_stack; clear - OFFB G3; lia
      | |- AZ_seq_iface.off_stack _ _ (SRC + _ + _ + _) _ => unfold AZ_seq_iface.off_stack; rewrite SQL; clear - OFFSRC G3 IPC IP0 RL R2R; lia
      | |- AZ_seq_iface.off_stack _ _ LITP _ => exact DOFF
      | |- nbSeq <> 0 -> AZ_seq_iface.off_stack _ _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (TT NZ)))
      | |- AZ_seq_iface.apart B0 _ DCTX _ => unfold AZ_seq_iface.apart, DCTX_SIZEOF; clear - BD; lia
      | |- AZ_seq_iface.apart B0 _ (SRC + _ + _ + _) _ => unfold AZ_seq_iface.apart; rewrite SQL; clear - BSRC IPC IP0 RL R2R; lia
      | |- nbSeq <> 0 -> AZ_seq_iface.apart B0 _ _ _ /\ _ => intros NZ; exact (proj1 (proj2 (proj2 (TT NZ))))
      | |- AZ_seq_iface.apart (SRC + _ + _ + _) _ _ _ => unfold AZ_seq_iface.apart, DCTX_SIZEOF, DCTX_entropy_rep; rewrite SQL; clear - SRCD IPC IP0 RL R2R; lia
      | |- AZ_seq_iface.apart LITP _ _ _ => exact DAP
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
      | |- areg _ _ LITP _ => rewrite ESZ; exact LAR
      | |- ahull _ _ LITP _ => rewrite ESZ; exact LAH
      | |- ainblk _ LITP _ => rewrite ESZ; exact LAI
      | |- mem_inv _ _ => exact MI
      | |- _ = _ => first [reflexivity | rewrite SQL; reflexivity]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
      destruct PO as (z5 & z6 & z7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m5 & rq & rq0 & rq1 & rq2
                      & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & BUF5 & REP5 & H35 & RR5 & RES5).
      rd_retlit.
      zstep.                                                   (* [comment removed for export] *)
      unfold DCTX_entropy_rep, DCTX_fseEntropy in MU5, FFR5, REP5.
      pose proof (db_ffr_pres_weaken _ [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPA - 4704, SPA)] _ _ _ FFR5
                    ltac:(unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; tauto)) as FFR5s.
      assert (H55 : dctx_h5 bsegs m5 DCTX wsv).
      { destruct H5 as [H5C WL']. split; [| exact WL'].
        eapply (fcall_cells_pres AI FHL _ _ _ _ _ _ _ _ (DCTX + 30096) (h5_cells wsv) AH); [ | | exact MU5| exact WM5| exact FFR5s| exact H5C].
        - rewrite (h5_cells_size _ WL'). apply INCONS. eapply db_inblk_sub; [exact D4| clear; lia| clear; lia].
        - rewrite (h5_cells_size _ WL'). cbn [disjoint_from]. clear - BD B0D DCB OFFD G2 G3. repeat split; lia. }
      assert (MU5' : munch ([(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPA - 4704, SPA)] ++ fake_area L) m4 m5).
      { eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside app]; intros x Hx. destruct Hx as (X1 & X2 & X3 & X4 & X5).
        split; [exact X1| split; [exact X2| split; [exact X3| exact X5]]]. }
      assert (FFR5' : ffr_pres [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4)] (FB0 FF :: LB) m4 m5).
      { eapply db_ffr_pres_weaken; [exact FFR5|]. unfold sub_fp; cbn [outside]; intros x Hx. destruct Hx as (X1 & X2 & X3 & X4 & _).
        split; [exact X1| split; [exact X2| split; [exact X3| exact I]]]. }
      eapply (p_post 4704 m4 m5 p0 p1 p2 huv lev fev wsv nbSeq jA jB w0 MXD rq rq0 rq1 rq2 wsv);
        [exact DBI| exact FRA| exact XM| exact XP| exact XS| exact KEEP| exact HINV| exact NBR| exact TABS| clear; lia| exact MU5'| exact WM5| exact MI5| exact ST5
        | exact FFR5'| exact AH5| exact BUF5| exact REP5| exact H35| exact H55| intros i _; reflexivity| exact RR5| exact RES5]. }
    (* [comment removed for export] *)
    assert (EL2 : LOC = ZSTD_split) by (clear - KL LOCS; unfold fk_held in LOCS; unfold ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in LOCS |- *; zify_cond KL; lia).
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    gf_unhold.
    zstep.                                                     (* [comment removed for export] *)
    unfold zd_seq_split_stmtA, zd_seq_split_stmtA_at, APZD_SEQ_SPLIT in SEQS.
    eapply evtF_cut.
    { eapply (SEQS L RNG st (FB0 FF :: LB)) with (SPV := SPA) (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (B0 := B0) (B1 := B1)
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
      | |- LOC = ZSTD_split => exact EL2
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
      | |- (fun _ => _) _ => cbv beta; exact EL2
      | |- 4096 <= B0 => apply DNN; intros E0; pose proof (DNULL E0) as C0; clear - C0 PLC EL2 LPLE; unfold ZSTD_split in EL2; lia
      | |- _ = _ => first [reflexivity | rewrite SQL; reflexivity]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m5 & rq & rq0 & rq1 & rq2 & ws5
                    & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & BUF5 & REP5 & H35 & H55 & KEEP5 & RR5 & RES5).
    rd_retlit.
    zstep.                                                     (* [comment removed for export] *)
    unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in MU5, FFR5, REP5.
    eapply (p_post 4704 m4 m5 p0 p1 p2 huv lev fev wsv nbSeq jA jB w0 MXD rq rq0 rq1 rq2 ws5);
      [exact DBI| exact FRA| exact XM| exact XP| exact XS| exact KEEP| exact HINV| exact NBR| exact TABS| clear; lia| exact MU5| exact WM5| exact MI5| exact ST5
      | exact FFR5| exact AH5| exact BUF5| exact REP5| exact H35| exact H55| exact KEEP5| exact RR5| exact RES5].
  Qed.

  Hypothesis SEQL : zd_seq_long_stmtA AI rng_fs.
  Hypothesis OFFINFO : zd_offinfo_stmtA.
  Notation p_long := (AZ_dblock_g.p_long AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws FF SHF FLG CTX FHL FFLAG FRL SEQL).

  (* [comment removed for export] *)
  Lemma p_norm : forall m3 p0 p1 p2 huv lev fev wsv r r2 nbSeq jA jB w0 MXD
                          (xra x5 x6 x7 xa0 xa1 xa2 xa5 xa6 xa7 xs3 xs7 xs8 x28 x29 x30 x31 : word),
    DBB p0 p1 p2 huv lev fev wsv m3 -> FRAME9 m3 jA jB MXD ->
    rw_cells bsegs m3 FF [C8 w0] -> rw_cells bsegs m3 (FF + 32) [C4 (Z_to_bv 64 nbSeq)] -> rw_cells bsegs m3 (FF + 56) [C8 (Z_to_bv 64 FLG)] -> rw_cells bsegs m3 SHF BSH4 ->
    (forall i, h5_block_owned i = false -> wnth wsv i = wnth ws i) -> bv_unsigned (Mem.sx32 (wnth wsv H5_ddictIsCold)) = 0 ->
    HUFINVw m3 DCTX huv lev -> cbs <= fh_bsmax h -> MXD = Z.min CAP (fh_bsmax h) ->
    1 <= r <= cbs -> declit_placed DCTX DST CAP (SRC + ip) cbs wsv ->
    0 <= r2 <= cbs - r -> 0 <= nbSeq <= 98047 -> (nbSeq <> 0 -> DST <> 0 /\ CAP <> 0) ->
    TABSX m3 p0 p1 p2 fev nbSeq ->
    evtF bsegs RNG POST (ST 0x896e8 m3 xra x5 x6 x7 xa0 xa1 xa2 (Z_to_bv 64 (SRC + ip + r + r2)) (Z_to_bv 64 (cbs - r - r2)) xa5 xa6 xa7
                           xs3 xs7 xs8 (Z_to_bv 64 (DCTX + 30204)) (Z_to_bv 64 (Z.shiftr (DCTX + 30204) 3 + SHB)) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I FRA XM XN XP XS KEEP KC HINV KB EMXD RL PLACED R2R NBR NZD TABS. db_open CTX. pose proof I as DBI. open_dbb I.
    unfold KHIGH in KLO.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    assert (INCONS : forall X k, ainblk LB X k -> ainblk (FB0 FF :: LB) X k)
      by (intros X k (bb & Hb & Hb1 & Hb2); exists bb; split; [right; exact Hb| split; [exact Hb1| exact Hb2]]).
    fk_hold DBI. fk_hold SEQD. fk_hold SEQS. fk_hold SEQL. fk_hold OFFINFO. fk_hold KEEP. fk_hold PLACED. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS. fk_hold DL. fk_hold ESHF.
    fk_hold KC. fk_hold EMXD. fk_hold INCONS.
    fk_hold H1. fk_hold H3. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    zstep; if_cases KH.                                        (* [comment removed for export] *)
    { rename m3 into m5.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (db_sh_rd0s mx DCTX 95992 (DCTX + 30204) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
      pose proof (db_sh_rng1 RNG DCTX (DCTX + 30204) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz end.
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep; if_false.
    destruct H5 as [H5C WL']. h5_open wsv WL'.
    pose proof (munch_refl [(DCTX + 30204, DCTX + 30208)] m5) as MU34. pose proof (wmono_refl bsegs m5) as WM34. fk_hold FRA.
    zstep.
    unfold fk_held in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    gf_unhold.
    lazymatch type of H5C with rw_cells _ _ _ ?cs => let wl := cells_words cs in assert (H54 : dctx_h5 bsegs m6 DCTX wl) by (split; [exact H5C| reflexivity]) end.
    lazymatch type of H54 with dctx_h5 _ _ _ ?wl => set (ws2 := wl) in H54 end.
    assert (DB4 : DBB p0 p1 p2 huv lev fev ws2 m6).
    { eapply (dbb_keep p0 p1 p2 huv lev fev _ ws2 m5 m6); [exact DBI| exact MU34| exact WM34| exact MI| exact H54|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; right; clear; lia]| apply Forall_nil]. }
    assert (KEEP2 : forall i, h5_block_owned i = false -> wnth ws2 i = wnth ws i).
    { intros i Hi. specialize (KEEP i Hi). subst ws2. do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP. }
    assert (HINV4 : HUFINVw m6 DCTX huv lev) by (eapply hufw_fine; [exact HINV| exact MU34|]; intros x Hx; cbn [outside]; clear - Hx; lia).
    assert (XM4 : rw_cells bsegs m6 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XN4 : rw_cells bsegs m6 (FF + 32) [C4 (Z_to_bv 64 nbSeq)]) by (eapply rw_cells_transport; [exact XN| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XP4 : rw_cells bsegs m6 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XS4 : rw_cells bsegs m6 SHF BSH4) by (eapply rw_cells_transport; [exact XS| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - DCSH; split; [lia| exact I]]).
    assert (TABS4 : (nbSeq = 0 /\ atbl_seq m6 DCTX p0 p1 p2 fev)
                    \/ (nbSeq <> 0 /\ seqhdr_tab m6 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                                      seqhdr_tab m6 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                                      seqhdr_tab m6 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)).
    { assert (OUT : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside [(DCTX + 30204, DCTX + 30208)] x) by (intros x Hx; cbn [outside]; clear - Hx; lia).
      destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)].
      - left. split; [exact NZ0| eapply db_atbl_seq_fine; [exact T0| exact MU34| assumption| exact OUT]].
      - right. split; [exact NZ1|]. assert (MI4 : mem_inv bsegs m6) by assumption.
        split; [| split]; (eapply db_seqhdr_tab_fine; [eassumption| | exact MU34| exact OUT| |]);
          first [ split; [first [apply all_default_at| apply aof_default_at| apply aml_default_at]; exact MI4| first [apply LL_default_ok| apply OF_default_ok| apply ML_default_ok]]
                | unfold DCTX_entropy_LLTable, DCTX_entropy_OFTable, DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia ]. }
    assert (W17 : wnth ws2 H5_ddictIsCold = Z_to_bv 64 0) by reflexivity.
    assert (FRA4 : FRAME9 m6 jA jB MXD)
      by (eapply rw_cells_transport; [exact FRA| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - OFFD G2 G3; split; [lia| exact I]]).
    assert (PL4 : declit_placed DCTX DST CAP (SRC + ip) cbs ws2).
    { pose proof PLACED as Q. destruct Q as (LITP' & LITSZ' & LITB' & LBE' & LOC' & EP & ES & EB & EE & EL & REST).
      exists LITP', LITSZ', LITB', LBE', LOC'. subst ws2.
      cbv [wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in EP, ES, EB, EE, EL |- *.
      exact (conj EP (conj ES (conj EB (conj EE (conj EL REST))))). }
    eapply (p_mid m6 p0 p1 p2 huv lev fev ws2 r r2 nbSeq jA jB w0 MXD);
      [exact DB4| exact FRA4| exact XM4| exact XN4| exact XP4| exact XS4| exact KEEP2| exact HINV4| exact KB| exact RL| exact PL4| exact R2R| exact NBR| exact NZD| exact TABS4]. }
    zstep.                                                     (* [comment removed for export] *)
    unfold fk_held in RF1, XN.
    zstep. try rewrite (sx32w_small nbSeq) by (clear - NBR; lia).   (* [comment removed for export] *)
    fk_hold RF1. fk_hold XN.
    zstep.                                                     (* [comment removed for export] *)
    zstep; if_cases KN.                                        (* [comment removed for export] *)
    { rename m3 into m5.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (db_sh_rd0s mx DCTX 95992 (DCTX + 30204) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
      pose proof (db_sh_rng1 RNG DCTX (DCTX + 30204) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz end.
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep; if_false.
    destruct H5 as [H5C WL']. h5_open wsv WL'.
    pose proof (munch_refl [(DCTX + 30204, DCTX + 30208)] m5) as MU34. pose proof (wmono_refl bsegs m5) as WM34. fk_hold FRA.
    zstep.
    unfold fk_held in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    gf_unhold.
    lazymatch type of H5C with rw_cells _ _ _ ?cs => let wl := cells_words cs in assert (H54 : dctx_h5 bsegs m6 DCTX wl) by (split; [exact H5C| reflexivity]) end.
    lazymatch type of H54 with dctx_h5 _ _ _ ?wl => set (ws2 := wl) in H54 end.
    assert (DB4 : DBB p0 p1 p2 huv lev fev ws2 m6).
    { eapply (dbb_keep p0 p1 p2 huv lev fev _ ws2 m5 m6); [exact DBI| exact MU34| exact WM34| exact MI| exact H54|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; right; clear; lia]| apply Forall_nil]. }
    assert (KEEP2 : forall i, h5_block_owned i = false -> wnth ws2 i = wnth ws i).
    { intros i Hi. specialize (KEEP i Hi). subst ws2. do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP. }
    assert (HINV4 : HUFINVw m6 DCTX huv lev) by (eapply hufw_fine; [exact HINV| exact MU34|]; intros x Hx; cbn [outside]; clear - Hx; lia).
    assert (XM4 : rw_cells bsegs m6 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XN4 : rw_cells bsegs m6 (FF + 32) [C4 (Z_to_bv 64 nbSeq)]) by (eapply rw_cells_transport; [exact XN| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XP4 : rw_cells bsegs m6 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XS4 : rw_cells bsegs m6 SHF BSH4) by (eapply rw_cells_transport; [exact XS| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - DCSH; split; [lia| exact I]]).
    assert (TABS4 : (nbSeq = 0 /\ atbl_seq m6 DCTX p0 p1 p2 fev)
                    \/ (nbSeq <> 0 /\ seqhdr_tab m6 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                                      seqhdr_tab m6 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                                      seqhdr_tab m6 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)).
    { assert (OUT : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside [(DCTX + 30204, DCTX + 30208)] x) by (intros x Hx; cbn [outside]; clear - Hx; lia).
      destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)].
      - left. split; [exact NZ0| eapply db_atbl_seq_fine; [exact T0| exact MU34| assumption| exact OUT]].
      - right. split; [exact NZ1|]. assert (MI4 : mem_inv bsegs m6) by assumption.
        split; [| split]; (eapply db_seqhdr_tab_fine; [eassumption| | exact MU34| exact OUT| |]);
          first [ split; [first [apply all_default_at| apply aof_default_at| apply aml_default_at]; exact MI4| first [apply LL_default_ok| apply OF_default_ok| apply ML_default_ok]]
                | unfold DCTX_entropy_LLTable, DCTX_entropy_OFTable, DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia ]. }
    assert (W17 : wnth ws2 H5_ddictIsCold = Z_to_bv 64 0) by reflexivity.
    assert (FRA4 : FRAME9 m6 jA jB MXD)
      by (eapply rw_cells_transport; [exact FRA| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - OFFD G2 G3; split; [lia| exact I]]).
    assert (PL4 : declit_placed DCTX DST CAP (SRC + ip) cbs ws2).
    { pose proof PLACED as Q. destruct Q as (LITP' & LITSZ' & LITB' & LBE' & LOC' & EP & ES & EB & EE & EL & REST).
      exists LITP', LITSZ', LITB', LBE', LOC'. subst ws2.
      cbv [wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in EP, ES, EB, EE, EL |- *.
      exact (conj EP (conj ES (conj EB (conj EE (conj EL REST))))). }
    eapply (p_mid m6 p0 p1 p2 huv lev fev ws2 r r2 nbSeq jA jB w0 MXD);
      [exact DB4| exact FRA4| exact XM4| exact XN4| exact XP4| exact XS4| exact KEEP2| exact HINV4| exact KB| exact RL| exact PL4| exact R2R| exact NBR| exact NZD| exact TABS4]. }
    assert (N9 : 9 <= nbSeq) by (clear - KN NBR; zify_cond KN; rewrite signed_lit in KN by (clear - NBR; lia); exact KN).
    (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    db_chk m3 (DCTX + 16) UD RD2 DG.                           (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    unfold fk_held in PTRS.
    zstep.                                                     (* [comment removed for export] *)
    gf_unhold.
    assert (NNZ : nbSeq <> 0) by (clear - N9; lia).
    destruct (NZD NNZ) as [DN0 CN0]. pose proof (DNB DN0) as HBB.
    assert (TOF : seqhdr_tab m3 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2) by (destruct TABS as [(NZ0 & _)|(_ & _ & T2 & _)]; [exfalso; exact (NNZ NZ0)| exact T2]).
    destruct (AZ_dblock_f.db_tab_ready fflag rng_fs L RNG LB tp SPV SPA lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF SHF FLG CTX
                m3 K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 (8 * (1 + 2^8)) TOF eq_refl ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; lia) ltac:(unfold DCTX_entropy_OFTable; reflexivity)
                ltac:(right; left; repeat split; reflexivity) UD ARO HBB) as (OFT & tOF & EP2 & OTA & ORG & OOFF & _ & _ & OARO & OIN & OM8).
    pose proof OTA as [_ OOK]. destruct (seq_tbl_len K_OF tOF OOK) as [OLEN OLR]. cbn [kind_maxLog] in OLR.
    assert (OPW : 2 ^ st_log tOF <= 2 ^ 8) by (apply Z.pow_le_mono_r; clear - OLR; lia).
    assert (OPL : 1 <= 2 ^ st_log tOF) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; clear - OLR; lia).
    assert (OHI : OFT + 2056 < 2^47).
    { destruct OIN as [(bb & Hb & Hb1 & Hb2)|HI]; [| unfold AIMG_HI in HI; clear - HI; lia].
      destruct Hb as [<- | Hb]; [cbn [ab_addr ab_size] in Hb1, Hb2; clear - Hb2 F3 ATR; lia|].
      pose proof (fk_ablk_lits _ _ (LBH bb Hb)) as BL. clear - BL Hb2 ATR. lia. }
    zstep.                                                     (* [comment removed for export] *)
    unfold zd_offinfo_stmtA, APZD_OFFINFO in OFFINFO.
    eapply evtF_cut.
    { eapply (OFFINFO RNG) with (SPV := SPA) (OFT := OFT) (t := tOF) (lo := lo);
      lazymatch goal with
      | |- seq_tbl_at _ _ _ _ _ => exact OTA
      | |- 4096 <= OFT => exact (proj1 ORG)
      | |- OFT + _ < _ => exact OHI
      | |- 0 <= SPA < _ => clear - G2 G3 SPH LO0; lia
      | |- stk _ _ lo SPA => exact STL
      | |- lo <= SPA - _ => clear - G2; lia
      | |- SPA < _ => clear - G3 SPH; lia
      | |- AZ_blk_iface.off_stack _ _ _ _ => unfold AZ_blk_iface.off_stack; unfold AZ_seq_iface.off_stack in OOFF; clear - OOFF OPW OPL; lia
      | |- aro _ _ _ _ => exact OARO
      | |- art _ => pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & RA & RB & RC & RD & RE & RF & RG & _); unfold art; split; [exact RA|]; split; [exact RB|]; split; [exact RD|]; split; [exact RF|]; split; [exact RG| exact RC]
      | |- astk _ _ _ => split; [unfold KHIGH; exact KLO| split; [eapply rng_sub'; [exact RSTK| clear - G2 G3; lia]| exact RI]]
      | |- mem_inv _ _ => exact MI
      | |- OFT mod 4 = 0 => clear - OM8; Z.div_mod_to_equations; lia      (* [comment removed for export] *)
      | |- _ = _ => first [reflexivity| exact EP2| symmetry; exact EP2]
      | |- ?G => idtac "LEFT:" G
      end. }
    cbv beta. intros ms' PO.
    destruct PO as (z5 & z6 & z7 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & z28 & z29 & z30 & z31 & m5 & -> & MU5 & WM5 & MI5 & ST5).
    rd_retlit.
    (* [comment removed for export] *)
    assert (DB5 : DBB p0 p1 p2 huv lev fev wsv m5) by exact (dbb_keep_stk p0 p1 p2 huv lev fev wsv m3 m5 DBI MU5 WM5 MI5 ST5).
    assert (DJ5 : forall X n, (X + n <= SPA - 16 \/ SPA <= X) -> disjoint_from [(SPA - 16, SPA)] X n) by (intros X n A; cbn; split; [exact A| exact I]).
    assert (FRA5 : FRAME9 m5 jA jB MXD)
      by (eapply rw_cells_transport; [exact FRA| exact MU5| exact WM5| apply DJ5; right; clear; lia]).
    assert (XM5 : rw_cells bsegs m5 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU5| exact WM5| apply DJ5; left; csz; clear - F3 G1 G2; lia]).
    assert (XN5 : rw_cells bsegs m5 (FF + 32) [C4 (Z_to_bv 64 nbSeq)]) by (eapply rw_cells_transport; [exact XN| exact MU5| exact WM5| apply DJ5; left; csz; clear - F3 G1 G2; lia]).
    assert (XP5 : rw_cells bsegs m5 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU5| exact WM5| apply DJ5; left; csz; clear - F3 G1 G2; lia]).
    assert (XS5 : rw_cells bsegs m5 SHF BSH4) by (eapply rw_cells_transport; [exact XS| exact MU5| exact WM5| apply DJ5; left; csz; clear - GS KLO G2; lia]).
    assert (HINV5 : HUFINVw m5 DCTX huv lev) by (eapply hufw_fine; [exact HINV| exact MU5|]; intros x Hx; cbn [outside]; clear - Hx OFFD G2 G3; lia).
    assert (TABS5 : TABSX m5 p0 p1 p2 fev nbSeq).
    { assert (OUT : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside [(SPA - 16, SPA)] x) by (intros x Hx; cbn [outside]; clear - Hx OFFD G2 G3; lia).
      destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)]; [exfalso; exact (NNZ NZ0)|].
      right. split; [exact NZ1|].
      split; [| split]; (eapply db_seqhdr_tab_fine; [eassumption| | exact MU5| exact OUT| |]);
        first [ split; [first [apply all_default_at| apply aof_default_at| apply aml_default_at]; exact MI5| first [apply LL_default_ok| apply OF_default_ok| apply ML_default_ok]]
              | unfold DCTX_entropy_LLTable, DCTX_entropy_OFTable, DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia ]. }
    clear PTRS H1 FP H3 H5 ESEQ EHUF EREP EWK EPAD XB SRCB BUF STL SAV STG AH FFR MU WM UD US UB ARO AZS AHD AHS AHB MI.
    clear FRA XM XN XP XS HINV TABS DBI TOF OTA OARO OIN OOFF OM8.
    rename DB5 into DBI. rename FRA5 into FRA. rename XM5 into XM. rename XN5 into XN. rename XP5 into XP. rename XS5 into XS. rename HINV5 into HINV. rename TABS5 into TABS.
    pose proof DBI as I. open_dbb I.
    fk_hold DBI. fk_hold KEEP. fk_hold PLACED. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS. fk_hold KC. fk_hold EMXD. fk_hold INCONS.
    fk_hold MU5. fk_hold WM5. fk_hold ST5. fk_hold DJ5. fk_hold OHI. fk_hold ORG. fk_hold EP2.
    fk_hold H1. fk_hold H3. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (db_sh_rd0s mx DCTX 95992 (DCTX + 30204) UD ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
      pose proof (db_sh_rng1 RNG DCTX (DCTX + 30204) RD2 (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz end.
    (* [comment removed for export] *)
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
    zstep; if_false.                                           (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct H5 as [H5C WL']. h5_open wsv WL'.
    pose proof (munch_refl [(DCTX + 30204, DCTX + 30208)] m5) as MU34. pose proof (wmono_refl bsegs m5) as WM34. fk_hold FRA.
    zstep.                                                     (* [comment removed for export] *)
    unfold fk_held in FRA.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    gf_unhold.
    lazymatch type of H5C with rw_cells _ _ _ ?cs => let wl := cells_words cs in assert (H54 : dctx_h5 bsegs m6 DCTX wl) by (split; [exact H5C| reflexivity]) end.
    lazymatch type of H54 with dctx_h5 _ _ _ ?wl => set (ws2 := wl) in H54 end.
    assert (DB4 : DBB p0 p1 p2 huv lev fev ws2 m6).
    { eapply (dbb_keep p0 p1 p2 huv lev fev _ ws2 m5 m6); [exact DBI| exact MU34| exact WM34| exact MI| exact H54|].
      apply Forall_cons; [cbn [fst snd]; split; [clear; lia| right; right; right; clear; lia]| apply Forall_nil]. }
    assert (KEEP2 : forall i, h5_block_owned i = false -> wnth ws2 i = wnth ws i).
    { intros i Hi. specialize (KEEP i Hi). subst ws2. do 44 (destruct i as [|i]; [first [discriminate Hi | exact KEEP]|]). exact KEEP. }
    assert (HINV4 : HUFINVw m6 DCTX huv lev) by (eapply hufw_fine; [exact HINV| exact MU34|]; intros x Hx; cbn [outside]; clear - Hx; lia).
    assert (XM4 : rw_cells bsegs m6 FF [C8 w0]) by (eapply rw_cells_transport; [exact XM| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XN4 : rw_cells bsegs m6 (FF + 32) [C4 (Z_to_bv 64 nbSeq)]) by (eapply rw_cells_transport; [exact XN| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XP4 : rw_cells bsegs m6 (FF + 56) [C8 (Z_to_bv 64 FLG)]) by (eapply rw_cells_transport; [exact XP| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - D5; split; [lia| exact I]]).
    assert (XS4 : rw_cells bsegs m6 SHF BSH4) by (eapply rw_cells_transport; [exact XS| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - DCSH; split; [lia| exact I]]).
    assert (TABS4 : (nbSeq = 0 /\ atbl_seq m6 DCTX p0 p1 p2 fev)
                    \/ (nbSeq <> 0 /\ seqhdr_tab m6 DCTX K_LL DCTX_entropy_LLTable APZD_LL_DEFAULT LL_defaultDTable p0 /\
                                      seqhdr_tab m6 DCTX K_OF DCTX_entropy_OFTable APZD_OF_DEFAULT OF_defaultDTable p2 /\
                                      seqhdr_tab m6 DCTX K_ML DCTX_entropy_MLTable APZD_ML_DEFAULT ML_defaultDTable p1)).
    { assert (OUT : forall x, DCTX + 32 <= x < DCTX + 10296 -> outside [(DCTX + 30204, DCTX + 30208)] x) by (intros x Hx; cbn [outside]; clear - Hx; lia).
      destruct TABS as [(NZ0 & T0)|(NZ1 & T1 & T2 & T3)].
      - left. split; [exact NZ0| eapply db_atbl_seq_fine; [exact T0| exact MU34| assumption| exact OUT]].
      - right. split; [exact NZ1|]. assert (MI4 : mem_inv bsegs m6) by assumption.
        split; [| split]; (eapply db_seqhdr_tab_fine; [eassumption| | exact MU34| exact OUT| |]);
          first [ split; [first [apply all_default_at| apply aof_default_at| apply aml_default_at]; exact MI4| first [apply LL_default_ok| apply OF_default_ok| apply ML_default_ok]]
                | unfold DCTX_entropy_LLTable, DCTX_entropy_OFTable, DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia ]. }
    assert (W17 : wnth ws2 H5_ddictIsCold = Z_to_bv 64 0) by reflexivity.
    assert (FRA4 : FRAME9 m6 jA jB MXD)
      by (eapply rw_cells_transport; [exact FRA| exact MU34| exact WM34| csz; cbn [disjoint_from]; clear - OFFD G2 G3; split; [lia| exact I]]).
    assert (PL4 : declit_placed DCTX DST CAP (SRC + ip) cbs ws2).
    { pose proof PLACED as Q. destruct Q as (LITP' & LITSZ' & LITB' & LBE' & LOC' & EP & ES & EB & EE & EL & REST).
      exists LITP', LITSZ', LITB', LBE', LOC'. subst ws2.
      cbv [wnth nth H5_litPtr H5_litSize H5_litBuffer H5_litBufferEnd H5_litBufferLocation] in EP, ES, EB, EE, EL |- *.
      exact (conj EP (conj ES (conj EB (conj EE (conj EL REST))))). }
    fk_hold DB4. fk_hold KEEP2. fk_hold HINV4. fk_hold XM4. fk_hold XN4. fk_hold XP4. fk_hold XS4. fk_hold TABS4. fk_hold W17. fk_hold PL4. fk_hold H54.
    fk_hold DBI. fk_hold KEEP. fk_hold PLACED. fk_hold HINV. fk_hold TABS. fk_hold NZD. fk_hold XM. fk_hold XN. fk_hold XP. fk_hold XS. fk_hold KC. fk_hold EMXD. fk_hold INCONS.
    fk_hold MU5. fk_hold WM5. fk_hold ST5. fk_hold DJ5. fk_hold OHI. fk_hold ORG. fk_hold EP2. fk_hold MU34. fk_hold H5C. fk_hold FRA.
    fk_hold H1. fk_hold H3. fk_hold ESEQ. fk_hold EHUF. fk_hold EREP. fk_hold EWK. fk_hold EPAD. fk_hold XB. fk_hold SRCB. fk_hold BUF. fk_hold STL. fk_hold SAV. fk_hold STG.
    fk_hold AH. fk_hold FFR. fk_hold MU. fk_hold WM. fk_hold US. fk_hold UB. fk_hold ARO. fk_hold AZS. fk_hold AHD. fk_hold AHS. fk_hold AHB. fk_hold PTRS. fk_hold FP.
    fk_hold FL. fk_hold LL. fk_hold FLSH. fk_hold DCSH. fk_hold WIN. fk_hold OFFD. fk_hold OFFB. fk_hold OFFSRC. fk_hold BD. fk_hold BSRC. fk_hold SRCD.
    fk_hold DNULL. fk_hold DNN. fk_hold D1. fk_hold D4. fk_hold D5. fk_hold S1. fk_hold S4. fk_hold S5. fk_hold OUTB. fk_hold F1. fk_hold F5. fk_hold F6. fk_hold L0. fk_hold L1. fk_hold L2. fk_hold L3. fk_hold L4.
    fk_hold R_src. fk_hold R_out. fk_hold RF1. fk_hold RF3. fk_hold LBH. fk_hold ASH. fk_hold RFS. fk_hold SPT. fk_hold RSTKT.
    zstep. zstep.                                              (* [comment removed for export] *)
    zstep.
    gf_unhold.
    zstep; if_cases KG.                                        (* [comment removed for export] *)
    { eapply (p_long m6 p0 p1 p2 huv lev fev ws2 r r2 nbSeq jA jB w0 MXD);
        [exact DB4| exact FRA4| exact XM4| exact XN4| exact XP4| exact XS4| exact KEEP2| exact W17| exact HINV4| exact KB| exact EMXD| exact RL| exact PL4| exact R2R| exact NBR| exact NZD| exact TABS4]. }
    zstep.                                                     (* [comment removed for export] *)
    eapply (p_mid m6 p0 p1 p2 huv lev fev ws2 r r2 nbSeq jA jB w0 MXD);
      [exact DB4| exact FRA4| exact XM4| exact XN4| exact XP4| exact XS4| exact KEEP2| exact HINV4| exact KB| exact RL| exact PL4| exact R2R| exact NBR| exact NZD| exact TABS4].
  Qed.
End DB.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
