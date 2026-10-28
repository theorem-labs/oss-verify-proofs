(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseWalkMem FseRdKit FseRdKit2 ZdWalkKit MemRange SepHide ZdSeqBuildW.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_bfse_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require AZ_fserd_err.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AZ_kx AZ_blk_iface AZ_blk_iface2 AZ_fserd_iface AZ_bst_env AZ_bst_a AZ_bst_b AZ_bst_c.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kxa_norm ::= unfold shspan in *.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_hide segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_hide segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_hide segs m m' MU WM.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Notation zlen l := (Z.of_nat (length l)).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.
Notation BF5 := (Z_to_bv 8 18446744073709551605).

Notation MAGIC := (Z_to_bv 64 0x41b58ab3).
Notation RETIRED := (Z_to_bv 64 0x45e0360e).
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF2 := (Z_to_bv 8 18446744073709551602).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).
Notation B02 := (Z_to_bv 8 2).
Notation B04 := (Z_to_bv 8 4).

Section CANSEC1. Context {rc : runConstT}.

Section BS.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis FRL : fake_release_law AI fflag.
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
            (m0 : amem) (SPV SPA lo FF SHF FLG : Z)
            (DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind) (dt0 wb0 : list byte) (srcb : list Z) (frw oldp nbw coldw : word).
  (* [comment removed for export] *)
  Hypothesis LD0 : zlen dt0 = 8 + 8 * 2^(kind_maxLog k).
  Hypothesis LW0 : 626 <= zlen wb0.
  Hypothesis FBY : Forall (fun c => 0 <= c < 256) srcb.
  Hypothesis SLEN : zlen srcb <= 1048576.
  Hypothesis TYR : 0 <= ty <= 3.
  Hypothesis DTP8 : DTP mod 8 = 0.
  Hypothesis DTS4 : DTS mod 4 = 0.      (* [comment removed for export] *)
  Hypothesis WAL2 : W mod 2 = 0.
  Hypothesis BASE4 : BASE mod 4 = 0.
  Hypothesis OLDP : frw <> Z_to_bv 64 0 -> 4096 <= bv_unsigned oldp < 2^47.
  (* [comment removed for export] *)
  Hypothesis G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 5136 /\ SPV - 208 <= SPA <= SPV - 192 /\ SPA mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0.
  Hypothesis G_dts : ablk DTS (DTS + zlen dt0) /\ (DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS) /\ (FF + 256 <= DTS \/ DTS + zlen dt0 <= FF) /\ 4096 <= DTS /\ DTS + zlen dt0 < 2^47.
  Hypothesis G_dtp : ablk DTP (DTP + 8) /\ (DTP + 8 <= lo \/ SPV + 16 <= DTP) /\ (FF + 256 <= DTP \/ DTP + 8 <= FF) /\ 4096 <= DTP /\ DTP + 8 < 2^47.
  Hypothesis G_w : ablk W (W + zlen wb0) /\ (W + zlen wb0 <= lo \/ SPV + 16 <= W) /\ (FF + 256 <= W \/ W + zlen wb0 <= FF) /\ 4096 <= W /\ W + zlen wb0 < 2^47.
  Hypothesis G_src : ablk SRC (SRC + zlen srcb) /\ (SRC + zlen srcb <= lo \/ SPV <= SRC) /\ (FF + 256 <= SRC \/ SRC + zlen srcb <= FF)
                     /\ 4096 <= SRC /\ SRC + zlen srcb < 2^47.
  Hypothesis G_img : 4096 <= BASE /\ BASE + 212 <= AIMG_HI /\ 4096 <= BITS /\ BITS + 53 <= AIMG_HI.
  Hypothesis G_sep : (DTS + zlen dt0 <= DTP \/ DTP + 8 <= DTS) /\ (DTS + zlen dt0 <= W \/ W + zlen wb0 <= DTS) /\ (DTS + zlen dt0 <= SRC \/ SRC + zlen srcb <= DTS)
                     /\ (DTP + 8 <= W \/ W + zlen wb0 <= DTP) /\ (DTP + 8 <= SRC \/ SRC + zlen srcb <= DTP) /\ (W + zlen wb0 <= SRC \/ SRC + zlen srcb <= W).
  Hypothesis G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ SHF = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ.
  Hypothesis G_flg : FLG = fflag L 2 FF /\ ablk FLG (FLG + 1) /\ FLG + 1 <= ATOP /\ (al_fake L <= FLG /\ FLG + 1 <= al_fake L + FAKESZ)
                     /\ (forall b, In b (FB2 FF :: LB) -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG)
                     /\ (DTS + zlen dt0 <= FLG \/ FLG + 1 <= DTS) /\ (DTP + 8 <= FLG \/ FLG + 1 <= DTP) /\ (W + zlen wb0 <= FLG \/ FLG + 1 <= W).
  (* [comment removed for export] *)
  Hypothesis RSTK : rng RNG lo (SPV + 16 - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis R_dts : rng RNG DTS (zlen dt0) /\ rng RNG (shad DTS) (shspan DTS (zlen dt0)).
  Hypothesis R_dtp : rng RNG DTP 8 /\ rng RNG (shad DTP) (shspan DTP 8).
  Hypothesis R_w : rng RNG W (zlen wb0) /\ rng RNG (shad W) (shspan W (zlen wb0)).
  Hypothesis R_src : rng RNG SRC (zlen srcb) /\ rng RNG (shad SRC) (shspan SRC (zlen srcb)).
  Hypothesis HSRC : ahull RNG m0 SRC (zlen srcb).
  Hypothesis R_img : aro RNG m0 BASE (4 * zlen (kind_base k)) /\ aro RNG m0 BITS (zlen (kind_bits k)).
  Hypothesis R_ff : rng RNG FF 256 /\ rng RNG SHF 32 /\ rng RNG FLG 1.
  Hypothesis LBH : ablkLB LB.
  Hypothesis G_in : ainblk LB DTS (zlen dt0) /\ ainblk LB DTP 8 /\ ainblk LB W (zlen wb0) /\ (0 < zlen srcb -> ainimg LB SRC (zlen srcb)).
  (* [comment removed for export] *)
  Hypothesis G_af : ashort LB 3 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ KHIGH <= lo.
  Hypothesis TP : tp = Z_to_bv 64 ATP.

  Notation WR := [(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0)].
  Notation POST := (zd_buildseq_postA AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV DTS DTP W DFLT k ty (zlen srcb) frw oldp dt0 (length wb0) lo m0).

  Notation BS_EXIT := (AZ_bst_a.bs_exitA AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo FF SHF FLG
                        DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb frw oldp G_lo G_dts G_dtp G_w G_img G_sep G_ff G_flg RSTK RI R_img R_ff LBH).
  Notation BINV := (AZ_bst_a.BINV AI L RNG st LB m0 SPV FF DTS DTP W dt0 wb0).
  Notation BINV_STEP := (AZ_bst_b.binv_step AI fflag L RNG st LB m0 SPV SPA lo FF SHF FLG DTS DTP SRC W BASE BITS dt0 wb0 srcb
                          G_lo G_dts G_dtp G_w G_src G_img G_sep G_ff G_flg R_dts R_dtp R_w R_ff LBH G_in).
  Notation BE := (AZ_bst_b.BE AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV SPA lo FF SHF FLG DTS DTP SRC W BASE BITS k dt0 wb0 srcb oldp nbw coldw).

  (* [comment removed for export] *)
  Notation STb pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 FF) x21 x22 (Z_to_bv 64 SHF) x24 x25 (Z_to_bv 64 SHB) x27 x28 x29 x30 x31)   (* [comment removed for export] *)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation CASE_ARGS f := (f AI fflag FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo FF SHF FLG DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb frw oldp nbw coldw) (only parsing).
  Notation CASE_ARGSR f := (f AI fflag rng_fs FRL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 SPV SPA lo FF SHF FLG DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb frw oldp nbw coldw) (only parsing).

  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FSERD : fse_read_any_stmtA AI rng_fs.
  Hypothesis BFSE : zd_buildfse_stmtA.

  (* [comment removed for export] *)
  Lemma bs_mainA : forall m1 (x1 x5 x6 x7 x16 x17 x28 x29 x30 x31 : word), BE m1 ->
    evtF bsegs RNG POST (STb 0x88e68 m1 x1 x5 x6 x7 (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 1) (Z_to_bv 64 18446744073709551603) (Z_to_bv 64 0x88cd8)
                             (Z_to_bv 64 18446744073709551602) (Z_to_bv 64 4) x16 x17 (Z_to_bv 64 FF) (Z_to_bv 64 ty) (Z_to_bv 64 (kind_max k)) frw
                             (Z_to_bv 64 SRC) (Z_to_bv 64 (zlen srcb)) (Z_to_bv 64 DFLT) x28 x29 x30 x31).
  Proof.
    intros until x31. intros I.
    zstep. bcase K1.                                        (* [comment removed for export] *)
    - rewrite signed_lit in K1 by (clear - TYR; lia).
      zstep. zstep. bcase K2.                               (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K2 by (clear - TYR; lia).
        eapply (CASE_ARGS AZ_bst_b.bs_repeatA); try eassumption. clear - K1 K2 TYR; lia.
      + rewrite ?unsigned_lit in K2 by (clear - TYR; lia).
        eapply (CASE_ARGSR AZ_bst_c.bs_compA); try eassumption.
    - rewrite signed_lit in K1 by (clear - TYR; lia).
      zstep. bcase K3.                                      (* [comment removed for export] *)
      + rewrite ?unsigned_lit in K3 by (clear - TYR; lia).
        eapply (CASE_ARGS AZ_bst_b.bs_rleA); try eassumption. clear - K1 K3 TYR; lia.
      + rewrite ?unsigned_lit in K3 by (clear - TYR; lia).
        eapply (CASE_ARGS AZ_bst_b.bs_basicA); try eassumption.
  Qed.
End BS.

Lemma ffr_pres_mono_nil2 : forall W LB (m m' : amem), ffr_pres [] LB m m' -> ffr_pres W LB m m'.
Proof.
  intros W LB m m' H. eapply AZ_bst_b.ffr_pres_mono; [| exact H]. intros a _. cbn. exact I.
Qed.

Lemma bytes_at_nil2 : forall (m m' : amem) A (bs : list byte), bytes_at bsegs m A bs -> length bs = 0%nat -> bytes_at bsegs m' A bs.
Proof. intros m m' A bs (B0 & B1 & B) L. destruct bs; [| discriminate L]. split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia. Qed.

Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM2K : forall k, Z.of_nat k < 4096 -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis FSERD : fse_read_any_stmtA AI rng_fs.
  Hypothesis BFSE : zd_buildfse_stmtA.

  Theorem zd_buildseq_proofA : zd_buildseq_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV lo DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb oldp nbw.
    intros DTA LD0 DTPC WA LW0 SB FBY SLEN BASEB BITSB ARGS TYR D4 D5 P4 P5 W4 W5 S4 S5 IBR ITR ST LOS LO4 SPH
           OD OP OW OS OB OT ADP ADW ADS ADB ADT ADV APW APS APB APT APV AWS AWB AWT AWV ASV
           AFP TP ARD IND ARP INP ARW INW ARS INS HSRC AROB AROT IMB IMT
           DTS4 DTP8 WAL2 BASE4 OLDP MI -> -> -> -> -> -> -> -> -> ->.     (* [comment removed for export] *)
    unfold off_stack in OD, OP, OW, OS, OB, OT. unfold apart in ADP, ADW, ADS, ADB, ADT, ADV, APW, APS, APB, APT, APV, AWS, AWB, AWT, AWV, ASV.
    hide_all_disj.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (bs_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [G1 G2].
    assert (LOS' : lo <= SPV - 176 - 4096) by (clear - LOS; lia).
    assert (LOC : ATOP <= lo) by (clear - BOT; lia).
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; clear - SPT LY3; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bspa_props SPV SP16) as (SPAB & SPA32 & _).
    assert (LOSb : lo <= SPV - 208 - 4096) by (clear - LOS; lia).
    unfold APZD_BUILDSEQ.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (bs_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOSb LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & jB & -> & MU1 & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    clear C0 GOT RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
    (* [comment removed for export] *)
    pose proof (ASH 2 ltac:(lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM2K (Z.to_nat (4096 - 3)) ltac:(lia)) as SMC. unfold stack_malloc_2k_stmt in SMC.
      eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (BSPA SPV)) by lia;
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS| lia| unfold SMK_STACK; lia | lazymatch goal with |- ?G => idtac "LEFT:" G end]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F256 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (BSPA SPV)) in ST2, HPR2, MUF2 by lia.
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SAV1 ltac:(left; left; cbn; lia)) as SAV2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (bs_hdr gp tp FR fc SPV lo SP16 LOSb LOC RNG RSTK);
        [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact MI2| exact FH| exact FC| exact F256| exact RFF| exact RSFF]. }
    cbv beta. intros ms' (m3 & jB' & j3 & j4 & -> & MU3 & WM3 & MI3 & FRA3 & STL3 & FFC3 & SHF3).
    (* [comment removed for export] *)
    pose proof (fk_ablk_lits _ _ FH) as FL.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (BSF : SHB + 788992 <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 32 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; clear - FL ATR; Z.div_mod_to_equations; lia).
    destruct (FFLAG _ _ _ _ _ 2 FF 256 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
    pose proof (fk_ablk_lits _ _ LBK) as LL. pose proof (LAP _ ltac:(left; reflexivity)) as LFF. cbn [ab_addr ab_size] in LFF.
    assert (KM : 0 <= kind_max k <= 52 /\ 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
    assert (P8K : 256 <= 2 ^ kind_maxLog k <= 512) by (destruct k; cbn; lia).
    assert (LKB : zlen (kind_bits k) = kind_max k + 1 /\ zlen (kind_base k) = kind_max k + 1) by (destruct k; split; reflexivity). destruct LKB as [LKB1 LKB2].
    pose proof (ARD ltac:(clear - LD0 P8K; lia)) as (ABD & UD0 & RD1 & RD2). pose proof (ARP ltac:(clear; lia)) as (ABP & UP0 & RP1 & RP2).
    pose proof (ARW ltac:(clear - LW0; lia)) as (ABW & UW0 & RW1 & RW2). pose proof ARS as (ABS & US0 & RS1 & RS2).
    pose proof AROB as (UB0 & RB1 & RB2). pose proof AROT as (UT0 & RT1 & RT2).
    pose proof (fk_ablk_lits _ _ ABD) as DL. pose proof (fk_ablk_lits _ _ ABP) as PL. pose proof (fk_ablk_lits _ _ ABW) as WL. pose proof (fk_ablk_lits _ _ ABS) as SL.
    unfold AIMG_HI in IMB, IMT. assert (KHI' : 17594333495296 <= lo) by (unfold KHIGH in KHI; exact KHI).
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DTS (zlen dt0) AH2 IND ltac:(clear - LD0 P8K; lia)) as APD.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DTP 8 AH2 INP ltac:(clear; lia)) as APP.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ W (zlen wb0) AH2 INW ltac:(clear - LW0; lia)) as APWF.
    assert (APS' : FF + 256 <= SRC \/ SRC + zlen srcb <= FF).
    { destruct INS as [(b & Hb & B1 & B2)|[IM1 IM2]].
      - pose proof (FFD b Hb) as HB. clear - HB B1 B2. lia.
      - unfold AIMG_HI in IM2. clear - IM2 FHa DB. lia. }
    (* [comment removed for export] *)
    assert (G_lo : ATOP + 4096 <= lo /\ lo <= SPV - 5136 /\ SPV - 208 <= BSPA SPV <= SPV - 192 /\ BSPA SPV mod 32 = 0 /\ SPV + 16 < 2^47 /\ SPV mod 16 = 0).
    { clear - BOT LOS SPAB SPA32 SPH SP16. repeat split; lia. }
    assert (G_dts : ablk DTS (DTS + zlen dt0) /\ (DTS + zlen dt0 <= lo \/ SPV + 16 <= DTS) /\ (FF + 256 <= DTS \/ DTS + zlen dt0 <= FF) /\ 4096 <= DTS /\ DTS + zlen dt0 < 2^47).
    { split; [exact ABD|]. split; [unfold hidden in OD, ADV; clear - OD ADV LD0 P8K; lia|]. split; [clear - APD; lia|]. clear - D4 D5; lia. }
    assert (G_dtp : ablk DTP (DTP + 8) /\ (DTP + 8 <= lo \/ SPV + 16 <= DTP) /\ (FF + 256 <= DTP \/ DTP + 8 <= FF) /\ 4096 <= DTP /\ DTP + 8 < 2^47).
    { split; [exact ABP|]. split; [unfold hidden in OP, APV; clear - OP APV; lia|]. split; [clear - APP; lia|]. clear - P4 P5; lia. }
    assert (G_w : ablk W (W + zlen wb0) /\ (W + zlen wb0 <= lo \/ SPV + 16 <= W) /\ (FF + 256 <= W \/ W + zlen wb0 <= FF) /\ 4096 <= W /\ W + zlen wb0 < 2^47).
    { split; [exact ABW|]. split; [unfold hidden in OW, AWV; clear - OW AWV LW0; lia|]. split; [clear - APWF; lia|]. clear - W4 W5; lia. }
    assert (G_src : ablk SRC (SRC + zlen srcb) /\ (SRC + zlen srcb <= lo \/ SPV <= SRC) /\ (FF + 256 <= SRC \/ SRC + zlen srcb <= FF) /\ 4096 <= SRC /\ SRC + zlen srcb < 2^47).
    { split; [exact ABS|]. split; [unfold hidden in OS; exact OS|]. split; [exact APS'|]. clear - S4 S5; lia. }
    assert (G_img : 4096 <= BASE /\ BASE + 212 <= AIMG_HI /\ 4096 <= BITS /\ BITS + 53 <= AIMG_HI) by (unfold AIMG_HI; clear - IBR ITR IMB IMT; lia).
    assert (G_sep : (DTS + zlen dt0 <= DTP \/ DTP + 8 <= DTS) /\ (DTS + zlen dt0 <= W \/ W + zlen wb0 <= DTS) /\ (DTS + zlen dt0 <= SRC \/ SRC + zlen srcb <= DTS)
                    /\ (DTP + 8 <= W \/ W + zlen wb0 <= DTP) /\ (DTP + 8 <= SRC \/ SRC + zlen srcb <= DTP) /\ (W + zlen wb0 <= SRC \/ SRC + zlen srcb <= W)).
    { unfold hidden in ADP, ADW, ADS, APW, APS, AWS. split; [exact ADP|]. split; [exact ADW|]. split; [exact ADS|]. split; [exact APW|]. split; [exact APS| exact AWS]. }
    assert (G_ff : ablk FF (FF + 256) /\ FF mod 256 = 0 /\ FF + 256 <= ATOP /\ Z.shiftr FF 3 + SHB = shad FF /\ al_fake L <= FF /\ FF + 256 <= al_fake L + FAKESZ).
    { split; [exact FH|]. split; [exact F256|]. split; [exact FC|]. split; [unfold shad, ASHOFF; lia|]. split; [exact FFA1| exact FFA2]. }
    assert (G_flg : fflag L 2 FF = fflag L 2 FF /\ ablk (fflag L 2 FF) (fflag L 2 FF + 1) /\ fflag L 2 FF + 1 <= ATOP /\ (al_fake L <= fflag L 2 FF /\ fflag L 2 FF + 1 <= al_fake L + FAKESZ)
                    /\ (forall b, In b (FB2 FF :: LB) -> fflag L 2 FF + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L 2 FF)
                    /\ (DTS + zlen dt0 <= fflag L 2 FF \/ fflag L 2 FF + 1 <= DTS) /\ (DTP + 8 <= fflag L 2 FF \/ fflag L 2 FF + 1 <= DTP) /\ (W + zlen wb0 <= fflag L 2 FF \/ fflag L 2 FF + 1 <= W)).
    { split; [reflexivity|]. split; [exact LBK|]. split; [exact LTOP|]. split; [exact LFA|]. split; [exact LAP|].
      destruct IND as (bd & Hbd & Bd1 & Bd2). destruct INP as (bp & Hbp & Bp1 & Bp2). destruct INW as (bw & Hbw & Bw1 & Bw2).
      pose proof (LAP bd ltac:(right; exact Hbd)) as Ld. pose proof (LAP bp ltac:(right; exact Hbp)) as Lp. pose proof (LAP bw ltac:(right; exact Hbw)) as Lw.
      clear - Ld Lp Lw Bd1 Bd2 Bp1 Bp2 Bw1 Bw2. repeat split; lia. }
    assert (RSTK16 : rng RNG lo (SPV + 16 - lo)) by (eapply rng_sub'; [exact RSTKT| clear - SPT KHI'; lia]).
    assert (R_dts : rng RNG DTS (zlen dt0) /\ rng RNG (shad DTS) (shspan DTS (zlen dt0))) by (split; [exact RD1| exact RD2]).
    assert (R_dtp : rng RNG DTP 8 /\ rng RNG (shad DTP) (shspan DTP 8)) by (split; [exact RP1| exact RP2]).
    assert (R_w : rng RNG W (zlen wb0) /\ rng RNG (shad W) (shspan W (zlen wb0))) by (split; [exact RW1| exact RW2]).
    assert (R_src : rng RNG SRC (zlen srcb) /\ rng RNG (shad SRC) (shspan SRC (zlen srcb))) by (split; [exact RS1| exact RS2]).
    assert (R_img : aro RNG m BASE (4 * zlen (kind_base k)) /\ aro RNG m BITS (zlen (kind_bits k))) by (split; [exact AROB| exact AROT]).
    assert (R_ff : rng RNG FF 256 /\ rng RNG (Z.shiftr FF 3 + SHB) 32 /\ rng RNG (fflag L 2 FF) 1).
    { split; [exact RFF|]. split; [replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia); exact RSFF| exact RL]. }
    assert (G_in : ainblk LB DTS (zlen dt0) /\ ainblk LB DTP 8 /\ ainblk LB W (zlen wb0) /\ (0 < zlen srcb -> ainimg LB SRC (zlen srcb))).
    { split; [exact IND|]. split; [exact INP|]. split; [exact INW| intros _; exact INS]. }
    assert (G_af : ashort LB 3 /\ rng_fs L RNG /\ SPV + 16 < al_top L /\ rng RNG lo (al_top L - lo) /\ KHIGH <= lo).
    { split; [exact ASH|]. split; [exact RFS|]. split; [exact SPT|]. split; [exact RSTKT| exact KHI]. }
    (* [comment removed for export] *)
    assert (FFR02 : ffr_pres [] LB m m2).
    { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; clear - BOT LOS; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2. }
    assert (FFR03 : ffr_pres [(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0)] LB m m3).
    { apply ffr_pres_mono_nil2.
      eapply (fk_ffr_fin AI L RNG st LB m m2 m3 2 FF 256 (Z.shiftr FF 3 + SHB) 32 [] [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36)]);
        [ exact AH2 | exact LBH | exact FH | clear - F256; Z.div_mod_to_equations; lia | unfold shad, ASHOFF; lia | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia| left; unfold KEND in SPK; clear - BOT LOS SPAB SPK; lia]|];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact FH | clear; lia]]]|];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 256); split; [exact FH | clear; lia]]]| constructor]
        | constructor
        | exact FFR02
        | cbn [app]; eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia
        | exact WM3 ]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU03 : munch ([(DTS, DTS + zlen dt0); (DTP, DTP + 8); (W, W + zlen wb0); (SPV - 5136, SPV)] ++ fake_area L) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx SPAB LOS; cbn [outside app fake_area] in *; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx SPAB LOS; cbn [outside app fake_area] in *; unfold SMK_STACK in *; lia|].
      eapply munch_weaken; [| exact MU3]; intros x Hx; clear - Hx FFA1 FFA2 SPAB LOS BOT F256 FHb FA8;
        cbn [outside app fake_area] in *; rewrite ?shad_div in *; rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold FAKESZ, ASHOFF in *;
        Z.div_mod_to_equations; lia. }
    assert (WM03 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn [fst snd]; left; left; cbn; unfold KEND in SPK; clear - BOT LOS SPAB SPK LY3 SPT; lia|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd] | constructor].
      replace (Z.shiftr FF 3 + SHB + 32 - (Z.shiftr FF 3 + SHB)) with 32 by (clear; lia). replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; lia).
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F256; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (BI3 : AZ_bst_a.BINV AI L RNG st LB m SPV FF DTS DTP W dt0 wb0 m3).
    { split; [exact AH3|]. split; [exact FFR03|]. split; [exact MU03|]. split; [exact WM03| exact MI3]. }
    (* [comment removed for export] *)
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 208, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [clear - HX Hn LOS; lia| exact I]. }
    assert (D3 : forall X n, (X + n <= lo \/ SPV <= X) -> (X + n <= FF \/ FF + 256 <= X) ->
                 (X + n <= 6443008 \/ (6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP) \/ lo <= X) -> 0 <= n ->
                 disjoint_from [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] X n).
    { intros X nn HX HF HB Hn. cbn [disjoint_from]. split; [clear - HX Hn SPAB LOS; lia|]. split; [clear - HF Hn; lia|]. split; [clear - HF Hn; lia|].
      split; [clear - HB BSF ATR Hn KHI'; lia| exact I]. }
    assert (MU13 : munch ([(SPV - 208, SPV)] ++ (fake_area L ++ [(BSPA SPV - SMK_STACK, BSPA SPV)]) ++
                          [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)]) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto|].
      eapply munch_weaken; [| exact MU3]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto. }
    assert (INLB : forall b, In b LB -> In b (FB2 FF :: LB)) by (intros b Hb; right; exact Hb).
    (* [comment removed for export] *)
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (BSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [exact SAV2| exact MU3| exact WM3| unfold BSAVED; cbn; clear - SPAB LOS BOT FHc BSF KHI'; lia]. }
    assert (STG3 : stk bsegs m3 (BSPA SPV + 88) (SPV + -104)).
    { eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn; clear - SPAB LOS BOT FHc BSF KHI'; lia]. }
    assert (XL3 : rw_cells bsegs m3 (fflag L 2 FF) [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_transport; [exact XL2| exact MU3| exact WM3| cbn; clear - LFF LL LTOP LOC LOS SPAB BSF ATR; lia]. }
    assert (ARGS3 : rw_cells bsegs m3 SPV [C8 nbw; C8 (Z_to_bv 64 W)]).
    { eapply rw_cells_transport; [| exact MU3| exact WM3| apply D3; [right; clear; lia| right; clear - FC BOT LOS; lia| right; right; right; clear - LOS; lia| clear; lia]].
      eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2); [| left; left; cbn; clear - SPAB SPH; lia].
      eapply rw_cells_transport; [exact ARGS| exact MU1| exact WM1| apply D1; [right; clear; lia| clear; lia]]. }
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 208, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb ATR BOT LOS. Z.div_mod_to_equations. lia. }
    assert (DS3' : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) ->
                 disjoint_from [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF in *.
      split; [left; clear - X0 Hn Hb ATR BOT LOS SPAB; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb HF F256; Z.div_mod_to_equations; lia| exact I]. }
    assert (DI13 : forall X n, 0 <= X -> 0 <= n -> X + n <= 6443008 ->
                 disjoint_from ([(SPV - 208, SPV)] ++ (fake_area L ++ [(BSPA SPV - SMK_STACK, BSPA SPV)]) ++
                                [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)]) X n
                 /\ disjoint_from ([(SPV - 208, SPV)] ++ (fake_area L ++ [(BSPA SPV - SMK_STACK, BSPA SPV)]) ++
                                [(BSPA SPV + 80, BSPA SPV + 88); (FF, FF + 24); (FF + 32, FF + 36); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 32)]) (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn XH. destruct LY5 as (_ & _ & FA1 & FA2). cbn [disjoint_from fake_area app]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      unfold ASHOFF, AIMG_HI, SMK_STACK, FAKESZ in *.
      split; repeat split; try exact I; clear - X0 Hn XH FL FABL FA1 FA2 ATR BOT LOS SPAB KHI'; Z.div_mod_to_equations; lia. }
    assert (U8T : forall X xs, u8arr bsegs m X xs -> ainblk LB X (zlen xs) -> (X + zlen xs <= lo \/ SPV <= X) -> (X + zlen xs <= FF \/ FF + 256 <= X) -> ablk X (X + zlen xs) -> u8arr bsegs m3 X xs).
    { intros X xs U IB HX HF HB. destruct U as [B WR]. pose proof (fk_ablk_lits _ _ HB) as XL.
      split; [| eapply wr_at_transport; [exact WR| exact WM03]].
      eapply bytes_at_transport; [| exact MU3| apply D3; [exact HX| exact HF| right; clear - XL; lia| clear; lia]].
      eapply (fk_bytes_pres AI); [exact HPR2| exact IB|].
      eapply bytes_at_transport; [exact B| exact MU1| apply D1; [exact HX| clear; lia]]. }
    pose proof (U8T DTS dt0 DTA IND ltac:(unfold hidden in OD; exact OD) ltac:(clear - APD; lia) ABD) as DTA3.
    pose proof (U8T W wb0 WA INW ltac:(unfold hidden in OW; exact OW) ltac:(clear - APWF; lia) ABW) as WA3.
    assert (DTPC3 : rw_cells bsegs m3 DTP [C8 oldp]).
    { eapply rw_cells_transport; [| exact MU3| exact WM3| change (Z.of_nat (cells_size [C8 oldp])) with 8; apply D3; [unfold hidden in OP; exact OP| clear - APP; lia| right; clear - PL; lia| clear; lia]].
      eapply (fk_cells_pres AI); [exact HPR2| exact INP|].
      eapply rw_cells_transport; [exact DTPC| exact MU1| exact WM1| change (Z.of_nat (cells_size [C8 oldp])) with 8; apply D1; [unfold hidden in OP; exact OP| clear; lia]]. }
    assert (UNT : forall X n, unpoisoned m X (X + n) -> ainblk LB X n -> 0 <= n -> 0 <= X -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) -> unpoisoned m3 X (X + n)).
    { intros X nn U IB Hn X0 Hb HF.
      eapply unpoisoned_munch; [| exact MU3| apply DS3'; [exact X0| exact Hn| exact Hb| exact HF]].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IB| exact Hn|].
      eapply unpoisoned_munch; [exact U| exact MU1| apply DS1; [exact X0| exact Hn| exact Hb]]. }
    pose proof (UNT DTS (zlen dt0) UD0 IND ltac:(clear - LD0 P8K; lia) ltac:(clear - DL; lia) ltac:(clear - D5; lia) ltac:(clear - APD; lia)) as UD3.
    pose proof (UNT DTP 8 UP0 INP ltac:(clear; lia) ltac:(clear - PL; lia) ltac:(clear - P5; lia) ltac:(clear - APP; lia)) as UP3.
    pose proof (UNT W (zlen wb0) UW0 INW ltac:(clear - LW0; lia) ltac:(clear - WL; lia) ltac:(clear - W5; lia) ltac:(clear - APWF; lia)) as UW3.
    destruct (DI13 BASE (4 * zlen (kind_base k)) ltac:(clear - IBR; lia) ltac:(clear - LKB2 KM; lia) ltac:(clear - IMB LKB2 KM; lia)) as [DB1 DB2].
    destruct (DI13 BITS (zlen (kind_bits k)) ltac:(clear - ITR; lia) ltac:(clear - LKB1 KM; lia) ltac:(clear - IMT LKB1 KM; lia)) as [DT1 DT2].
    assert (BASEB3 : bytes_at bsegs m3 BASE (u32s (map (Z_to_bv 64) (kind_base k))))
      by (eapply bytes_at_transport; [exact BASEB| exact MU13| rewrite u32s_length, length_map; replace (Z.of_nat (4 * length (kind_base k))) with (4 * zlen (kind_base k)) by (clear; lia); exact DB1]).
    assert (BITSB3 : bytes_at bsegs m3 BITS (map (Z_to_bv 8) (kind_bits k))) by (eapply bytes_at_transport; [exact BITSB| exact MU13| rewrite length_map; exact DT1]).
    pose proof (unpoisoned_munch _ _ _ _ _ UB0 MU13 DB2) as UB3. pose proof (unpoisoned_munch _ _ _ _ _ UT0 MU13 DT2) as UT3.
    assert (SBUS3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) srcb) /\ unpoisoned m3 SRC (SRC + zlen srcb)).
    { destruct (Z.eq_dec (zlen srcb) 0) as [Z0|NZ].
      - split.
        + apply (bytes_at_nil2 m). exact SB. rewrite length_map. clear - Z0; lia.
        + destruct US0 as (U0 & U1 & _). split; [exact U0|]. split; [exact U1|]. intros G HG. exfalso. clear - HG Z0. lia.
      - destruct INS as [IB|[IM1 IM2]].
        + split.
          * eapply bytes_at_transport; [| exact MU3| rewrite length_map; apply D3; [unfold hidden in OS; exact OS| clear - APS'; lia| right; clear - SL; lia| clear - NZ DB; lia]].
            eapply (fk_bytes_pres AI); [exact HPR2| rewrite length_map; exact IB|].
            eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply D1; [unfold hidden in OS; exact OS| clear - DB; lia]].
          * apply (UNT SRC (zlen srcb) US0 IB); [clear - DB; lia| clear - SL; lia| clear - S5; lia| clear - APS'; lia].
        + unfold AIMG_HI in IM2. destruct (DI13 SRC (zlen srcb) ltac:(clear - S4; lia) ltac:(clear - DB; lia) ltac:(exact IM2)) as [DX1 DX2]. split.
          * eapply bytes_at_transport; [exact SB| exact MU13| rewrite length_map; exact DX1].
          * exact (unpoisoned_munch _ _ _ _ _ US0 MU13 DX2). }
    destruct SBUS3 as [SB3 US3].
    (* [comment removed for export] *)
    eapply (bs_mainA AI fflag rng_fs FREL L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (BSPA SPV) lo FF (Z.shiftr FF 3 + SHB) (fflag L 2 FF)
              DTS DTP SRC W DFLT BASE BITS ty k dt0 wb0 srcb t5 oldp nbw t6); try eassumption.
    split; [exact BI3|]. split; [exact SAV3|]. split; [exists jA, jB'; exact FRA3|]. split; [exact STL3|]. split; [exact STG3|].
    split; [exists j3, j4; exact FFC3|]. split; [exact XL3|]. split; [exact SHF3|]. split; [exact DTA3|]. split; [exact DTPC3|]. split; [exact WA3|].
    split; [exact SB3|]. split; [exact BASEB3|]. split; [exact BITSB3|]. split; [exact ARGS3|].
    split; [exact UD3|]. split; [exact UP3|]. split; [exact UW3|]. split; [exact US3|]. split; [exact UB3| exact UT3].
  Qed.
End Thm.
End CANSEC1.
