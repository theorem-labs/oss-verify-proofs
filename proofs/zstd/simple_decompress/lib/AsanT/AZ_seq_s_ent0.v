(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase
     AZ_seq_s_sbase AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_last AZ_seq_s_xat AZ_seq_s_a1_at AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_ekit2 AZ_seq_s_lkit2 AZ_seq_s_akit2 AZ_seq_s_xkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)
Ltac sqs_ent_lastframe H := sqs_blob_seg H 11%nat 14%nat; sqs_blob_seg H 7%nat 10%nat; sqs_blob_seg H 0%nat 2%nat.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_ent0 : forall P,
  sqs_mem P -> sqs_ranges P -> sqs_side P -> sqs_sep P -> (v_nbSeq P <> 0 -> sqs_tables P) -> sqs_astat P -> sqs_asan P (v_m P) -> sqs_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA ->
  (v_nbSeq P <> 0 -> v_LLT P + 4104 <= 2^47 /\ v_OFT P + 2056 <= 2^47 /\ v_MLT P + 4104 <= 2^47) ->
  (v_nbSeq P <> 0 -> (v_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_LLT P) /\ (v_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= v_OFT P) /\
                    (v_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_MLT P)) ->
  sqs_at_last P -> sqs_at_fin P ->
  (forall OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = v_LOC P -> ai_I0 P OEND LLO LEND LOCV) ->
  v_CAP P = 0 -> sqs_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS TH3 TB3 LASTK FINK INITK C0.
  pose proof MEM as MEM0. pose proof RG as RG0. pose proof SD as SD0. pose proof SEP as SEP0. pose proof TBL as TBL0. pose proof AS as AS0. pose proof ASN as ASN0. pose proof PRO as PRO0.
  pose proof (sqs_static_m2 P) as STM0. pose proof (sqs_iinv_anchor P) as IANC. pose proof (sqs_asan_transport0 P) as AT0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_at_anchor sqs_at_last sqs_at_fin sqs_finv ai_I0 sqs_iregs sqs_ifrI sqs_imidA sqs_iffA] in *.
  cbn [app sqs_mem sqs_ranges sqs_side sqs_sep sqs_tables sqs_astat sqs_asan sqs_pro sqs_saved sqs_Wb sqs_post sqs_fe v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  intros ja jb jds jp jm x5 x6 x7 x11 x12 x13 x14 x17 x22 x26 x28 x29 x30 FR0 FF0 SH0 STK GAP SAV.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & XRD & MI). pose proof BUF as BUF0.
  destruct (h5_view2 m DCTX ws HH5) as (H5V & H5L). rewrite L4 in H5V. cbv beta delta [h5_vcells] in H5V. rewrite L1, L2, L3 in H5V. clear HH5.
  unfold dctx_ptrs, dctx_h1, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  destruct ASN as (ARD & AHD & ASQ & ATBL & ACL & AOUT & ALT & ALH & AZS & ART).
  pose proof ARD as ARD0. unfold DCTX_SIZEOF in ARD0. destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & UD & RD & RDS). unfold DCTX_SIZEOF in BD, UD, RD, RDS.
  pose proof (ablk_lits _ _ BD) as BDL. pose proof (ablk_lits _ _ FBK) as FBL.
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  unfold KHIGH in AST1.
  assert (DST0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [rewrite E; apply Z.le_refl | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
  assert (RGF : 6443008 <= FF /\ FF + 256 + 320 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 17594333495296 <= FRB /\ FRB + 384 <= SPV /\ lo + 4304 <= FRB /\
                4096 <= DST < 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495264 /\ 512 <= D8 /\ D8 + 11999 <= 2^44 /\ DCTX = 8 * D8).
  { rewrite ESHF, shad_div; unfold ASHOFF. clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R13 R14 R15 Y15 ES1 ATL AST1 ED8 DST0 BDL.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. lia. }
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G11 & G12 & GD1 & GD2 & GD3).
  assert (TLLB : nbSeq <> 0 -> 4096 <= LLT /\ 4096 <= OFT /\ 4096 <= MLT) by (intros NZ; destruct (TBL NZ) as (_ & _ & _ & T4 & T5 & T6 & _); clear - T4 T5 T6; lia).
  clear TBL.
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] m m) by apply munch_refl.
  assert (WMl : wmono bsegs m m) by apply wmono_refl.
  unfold ZSTD_split in Y14.
  (* [comment removed for export] *)
  assert (BLT : LBE + 32 <= 2147446784 \/ 17594333495296 <= LITP) by (destruct (ALT ltac:(clear - R11; lia)) as (BL0 & _); pose proof (ablk_lits _ _ BL0) as BL; clear - BL; lia).
  pose proof (sqs_loc_shadow RNG m DCTX D8 ARD0 GD3) as RZ1. pose proof RZ1 as RZ.
  pose proof (bytes_at_sh1 m _ _ _ eq_refl RZ1 ltac:(clear - GD1; lia) ltac:(clear - GD2; lia)) as RDS1.
  lazymatch type of RDS1 with bytes_at _ _ _ (?b :: nil) =>
    assert (RDC1 : ro_cells bsegs m (2147450880 + D8 + 3796) [C1 b]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS1]) end.
  clear RDS1.
  (* [comment removed for export] *)
  assert (Z5 : m (wa (shad (DCTX + 30360))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m DCTX 95992); [exact UD | clear; lia | clear - GD3; Z.div_mod_to_equations; lia]).
  rewrite shad_div in Z5. unfold ASHOFF in Z5. replace ((DCTX + 30360) / 8) with (D8 + 3795) in Z5 by (clear - GD3; Z.div_mod_to_equations; lia).
  assert (RZ2 : rdn bsegs m (wa (2147450880 + D8 + 3795)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))) by (cbn [rdn]; replace (2147450880 + D8 + 3795) with (2147450880 + (D8 + 3795)) by (clear; lia); rewrite Z5; reflexivity).
  pose proof (bytes_at_sh1 m _ _ _ eq_refl RZ2 ltac:(clear - GD1; lia) ltac:(clear - GD2; lia)) as RDS2.
  lazymatch type of RDS2 with bytes_at _ _ _ (?b :: nil) =>
    assert (RDC2 : ro_cells bsegs m (2147450880 + D8 + 3795) [C1 b]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS2]) end.
  clear RDS2 Z5.
  assert (RT2 : rng RNG (2147450880 + D8 + 3795) 1) by (eapply rng_sub'; [exact RDS |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - GD3; Z.div_mod_to_equations; lia).
  assert (RT1 : rng RNG (2147450880 + D8 + 3796) 1) by (eapply rng_sub'; [exact RDS |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - GD3; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (SHFD8 : SHF + 32 <= 2147450880 + D8 \/ 2147450880 + D8 + 11999 <= SHF).
  { rewrite ESHF, shad_div; unfold ASHOFF. unfold held in AFD. clear - AFD GD3 GD1 FFc. Z.div_mod_to_equations. lia. }
  assert (FLO : FF + 256 <= lo) by (clear - FFb ATL; lia).
  assert (DLO : DCTX + 95992 <= lo) by (unfold held in BDL; clear - BDL ATR ATL AST1; lia).
  pose proof STK as STKm. pose proof GAP as GAPm. pose proof SAV as SAVm.
  rewrite C0 in *.
  assert (NB : nbSeq = 0) by (unfold held in Y12; clear - Y12; destruct (Z.eq_dec nbSeq 0) as [E|E]; [exact E | specialize (Y12 E); lia]). rewrite NB in *.
    hold BUF0. hold MU0. hold WM0. hold FFR0. hold AH. hold AT0. hold STM0. hold IANC. hold XRD. hold RZ. hold EXS. hold Y9. hold Y13. hold Y14. hold Y15. hold FBL. hold STKm. hold GAPm. hold SAVm. hold LASTK. hold FINK. hold INITK. hold RG0. hold SD0. hold SEP0. hold TBL0. hold AS0. hold ASN0. hold PRO0. hold MMV. hold MCP. hold EXE. hold TH3. hold TB3. hold MEM0. hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold Y3. hold Y4. hold Y5. hold Y7. hold Y8. hold Y10. hold Y11. hold Y12. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBH. hold INB_D. hold INB_O. hold FBK. hold BDL. hold LRD. hold BUF. hold TLLB. hold SQB.
    rewrite GD3 in H5V, HH1, HH3, REP, UD, RD, RDS, MUL |- *.
    kx_autoFLA (FR0, FF0, SH0, HH1, HH3, H5V, REP, RDC1, RDC2) [KAApp FRB 280; KAApp FF 256; KAApp (8 * D8) 95992; KAUnp (8 * D8) 95992] [0x8f668; 0x8f4f8; 0x9263c; 0x92650; 0x92668; 0x92680; 0x92908; 0x9290c; 0x92914; 0x9291c; 0x92920; 0x90d6c] 379%nat
    [KZRange SPV 17594333499936 (2^47); KZRange FRB 17594333495296 (2^47 - 384); KZRange FF 6443008 (2^47 - 576); KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495264; KZRange D8 512 (2^44 - 11999);
     KZRange DST 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47 - 32); KZRange nbSeq 0 98047;
     KZWord (2147450880 + D8 + 3796) 1 0; KZDisj FRB 280 (2147450880 + D8 + 3796) 1; KZDisj FF 256 (2147450880 + D8 + 3796) 1; KZDisj SHF 32 (2147450880 + D8 + 3796) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3796) 1;
     KZWord (2147450880 + D8 + 3795) 1 0; KZDisj FRB 280 (2147450880 + D8 + 3795) 1; KZDisj FF 256 (2147450880 + D8 + 3795) 1; KZDisj SHF 32 (2147450880 + D8 + 3795) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3795) 1;
     KZRange SEQ 4096 (2^47);
     KZWr FRB 280; KZWr FF 256; KZWr SHF 32; KZWr (8 * D8 + 30004) 4;
     KZDisj FF 256 FRB 280; KZDisj SHF 32 FRB 280; KZDisj SHF 32 FF 256; KZDisj FRB 280 (8 * D8) 95992; KZDisj FF 256 (8 * D8) 95992; KZDisj SHF 32 (8 * D8) 95992;
     KZDisj SHF 32 (2147450880 + D8) 11999]
    [(FRB, 280); (FF, 256); (2147450880 + D8 + 3796, 1); (2147450880 + D8 + 3795, 1)]
    [(FRB, 280); (FF, 256); (SHF, 32); (8 * D8, 95992)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ mod 8 = 0 => split; [lia | assumption] | |- _ /\ rng _ _ _ => split; [lia | eapply rng_sub; [exact RSTK | clear - R13 R15 G4 G5 G6; lia | clear - R13 R15 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - GD1 GD2; lia | split; [clear - GD1; lia | split; [clear - GD2; lia | first [exact RZ1 | exact RZ2]]]] end).
    all: try sqs_aclose.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold held in FBL; unfold held in BDL; unfold held in AFD; unfold KXKEND, KXSHLO, KXSHHI; clear - AFD FBL BDL G1 G2 G3 G4 G5 G6 G7 G11 G12 GD1 GD2 GD3 ATL ATR; lia end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: kx_mem.
    all: rewrite <- GD3 in *.
    all: (unfold held in BUF0, MU0, WM0, FFR0, AH, AT0, STM0, IANC, XRD, RZ, EXS, Y9, Y13, Y14, Y15, FBL, STKm, GAPm, SAVm, LASTK, FINK, INITK, RG0, SD0, SEP0, TBL0, AS0, ASN0, PRO0, MMV, MCP, EXE, TH3, TB3, MEM0, P1, P2, P3, P4, P5, P6, P7, P8, Y3, Y4, Y5, Y7, Y8, Y10, Y11, Y12, AFD, AFO, AFS, AFL, AFT, LBH, INB_D, INB_O, FBK, BDL, LRD, BUF, TLLB, SQB; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8f668) _ _ _ _) => fail | |- evtF _ _ _ _ => exfalso; clear - KXBR NB; lia end).
    (* [comment removed for export] *)
    unfold held in LASTK. unfold held in AT0. unfold held in LRD. unfold held in BUF. unfold held in XRD. unfold held in Y9. unfold held in Y13. unfold held in Y14. unfold held in Y15.
    sqs_blob_last FF0. sqs_blob_all SH0.
    assert (MUB : munch [(DST, DST + 0); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m m1).
    { eapply munch_weaken; [| exact MUL]. unfold sub_fp; cbn [outside]; intros x Hx. clear - Hx G4 G5 ES1. lia. }
    pose proof (AT0 m1 RG0 SD0 SEP0 TBL0 AS0 PRO0 ASN0 TH3 MUB WMl) as ASN1.
    destruct ASN1 as (ARD1 & AHD1 & _ & _ & _ & AOUT1 & ARL1 & AHL1 & _ & ART1).
    assert (BUF1 : stk bsegs m1 B0 B1).
    { destruct (Z_lt_le_dec B0 B1) as [BB|BB].
      - destruct (AOUT1 BB) as (AO1 & _). destruct (AO1 ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
        unfold held in P2. unfold held in P5. pose proof (AFO BB) as AFB. unfold held in AFB.
        eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WMl |]. cbn [disjoint_from].
        split; [clear - BB P2 G4 G5 G6; lia|]. split; [clear - BB AFB; lia|]. split; [clear - BB BOL G11 G12; lia|]. split; [clear - BB P5; lia| exact I].
      - exact (stk_keep_empty m m1 _ _ BUF BB). }
    assert (LRD1 : rdbl bsegs m1 LITP (LBE + 32)).
    { unfold held in P4. unfold held in P5. unfold held in AFL. unfold held in BDL.
      eapply rdbl_transport; [exact LRD | exact MUL |]. intros x Hx; left; cbn [outside].
      split; [clear - Hx P4 G4 G5 G6; lia|]. split; [clear - Hx AFL; lia|]. split; [unfold held in BLT; clear - Hx BLT G11 G12 R10; lia|]. split; [unfold ZSTD_split in Y9; clear - Hx Y9 Y14 P5 R6 R7; lia| exact I]. }
    assert (XRD1 : rdbl bsegs m1 (DCTX + 30372) (DCTX + 95940)).
    { unfold ZSTD_split, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in XRD. unfold held in P1. unfold held in AFD. unfold held in BDL.
      replace (DCTX + 95940) with (DCTX + 30372 + 65568) by (clear; lia).
      eapply rdbl_transport; [exact (XRD Y14) | exact MUL |]. intros x Hx; left; cbn [outside].
      split; [clear - Hx P1 G4 G5 G6; lia|]. split; [clear - Hx AFD; lia|]. split; [clear - Hx BDL G11 G12; lia|]. split; [clear - Hx; lia| exact I]. }
    (* [comment removed for export] *)
    sqs_ent_lastframe FR0;
    eapply LASTK; [exact FR0 | exact FF0 | exact SH0 | eexists; eexists; eexists; exact REP | exact HH3 | split; [unfold h5_vcells; rewrite L1, L2, L3; exact H5V | exact H5L] | exact BUF1 | exact STK | exact GAP | exact SAV
                  | exact MUB | exact WMl | exact KXMI | exact LRD1 | intros _; exact XRD1 | | | | | exact ART1 | exact ARD1 | exact AHD1 | | | ].
    + clear; lia.
    + clear - R8; lia.
    + clear; lia.
    + right. clear - R11 R10 Y14; repeat split; lia.
    + intros BB. destruct (AOUT1 BB) as (AO1 & AH1). split; [exact (AO1 ltac:(clear - BB; lia)) | exact AH1].
    + clear - GD3; lia.
    + clear - GD3; lia.
Qed.

End CANSEC1.
