(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_zkit AZ_seq_l_tkit AZ_seq_l_ibase AZ_seq_l_sbase AZ_seq_l_fin AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_xat AZ_seq_l_la_at AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_ekit2 AZ_seq_l_akit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sql_oend_of FR k :=
  lazymatch type of FR with rw_cells _ _ _ ?cs =>
    let c := eval cbn [nth] in (nth 21 cs (CB 0 nil)) in
    lazymatch c with C8 (Z_to_bv 64 ?oe) => k oe end end.

(* [comment removed for export] *)
Ltac en_take240 FR H :=
  lazymatch type of FR with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn 23 cs) in
    let mid := eval cbn [firstn skipn] in (firstn 1 (skipn 23 cs)) in
    let post := eval cbn [skipn] in (skipn 24 cs) in
    pose proof FR as H; change (rw_cells sg mm A (pre ++ mid ++ post)) in H;
    apply rw_cells_app in H; destruct H as [_ H]; apply rw_cells_app in H; destruct H as [H _];
    cbn [cells_size csize Nat.add length] in H; replace (A + Z.of_nat 240) with (A + 240) in H by (clear; lia)
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_en7b : forall P,
  sql_mem P -> sql_ranges P -> sql_side P -> sql_sep P -> (l_nbSeq P <> 0 -> sql_tables P) -> sql_astat P -> sql_asan P (l_m P) -> sql_pro P ->
  zd_memmoveZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA ->
  (l_nbSeq P <> 0 -> l_LLT P + 4104 <= 2^47 /\ l_OFT P + 2056 <= 2^47 /\ l_MLT P + 4104 <= 2^47) ->
  (l_nbSeq P <> 0 -> (l_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_LLT P) /\ (l_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= l_OFT P) /\
                    (l_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_MLT P)) ->
  sql_at_lastx P -> sql_at_fin P ->
  (forall OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> ai_I0 P OEND) ->
  l_LOC P = 2 -> l_CAP P <> 0 -> l_nbSeq P <> 0 -> zlen (l_sq P) = 0 -> 8 <= l_nbSeq P -> 
  sql_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8.
  pose proof MEM as MEM0. pose proof RG as RG0. pose proof SD as SD0. pose proof SEP as SEP0. pose proof TBL as TBL0. pose proof AS as AS0. pose proof ASN as ASN0. pose proof PRO as PRO0.
  pose proof (sql_static_m P) as STM0. pose proof (sql_iinv_anchor P) as IANC. pose proof (sql_asan_transport0 P) as AT0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [sql_at_anchor sql_at_lastx sql_at_fin sql_finv ai_I0 sql_iregs sql_ifrI sql_imidA sql_iffA] in *.
  cbn [app sql_mem sql_ranges sql_side sql_sep sql_tables sql_astat sql_asan sql_pro sql_saved sql_Wb sql_post sql_fe l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  intros ja jb jc jd je jds jp jm x1 x5 x6 x7 x12 x13 x14 x17 x26 x28 x29 x30 FR0 FF0 SH0 STK GAP SAV.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & XRD & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5V & H5L). rewrite L4 in H5V. cbv beta delta [h5_vcells] in H5V. rewrite L1, L2, L3 in H5V. clear HH5.
  unfold dctx_ptrs, dctx_h1, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  destruct ASN as (ARD & AHD & ASQ & ATBL & ACL & AOUT & ALT & ALH & AZS & ART).
  pose proof ARD as ARD0. unfold DCTX_SIZEOF in ARD0. destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & UD & RD & RDS). unfold DCTX_SIZEOF in BD, UD, RD, RDS.
  pose proof (ablk_lits _ _ BD) as BDL. pose proof (ablk_lits _ _ FBK) as FBL.
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  unfold KHIGH in AST1.
  assert (DST0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [rewrite E; apply Z.le_refl | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
  assert (RGF : 6443008 <= FF /\ FF + 256 + 320 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 17594333495296 <= FRB /\ FRB + 672 <= SPV /\ lo + 4304 <= FRB /\
                0 <= DST < 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495264 /\ 512 <= D8 /\ D8 + 11999 <= 2^44 /\ DCTX = 8 * D8).
  { rewrite ESHF, shad_div; unfold ASHOFF. clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R13 R14 R15 ES1 ATL AST1 ED8 DST0 BDL.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. lia. }
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G11 & G12 & GD1 & GD2 & GD3).
  assert (FF8 : FF mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (TLLB : nbSeq <> 0 -> 4096 <= LLT /\ 4096 <= OFT /\ 4096 <= MLT) by (intros NZ; destruct (TBL NZ) as (_ & _ & _ & T4 & T5 & T6 & _); clear - T4 T5 T6; lia).
  clear TBL.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] m m) by apply munch_refl.
  assert (WMl : wmono bsegs m m) by apply wmono_refl.
  unfold ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in Y6, Y7, Y8, Y9, P8, XRD.
  (* [comment removed for export] *)
  assert (BLT : LBE + 32 <= 2147446784 \/ 17594333495296 <= LITP) by (destruct (ALT ltac:(clear - R11; lia)) as (BL0 & _); pose proof (ablk_lits _ _ BL0) as BL; clear - BL; lia).
  pose proof ARD0 as ARD8. rewrite GD3 in ARD8.
  destruct (areg_dctx_shadow RNG m D8 30368 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ1 & RR1).
  destruct (areg_dctx_shadow RNG m D8 30360 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ2 & RR2).
  destruct (areg_dctx_shadow RNG m D8 30352 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ3 & RR3).
  destruct (areg_dctx_shadow RNG m D8 30120 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ4 & RR4).
  destruct (areg_dctx_shadow RNG m D8 30000 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ5 & RR5).
  destruct (areg_dctx_shadow RNG m D8 29912 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ6 & RR6).
  destruct (areg_dctx_shadow RNG m D8 29904 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ7 & RR7).
  destruct (areg_dctx_shadow RNG m D8 29896 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ8 & RR8).
  destruct (areg_dctx_shadow RNG m D8 26688 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ9 & RR9).
  destruct (areg_dctx_shadow RNG m D8 26680 ARD8 ltac:(clear; lia) ltac:(unfold DCTX_SIZEOF; clear; lia) eq_refl) as (RZ10 & RR10).
  change (30368 / 8) with 3796 in RZ1, RR1. change (30360 / 8) with 3795 in RZ2, RR2. change (30352 / 8) with 3794 in RZ3, RR3. change (30120 / 8) with 3765 in RZ4, RR4. change (30000 / 8) with 3750 in RZ5, RR5. change (29912 / 8) with 3739 in RZ6, RR6. change (29904 / 8) with 3738 in RZ7, RR7. change (29896 / 8) with 3737 in RZ8, RR8. change (26688 / 8) with 3336 in RZ9, RR9. change (26680 / 8) with 3335 in RZ10, RR10.
  clear ARD8.
  assert (SHFD8 : SHF + 32 <= 2147450880 + D8 \/ 2147450880 + D8 + 11999 <= SHF).
  { rewrite ESHF, shad_div; unfold ASHOFF. clear - AFD GD3 GD1 FFc. Z.div_mod_to_equations. lia. }
  assert (FLO : FF + 256 <= lo) by (clear - FFb ATL; lia).
  assert (DLO : DCTX + 95992 <= lo) by (clear - BDL ATR ATL AST1; lia).
  pose proof STK as STKm. pose proof GAP as GAPm. pose proof SAV as SAVm.
  subst LOC.
  rewrite NS in *. assert (NB' : 1 <= nbSeq) by (clear - NB R5; lia). clear NB. rename NB' into NB.
  assert (CP : 1 <= CAP) by (clear - C0 R8; lia).
  assert (D4 : 4096 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [destruct (Y3 E) as (EC & _); exfalso; clear - EC CP; lia | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
    try hold MU0. try hold WM0. try hold FFR0. try hold AH. try hold AT0. try hold STM0. try hold IANC. try hold XRD. try hold EXS. try hold Y9. try hold Y13. try hold FBL. try hold STKm. try hold GAPm. try hold SAVm. try hold LASTK. try hold FINK. try hold INITK. try hold RG0. try hold SD0. try hold SEP0. try hold TBL0. try hold AS0. try hold ASN0. try hold PRO0. try hold MMV. try hold EXE. try hold TH3. try hold TB3. try hold MEM0. try hold P1. try hold P2. try hold P3. try hold P4. try hold P5. try hold P6. try hold P7. try hold P8. try hold Y3. try hold Y4. try hold Y5. try hold Y7. try hold Y8. try hold Y10. try hold Y11. try hold Y12. try hold AFD. try hold AFO. try hold AFS. try hold AFL. try hold AFT. try hold LBH. try hold INB_D. try hold INB_O. try hold FBK. try hold BDL. try hold LRD. try hold BUF. try hold TLLB. try hold SQB. try hold BLT.
    rewrite GD3 in H5V, HH1, HH3, REP, UD, RD, RDS, MUL |- *.
    kx_autoFLA (FR0, FF0, SH0, HH1, HH3, H5V, REP) [KAApp FRB 568; KAApp FF 256; KAApp (8 * D8) 95992; KAUnp (8 * D8) 95992] [0x8e5f8; 0x89e20; 0x89ae4; 0x89b08; 0x89b40; 0x89b68; 0x89b7c; 0x89b94; 0x89bac; 0x89c1c; 0x89c44; 0x89c74; 0x89c9c; 0x89e1c] 480%nat
    [KZRange SPV 17594333499936 (2^47); KZRange FRB 17594333495296 (2^47 - 672); KZRange FF 6443008 (2^47 - 576); KZAlign SPV 16; KZAlign FF 8;
     KZRange SHF 2147450880 17594333495264; KZRange D8 512 (2^44 - 11999);
     KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47 - 32);
     KZWord (2147450880 + D8 + 3796) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3796) 1; KZDisj FF 256 (2147450880 + D8 + 3796) 1; KZDisj SHF 32 (2147450880 + D8 + 3796) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3796) 1;
     KZWord (2147450880 + D8 + 3795) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3795) 1; KZDisj FF 256 (2147450880 + D8 + 3795) 1; KZDisj SHF 32 (2147450880 + D8 + 3795) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3795) 1;
     KZWord (2147450880 + D8 + 3794) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3794) 1; KZDisj FF 256 (2147450880 + D8 + 3794) 1; KZDisj SHF 32 (2147450880 + D8 + 3794) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3794) 1;
     KZWord (2147450880 + D8 + 3765) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3765) 1; KZDisj FF 256 (2147450880 + D8 + 3765) 1; KZDisj SHF 32 (2147450880 + D8 + 3765) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3765) 1;
     KZWord (2147450880 + D8 + 3750) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3750) 1; KZDisj FF 256 (2147450880 + D8 + 3750) 1; KZDisj SHF 32 (2147450880 + D8 + 3750) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3750) 1;
     KZWord (2147450880 + D8 + 3739) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3739) 1; KZDisj FF 256 (2147450880 + D8 + 3739) 1; KZDisj SHF 32 (2147450880 + D8 + 3739) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3739) 1;
     KZWord (2147450880 + D8 + 3738) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3738) 1; KZDisj FF 256 (2147450880 + D8 + 3738) 1; KZDisj SHF 32 (2147450880 + D8 + 3738) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3738) 1;
     KZWord (2147450880 + D8 + 3737) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3737) 1; KZDisj FF 256 (2147450880 + D8 + 3737) 1; KZDisj SHF 32 (2147450880 + D8 + 3737) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3737) 1;
     KZWord (2147450880 + D8 + 3336) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3336) 1; KZDisj FF 256 (2147450880 + D8 + 3336) 1; KZDisj SHF 32 (2147450880 + D8 + 3336) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3336) 1;
     KZWord (2147450880 + D8 + 3335) 1 0; KZDisj FRB 568 (2147450880 + D8 + 3335) 1; KZDisj FF 256 (2147450880 + D8 + 3335) 1; KZDisj SHF 32 (2147450880 + D8 + 3335) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3335) 1;
     KZRange SEQ 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 4097 (2^47); KZRange nbSeq 8 98047;
     KZWr FRB 568; KZWr FF 256; KZWr SHF 32; KZWr (8 * D8 + 30004) 4;
     KZDisj FF 256 FRB 568; KZDisj SHF 32 FRB 568; KZDisj SHF 32 FF 256; KZDisj FRB 568 (8 * D8) 95992; KZDisj FF 256 (8 * D8) 95992; KZDisj SHF 32 (8 * D8) 95992;
     KZDisj SHF 32 (2147450880 + D8) 11999]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SHF, 32); (8 * D8, 95992); (2147450880 + D8 + 3796, 1); (2147450880 + D8 + 3795, 1); (2147450880 + D8 + 3794, 1); (2147450880 + D8 + 3765, 1); (2147450880 + D8 + 3750, 1); (2147450880 + D8 + 3739, 1); (2147450880 + D8 + 3738, 1); (2147450880 + D8 + 3737, 1); (2147450880 + D8 + 3336, 1); (2147450880 + D8 + 3335, 1)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ mod 8 = 0 => split; [lia | assumption] | |- _ /\ rng _ _ _ => split; [lia | eapply rng_sub; [exact RSTK | clear - R13 R15 G4 G5 G6; lia | clear - R13 R15 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - GD1 GD2; lia | split; [clear - GD1; lia | split; [clear - GD2; lia | first [exact RZ1 | exact RZ2 | exact RZ3 | exact RZ4 | exact RZ5 | exact RZ6 | exact RZ7 | exact RZ8 | exact RZ9 | exact RZ10]]]] end).
    all: try sql_aclose.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold held in FBL; unfold held in BDL; unfold held in AFD; unfold KXKEND, KXSHLO, KXSHHI; clear - AFD FBL BDL G1 G2 G3 G4 G5 G6 G7 G11 G12 GD1 GD2 GD3 ATL ATR; lia end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: kx_mem.
    all: rewrite <- GD3 in *.
    all: (try unfold held in MU0; try unfold held in WM0; try unfold held in FFR0; try unfold held in AH; try unfold held in AT0; try unfold held in STM0; try unfold held in IANC; try unfold held in XRD; try unfold held in EXS; try unfold held in Y9; try unfold held in Y13; try unfold held in FBL; try unfold held in STKm; try unfold held in GAPm; try unfold held in SAVm; try unfold held in LASTK; try unfold held in FINK; try unfold held in INITK; try unfold held in RG0; try unfold held in SD0; try unfold held in SEP0; try unfold held in TBL0; try unfold held in AS0; try unfold held in ASN0; try unfold held in PRO0; try unfold held in MMV; try unfold held in EXE; try unfold held in TH3; try unfold held in TB3; try unfold held in MEM0; try unfold held in P1; try unfold held in P2; try unfold held in P3; try unfold held in P4; try unfold held in P5; try unfold held in P6; try unfold held in P7; try unfold held in P8; try unfold held in Y3; try unfold held in Y4; try unfold held in Y5; try unfold held in Y7; try unfold held in Y8; try unfold held in Y10; try unfold held in Y11; try unfold held in Y12; try unfold held in AFD; try unfold held in AFO; try unfold held in AFS; try unfold held in AFL; try unfold held in AFT; try unfold held in LBH; try unfold held in INB_D; try unfold held in INB_O; try unfold held in FBK; try unfold held in BDL; try unfold held in LRD; try unfold held in BUF; try unfold held in TLLB; try unfold held in SQB; try unfold held in BLT; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ _ _) => fail | |- evtF _ _ _ _ => exfalso; clear - KXBR NB; lia end).
    (* [comment removed for export] *)
    all: (unfold held in FINK; unfold held in BUF; unfold held in P3; unfold held in FBL; unfold held in P2).
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (BUF1 : stk bsegs mx B0 B1)
      by (destruct (Z_lt_le_dec B0 B1) as [BB|BB];
          [ destruct (AOUT BB) as (AO1 & _); destruct (AO1 ltac:(clear - BB; lia)) as (BO & _); pose proof (ablk_lits _ _ BO) as BOL;
            unfold held in P2; unfold held in P5; unfold held in AFO; pose proof (AFO BB) as AFB; unfold held in AFB;
            eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WMl |]; cbn [disjoint_from];
            split; [clear - BB P2 G4 G5 G6; lia|]; split; [clear - BB AFB; lia|]; split; [clear - BB BOL G11 G12; lia|]; split; [clear - BB P5; lia| exact I]
          | exact (stk_keep_empty m mx _ _ BUF BB) ])
    end.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8e5f8) _ _ ?my _) =>
      assert (NBF : (nbSeq =? 0) = false) by (apply Z.eqb_neq; clear - NB; lia);
      unfold sql_fe in FINK; cbn [l_nbSeq l_fe] in FINK; try rewrite NBF in FINK;
      eapply (FINK my 18446744073709551596); [| clear; lia | left; reflexivity];
      sql_blob_last FF0; sql_blob_all SH0; sql_blob_all FR0;
      pose proof (stk_of_rw_cells bsegs _ _ _ FR0) as FRS; cbn [cells_size csize Nat.add] in FRS;
      assert (MUB : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m my)
        by (eapply munch_weaken; [| exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx G4 G5 G6 ES1; lia);
      split; [eexists; exact FF0|]; split; [eexists; exact SH0|];
      split; [eexists; eexists; eexists; exact REP|];
      split; [exact HH3|];
      split; [exact BUF1|];
      split; [exact STK|];
      split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|];
      split; [exact SAV|];
      split; [eexists; split; [unfold h5_vcells; rewrite L1, L2, L3; exact H5V | exact H5L]|];
      split; [exact MUB|];
      split; [exact WMl | match goal with H : mem_inv bsegs my |- _ => exact H end]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF after the error run, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal after the error run:" UNEXPECTED
    end.
Qed.

End CANSEC1.
