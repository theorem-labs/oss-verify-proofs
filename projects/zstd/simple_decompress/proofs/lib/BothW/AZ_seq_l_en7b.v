(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_zkit AZ_seq_l_tkit AZ_seq_l_ibase AZ_seq_l_sbase AZ_seq_l_fin AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_xat AZ_seq_l_la_at AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_ickit AZ_seq_l_ekit2 AZ_seq_l_akit2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  zd_memmoveZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA -> zd_reload_int_stmtA -> zd_dbs_stmtA -> sql_bit_init_stmtG APZD_BITINIT ->
  (l_nbSeq P <> 0 -> l_LLT P + 4104 <= 2^47 /\ l_OFT P + 2056 <= 2^47 /\ l_MLT P + 4104 <= 2^47) ->
  (l_nbSeq P <> 0 -> (l_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_LLT P) /\ (l_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= l_OFT P) /\
                    (l_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_MLT P)) ->
  sql_at_lastx P -> sql_at_fin P ->
  (forall OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> ai_I0 P OEND) ->
  l_LOC P = 2 -> l_CAP P <> 0 -> l_nbSeq P <> 0 -> zlen (l_sq P) = 0 -> 8 <= l_nbSeq P -> 
  sql_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS RLI DBS BIS TH3 TB3 LASTK FINK INITK EL C0 NB NS NB8.
  pose proof MEM as MEM0. pose proof RG as RG0. pose proof SD as SD0. pose proof SEP as SEP0. pose proof TBL as TBL0. pose proof AS as AS0. pose proof ASN as ASN0. pose proof PRO as PRO0.
  pose proof (sql_static_m P) as STM0. pose proof (sql_iinv_anchor P) as IANC. pose proof (sql_asan_transport0 P) as AT0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [sql_at_anchor sql_at_lastx sql_at_fin sql_finv ai_I0 sql_iregs sql_ifrI sql_imidA sql_iffA] in *.
  cbn [app sql_mem sql_ranges sql_side sql_sep sql_tables sql_astat sql_asan sql_pro sql_saved sql_Wb sql_post sql_fe l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  intros ja jb jc jd jds jp jm x1 x5 x6 x7 x10 x11 x13 x15 x25 x26 x27 x28 x29 x30 x31 FR0 FF0 SH0 STK GAP SAV.
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
  assert (RGF : 6459392 <= FF /\ FF + 256 + 320 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 17594333495296 <= FRB /\ FRB + 736 <= SPV /\ lo + 4304 <= FRB /\
                0 <= DST < 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495264 /\ 512 <= D8 /\ D8 + 11999 <= 2^44 /\ DCTX = 8 * D8).
  { rewrite ESHF, shad_div; unfold ASHOFF. clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R13 R14 R15 ES1 ATL AST1 ED8 DST0 BDL.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. lia. }
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G11 & G12 & GD1 & GD2 & GD3).
  assert (FF8 : FF mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (TLLB : nbSeq <> 0 -> 4096 <= LLT /\ 4096 <= OFT /\ 4096 <= MLT) by (intros NZ; destruct (TBL NZ) as (_ & _ & _ & T4 & T5 & T6 & _); clear - T4 T5 T6; lia).
  clear TBL.
  assert (MUL : munch [(FRB, FRB + 632); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] m m) by apply munch_refl.
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
    try hold RLI. try hold DBS. try hold BIS. try hold MU0. try hold WM0. try hold FFR0. try hold AH. try hold AT0. try hold STM0. try hold IANC. try hold XRD. try hold EXS. try hold Y9. try hold Y13. try hold FBL. try hold STKm. try hold GAPm. try hold SAVm. try hold LASTK. try hold FINK. try hold INITK. try hold RG0. try hold SD0. try hold SEP0. try hold TBL0. try hold AS0. try hold ASN0. try hold PRO0. try hold MMV. try hold EXE. try hold TH3. try hold TB3. try hold MEM0. try hold P1. try hold P2. try hold P3. try hold P4. try hold P5. try hold P6. try hold P7. try hold P8. try hold Y3. try hold Y4. try hold Y5. try hold Y7. try hold Y8. try hold Y10. try hold Y11. try hold Y12. try hold AFD. try hold AFO. try hold AFS. try hold AFL. try hold AFT. try hold LBH. try hold INB_D. try hold INB_O. try hold FBK. try hold BDL. try hold LRD. try hold BUF. try hold TLLB. try hold SQB. try hold BLT.
    rewrite GD3 in H5V, HH1, HH3, REP, UD, RD, RDS, MUL |- *.
    kx_autoFLA (FR0, FF0, SH0, HH1, HH3, H5V, REP) [KAApp FRB 632; KAApp FF 256; KAApp (8 * D8) 95992; KAUnp (8 * D8) 95992] [0x8b23c; 0x95b74; 0x5ad30; 0x5add0; 0x5ae70; 0x5af10; 0x5b050; 0x5b190; 0x5b370; 0x5b410] 480%nat
    [KZRange SPV 17594333499936 (2^47); KZRange FRB 17594333495296 (2^47 - 736); KZRange FF 6459392 (2^47 - 576); KZAlign SPV 16; KZAlign FF 8;
     KZRange SHF 2147450880 17594333495264; KZRange D8 512 (2^44 - 11999);
     KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47 - 32);
     KZWord (2147450880 + D8 + 3796) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3796) 1; KZDisj FF 256 (2147450880 + D8 + 3796) 1; KZDisj SHF 32 (2147450880 + D8 + 3796) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3796) 1;
     KZWord (2147450880 + D8 + 3795) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3795) 1; KZDisj FF 256 (2147450880 + D8 + 3795) 1; KZDisj SHF 32 (2147450880 + D8 + 3795) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3795) 1;
     KZWord (2147450880 + D8 + 3794) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3794) 1; KZDisj FF 256 (2147450880 + D8 + 3794) 1; KZDisj SHF 32 (2147450880 + D8 + 3794) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3794) 1;
     KZWord (2147450880 + D8 + 3765) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3765) 1; KZDisj FF 256 (2147450880 + D8 + 3765) 1; KZDisj SHF 32 (2147450880 + D8 + 3765) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3765) 1;
     KZWord (2147450880 + D8 + 3750) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3750) 1; KZDisj FF 256 (2147450880 + D8 + 3750) 1; KZDisj SHF 32 (2147450880 + D8 + 3750) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3750) 1;
     KZWord (2147450880 + D8 + 3739) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3739) 1; KZDisj FF 256 (2147450880 + D8 + 3739) 1; KZDisj SHF 32 (2147450880 + D8 + 3739) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3739) 1;
     KZWord (2147450880 + D8 + 3738) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3738) 1; KZDisj FF 256 (2147450880 + D8 + 3738) 1; KZDisj SHF 32 (2147450880 + D8 + 3738) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3738) 1;
     KZWord (2147450880 + D8 + 3737) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3737) 1; KZDisj FF 256 (2147450880 + D8 + 3737) 1; KZDisj SHF 32 (2147450880 + D8 + 3737) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3737) 1;
     KZWord (2147450880 + D8 + 3336) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3336) 1; KZDisj FF 256 (2147450880 + D8 + 3336) 1; KZDisj SHF 32 (2147450880 + D8 + 3336) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3336) 1;
     KZWord (2147450880 + D8 + 3335) 1 0; KZDisj FRB 632 (2147450880 + D8 + 3335) 1; KZDisj FF 256 (2147450880 + D8 + 3335) 1; KZDisj SHF 32 (2147450880 + D8 + 3335) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3335) 1;
     KZRange SEQ 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 4097 (2^47); KZRange nbSeq 8 98047;
     KZWr FRB 632; KZWr FF 256; KZWr SHF 32; KZWr (8 * D8 + 30004) 4;
     KZDisj FF 256 FRB 632; KZDisj SHF 32 FRB 632; KZDisj SHF 32 FF 256; KZDisj FRB 632 (8 * D8) 95992; KZDisj FF 256 (8 * D8) 95992; KZDisj SHF 32 (8 * D8) 95992;
     KZDisj SHF 32 (2147450880 + D8) 11999]
    [(FRB, 632); (FF, 256)]
    [(FRB, 632); (FF, 256); (SHF, 32); (8 * D8, 95992); (2147450880 + D8 + 3796, 1); (2147450880 + D8 + 3795, 1); (2147450880 + D8 + 3794, 1); (2147450880 + D8 + 3765, 1); (2147450880 + D8 + 3750, 1); (2147450880 + D8 + 3739, 1); (2147450880 + D8 + 3738, 1); (2147450880 + D8 + 3737, 1); (2147450880 + D8 + 3336, 1); (2147450880 + D8 + 3335, 1)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ mod 8 = 0 => split; [lia | assumption] | |- _ /\ rng _ _ _ => split; [lia | eapply rng_sub; [exact RSTK | clear - R13 R15 G4 G5 G6; lia | clear - R13 R15 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - GD1 GD2; lia | split; [clear - GD1; lia | split; [clear - GD2; lia | first [exact RZ1 | exact RZ2 | exact RZ3 | exact RZ4 | exact RZ5 | exact RZ6 | exact RZ7 | exact RZ8 | exact RZ9 | exact RZ10]]]] end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 588632) _ _ _ _) => kx_trap_fast end).
    all: try sql_aclose.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold held in FBL; unfold held in BDL; unfold held in AFD; unfold KXKEND, KXSHLO, KXSHHI; clear - AFD FBL BDL G1 G2 G3 G4 G5 G6 G7 G11 G12 GD1 GD2 GD3 ATL ATR; lia end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: kx_mem.
    all: rewrite <- GD3 in *.
    all: (try unfold held in RLI; try unfold held in DBS; try unfold held in BIS; try unfold held in MU0; try unfold held in WM0; try unfold held in FFR0; try unfold held in AH; try unfold held in AT0; try unfold held in STM0; try unfold held in IANC; try unfold held in XRD; try unfold held in EXS; try unfold held in Y9; try unfold held in Y13; try unfold held in FBL; try unfold held in STKm; try unfold held in GAPm; try unfold held in SAVm; try unfold held in LASTK; try unfold held in FINK; try unfold held in INITK; try unfold held in RG0; try unfold held in SD0; try unfold held in SEP0; try unfold held in TBL0; try unfold held in AS0; try unfold held in ASN0; try unfold held in PRO0; try unfold held in MMV; try unfold held in EXE; try unfold held in TH3; try unfold held in TB3; try unfold held in MEM0; try unfold held in P1; try unfold held in P2; try unfold held in P3; try unfold held in P4; try unfold held in P5; try unfold held in P6; try unfold held in P7; try unfold held in P8; try unfold held in Y3; try unfold held in Y4; try unfold held in Y5; try unfold held in Y7; try unfold held in Y8; try unfold held in Y10; try unfold held in Y11; try unfold held in Y12; try unfold held in AFD; try unfold held in AFO; try unfold held in AFS; try unfold held in AFL; try unfold held in AFT; try unfold held in LBH; try unfold held in INB_D; try unfold held in INB_O; try unfold held in FBK; try unfold held in BDL; try unfold held in LRD; try unfold held in BUF; try unfold held in TLLB; try unfold held in SQB; try unfold held in BLT; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95b74) _ _ _ _) => fail | |- evtF _ _ _ _ => exfalso; clear - KXBR NB; lia end).
    (* [comment removed for export] *)
    all: (unfold held in BIS; unfold held in FINK; unfold held in BUF; unfold held in P3; unfold held in FBL; unfold held in P2).
    all: apply sql_sh14 in SH0.
    (* [comment removed for export] *)
    all: lazymatch type of FF0 with rw_cells _ ?mx _ (?c0 :: CB 88 ?j :: ?rest) =>
      apply (rw_cells_split_CB bsegs mx FF [c0] 88 j rest [40; 48]%nat) in FF0; [| reflexivity]; cbn [mk_CB_cells app] in FF0 end.
    all: lazymatch type of FF0 with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?rest) =>
      pose proof FF0 as FFX; change (rw_cells bsegs mx FF ([c0] ++ [c1] ++ rest)) in FFX;
      apply rw_cells_app in FFX; destruct FFX as (FH0 & FFX); apply rw_cells_app in FFX; destruct FFX as (BDC & FT0);
      cbn [cells_size csize Nat.add length] in FH0, BDC, FT0 end.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (BUF1 : stk bsegs mx B0 B1)
      by (destruct (Z_lt_le_dec B0 B1) as [BB|BB];
          [ destruct (AOUT BB) as (AO1 & _); destruct (AO1 ltac:(clear - BB; lia)) as (BO & _); pose proof (ablk_lits _ _ BO) as BOL;
            unfold held in P2; unfold held in P5; unfold held in AFO; pose proof (AFO BB) as AFB; unfold held in AFB;
            eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WMl |]; cbn [disjoint_from];
            split; [clear - BB P2 G4 G5 G6; lia|]; split; [clear - BB AFB; lia|]; split; [clear - BB BOL G11 G12; lia|]; split; [clear - BB P5; lia| exact I]
          | exact (stk_keep_empty m mx _ _ BUF BB) ]);
    assert (UBD : unpoisoned mx (FF + 32) (FF + 32 + 112))
      by (eapply sql_fsh_unp; [exact SH0 | rewrite ESHF, shad_div; reflexivity | clear - FFc; Z.div_mod_to_equations; lia | clear - G1; lia | clear - G2; lia]);
    assert (AOBD : aro RNG mx (FF + 32) 40)
      by (split; [eapply unpoisoned_sub; [exact UBD | clear; lia | clear; lia]|];
          split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|];
          eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - FFc; Z.div_mod_to_equations; lia);
    assert (AHB : ahull RNG mx (FF + 32) 40)
      by (exists FF, (FF + 256); split; [clear; lia|]; split; [clear; lia|]; split; [clear - FFc; Z.div_mod_to_equations; lia|]; split; [clear - FFc; Z.div_mod_to_equations; lia|];
          split; [clear - G1; lia|]; split; [unfold KEND; clear - G2; lia|];
          replace (shad (FF + 256) - shad FF) with 32 by (rewrite !shad_div; clear - FFc; Z.div_mod_to_equations; lia); rewrite <- ESHF;
          split; [eapply (SysStep.rw_cells_wr_at bsegs mx SHF _ 32 SH0); cbn [cells_size csize Nat.add length]; clear; lia | exact RSHF]);
    assert (ABD : app_blk (FF + 32) (FF + 32 + 40))
      by (eapply app_blk_sub; [apply ablk_app_blk; [exact FBK | clear; lia] | clear; lia | clear; lia | clear; lia]);
    assert (ART1 : art mx)
      by (eapply (sql_art_trW m mx); [exact ART | exact MUL | exact WMl | intros A k HA HK; cbn [disjoint_from]; unfold held in BDL; clear - HA HK G1 G4 G11 BDL; repeat split; try exact I; lia]);
    assert (ASTK1 : astk RNG lo FRB) by (split; [unfold KHIGH; exact AST1 | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - G5; lia] | exact RAI]])
    end.
    all: hold MUL. all: hold WMl.
    all: (eapply evtF_cut;
    [ eapply BIS;
      [ exact KXMI | exact BDC | clear - FFc; Z.div_mod_to_equations; lia | apply bytes_at_nil; clear - R3 R4; unfold zlen in *; lia | reflexivity
      | clear - G1; lia | clear - G2; lia | clear - R3; lia | clear - R4 NS; unfold zlen in *; lia | intros; exfalso; lia
      | exact STK | clear - G6; lia | clear - G3 G5; lia | left; clear - FLO; lia | unfold off_stack in P3; clear - P3 G5; lia
      | exact ABD | exact AOBD | exact AHB | intros; exfalso; lia | exact ART1 | exact ASTK1 ] | ]).
    all: clear BDC UBD AOBD AHB ABD ART1 ASTK1.
    all: intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc & r & -> & MUc & WMc & MIc & STKc & RES).
    all: destruct RES as [(_ & N1 & _) | (ER & HR & bs & BDC2)]; [exfalso; clear - N1; lia|].
    all: replace (ret_pc (Z_to_bv 64 567308)) with (Z_to_bv 64 567308) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    all: apply zd_is_error_true_iff in ER. all: unfold ZE_maxCode in ER.
    (* [comment removed for export] *)
    all: lazymatch type of FR0 with rw_cells _ ?mx _ _ =>
    assert (DJC : forall X k, 0 <= k -> (X + k <= FF + 32 \/ FF + 32 + 40 <= X) -> (X + k <= FRB - 2224 \/ FRB <= X) -> disjoint_from [(FF + 32, FF + 32 + 40); (FRB - 2224, FRB)] X k)
      by (intros X k Hk D1 D2; cbn [disjoint_from]; split; [exact D1 | split; [exact D2 | exact I]]);
    eapply (rw_cells_transport bsegs _ mx mc) in FR0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | right; clear - FLO G6; lia | right; clear; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in SH0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | unfold held in FBL; cbn [cells_size csize Nat.add length]; clear - FBL ESHF FFc; rewrite ESHF, shad_div; unfold ASHOFF; destruct FBL as [[F1 F2]|[F1 F2]]; [right | left]; Z.div_mod_to_equations; lia | left; cbn [cells_size csize Nat.add length]; clear - G12 G6 AST1; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in FH0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | left; cbn; clear; lia | left; cbn; clear - FLO G6; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in FT0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | right; clear; lia | left; cbn [cells_size csize Nat.add length]; clear - FLO G6; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in REP; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | unfold held in AFD; cbn [cells_size csize Nat.add length]; clear - AFD; lia | left; cbn [cells_size csize Nat.add length]; clear - DLO G6; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in HH3; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | unfold held in AFD; cbn [cells_size csize Nat.add length]; clear - AFD; lia | left; cbn [cells_size csize Nat.add length]; clear - DLO G6; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in H5V; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | unfold held in AFD; cbn [cells_size csize Nat.add length h5_vcells]; clear - AFD; lia | left; cbn [cells_size csize Nat.add length h5_vcells]; clear - DLO G6; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in SAV; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | right; cbn; clear - FLO G6 G5; lia | right; cbn; clear - G5; lia]];
    eapply (stk_transport_disjoint bsegs _ mx mc) in GAP; [| exact MUc | exact WMc | apply DJC; [clear - G5; lia | right; clear - FLO G6; lia | right; clear; lia]];
    assert (BUFc : stk bsegs mc B0 B1)
      by (destruct (Z_lt_le_dec B0 B1) as [BB|BB];
          [ pose proof (AFO BB) as AFB; unfold held in AFB;
            eapply (stk_transport_disjoint bsegs _ mx mc); [exact BUF1 | exact MUc | exact WMc | apply DJC; [clear - BB; lia | clear - BB AFB; lia | unfold off_stack in P2; clear - BB P2 G5 G6; lia]]
          | exact (stk_keep_empty mx mc _ _ BUF1 BB) ])
    end.
    all: assert (FF1 : rw_cells bsegs mc FF ([CB 32 jfh] ++ [CB 40 bs] ++ _)) by (apply rw_cells_app; split; [exact FH0 | apply rw_cells_app; cbn [cells_size csize Nat.add length]; split; [exact BDC2 | exact FT0]]).
    all: cbn [app] in FF1. all: clear FH0 BDC2 FT0.
    all: assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] mc mc) by apply munch_refl. all: assert (WMX : wmono bsegs mc mc) by apply wmono_refl.
    all: sql_blob_all SH0.
    all: assert (DSF : SHF + 32 <= FF \/ FF + 256 <= SHF) by (unfold held in FBL; clear - FBL ESHF FFc; rewrite ESHF, shad_div; unfold ASHOFF; destruct FBL as [[F1 F2]|[F1 F2]]; [right | left]; Z.div_mod_to_equations; lia).
    all: (hold MUc; hold WMc; hold ER; hold HR; hold DJC; hold BUFc; hold STKc; hold REP; hold HH3; hold H5V).
    all: try hold RLI. all: try hold DBS. all: try hold BIS. all: try hold MU0. all: try hold WM0. all: try hold FFR0. all: try hold AH. all: try hold AT0. all: try hold STM0. all: try hold IANC. all: try hold XRD. all: try hold EXS. all: try hold Y9. all: try hold Y13. all: try hold FBL. all: try hold STKm. all: try hold GAPm. all: try hold SAVm. all: try hold LASTK. all: try hold FINK. all: try hold INITK. all: try hold RG0. all: try hold SD0. all: try hold SEP0. all: try hold TBL0. all: try hold AS0. all: try hold ASN0. all: try hold PRO0. all: try hold MMV. all: try hold EXE. all: try hold TH3. all: try hold TB3. all: try hold MEM0. all: try hold P1. all: try hold P2. all: try hold P3. all: try hold P4. all: try hold P5. all: try hold P6. all: try hold P7. all: try hold P8. all: try hold Y3. all: try hold Y4. all: try hold Y5. all: try hold Y7. all: try hold Y8. all: try hold Y10. all: try hold Y11. all: try hold Y12. all: try hold AFD. all: try hold AFO. all: try hold AFS. all: try hold AFL. all: try hold AFT. all: try hold LBH. all: try hold INB_D. all: try hold INB_O. all: try hold FBK. all: try hold BDL. all: try hold LRD. all: try hold BUF. all: try hold TLLB. all: try hold SQB. all: try hold BLT.
    all: kx_autoFLA (FR0, FF1, SH0) [] [0x8fa74] 60%nat
      [KZRange SPV 17594333495296 (2^47); KZRange FRB 17594333495296 (2^47 - 736); KZRange FF 6459392 (2^47 - 576); KZAlign SPV 16;
       KZRange SHF 2147450880 17594333495296; KZRange r (2^64 - 119) (2^64 - 1);
       KZWr FRB 632; KZWr FF 256; KZDisj FF 256 FRB 632; KZWr SHF 32; KZDisj SHF 32 FRB 632; KZDisj SHF 32 FF 256]
      [(FRB, 632); (FF, 256)]
      [(FRB, 632); (FF, 256); (SHF, 32)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_z]).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in MUc; unfold held in WMc; unfold held in ER; unfold held in HR; unfold held in MUL; unfold held in WMl; unfold held in BUFc; unfold held in STKc; unfold held in REP; unfold held in HH3; unfold held in H5V.
    all: (try unfold held in RLI; try unfold held in DBS; try unfold held in BIS; try unfold held in MU0; try unfold held in WM0; try unfold held in FFR0; try unfold held in AH; try unfold held in AT0; try unfold held in STM0; try unfold held in IANC; try unfold held in XRD; try unfold held in EXS; try unfold held in Y9; try unfold held in Y13; try unfold held in FBL; try unfold held in STKm; try unfold held in GAPm; try unfold held in SAVm; try unfold held in LASTK; try unfold held in FINK; try unfold held in INITK; try unfold held in RG0; try unfold held in SD0; try unfold held in SEP0; try unfold held in TBL0; try unfold held in AS0; try unfold held in ASN0; try unfold held in PRO0; try unfold held in MMV; try unfold held in EXE; try unfold held in TH3; try unfold held in TB3; try unfold held in MEM0; try unfold held in P1; try unfold held in P2; try unfold held in P3; try unfold held in P4; try unfold held in P5; try unfold held in P6; try unfold held in P7; try unfold held in P8; try unfold held in Y3; try unfold held in Y4; try unfold held in Y5; try unfold held in Y7; try unfold held in Y8; try unfold held in Y10; try unfold held in Y11; try unfold held in Y12; try unfold held in AFD; try unfold held in AFO; try unfold held in AFS; try unfold held in AFL; try unfold held in AFT; try unfold held in LBH; try unfold held in INB_D; try unfold held in INB_O; try unfold held in FBK; try unfold held in BDL; try unfold held in LRD; try unfold held in BUF; try unfold held in TLLB; try unfold held in SQB; try unfold held in BLT; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - ER HR; lia end).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8fa74) _ _ ?my _) =>
      assert (NBF : (nbSeq =? 0) = false) by (apply Z.eqb_neq; clear - NB; lia);
      unfold sql_fe in FINK; cbn [l_nbSeq l_fe] in FINK; try rewrite NBF in FINK;
      eapply (FINK my 18446744073709551596); [| clear; lia | left; reflexivity];
      sql_blob_last FF1; sql_blob_all SH0; en_take240 FR0 F240; sql_blob_all FR0;
      pose proof (stk_of_rw_cells bsegs _ _ _ FR0) as FRS; cbn [cells_size csize Nat.add] in FRS;
      assert (MUB : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m my)
        by (eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MUc]] | eapply munch_weaken; [| exact MUX]];
            unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx G4 G5 G6 ES1; lia);
      split; [eexists; exact FF1|]; split; [eexists; exact SH0|]; split; [exact F240|];
      split; [eexists; eexists; eexists; eapply rw_cells_transport; [exact REP | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in AFD; unfold held in BDL; clear - AFD BDL G11 G12; split; [lia| split; [lia| exact I]]]|];
      split; [eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; unfold held in AFD; unfold held in BDL; clear - AFD BDL G11 G12; split; [lia| split; [lia| exact I]]]|];
      split; [destruct (Z_lt_le_dec B0 B1) as [BB|BB]; [ unfold held in AFO; pose proof (AFO BB) as AFB; unfold held in AFB; destruct (AOUT BB) as (AO1 & _); destruct (AO1 ltac:(clear - BB; lia)) as (BO & _); pose proof (ablk_lits _ _ BO) as BOL;
               eapply stk_transport_disjoint; [exact BUFc | exact MUX | exact WMX | cbn [disjoint_from]; split; [clear - BB BOL G11 G12; lia| split; [clear - BB AFB; lia| exact I]]] | exact (stk_keep_empty mc my _ _ BUFc BB)]|];
      split; [eapply stk_transport_disjoint; [exact STKc | exact MUX | exact WMX | cbn [disjoint_from]; split; [clear - G12 G6 AST1; lia | split; [clear - FLO; lia | exact I]]]|];
      split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|];
      split; [exact SAV|];
      split; [eexists; split; [eapply rw_cells_transport; [unfold h5_vcells; rewrite L1, L2, L3; exact H5V | exact MUX | exact WMX | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; unfold held in AFD; unfold held in BDL; clear - AFD BDL G11 G12; split; [lia| split; [lia| exact I]]] | exact H5L]|];
      split; [exact MUB|];
      split; [eapply wmono_trans; [eapply wmono_trans; [exact WMl | exact WMc] | exact WMX] | match goal with H : mem_inv bsegs my |- _ => exact H end]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF after the error run, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal after the error run:" UNEXPECTED
    end.
Qed.

End CANSEC1.
