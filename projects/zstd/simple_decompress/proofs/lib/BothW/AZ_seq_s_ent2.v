(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase
     AZ_seq_s_sbase AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_last AZ_seq_s_xat AZ_seq_s_a1_at AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_ekit2 AZ_seq_s_lkit2 AZ_seq_s_akit2 AZ_seq_s_xkit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
Ltac sqs_ent_lastframe H := sqs_blob_seg H 5%nat 8%nat; sqs_blob_seg H 0%nat 4%nat.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_ent2 : forall P,
  sqs_mem P -> sqs_ranges P -> sqs_side P -> sqs_sep P -> (v_nbSeq P <> 0 -> sqs_tables P) -> sqs_astat P -> sqs_asan P (v_m P) -> sqs_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA -> zd_execend_split_stmtA -> zd_reload_int_stmtA -> zd_dbs_stmtA -> sqs_bit_init_stmtG APZD_BITINIT ->
  (v_nbSeq P <> 0 -> v_LLT P + 4104 <= 2^47 /\ v_OFT P + 2056 <= 2^47 /\ v_MLT P + 4104 <= 2^47) ->
  (v_nbSeq P <> 0 -> (v_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_LLT P) /\ (v_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= v_OFT P) /\
                    (v_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= v_MLT P)) ->
  sqs_at_last P -> sqs_at_fin P ->
  (forall OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> LOCV = v_LOC P -> ai_I0 P OEND LLO LEND LOCV) ->
  v_CAP P <> 0 -> v_nbSeq P <> 0 -> zlen (v_sq P) = 0 -> sqs_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE EXS RLI DBS BIS TH3 TB3 LASTK FINK INITK C0 NB NS.
  pose proof MEM as MEM0. pose proof RG as RG0. pose proof SD as SD0. pose proof SEP as SEP0. pose proof TBL as TBL0. pose proof AS as AS0. pose proof ASN as ASN0. pose proof PRO as PRO0.
  pose proof (sqs_static_m2 P) as STM0. pose proof (sqs_iinv_anchor P) as IANC. pose proof (sqs_asan_transport0 P) as AT0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_at_anchor sqs_at_last sqs_at_fin sqs_finv ai_I0 sqs_iregs sqs_ifrI sqs_imidA sqs_iffA] in *.
  cbn [app sqs_mem sqs_ranges sqs_side sqs_sep sqs_tables sqs_astat sqs_asan sqs_pro sqs_saved sqs_Wb sqs_post sqs_fe v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  intros ja jb jds jp jm x1 x5 x7 x10 x11 x12 x13 x14 x24 x25 x27 x28 x29 x30 x31 FR0 FF0 SH0 STK GAP SAV.
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
  assert (RGF : 6459392 <= FF /\ FF + 256 + 320 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 17594333495296 <= FRB /\ FRB + 384 <= SPV /\ lo + 4304 <= FRB /\
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
  rewrite NS in *. assert (NB' : 1 <= nbSeq) by (clear - NB R5; lia). clear NB. rename NB' into NB.
    hold RLI. hold DBS. hold BIS. hold BUF0. hold MU0. hold WM0. hold FFR0. hold AH. hold AT0. hold STM0. hold IANC. hold XRD. hold RZ. hold EXS. hold Y9. hold Y13. hold Y14. hold Y15. hold FBL. hold STKm. hold GAPm. hold SAVm. hold LASTK. hold FINK. hold INITK. hold RG0. hold SD0. hold SEP0. hold TBL0. hold AS0. hold ASN0. hold PRO0. hold MMV. hold MCP. hold EXE. hold TH3. hold TB3. hold MEM0. hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold Y3. hold Y4. hold Y5. hold Y7. hold Y8. hold Y10. hold Y11. hold Y12. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBH. hold INB_D. hold INB_O. hold FBK. hold BDL. hold LRD. hold BUF. hold TLLB. hold SQB.
    rewrite GD3 in H5V, HH1, HH3, REP, UD, RD, RDS, MUL |- *.
    kx_autoFLA (FR0, FF0, SH0, HH1, HH3, H5V, REP, RDC1, RDC2) [KAApp FRB 280; KAApp FF 256; KAApp (8 * D8) 95992; KAUnp (8 * D8) 95992] [0x91970; 0x95b74; 0x937d0; 0x937d4; 0x937e8; 0x93800; 0x9381c; 0x938b0; 0x938b4; 0x938bc; 0x938c4; 0x938c8; 0x93170] 400%nat
    [KZRange SPV 17594333499936 (2^47); KZRange FRB 17594333495296 (2^47 - 384); KZRange FF 6459392 (2^47 - 576); KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495264; KZRange D8 512 (2^44 - 11999);
     KZRange DST 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47 - 32); KZRange nbSeq 0 98047;
     KZWord (2147450880 + D8 + 3796) 1 0; KZDisj FRB 280 (2147450880 + D8 + 3796) 1; KZDisj FF 256 (2147450880 + D8 + 3796) 1; KZDisj SHF 32 (2147450880 + D8 + 3796) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3796) 1;
     KZWord (2147450880 + D8 + 3795) 1 0; KZDisj FRB 280 (2147450880 + D8 + 3795) 1; KZDisj FF 256 (2147450880 + D8 + 3795) 1; KZDisj SHF 32 (2147450880 + D8 + 3795) 1; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3795) 1;
     KZRange SEQ 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 1 (2^47); KZRange nbSeq 1 98047;
     KZWr FRB 280; KZWr FF 256; KZWr SHF 32; KZWr (8 * D8 + 30004) 4;
     KZDisj FF 256 FRB 280; KZDisj SHF 32 FRB 280; KZDisj SHF 32 FF 256; KZDisj FRB 280 (8 * D8) 95992; KZDisj FF 256 (8 * D8) 95992; KZDisj SHF 32 (8 * D8) 95992;
     KZDisj SHF 32 (2147450880 + D8) 11999]
    [(FRB, 280); (FF, 256); (2147450880 + D8 + 3796, 1); (2147450880 + D8 + 3795, 1)]
    [(FRB, 280); (FF, 256); (SHF, 32); (8 * D8, 95992)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ mod 8 = 0 => split; [lia | assumption] | |- _ /\ rng _ _ _ => split; [lia | eapply rng_sub; [exact RSTK | clear - R13 R15 G4 G5 G6; lia | clear - R13 R15 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - GD1 GD2; lia | split; [clear - GD1; lia | split; [clear - GD2; lia | first [exact RZ1 | exact RZ2]]]] end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x937d0) _ _ _ _) => kx_trap_fast end).
    all: try sqs_aclose.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold held in FBL; unfold held in BDL; unfold held in AFD; unfold KXKEND, KXSHLO, KXSHHI; clear - AFD FBL BDL G1 G2 G3 G4 G5 G6 G7 G11 G12 GD1 GD2 GD3 ATL ATR; lia end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: kx_mem.
    all: rewrite <- GD3 in *.
    all: (unfold held in RLI, DBS, BIS, BUF0, MU0, WM0, FFR0, AH, AT0, STM0, IANC, XRD, RZ, EXS, Y9, Y13, Y14, Y15, FBL, STKm, GAPm, SAVm, LASTK, FINK, INITK, RG0, SD0, SEP0, TBL0, AS0, ASN0, PRO0, MMV, MCP, EXE, TH3, TB3, MEM0, P1, P2, P3, P4, P5, P6, P7, P8, Y3, Y4, Y5, Y7, Y8, Y10, Y11, Y12, AFD, AFO, AFS, AFL, AFT, LBH, INB_D, INB_O, FBK, BDL, LRD, BUF, TLLB, SQB; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x95b74) _ _ _ _) => fail | |- evtF _ _ _ _ => exfalso; clear - KXBR NB; lia end).
    (* [comment removed for export] *)
    unfold held in BIS. unfold held in FINK. unfold held in BUF. unfold held in P3. unfold held in FBL. unfold held in P2.
    apply sqs_sh14 in SH0.
    (* [comment removed for export] *)
    lazymatch type of FF0 with rw_cells _ ?mx _ (?c0 :: CB 88 ?j :: ?rest) =>
      apply (rw_cells_split_CB bsegs mx FF [c0] 88 j rest [40; 48]%nat) in FF0; [| reflexivity]; cbn [mk_CB_cells app] in FF0 end.
    lazymatch type of FF0 with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?rest) =>
      pose proof FF0 as FFX; change (rw_cells bsegs mx FF ([c0] ++ [c1] ++ rest)) in FFX;
      apply rw_cells_app in FFX; destruct FFX as (FH0 & FFX); apply rw_cells_app in FFX; destruct FFX as (BDC & FT0);
      cbn [cells_size csize Nat.add length] in FH0, BDC, FT0 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (BUF1 : stk bsegs mx B0 B1)
      by (destruct (Z_lt_le_dec B0 B1) as [BB|BB];
          [ destruct (AOUT BB) as (AO1 & _); destruct (AO1 ltac:(clear - BB; lia)) as (BO & _); pose proof (ablk_lits _ _ BO) as BOL;
            unfold held in P2; unfold held in P5; unfold held in AFO; pose proof (AFO BB) as AFB; unfold held in AFB;
            eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WMl |]; cbn [disjoint_from];
            split; [clear - BB P2 G4 G5 G6; lia|]; split; [clear - BB AFB; lia|]; split; [clear - BB BOL G11 G12; lia|]; split; [clear - BB P5; lia| exact I]
          | exact (stk_keep_empty m mx _ _ BUF BB) ]);
    assert (UBD : unpoisoned mx (FF + 32) (FF + 32 + 112))
      by (eapply sqs_fsh_unp; [exact SH0 | rewrite ESHF, shad_div; reflexivity | clear - FFc; Z.div_mod_to_equations; lia | clear - G1; lia | clear - G2; lia]);
    assert (AOBD : aro RNG mx (FF + 32) 40)
      by (split; [eapply unpoisoned_sub; [exact UBD | clear; lia | clear; lia]|];
          split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|];
          eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - FFc; Z.div_mod_to_equations; lia);
    assert (AHB : ahull RNG mx (FF + 32) 40)
      by (exists FF, (FF + 256); split; [clear; lia|]; split; [clear; lia|]; split; [clear - FFc; Z.div_mod_to_equations; lia|]; split; [clear - FFc; Z.div_mod_to_equations; lia|];
          split; [clear - G1; lia|]; split; [unfold KEND; clear - G2; lia|];
          replace (shad (FF + 256) - shad FF) with 32 by (rewrite !shad_div; clear - FFc; Z.div_mod_to_equations; lia); rewrite <- ESHF;
          split; [eapply (rw_cells_wr_at bsegs mx SHF _ 32 SH0); cbn [cells_size csize Nat.add length]; clear; lia | exact RSHF]);
    assert (ABD : app_blk (FF + 32) (FF + 32 + 40))
      by (eapply app_blk_sub; [apply ablk_app_blk; [exact FBK | clear; lia] | clear; lia | clear; lia | clear; lia]);
    assert (ART1 : art mx)
      by (eapply (sqs_art_trW m mx); [exact ART | exact MUL | exact WMl | intros A k HA HK; cbn [disjoint_from]; unfold held in BDL; clear - HA HK G1 G4 G11 BDL; repeat split; try exact I; lia]);
    assert (ASTK1 : astk RNG lo FRB) by (split; [unfold KHIGH; exact AST1 | split; [eapply rng_sub; [exact RSTK | clear; lia | clear - G5; lia] | exact RAI]])
    end.
    hold MUL. hold WMl.
    eapply evtF_cut.
    { eapply BIS;
      [ exact KXMI | exact BDC | clear - FFc; Z.div_mod_to_equations; lia | apply bytes_at_nil; clear - R3 R4; unfold zlen in *; lia | reflexivity
      | clear - G1; lia | clear - G2; lia | clear - R3; lia | clear - R4 NS; unfold zlen in *; lia | intros; exfalso; lia
      | exact STK | clear - G6; lia | clear - G3 G5; lia | left; clear - FLO; lia | unfold off_stack in P3; clear - P3 G5; lia
      | exact ABD | exact AOBD | exact AHB | intros; exfalso; lia | exact ART1 | exact ASTK1 ]. }
    clear BDC UBD AOBD AHB ABD ART1 ASTK1.
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc & r & -> & MUc & WMc & MIc & STKc & RES).
    destruct RES as [(_ & N1 & _) | (ER & HR & bs & BDC2)]; [exfalso; clear - N1; lia|].
    replace (ret_pc (Z_to_bv 64 591384)) with (Z_to_bv 64 591384) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    apply zd_is_error_true_iff in ER. unfold ZE_maxCode in ER.
    (* [comment removed for export] *)
    lazymatch type of FR0 with rw_cells _ ?mx _ _ =>
    assert (DJC : forall X k, 0 <= k -> (X + k <= FF + 32 \/ FF + 32 + 40 <= X) -> (X + k <= FRB - 2224 \/ FRB <= X) -> disjoint_from [(FF + 32, FF + 32 + 40); (FRB - 2224, FRB)] X k)
      by (intros X k Hk D1 D2; cbn [disjoint_from]; split; [exact D1 | split; [exact D2 | exact I]]);
    eapply (rw_cells_transport bsegs _ mx mc) in FR0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | right; clear - FLO G6; lia | right; clear; lia]];
    eapply (rw_cells_transport bsegs _ mx mc) in SH0; [| exact MUc | exact WMc | apply DJC; [clear; cbn; lia | unfold held in FBL; cbn [cells_size csize Nat.add length]; clear - FBL ESHF FFc; rewrite ESHF, shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | left; cbn [cells_size csize Nat.add length]; clear - G12 G6 AST1; lia]];
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
    assert (FF1 : rw_cells bsegs mc FF ([CB 32 jfh] ++ [CB 40 bs] ++ _)) by (apply rw_cells_app; split; [exact FH0 | apply rw_cells_app; cbn [cells_size csize Nat.add length]; split; [exact BDC2 | exact FT0]]).
    cbn [app] in FF1. clear FH0 BDC2 FT0.
    assert (MUX : munch [(SHF, SHF + 32); (FF, FF + 256)] mc mc) by apply munch_refl. assert (WMX : wmono bsegs mc mc) by apply wmono_refl.
    sqs_blob_all SH0.
    assert (DSF : SHF + 32 <= FF \/ FF + 256 <= SHF) by (unfold held in FBL; clear - FBL ESHF FFc; rewrite ESHF, shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
    hold MUc. hold WMc. hold ER. hold HR. hold DJC. hold BUFc. hold STKc. hold REP. hold HH3. hold H5V.
    try hold RLI. try hold DBS. try hold BIS. try hold BUF0. try hold MU0. try hold WM0. try hold FFR0. try hold AH. try hold AT0. try hold STM0. try hold IANC. try hold XRD. try hold RZ. try hold EXS. try hold Y9. try hold Y13. try hold Y14. try hold Y15. try hold FBL. try hold STKm. try hold GAPm. try hold SAVm. try hold LASTK. try hold FINK. try hold INITK. try hold RG0. try hold SD0. try hold SEP0. try hold TBL0. try hold AS0. try hold ASN0. try hold PRO0. try hold MMV. try hold MCP. try hold EXE. try hold TH3. try hold TB3. try hold MEM0. try hold P1. try hold P2. try hold P3. try hold P4. try hold P5. try hold P6. try hold P7. try hold P8. try hold Y3. try hold Y4. try hold Y5. try hold Y7. try hold Y8. try hold Y10. try hold Y11. try hold Y12. try hold AFD. try hold AFO. try hold AFS. try hold AFL. try hold AFT. try hold LBH. try hold INB_D. try hold INB_O. try hold FBK. try hold BDL. try hold LRD. try hold BUF. try hold TLLB. try hold SQB.
    kx_autoFLA (FR0, FF1, SH0) [] [0x92fe8] 48%nat
      [KZRange SPV 17594333495296 (2^47); KZRange FRB 17594333495296 (2^47 - 384); KZRange FF 6459392 (2^47 - 576); KZAlign SPV 16;
       KZRange SHF 2147450880 17594333495296; KZRange r (2^64 - 119) (2^64 - 1);
       KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZWr SHF 32; KZDisj SHF 32 FRB 280; KZDisj SHF 32 FF 256]
      [(FRB, 280); (FF, 256)]
      [(FRB, 280); (FF, 256); (SHF, 32)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_z]).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
    all: try sqs_aclose.
    all: kx_mem.
    all: unfold held in MUc; unfold held in WMc; unfold held in ER; unfold held in HR; unfold held in MUL; unfold held in WMl; unfold held in BUFc; unfold held in STKc; unfold held in REP; unfold held in HH3; unfold held in H5V.
    all: (unfold held in RLI, DBS, BIS, BUF0, MU0, WM0, FFR0, AH, AT0, STM0, IANC, XRD, RZ, EXS, Y9, Y13, Y14, Y15, FBL, STKm, GAPm, SAVm, LASTK, FINK, INITK, RG0, SD0, SEP0, TBL0, AS0, ASN0, PRO0, MMV, MCP, EXE, TH3, TB3, MEM0, P1, P2, P3, P4, P5, P6, P7, P8, Y3, Y4, Y5, Y7, Y8, Y10, Y11, Y12, AFD, AFO, AFS, AFL, AFT, LBH, INB_D, INB_O, FBK, BDL, LRD, BUF, TLLB, SQB; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - ER HR; lia end).
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x92fe8) _ _ ?my _) =>
      assert (NBF : (nbSeq =? 0) = false) by (apply Z.eqb_neq; clear - NB; lia);
      unfold sqs_fe in FINK; cbn [v_nbSeq v_fe] in FINK; try rewrite NBF in FINK;
      eapply (FINK my 18446744073709551596); [| clear; lia | left; reflexivity];
      sqs_blob_last FF1; sqs_blob_all SH0; sqs_blob_all FR0;
      pose proof (stk_of_rw_cells bsegs _ _ _ FR0) as FRS; cbn [cells_size csize Nat.add] in FRS;
      assert (MUB : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m my)
        by (eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MUL] | eapply munch_weaken; [| exact MUc]] | eapply munch_weaken; [| exact MUX]];
            unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx G4 G5 G6 ES1; lia);
      split; [eexists; exact FF1|]; split; [eexists; exact SH0|];
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
