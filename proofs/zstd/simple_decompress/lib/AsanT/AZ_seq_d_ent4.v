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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase
     AZ_seq_d_sbase AZ_seq_d_fin AZ_seq_d_last AZ_seq_d_xat AZ_seq_d_ad_at AZ_seq_d_iat AZ_seq_d_ikit AZ_seq_d_ickit AZ_seq_d_ekit2 AZ_seq_d_lkit2 AZ_seq_d_akit2 AZ_seq_d_end.
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

Section CANSEC1. Context {rc : runConstT}.

Lemma sqd_ent4 : forall P,
  sqd_mem P -> sqd_ranges P -> sqd_side P -> sqd_sep P -> (w_nbSeq P <> 0 -> sqd_tables P) -> sqd_astat P -> sqd_asan P (w_m P) -> sqd_pro P ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> zd_execend_stmtA ->
  (w_nbSeq P <> 0 -> w_LLT P + 4104 <= 2^47 /\ w_OFT P + 2056 <= 2^47 /\ w_MLT P + 4104 <= 2^47) ->
  (w_nbSeq P <> 0 -> (w_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_LLT P) /\ (w_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= w_OFT P) /\
                    (w_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= w_MLT P)) ->
  sqd_at_last P -> sqd_at_fin P ->
  (forall OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> LOCV = w_LOC P -> ai_I0 P OEND LLO LEND LOCV) ->
  w_LOC P = 1 -> w_nbSeq P <> 0 -> 1 <= zlen (w_sq P) -> sqd_at_anchor P.
Proof.
  intros P MEM RG SD SEP TBL AS ASN PRO MMV MCP EXE TH3 TB3 LASTK FINK INITK EL NB NS.
  pose proof MEM as MEM0. pose proof RG as RG0. pose proof SD as SD0. pose proof SEP as SEP0. pose proof TBL as TBL0. pose proof AS as AS0. pose proof ASN as ASN0. pose proof PRO as PRO0.
  pose proof (sqd_static_m0 P) as STM0. pose proof (sqd_static_m1 P) as STM1. pose proof (sqd_iinv_anchor P) as IANC. pose proof (sqd_asan_transport0 P) as AT0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqd_at_anchor sqd_at_last sqd_at_fin sqd_finv ai_I0 sqd_iregs sqd_ifrI sqd_imidA sqd_ic176A sqd_ifrA sqd_iffA] in *.
  cbn [app sqd_mem sqd_ranges sqd_side sqd_sep sqd_tables sqd_astat sqd_asan sqd_pro sqd_saved sqd_Wb sqd_post sqd_fe w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  intros ja jb jc jds jp jm x1 x5 x6 x7 x17 x25 x28 x29 x30 x31 FR0 FF0 SH0 STK GAP SAV.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5V & H5L). rewrite L4 in H5V. cbv beta delta [h5_vcells] in H5V. rewrite L1, L2, L3 in H5V. clear HH5.
  unfold dctx_ptrs, dctx_h1, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  destruct ASN as (ARD & AHD & ASQ & ATBL & ACL & AOUT & ALT & ALH & AZS & ART).
  destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & UD & RD & RDS). unfold DCTX_SIZEOF in BD, UD, RD, RDS.
  pose proof (ablk_lits _ _ BD) as BDL. pose proof (ablk_lits _ _ FBK) as FBL.
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  unfold KHIGH in AST1.
  assert (DST0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [rewrite E; apply Z.le_refl | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
  assert (RGF : 6443008 <= FF /\ FF + 256 + 320 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 17594333495296 <= FRB /\ FRB + 320 <= SPV /\ lo + 4304 <= FRB /\
                0 <= DST < 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495264 /\ 512 <= D8 /\ D8 + 11999 <= 2^44 /\ DCTX = 8 * D8).
  { rewrite ESHF, shad_div; unfold ASHOFF. clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R13 R14 R15 ES1 ATL AST1 ED8 DST0 BDL.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. lia. }
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G11 & G12 & GD1 & GD2 & GD3).
  assert (TLLB : nbSeq <> 0 -> 4096 <= LLT /\ 4096 <= OFT /\ 4096 <= MLT) by (intros NZ; destruct (TBL NZ) as (_ & _ & _ & T4 & T5 & T6 & _); clear - T4 T5 T6; lia).
  clear TBL.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256); (SHF, SHF + 32); (DCTX + 30004, DCTX + 30004 + 4)] m m) by apply munch_refl.
  assert (WMl : wmono bsegs m m) by apply wmono_refl.
  assert (LOC01 : LOC = 0 \/ LOC = 1) by (unfold ZSTD_not_in_dst, ZSTD_in_dst in Y6; exact Y6).
  (* [comment removed for export] *)
  assert (Z0 : m (wa (shad (DCTX + 26684))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m DCTX 95992); [exact UD | clear; lia | clear - GD3; Z.div_mod_to_equations; lia]).
  assert (Z1 : m (wa (shad (DCTX + 26688))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m DCTX 95992); [exact UD | clear; lia | clear - GD3; Z.div_mod_to_equations; lia]).
  rewrite shad_div in Z0, Z1. unfold ASHOFF in Z0, Z1.
  replace ((DCTX + 26684) / 8) with (D8 + 3335) in Z0 by (clear - GD3; Z.div_mod_to_equations; lia).
  replace ((DCTX + 26688) / 8) with (D8 + 3336) in Z1 by (clear - GD3; Z.div_mod_to_equations; lia).
  assert (RZ0 : rdn bsegs m (wa (2147450880 + D8 + 3335)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))) by (cbn [rdn]; replace (2147450880 + D8 + 3335) with (2147450880 + (D8 + 3335)) by (clear; lia); rewrite Z0; reflexivity).
  assert (RZ1 : rdn bsegs m (wa (2147450880 + D8 + 3336)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))) by (cbn [rdn]; replace (2147450880 + D8 + 3336) with (2147450880 + (D8 + 3336)) by (clear; lia); rewrite Z1; reflexivity).
  pose proof (bytes_at_sh2 m _ _ _ _ _ _ eq_refl eq_refl RZ0 RZ1 ltac:(clear; lia) ltac:(clear - GD1; lia) ltac:(clear - GD2; lia)) as RDS2.
  lazymatch type of RDS2 with bytes_at _ _ _ (?b0 :: ?b1 :: nil) =>
    assert (RDC : ro_cells bsegs m (2147450880 + D8 + 3335) [C1 b0; C1 b1]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS2]) end.
  clear RDS2 Z0 Z1.
  assert (RT2 : rng RNG (2147450880 + D8 + 3335) 2) by (eapply rng_sub'; [exact RDS |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - GD3; Z.div_mod_to_equations; lia).
  assert (SHFD8 : SHF + 32 <= 2147450880 + D8 \/ 2147450880 + D8 + 11999 <= SHF).
  { rewrite ESHF, shad_div; unfold ASHOFF. unfold held in AFD. clear - AFD GD3 GD1 FFc. Z.div_mod_to_equations. lia. }
  assert (FLO : FF + 256 <= lo) by (clear - FFb ATL; lia).
  assert (DLO : DCTX + 95992 <= lo) by (unfold held in BDL; clear - BDL ATR ATL AST1; lia).
  pose proof STK as STKm. pose proof GAP as GAPm. pose proof SAV as SAVm.
  rewrite EL in *.
  assert (LITBR : 0 <= LITB <= 2^47) by (destruct (Y7 eq_refl) as ((YA & YB) & _); clear - YA YB G7 R7 R8 R9; lia).
  assert (NB' : 1 <= nbSeq) by (clear - NB R5; lia). clear NB. rename NB' into NB.
    hold MU0. hold WM0. hold FFR0. hold AH. hold AT0. hold STM0. hold STM1. hold IANC. hold FBL. hold STKm. hold GAPm. hold SAVm. hold LASTK. hold FINK. hold INITK. hold RG0. hold SD0. hold SEP0. hold TBL0. hold AS0. hold ASN0. hold PRO0. hold MMV. hold MCP. hold EXE. hold TH3. hold TB3. hold MEM0. hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold Y3. hold Y4. hold Y5. hold Y7. hold Y8. hold Y10. hold Y11. hold Y12. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBH. hold INB_D. hold INB_O. hold FBK. hold BDL. hold LRD. hold BUF. hold TLLB. hold SQB.
    rewrite GD3 in H5V, HH1, HH3, REP, UD, RD, RDS, MUL |- *.
    rewrite (Z.shiftr_div_pow2 (8 * D8 + 30368) 3) by lia. change (2 ^ 3) with 8.
    kx_autoFLA (FR0, FF0, SH0, HH1, HH3, H5V, REP, RDC) [KAApp FRB 216; KAApp FF 256; KAApp (8 * D8) 95992; KAUnp (8 * D8) 95992; KAShp ((8 * D8 + 30368) / 8 + 2147450880) (8 * D8 + 30368)] [0x94840; 0x930fc; 0x94a04; 0x94a2c; 0x94a44; 0x94a5c; 0x94a74; 0x94cac; 0x94cb0; 0x94cb8; 0x94cc0; 0x94cc8; 0x93270] 400%nat
    [KZRange SPV 17594333499936 (2^47); KZRange FRB 17594333495296 (2^47 - 320); KZRange FF 6443008 (2^47 - 576); KZAlign SPV 16;
     KZRange SHF 2147450880 17594333495264; KZRange D8 512 (2^44 - 11999);
     KZRange DST 0 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32); KZRange (LITP + LITSZ) 4096 (2^47 - 32);
     KZRange SEQ 4096 (2^47); KZRange CAP 0 (2^47); KZRange LITB 0 (2^47); KZRange nbSeq 1 98047; KZRange (zlen sq) 1 (2^47);
     KZWord (2147450880 + D8 + 3335) 1 0; KZWord (2147450880 + D8 + 3336) 1 0;
     KZDisj FRB 216 (2147450880 + D8 + 3335) 2; KZDisj FF 256 (2147450880 + D8 + 3335) 2; KZDisj SHF 32 (2147450880 + D8 + 3335) 2; KZDisj (8 * D8 + 30004) 4 (2147450880 + D8 + 3335) 2;
     KZWr FRB 216; KZWr FF 256; KZWr SHF 32; KZWr (8 * D8 + 30004) 4;
     KZDisj FF 256 FRB 216; KZDisj SHF 32 FRB 216; KZDisj SHF 32 FF 256; KZDisj FRB 216 (8 * D8) 95992; KZDisj FF 256 (8 * D8) 95992; KZDisj SHF 32 (8 * D8) 95992;
     KZDisj SHF 32 (2147450880 + D8) 11999]
    [(FRB, 216); (FF, 256); (2147450880 + D8 + 3335, 2)]
    [(FRB, 216); (FF, 256); (SHF, 32); (8 * D8, 95992)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ mod 8 = 0 => split; [lia | assumption] | |- _ /\ rng _ _ _ => split; [lia | eapply rng_sub; [exact RSTK | clear - R13 R15 G4 G5 G6; lia | clear - R13 R15 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - GD1 GD2; lia | split; [clear - GD1; lia | split; [clear - GD2; lia | first [exact RZ0 | exact RZ1]]]] end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93270) _ _ _ _) => try sqd_oranges; try sqd_bvr; sqd_dead_core end).
    all: try sqd_aclose.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => unfold held in FBL; unfold held in BDL; unfold held in AFD; unfold KXKEND, KXSHLO, KXSHHI; clear - AFD FBL BDL G1 G2 G3 G4 G5 G6 G7 G11 G12 GD1 GD2 GD3 ATL ATR; lia end).
    all: lazymatch goal with |- evtF _ _ _ _ => idtac end.
    all: kx_mem.
    all: rewrite <- GD3 in *.
    all: (unfold held in MU0, WM0, FFR0, AH, AT0, STM0, STM1, IANC, FBL, STKm, GAPm, SAVm, LASTK, FINK, INITK, RG0, SD0, SEP0, TBL0, AS0, ASN0, PRO0, MMV, MCP, EXE, TH3, TB3, MEM0, P1, P2, P3, P4, P5, P6, P7, P8, Y3, Y4, Y5, Y7, Y8, Y10, Y11, Y12, AFD, AFO, AFS, AFL, AFT, LBH, INB_D, INB_O, FBK, BDL, LRD, BUF, TLLB, SQB; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x930fc) _ _ _ _) => fail | |- evtF _ _ _ _ => exfalso; clear - KXBR NB; lia end).
    (* [comment removed for export] *)
    unfold held in INITK. unfold held in IANC. unfold held in STM1. unfold held in MEM0. unfold held in TBL0. unfold held in TB3. unfold held in TH3.
    unfold held in STKm. unfold held in GAPm. unfold held in SAVm.
    unfold held in RG0. unfold held in SD0. unfold held in SEP0. unfold held in AS0. unfold held in ASN0. unfold held in PRO0. unfold held in MMV. unfold held in MCP. unfold held in EXE.
    apply sqd_sh14 in SH0.
    assert (NZ : nbSeq <> 0) by (clear - NB; lia).
    assert (NBF : (nbSeq =? 0) = false) by (apply Z.eqb_neq; exact NZ).
    unfold sqd_fe in IANC. cbn [w_nbSeq w_fe] in IANC. try rewrite NBF in IANC.
    destruct (TB3 NZ) as (TBa & TBb & TBc).
    (* [comment removed for export] *)
    lazymatch type of FF0 with rw_cells _ ?mx _ (?c0 :: CB 88 ?j :: ?rest) =>
      apply (rw_cells_split_CB bsegs mx FF [c0] 88 j rest [40; 48]%nat) in FF0; [| reflexivity]; cbn [mk_CB_cells app] in FF0 end.
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?oe) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (STM1 oe RG0 SD0 SEP0 (TBL0 NZ) AS0 ASN0 PRO0 MMV MCP EXE (TH3 NZ) NZ NS (eq_refl _) ltac:(reflexivity)) as ST;
      eapply (INITK _ _ _ _ ST (eq_refl _) m1);
      [ eapply (IANC _ _ _ _ m1); [exact ST | exact MEM0 | exact (TBL0 NZ) | reflexivity | clear; lia | exact TBa | exact TBb | exact TBc | exact MUL | exact WMl | exact KXMI | exact FR0 | exact FF0 | exact SH0 | exact HH3 | exact STKm | exact GAPm | exact SAVm]
      | .. ]
    end end.
    all: first [reflexivity | clear - GD3; lia | clear - GD3; Z.div_mod_to_equations; lia].
Qed.

End CANSEC1.
