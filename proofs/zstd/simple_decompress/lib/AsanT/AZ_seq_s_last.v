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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2 AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_xkit.
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

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqs_areg_trW : forall W RNG (m m' : amem) X n,
  areg RNG m X n -> munch W m m' -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X) -> areg RNG m' X n.
Proof.
  intros W RNG m m' X n A MU D Hn. destruct (A Hn) as (BK & U & R1 & R2).
  split; [exact BK|]. split; [eapply unp_tr; [exact U | exact MU | exact D]|]. split; [exact R1 | exact R2].
Qed.
Lemma sqs_aregU_trW : forall W RNG (m m' : amem) X n,
  aregU RNG m X n -> munch W m m' -> disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X) -> aregU RNG m' X n.
Proof.
  intros W RNG m m' X n (BK & U & R1 & R2) MU D.
  split; [exact BK|]. split; [eapply unp_tr; [exact U | exact MU | exact D]|]. split; [exact R1 | exact R2].
Qed.
Lemma sqs_art_trW : forall W (m m' : amem), art m -> munch W m m' -> wmono bsegs m m' ->
  (forall A cs, A + Z.of_nat (cells_size cs) <= 6443008 -> disjoint_from W A (Z.of_nat (cells_size cs))) -> art m'.
Proof.
  intros W m m' (G1 & G2 & G3 & G4 & G5 & G6) MU WM DJ.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU | exact WM | apply DJ; exact HA]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma sqs_mmove_spec : zd_memmoveZ_stmtA ->
  forall (RNG : footprint) (D S n SPz : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem) lo,
  stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) -> 0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMMOVE_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMMOVE_STACK_A \/ SPz <= S) -> (D + n <= lo \/ SPz <= D) ->
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk D (D + n) -> aro RNG m D n -> ahull RNG m D n ->
  art m -> astk RNG lo SPz -> mem_inv bsegs m ->
  evtF bsegs RNG (sqd_mcpy_post RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz D n lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMMOVE) fc None m (seg_rom bsegs)).
Proof.
  intros MM RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         STD RDS Hn STK LO SPT SS SD ABS AOS AHS ABD AOD AHD ART AST MI.
  unfold zd_memmoveZ_stmtA in MM.
  eapply evtF_mono.
  - eapply (MM RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
      [ exact STD | exact RDS | exact Hn | exact STK | exact LO | exact SPT | exact SS | exact SD
      | exact ABS | exact AOS | exact AHS | exact ABD | exact AOD | exact AHD | exact ART | exact AST | exact MI
      | reflexivity | reflexivity | reflexivity ].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DST').
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'| exact DST'].
Qed.

(* [comment removed for export] *)
Definition sqs_at_last (P : ssq) : Prop :=
  forall (m1 : amem) (OEND OP LP LEND LOCV S3 S5 : Z) (ja jb jc jd je jf jsh : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x24 x25 x26 x28 x29 x30 x31 : word),
  rw_cells bsegs m1 (v_FRB P) [CB 72 ja; C8 (Z_to_bv 64 (v_DCTX P)); C8 (Z_to_bv 64 (v_DST P)); CB 48 jb; C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P)); CB 40 jc;
                               C8 (Z_to_bv 64 LEND); CB 48 jd; C8 (Z_to_bv 64 LP); CB 24 je] ->
  rw_cells bsegs m1 (v_FF P) [CB 248 jf; C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))] ->
  rw_cells bsegs m1 (v_SHF P) [CB 32 jsh] ->
  (exists r0' r1' r2', rw_cells bsegs m1 (v_DCTX P + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) ->
  dctx_h3 bsegs m1 (v_DCTX P) (v_pcs P) (v_dsz P) (v_bt P) (v_stg P) (v_le P) (sqs_fe P) ->
  h5_viewed m1 (v_DCTX P) (v_ws P) (Z_to_bv 64 LOCV) ->
  stk bsegs m1 (v_B0 P) (v_B1 P) -> stk bsegs m1 (v_lo P) (v_FRB P) -> stk bsegs m1 (v_FRB P + 280) (v_SPV P + -104) ->
  rw_cells bsegs m1 (v_SPV P + -104) (sqs_saved P) ->
  munch (sqs_Wb P) (v_m P) m1 -> wmono bsegs (v_m P) m1 -> mem_inv bsegs m1 ->
  rdbl bsegs m1 LP (LEND + 32) ->
  (LOCV = 2 -> rdbl bsegs m1 (v_DCTX P + 30372) (v_DCTX P + 95940)) ->
  v_DST P <= OP -> OP <= OEND -> OEND <= v_DST P + v_CAP P ->
  ((LOCV = 0 /\ v_DCTX P + 30372 <= LP /\ LP <= LEND /\ LEND + 32 <= v_DCTX P + 95940) \/ (LOCV = 2 /\ v_LITP P <= LP /\ LP <= LEND /\ LEND = v_LBE P)) ->
  (* [comment removed for export] *)
  art m1 -> areg (v_RNG P) m1 (v_DCTX P) DCTX_SIZEOF -> ahull (v_RNG P) m1 (v_DCTX P) DCTX_SIZEOF ->
  (v_B0 P < v_B1 P -> aregU (v_RNG P) m1 (v_B0 P) (v_B1 P - v_B0 P) /\ ahull (v_RNG P) m1 (v_B0 P) (v_B1 P - v_B0 P)) ->
  (* [comment removed for export] *)
  S3 = v_DCTX P + 30368 -> S5 = 2147450880 + v_D8 P + 3796 ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10
             x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 S3) (Z_to_bv 64 OEND) (Z_to_bv 64 S5) x22 (Z_to_bv 64 OP) x24 x25 x26 (Z_to_bv 64 (v_SHF P))
             x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x8f668) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Local Ltac last_fin FIN FR FRF SHS REP HH3 BUF STK GAP SAV H5V MU WM G5 :=
  let FRS := fresh "FRS" in
  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
  eapply FIN;
  [ split; [eexists; exact FRF|]; split; [eexists; exact SHS|]; split; [eexists; eexists; eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|]; split; [exact SAV|]; split; [eexists; exact H5V|]; split; [exact MU|]; split; [exact WM | assumption]
  | | ].

Lemma sqs_last_ok : forall P, sqs_ranges P -> sqs_side P -> sqs_sep P -> sqs_astat P -> sqs_pro P -> v_LBE P - v_LITP P < 2^32 ->
  zd_memmoveZ_stmtA -> sqs_at_fin P -> sqs_at_lastb P -> sqs_at_last P.
Proof.
  intros P RG SD SEP AS PRO HLSZ MMV FIN LASTK. unfold sqs_at_last.
  intros m1 OEND OP LP LEND LOCV S3 S5 ja jb jc jd je jf jsh x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x24 x25 x26 x28 x29 x30 x31
         FR FRF SHS REP HH3 H5V BUF STK GAP SAV MU WM MI LIT XLIT H1 H2 H3 PH ART AD ADH AB ES3 ES5. subst S3 S5.
  unfold sqs_at_fin, sqs_finv, sqs_fe in FIN. unfold sqs_at_lastb, sqs_fe in LASTK. unfold sqs_fe in HH3. destruct REP as (r0' & r1' & r2' & REP).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_ranges sqs_side sqs_sep sqs_astat sqs_pro sqs_Wb sqs_saved sqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN, LASTK, REP, HH3, MU. destruct H5V as (H5R & H5L). unfold h5_vcells in H5R.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  remember (fflag L 2 FF) as FLG eqn:EFLG. remember (LEND - LP) as ll eqn:Ell.
  assert (BB : B0 < B1) by (apply Y13; clear - Y15 R6; lia).
  pose proof (Y9 Y14) as (LD1 & LD2).
  assert (RGF : 6443008 <= FF /\ FF + 256 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 4096 <= FRB /\ FRB + 384 <= SPV /\ lo + 4304 <= FRB /\
                4096 <= OP < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DST < 2^47 /\ 0 <= ll < 2^32 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296 /\ 4096 <= LP /\ LEND + 32 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 512 <= D8 /\ D8 + 11999 < 2^44)
    by (rewrite ESHF, shad_div; unfold ASHOFF; clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 Y15 ES1 ED8 ATL H1 H2 H3 PH Ell HLSZ; Z.div_mod_to_equations; lia).
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. clear - BL Hb1 Hb2. lia. }
  pose proof (ablk_lits _ _ FBK) as FBL.
  destruct (AB BB) as (ABU1 & ABH1). pose proof (ablk_lits _ _ (proj1 ABU1)) as BOL. replace (B0 + (B1 - B0)) with B1 in BOL by (clear; lia).
  unfold DCTX_SIZEOF in AD, ADH. destruct (AD ltac:(clear; lia)) as (BD & UD & RD & RSD).
  assert (RT1 : rng RNG (2147450880 + D8 + 3796) 1) by (eapply rng_sub'; [exact RSD |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - ED8; Z.div_mod_to_equations; lia).
  pose proof (sqs_loc_shadow RNG m1 DCTX D8 AD ED8) as RZ.
  pose proof (bytes_at_sh1 m1 _ _ _ eq_refl RZ ltac:(clear - G17; lia) ltac:(clear - G18; lia)) as RDS.
  lazymatch type of RDS with bytes_at _ _ _ (?b :: nil) =>
    assert (RDC : ro_cells bsegs m1 (2147450880 + D8 + 3796) [C1 b]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS]) end.
  clear RDS RZ.
  assert (MU1 : munch [(FF, FF + 256)] m1 m1) by apply munch_refl. assert (WM1 : wmono bsegs m1 m1) by apply wmono_refl.
  (* [comment removed for export] *)
  assert (KD1 : DCTX + 30096 + 276 <= FRB \/ FRB + 280 <= DCTX + 30096) by (clear - P1 G5 G6; lia).
  assert (KD2 : DCTX + 30096 + 276 <= FF \/ FF + 256 <= DCTX + 30096) by (clear - AFD; lia).
  assert (KD3 : DCTX + 30096 + 276 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= DCTX + 30096) by (clear - BDL ED8 ATR; lia).
  assert (KD4 : FRB + 280 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= FRB) by (clear - G18 G5 G6 ATL ATR; lia).
  hold REP. hold HH3. hold MU. hold WM. hold MU0. hold WM0. hold FFR0. hold AH. hold FIN. hold LASTK. hold LIT. hold XLIT. hold AD. hold ADH. hold AB. hold MMV. hold ABU1. hold ABH1.
  hold Y1. hold Y2. hold Y3. hold Y4. hold Y5. hold Y6. hold Y7. hold Y8. hold Y9. hold Y10. hold Y11. hold Y12. hold Y13. hold Y14. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBA. hold LBH. hold INB_D. hold INB_O.
  hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold BDL. hold FFL. hold FRL. hold BOL. hold ED8. hold ESHF. hold FFc. hold ES1b.
  destruct PH as [(EL & Q1 & Q2 & Q3)|(EL & Q1 & Q2 & Q3)]; subst LOCV.
  (* [comment removed for export] *)
  all: kx_autoFLA (FR, FRF, H5R, RDC) [] [0x8f6d0; 0x91ffc; 0x53ee0] 60%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange DST 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992); KZRange D8 512 (2^44);
     KZRange SHF 2147450880 17594333495264; KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 280;
     KZDisj FRB 280 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276; KZDisj (DCTX + 30096) 276 (2147450880 + D8 + 3796) 1; KZDisj FRB 280 (2147450880 + D8 + 3796) 1]
    [(FRB, 280); (FF, 256); (DCTX + 30096, 276); (2147450880 + D8 + 3796, 1)]
    [(FRB, 280); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: try sqs_aclose.
  all: kx_mem.
  all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, XLIT, AD, ADH, AB, MMV, ABU1, ABH1.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8f6d0) _ _ ?mx _) =>
        (* [comment removed for export] *)
        eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3 | split; [exact H5R | exact H5L] | exact BUF | exact STK | exact GAP | exact SAV
                      | exact MU | exact WM | assumption | exact LIT | exact H1 | exact H2 | exact H3 | exact Q1 | exact Q2 | exact Q3 | exact ART | exact AD | exact ADH | exact AB]
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x91ffc) _ _ ?mx _) =>
        (* [comment removed for export] *)
        sqs_blob_last FRF;
        assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
          by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
        assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
        unfold held in AFD;
        assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
          by (eapply sqd_dctx_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
        assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
          by (eapply sqd_dctx_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
        assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 2)) by (split; [exact H5R | exact H5L]);
        replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
        last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x53ee0) _ _ _ _) => idtac
    end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia).
  unfold held in BOL. unfold held in BDL.
  (* [comment removed for export] *)
  assert (ABU : aregU RNG mA B0 (B1 - B0)) by (eapply sqd_aregU_trF; [exact ABU1 | exact MU1 | clear - BOL; lia | clear - BB; lia | clear - BOL ATR; lia | clear - FBL; lia | clear - G1; lia]).
  assert (ABH : ahull RNG mA B0 (B1 - B0)) by (eapply sqd_ahull_tr; [exact ABH1 | exact WM1]).
  rename ART into ART1.
  assert (ART : art mA) by (eapply sqd_art_trF; [exact ART1 | exact MU1 | exact WM1 | exact G1]).
  unfold held in LIT. unfold held in XLIT. unfold held in P1. unfold held in P2. unfold held in P5. unfold held in AFD. unfold held in AFO. unfold held in MMV.
  assert (OB : B0 <= OP /\ OP + ll <= B1 /\ OP + ll <= OEND) by (clear - H1 H2 H3 HFIT R6 R7 G10; lia). destruct OB as (OB1 & OB2 & OB3).
  assert (SB : B0 <= LP /\ LP + ll <= B1) by (clear - LD1 LD2 Q1 Q2 Q3 Ell R6 R7 G10; lia). destruct SB as (SB1 & SB2).
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?nn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    assert (Enn : nn = ll) by (clear - Ell; lia); rewrite Enn end.
  eapply evtF_cut.
  { eapply (sqs_mmove_spec MMV RNG OP LP ll FRB);
      [ eapply stk_sub; [exact BUF | exact OB1 | clear - G10; lia | exact OB2]
      | eapply rdbl_sub; [exact LIT | clear; lia | clear - Ell G10; lia]
      | clear - G10; lia
      | exact STK | clear - G6; lia | clear - G4 G5 G3; lia
      | clear - P2 SB1 SB2 G5 G6 R13; lia
      | clear - P2 OB1 OB2 G6 G5 R13; lia
      | eapply aregU_app_blk; [eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact SB1 | clear - G10; lia | clear - SB2; lia] | clear - G10; lia]
      | apply aregU_aro; eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact SB1 | clear - G10; lia | clear - SB2; lia]
      | eapply ahull_sub; [exact ABH | exact SB1 | clear - SB2; lia]
      | eapply aregU_app_blk; [eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact OB1 | clear - G10; lia | clear - OB2; lia] | clear - G10; lia]
      | apply aregU_aro; eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact OB1 | clear - G10; lia | clear - OB2; lia]
      | eapply ahull_sub; [exact ABH | exact OB1 | clear - OB2; lia]
      | exact ART
      | exact (astk_sub RNG lo SPV FRB (conj AST1 (conj RSTK RAI)) ltac:(clear - G5 G6 R13; lia))
      | assumption ]. }
  cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mC & -> & MUC & WMC & MIC & STKC & DSTC).
  replace (ret_pc (Z_to_bv 64 0x8f698)) with (Z_to_bv 64 0x8f698) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (DJS : forall A k, 0 <= k -> (A + k <= FRB - MEMMOVE_STACK_A \/ FRB <= A) -> (A + k <= OP \/ OP + ll <= A) -> disjoint_from [(FRB - MEMMOVE_STACK_A, FRB); (OP, OP + ll)] A k).
  { intros A k Hk X1 X2. cbn [disjoint_from]. split; [clear - X1 Hk; lia|]. split; [clear - X2 Hk; lia| exact I]. }
  unfold KHIGH in AST1.
  assert (FRc : rw_cells bsegs mC FRB [CB 72 ja; C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST); CB 48 jb; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); CB 40 jc;
                                       C8 (Z_to_bv 64 LEND); CB 48 jd; C8 (Z_to_bv 64 LP); CB 24 je]).
  { eapply rw_cells_transport; [exact FR | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
  assert (FRFc : rw_cells bsegs mC FF [CB 248 jf; C8 (Z_to_bv 64 FLG)]).
  { eapply rw_cells_transport; [exact FRF | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - FFb ATL G6; lia | clear - AFO BB OB1 OB2; lia]]. }
  assert (SHSc : rw_cells bsegs mC SHF [CB 32 jsh]).
  { eapply rw_cells_transport; [exact SHS | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G12 AST1 G6; lia | clear - BOL OB1 OB2 G11 G12 ATR; lia]]. }
  assert (REPc : rw_cells bsegs mC (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2']).
  { eapply rw_cells_transport; [exact REP | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
  assert (HH3c : rw_cells bsegs mC (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)]).
  { eapply rw_cells_transport; [exact HH3 | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
  assert (H5Rc : rw_cells bsegs mC (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (Z_to_bv 64 2)]).
  { eapply rw_cells_transport; [exact H5R | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
  lazymatch type of RDC with ro_cells _ _ _ ?cs => assert (RDCc : ro_cells bsegs mC (2147450880 + D8 + 3796) cs) end.
  { eapply ro_cells_transport; [exact RDC | exact MUC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G18 ATL G6 ATR; lia | clear - BOL OB1 OB2 G17 G18 ATR; lia]]. }
  assert (GAPc : stk bsegs mC (FRB + 280) (SPV + -104)).
  { eapply stk_transport_disjoint; [exact GAP | exact MUC | exact WMC | apply DJS; [clear - G5; lia | clear; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
  assert (SAVc : rw_cells bsegs mC (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact SAV | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G5; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
  assert (BUFc : stk bsegs mC B0 B1).
  { destruct (stk_split bsegs mA B0 OP B1 BUF ltac:(clear - OB1 OB2 G10; lia)) as [BL BR0].
    destruct (stk_split bsegs mA OP (OP + ll) B1 BR0 ltac:(clear - OB2 G10; lia)) as [_ BR].
    apply (stk_merge bsegs mC B0 OP B1); [| | clear - OB1 OB2 G10; lia].
    - eapply stk_transport_disjoint; [exact BL | exact MUC | exact WMC | apply DJS; [clear - OB1; lia | clear - P2 OB1 OB2 G10 G5 G6 R13; lia | clear; lia]].
    - apply (stk_merge bsegs mC OP (OP + ll) B1); [exact DSTC | | clear - OB2 G10; lia].
      eapply stk_transport_disjoint; [exact BR | exact MUC | exact WMC | apply DJS; [clear - OB2 G10; lia | clear - P2 OB1 OB2 G10 G5 G6 R13; lia | clear; lia]]. }
  assert (XLITc : rdbl bsegs mC (DCTX + 30372) (DCTX + 95940)).
  { eapply rdbl_transport; [exact (XLIT eq_refl) | exact MUC |]. intros x Hx; left. apply (disjoint_outside _ x 1 x); [| clear; lia]. apply DJS; [clear; lia | clear - P1 G5 G6 Hx; lia | clear - P5 OB1 OB2 BB Hx; lia]. }
  assert (MUc : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mC).
  { eapply munch_trans; [exact MU | eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUC]]];
      unfold sub_fp; cbn [outside]; intros x Hx; [clear - Hx; lia | clear - Hx ES1 G6 R13 H1 OB3 H3; lia]. }
  assert (WMc : wmono bsegs m mC) by (eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WMC]]).
  assert (ARTc : art mC).
  { eapply sqs_art_trW; [exact ART | exact MUC | exact WMC |]. intros A cs HA. apply DJS; [clear; lia | clear - HA G5 G6 ATL ATR; lia | clear - HA BOL OB1 OB2; lia]. }
  assert (ADa : areg RNG mA DCTX 95992).
  { eapply sqs_areg_trW; [exact AD | exact MU1 |]. rewrite !shad_div; unfold ASHOFF. cbn [disjoint_from]. split; [clear - G15 G16 FBL ATR; Z.div_mod_to_equations; lia | exact I]. }
  assert (ADc : areg RNG mC DCTX 95992).
  { eapply sqs_areg_trW; [exact ADa | exact MUC |]. rewrite !shad_div; unfold ASHOFF. apply DJS; [clear - G15; Z.div_mod_to_equations; lia | clear - G15 G16 G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - G15 G16 BOL OB1 OB2 ATR; Z.div_mod_to_equations; lia]. }
  assert (ADHc : ahull RNG mC DCTX 95992) by (eapply sqd_ahull_tr; [eapply sqd_ahull_tr; [exact ADH | exact WM1] | exact WMC]).
  assert (ABUc : aregU RNG mC B0 (B1 - B0)).
  { eapply sqs_aregU_trW; [exact ABU | exact MUC |]. replace (B0 + (B1 - B0) - 1) with (B1 - 1) by (clear; lia). rewrite !shad_div; unfold ASHOFF.
    apply DJS; [clear - BB; Z.div_mod_to_equations; lia | clear - BOL BB G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - BOL BB OB1 OB2 ATR; Z.div_mod_to_equations; lia]. }
  assert (ABHc : ahull RNG mC B0 (B1 - B0)) by (eapply sqd_ahull_tr; [exact ABH | exact WMC]).
  clear FR FRF SHS REP HH3 H5R RDC GAP SAV BUF STK DSTC ART ADa ABU ABH AD ADH AB ABU1 ABH1 ART1 LIT XLIT.
  assert (MU2 : munch [(FRB, FRB + 280); (DCTX + 30368, DCTX + 30368 + 4)] mC mC) by apply munch_refl. assert (WM2 : wmono bsegs mC mC) by apply wmono_refl.
  assert (KAD : DCTX + 30368 + 4 <= 2147450880 \/ 17594333495296 <= DCTX + 30368) by (clear - BDL; lia).
  unfold held in ED8. pose proof (sqs_loc_shadow RNG mC DCTX D8 ADc ED8) as RZc.
  hold FIN. hold LASTK. hold MMV. hold XLITc. hold P1. hold P2. hold P5. hold AFD. hold AFO. hold BDL. hold BOL. hold REPc. hold HH3c. hold SHSc. hold GAPc. hold SAVc. hold BUFc. hold STKC.
  hold MUc. hold WMc. hold MUC. hold WMC. hold ARTc. hold ADc. hold ADHc. hold ABUc. hold ABHc. hold DJS.
  (* [comment removed for export] *)
  kx_autoFLA (FRc, H5Rc, RDCc) [KAApp (DCTX + 30368) 4] [0x8f6d0] 40%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange DST 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992); KZRange D8 512 (2^44);
     KZWord (2147450880 + D8 + 3796) 1 0;
     KZWr FRB 280; KZWr (DCTX + 30368) 4;
     KZDisj FRB 280 (DCTX + 30096) 276; KZDisj (DCTX + 30096) 276 (2147450880 + D8 + 3796) 1; KZDisj FRB 280 (2147450880 + D8 + 3796) 1]
    [(FRB, 280); (DCTX + 30096, 276); (2147450880 + D8 + 3796, 1)]
    [(FRB, 280); (DCTX + 30368, 4)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ _ => split; [clear - G17 G18; lia | split; [clear - G17; lia | split; [clear - G18; lia | exact RZc]]] end).
  all: try sqs_aclose.
  all: kx_mem.
  all: unfold held in FIN, LASTK, MMV, XLITc, P1, P2, P5, AFD, AFO, BDL, BOL, REPc, HH3c, SHSc, GAPc, SAVc, BUFc, STKC.
  all: unfold held in MUc, WMc, MUC, WMC, ARTc, ADc, ADHc, ABUc, ABHc, DJS.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8f6d0) _ _ ?mx _) =>
        assert (DJ2 : forall A k, 0 <= k -> (A + k <= FRB \/ FRB + 280 <= A) -> (A + k <= DCTX + 30368 \/ DCTX + 30368 + 4 <= A) -> disjoint_from [(FRB, FRB + 280); (DCTX + 30368, DCTX + 30368 + 4)] A k)
          by (intros A k Hk X1 X2; cbn [disjoint_from]; split; [clear - X1 Hk; lia|]; split; [clear - X2 Hk; lia| exact I]);
        assert (REPf : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
          by (eapply rw_cells_transport; [exact REPc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - P1 G5 G6; lia | clear; lia]]);
        assert (HH3f : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
          by (eapply rw_cells_transport; [exact HH3c | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - P1 G5 G6; lia | clear; lia]]);
        assert (SHSf : rw_cells bsegs mx SHF [CB 32 jsh])
          by (eapply rw_cells_transport; [exact SHSc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - G12 AST1 ATL G6; lia | clear - KAD G11 G12; lia]]);
        assert (GAPf : stk bsegs mx (FRB + 280) (SPV + -104))
          by (eapply stk_transport_disjoint; [exact GAPc | exact MU2 | exact WM2 | apply DJ2; [clear - G5; lia | clear; lia | clear - P1 G5 G6; lia]]);
        assert (SAVf : rw_cells bsegs mx (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
          by (eapply rw_cells_transport; [exact SAVc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - G5; lia | clear - P1 G5 G6; lia]]);
        assert (BUFf : stk bsegs mx B0 B1)
          by (eapply stk_transport_disjoint; [exact BUFc | exact MU2 | exact WM2 | apply DJ2; [clear - BB; lia | clear - P2 G5 G6 R13; lia | clear - P5 BB; lia]]);
        assert (STKf : stk bsegs mx lo FRB)
          by (eapply stk_transport_disjoint; [exact STKC | exact MU2 | exact WM2 | apply DJ2; [clear - G6; lia | clear; lia | clear - P1 G5 G6; lia]]);
        assert (XLITf : rdbl bsegs mx (DCTX + 30372) (DCTX + 95940))
          by (eapply rdbl_transport; [exact XLITc | exact MU2 |]; intros x Hx; left; apply (disjoint_outside _ x 1 x); [| clear; lia]; apply DJ2; [clear; lia | clear - P1 G5 G6 Hx; lia | clear - Hx; lia]);
        assert (MUf : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
          by (eapply munch_trans; [exact MUc | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx ES1 R13; lia]);
        assert (WMf : wmono bsegs m mx) by (eapply wmono_trans; [exact WMc | exact WM2]);
        assert (ARTf : art mx)
          by (eapply sqs_art_trW; [exact ARTc | exact MU2 | exact WM2 |]; intros A cs HA; apply DJ2; [clear; lia | clear - HA G5 G6 ATL ATR; lia | clear - HA BDL; lia]);
        assert (ADf : areg RNG mx DCTX 95992)
          by (eapply sqs_areg_trW; [exact ADc | exact MU2 |]; rewrite !shad_div; unfold ASHOFF; apply DJ2; [clear - G15; Z.div_mod_to_equations; lia | clear - G15 G16 G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - G15 G16 BDL ATR; Z.div_mod_to_equations; lia]);
        assert (ADHf : ahull RNG mx DCTX 95992) by (eapply sqd_ahull_tr; [exact ADHc | exact WM2]);
        assert (ABUf : aregU RNG mx B0 (B1 - B0))
          by (eapply sqs_aregU_trW; [exact ABUc | exact MU2 |]; replace (B0 + (B1 - B0) - 1) with (B1 - 1) by (clear; lia); rewrite !shad_div; unfold ASHOFF;
              apply DJ2; [clear - BB; Z.div_mod_to_equations; lia | clear - BOL BB G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - BOL BB BDL ATR; Z.div_mod_to_equations; lia]);
        assert (ABHf : ahull RNG mx B0 (B1 - B0)) by (eapply sqd_ahull_tr; [exact ABHc | exact WM2]);
        eapply LASTK; [exact FRc | exact FRFc | exact SHSf | eexists; eexists; eexists; exact REPf | exact HH3f | split; [exact H5Rc | exact H5L] | exact BUFf | exact STKf | exact GAPf | exact SAVf
                      | exact MUf | exact WMf | assumption | eapply rdbl_sub; [exact XLITf | clear; lia | clear; lia] | clear - H1 HFIT G10; lia | clear - OB3; lia | exact H3
                      | clear; lia | clear; lia | clear; lia | exact ARTf | exact ADf | exact ADHf | intros _; split; [exact ABUf | exact ABHf]]
    end.
  Unshelve. all: try exact 0%nat. all: try exact nil.
Qed.

End CANSEC1.
