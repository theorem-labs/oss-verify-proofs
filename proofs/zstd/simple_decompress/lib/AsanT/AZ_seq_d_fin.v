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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Ltac sqd_blob_last H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let n := eval cbv in (Nat.pred (length cs)) in
    let mid := eval cbn [firstn] in (firstn n cs) in
    let lst := eval cbn [skipn] in (skipn n cs) in
    change (rw_cells sg mm A ([] ++ mid ++ lst)) in H;
    apply (rw_cells_merge sg mm A [] mid lst) in H;
    cbn [app cells_size csize Nat.add length] in H
  end.
(* [comment removed for export] *)
Ltac sqd_blob_all H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    change (rw_cells sg mm A ([] ++ cs ++ [])) in H;
    apply (rw_cells_merge sg mm A [] cs []) in H;
    cbn [app cells_size csize Nat.add length] in H
  end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqd_byte_of_c1 : forall (m : amem) s b, rw_cells bsegs m s [C1 b] -> 0x625000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqd_byte_of_cb1 : forall (m : amem) s b, rw_cells bsegs m s [CB 1 [b]] -> 0x625000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.

Lemma sqd_mem_eq_single : forall (mp m' : amem) A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> forall x, m' x = write_to_mem mp (wa A) [b] x.
Proof.
  intros mp m' A b HA HB MU Hb x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Lemma sqd_aheap_eq : forall AI L RNG st LB (m m' : amem), AHEAP AI L RNG st LB m -> (forall x, m' x = m x) -> AHEAP AI L RNG st LB m'.
Proof.
  intros AI L RNG st LB m m' AH E. eapply (AI_frame AI) with (W := []); [exact AH| | | constructor].
  - intros x _. apply E.
  - intros x Hx. unfold wview in *. rewrite E. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sqd_aheap_now : forall P (m1 : amem), sqd_ranges P -> sqd_astat P -> sqd_pro P ->
  munch (sqd_Wb P) (w_m P) m1 -> wmono bsegs (w_m P) m1 ->
  AHEAP (w_AI P) (w_L P) (w_RNG P) (w_st P) (FKB 2 (w_FF P) 256 :: w_LB P) m1.
Proof.
  intros P m1 RG AS PRO MU WM.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_ranges sqd_astat sqd_pro sqd_Wb w_m w_AI w_L w_RNG w_st w_FF w_LB] in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa.
  assert (ESHF' : 8 * (SHF - ASHOFF) = FF).
  { rewrite ESHF, shad_div. unfold ASHOFF. clear - FFc FFa. Z.div_mod_to_equations. lia. }
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_SIZEOF in *.
  (* [comment removed for export] *)
  assert (C_D1 : aclient_range (aci AI) (FKB 2 FF 256 :: LB) (ATOP + 4096) (DCTX + 26684) (DCTX + 26684 + 12 - (DCTX + 26684))).
  { right; left. destruct INB_D as (b & Hb & H1 & H2). exists b. split; [right; exact Hb | clear - H1 H2; lia]. }
  assert (C_D2 : aclient_range (aci AI) (FKB 2 FF 256 :: LB) (ATOP + 4096) (DCTX + 30004) (DCTX + 30004 + 4 - (DCTX + 30004))).
  { right; left. destruct INB_D as (b & Hb & H1 & H2). exists b. split; [right; exact Hb | clear - H1 H2; lia]. }
  assert (C_S : aclient_range (aci AI) (FKB 2 FF 256 :: LB) (ATOP + 4096) (SPV - SEQ_STACK_A) (SPV - (SPV - SEQ_STACK_A))).
  { left; left. clear - ATL R13 R14. lia. }
  assert (C_F : aclient_range (aci AI) (FKB 2 FF 256 :: LB) (ATOP + 4096) FF (FF + 256 - FF)).
  { left; right; right. exists 2, FF, 256. split; [left; reflexivity | clear; lia]. }
  assert (C_H : aclient_range (aci AI) (FKB 2 FF 256 :: LB) (ATOP + 4096) SHF (SHF + 32 - SHF)).
  { right; right. rewrite ESHF'. right; right. exists 2, FF, 256. split; [left; reflexivity | clear; lia]. }
  destruct (Z.eq_dec CAP 0) as [C0|C0].
  - subst CAP. pose proof (munch_drop_empty DST _ m m1 MU) as MU5.
    eapply (AI_frame AI); [exact AH | exact MU5 | exact WM |].
    constructor; [exact C_D1|]. constructor; [exact C_D2|]. constructor; [exact C_S|]. constructor; [exact C_F|]. constructor; [exact C_H| constructor].
  - eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
    constructor.
    { cbn [fst snd]. right; left. assert (BB : B0 < B1) by (clear - R6 R7 R8 C0; lia).
      destruct (INB_O BB) as (b & Hb & H1 & H2). exists b. split; [right; exact Hb | clear - H1 H2 R6 R7 R8; lia]. }
    constructor; [exact C_D1|]. constructor; [exact C_D2|]. constructor; [exact C_S|]. constructor; [exact C_F|]. constructor; [exact C_H| constructor].
Qed.

(* [comment removed for export] *)
Definition sqd_finv (P : sqp) (m1 : amem) : Prop :=
  (exists jf, rw_cells bsegs m1 (w_FF P) [CB 248 jf; C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))]) /\
  (exists jsh, rw_cells bsegs m1 (w_SHF P) [CB 32 jsh]) /\
  (exists r0' r1' r2', rw_cells bsegs m1 (w_DCTX P + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) /\
  dctx_h3 bsegs m1 (w_DCTX P) (w_pcs P) (w_dsz P) (w_bt P) (w_stg P) (w_le P) (sqd_fe P) /\
  stk bsegs m1 (w_B0 P) (w_B1 P) /\ stk bsegs m1 (w_lo P) (w_FRB P) /\ stk bsegs m1 (w_FRB P) (w_SPV P + -104) /\
  rw_cells bsegs m1 (w_SPV P + -104) (sqd_saved P) /\
  munch (sqd_Wb P) (w_m P) m1 /\ wmono bsegs (w_m P) m1 /\ mem_inv bsegs m1.

(* [comment removed for export] *)
Definition sqd_at_fin (P : sqp) : Prop :=
  forall (m1 : amem) (r : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  sqd_finv P m1 -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= w_CAP P) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) (Z_to_bv 64 r)
             (Z_to_bv 64 18446744073709551605) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 x20 x21 x22 (Z_to_bv 64 (w_FF P)) x24 x25 x26
             x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x94908) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqd_ffr_fin : forall AI L RNG st LB (m0 m m5 : amem) FF SHF FLG DST CAP DCTX SPV lo,
  AHEAP AI L RNG st (FKB 2 FF 256 :: LB) m ->
  (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
  (forall b, In b LB -> FF + 256 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
  (forall b, In b LB -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG) ->
  ablk FLG (FLG + 1) -> ablk FF (FF + 256) -> 0 <= FF -> FF + 256 <= 2^47 -> FF mod 8 = 0 -> SHF = shad FF -> ATOP + 4096 <= lo -> lo <= SPV - SEQ_STACK_A -> SPV <= 2^47 ->
  (CAP <= 0 \/ (6443008 <= DST /\ DST + CAP <= 2147446784) \/ (17594333495296 <= DST /\ DST + CAP <= 2^47)) ->
  ((6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= 2^47)) ->
  ffr_pres [] LB m0 m ->
  munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4);
         (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32); (FLG, FLG + 1)] m m5 ->
  wmono bsegs m m5 ->
  ffr_pres [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4)] LB m0 m5.
Proof.
  intros AI L RNG st LB m0 m m5 FF SHF FLG DST CAP DCTX SPV lo AH LBH LBA FLA FLB FBK FF0 FF1 FF8 ESHF LO LO2 SPT BO BD FFR MU WM.
  pose proof atop_range as ATR. pose proof (ablk_lits _ _ FBK) as FBL.
  unfold ffr_pres in *.
  eapply magree_trans; [eapply magree_mono; [exact FFR |]; intros a [(H1 & _)|H2]; [left; split; [exact H1| cbn; exact I] | right; exact H2]|].
  eapply magree_mono; [eapply magree_of_munch; [exact MU | exact WM] |].
  intros a [((cls & FA & fn & Hin & Ha) & OUT)|(a' & (cls & FA & fn & Hin & Ha') & ->)]; cbn [outside].
  - (* [comment removed for export] *)
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    pose proof (LBA _ Hin) as A1. pose proof (FLA _ Hin) as A2. pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A1, A2, A3.
    cbn [outside] in OUT. destruct OUT as (O1 & O2 & O3 & _).
    pose proof (ablk_lits _ _ A3) as A4. rewrite ESHF, shad_div. unfold ASHOFF, AIMG_HI in *.
    clear - Ha B1 B2 B3 A1 A2 A4 O1 O2 O3 LO LO2 SPT FF0 FF1 ATR. Z.div_mod_to_equations. repeat (split; [lia|]). exact I.
  - (* [comment removed for export] *)
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH ltac:(right; exact Hin)) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
    pose proof (LBA _ Hin) as A1. pose proof (LBH _ Hin) as A3. cbn [ab_addr ab_size] in A1, A3.
    pose proof (ablk_lits _ _ A3) as A4. pose proof (ablk_lits _ _ FLB) as A5.
    rewrite ESHF, !shad_div. unfold ASHOFF, AIMG_HI, DCTX_entropy_rep, DCTX_fseEntropy in *.
    (* [comment removed for export] *)
    clear - Ha' B1 B2 B3 A1 A4 A5 LO LO2 SPT FF0 FF1 FF8 ATR BO BD FBL. Z.div_mod_to_equations. repeat (split; [lia|]). exact I.
Qed.

(* [comment removed for export] *)
Lemma sqd_fin_ok : forall P, sqd_ranges P -> sqd_astat P -> sqd_pro P -> sqd_at_fin P.
Proof.
  intros P RG AS PRO. unfold sqd_at_fin.
  intros m1 r x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 FINV HR RES.
  pose proof (sqd_aheap_now P m1 RG AS PRO) as AHN.
  destruct FINV as ((jf & FRF) & (jsh & SHS) & (r0' & r1' & r2' & REP) & HH3 & BUF & STK & GAP & SAV & MU & WM & MI).
  specialize (AHN MU WM).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_ranges sqd_astat sqd_pro sqd_Wb sqd_saved sqd_fe sqd_post w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. destruct AST as (AST1 & RSTK & RAI).
  (* [comment removed for export] *)
  destruct (FFL _ _ _ _ _ _ _ _ AHN ltac:(left; reflexivity)) as (FLC & RFL & FLB & FLT & FLA & FLI & FLlo & FLhi).
  remember (fflag L 2 FF) as FLG eqn:EFLG.
  pose proof (ablk_lits _ _ FLB) as FLL. pose proof (ablk_lits _ _ FBK) as FBL.
  assert (ESHF' : SHF = 2147450880 + FF / 8) by (rewrite ESHF, shad_div; reflexivity).
  assert (FF8 : FF mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (RGF : 6443008 <= FF <= 2^47 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296 /\ 17594333499936 <= SPV < 2^47 /\ 4096 <= FRB /\ FRB + 320 <= SPV /\ lo <= FRB /\ 6443008 <= FLG /\ FLG + 1 <= ATOP)
    by (clear - FFa FFb ATR ESHF' R13 R14 R15 ES1 ATL FLL FLT; Z.div_mod_to_equations; lia).
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. unfold DCTX_SIZEOF in *. clear - BL Hb1 Hb2. lia. }
  (* [comment removed for export] *)
  assert (MU1 : munch [(SHF, SHF + 32)] m1 m1) by apply munch_refl. assert (WM1 : wmono bsegs m1 m1) by apply wmono_refl.
  hold REP. hold HH3. hold MU. hold WM. hold AHN. hold FLC. hold MU0. hold WM0. hold FFR0.
  kx_autoFLA (SHS, FRF) [] [0x9498c] 48%nat
    [KZRange FF 6443008 (2^47); KZRange SHF 2147450880 17594333495264; KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47);
     KZWr SHF 32; KZDisj SHF 32 FF 256]
    [(FF, 256)]
    [(FF, 256); (SHF, 32)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 ESHF' FBL FLL ATR; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6 G7; lia | clear - R13 G4 G5 G6 G7; lia]] end).
  all: kx_mem.
  unfold held in REP, HH3, MU, WM, AHN, FLC, MU0, WM0, FFR0.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  (* [comment removed for export] *)
  assert (AH2 : AHEAP AI L RNG st (FKB 2 FF 256 :: LB) mA).
  { eapply (AI_frame AI); [exact AHN | exact MU1 | exact WM1 |].
    constructor; [| constructor]. cbn [fst snd]. right; right.
    replace (8 * (SHF - ASHOFF)) with FF by (rewrite ESHF'; unfold ASHOFF; clear - FF8 G1; Z.div_mod_to_equations; lia).
    right; right. exists 2, FF, 256. split; [left; reflexivity | clear; lia]. }
  assert (FLC2 : rw_cells bsegs mA FLG [C1 (Z_to_bv 8 1)]).
  { eapply rw_cells_transport; [exact FLC | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. split; [clear - FLL G2 G3 ATR; lia| exact I]. }
  (* [comment removed for export] *)
  assert (MU2 : munch [(FLG, FLG + 1)] mA mA) by apply munch_refl. assert (WM2 : wmono bsegs mA mA) by apply wmono_refl.
  hold REP. hold HH3. hold MU. hold WM. hold AHN. hold AH2. hold MU0. hold WM0. hold FFR0. hold MU1. hold WM1.
  kx_autoFLA (SAV, FLC2) [] [] 40%nat
    [KZRange FLG 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47);
     KZWr FLG 1; KZDisj FLG 1 (SPV - 104) 104]
    [(SPV - 104, 104)]
    [(SPV - 104, 104); (FLG, 1)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 ESHF' FBL FLL ATR ATL R13; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6 G7; lia | clear - R13 G4 G5 G6 G7; lia]] end).
  all: kx_mem.
  unfold held in REP, HH3, MU, WM, AHN, AH2, MU0, WM0, FFR0, MU1, WM1.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
  (* [comment removed for export] *)
  assert (AH3 : AHEAP AI L RNG st LB mB).
  { eapply sqd_aheap_eq; [exact (FRL _ _ _ _ _ _ _ _ AH2) |].
    subst FLG. apply (sqd_mem_eq_single mA mB (fflag L 2 FF) (Z_to_bv 8 0)); [clear - G8; lia | clear - G9 ATR; lia | exact MU2 |].
    change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in FLC2.
    apply sqd_byte_of_cb1; [exact FLC2 | clear - G8; lia]. }
  zstep.
  apply evtF_done. unfold zd_seq_default_postA.
  do 14 eexists. exists mB, r, r0', r1', r2'.
  split; [reflexivity|].
  (* [comment removed for export] *)
  assert (MU13 : munch [(SHF, SHF + 32); (FLG, FLG + 1)] m1 mB).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
  assert (WM13 : wmono bsegs m1 mB) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  assert (DJD : forall k n, 0 <= k -> 0 <= n -> k + n <= 95992 -> disjoint_from [(SHF, SHF + 32); (FLG, FLG + 1)] (DCTX + k) n).
  { intros k n Hk Hn Hkn. destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (FLA b ltac:(right; exact Hb)) as FB. unfold DCTX_SIZEOF in *.
    cbn [disjoint_from]. split; [clear - BDL G2 G3 Hk Hn Hkn ATR; lia|]. split; [clear - FB Hb1 Hb2 Hk Hn Hkn; lia| exact I]. }
  split.
  { (* [comment removed for export] *)
    unfold fake_area. cbn [app].
    eapply munch_trans; [eapply munch_weaken; [| exact MU0] |].
    { unfold sub_fp, fake_area; cbn [outside app]; intros x Hx. clear - Hx. lia. }
    eapply munch_trans; [eapply munch_weaken; [| exact MU] |].
    { unfold sub_fp; cbn [outside]; intros x Hx. rewrite shad_div in Hx. rewrite ESHF'. unfold ASHOFF, FAKESZ in *. clear - Hx AF1 AF2 FF8 G1. Z.div_mod_to_equations. lia. }
    eapply munch_weaken; [| exact MU13].
    unfold sub_fp; cbn [outside]; intros x Hx. rewrite shad_div in Hx. rewrite ESHF'. unfold ASHOFF, FAKESZ in *. clear - Hx AF1 AF2 FF8 G1 FLlo FLhi. Z.div_mod_to_equations. lia. }
  split; [eapply wmono_trans; [exact WM0 | eapply wmono_trans; [exact WM | exact WM13]]|].
  split; [assumption|].
  split.
  { (* [comment removed for export] *)
    pose proof (stk_of_rw_cells bsegs _ _ _ SAV) as SAVS. cbn [cells_size csize Nat.add length] in SAVS.
    eapply stk_merge; [exact STK | eapply stk_merge; [exact GAP | | clear - G4 G5 G6; lia] | clear - G5 G6 G7; lia].
    replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by (clear; lia). exact SAVS. }
  split.
  { (* [comment removed for export] *)
    eapply (sqd_ffr_fin AI L RNG st LB m0 m mB FF SHF FLG DST CAP DCTX SPV lo AH LBH LBA (fun b Hb => FLA b (or_intror Hb)) FLB FBK);
      [clear - G1; lia | clear - FBL ATR; lia | exact FF8 | exact ESHF | exact ATL | exact R13 | clear - R14; lia | | clear - BDL ATR; lia | exact FFR0 | | ].
    - destruct (Z.eq_dec CAP 0) as [C0|C0]; [left; clear - C0; lia| right].
      destruct (INB_O ltac:(clear - R6 R7 R8 C0; lia)) as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. pose proof ATR. clear - BL Hb1 Hb2 R6 R7 R8 ATR. lia.
    - eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU13]]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia.
    - eapply wmono_trans; [exact WM | exact WM13]. }
  split; [exact AH3|].
  split; [exact BUF|].
  split; [eapply rw_cells_transport; [exact REP | exact MU13 | exact WM13 | cbn [cells_size csize Nat.add]; unfold DCTX_entropy_rep; apply DJD; clear; lia]|].
  split; [unfold dctx_h3 in HH3 |- *; eapply rw_cells_transport; [exact HH3 | exact MU13 | exact WM13 | cbn [cells_size csize Nat.add]; unfold DCTX_fseEntropy; apply DJD; clear; lia]|].
  split; [exact HR | exact RES].
Qed.

End CANSEC1.
