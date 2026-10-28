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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_zkit AZ_seq_l_fin AZ_seq_l_last2.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_at_lastx (P : slq) : Prop :=
  forall (m1 : amem) (OEND OP LP LEND LOCV : Z) (ja jb jc jd je jff jsh : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30 : word),
  rw_cells bsegs m1 (l_FRB P) [CB 168 ja; C8 (Z_to_bv 64 OEND); CB 56 jb; C8 (Z_to_bv 64 (l_DST P)); CB 8 jc; C8 (Z_to_bv 64 (l_FF P)); CB 280 jd; C8 (Z_to_bv 64 LP); CB 24 je] ->
  rw_cells bsegs m1 (l_FF P) [CB 248 jff; C8 (Z_to_bv 64 (l_fflag P (l_L P) 2 (l_FF P)))] ->
  rw_cells bsegs m1 (l_SHF P) [CB 32 jsh] ->
  (exists r0' r1' r2', rw_cells bsegs m1 (l_DCTX P + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) ->
  dctx_h3 bsegs m1 (l_DCTX P) (l_pcs P) (l_dsz P) (l_bt P) (l_stg P) (l_le P) (sql_fe P) ->
  h5_viewed m1 (l_DCTX P) (l_ws P) (Z_to_bv 64 LOCV) ->
  stk bsegs m1 (l_B0 P) (l_B1 P) -> stk bsegs m1 (l_lo P) (l_FRB P) -> stk bsegs m1 (l_FRB P + 568) (l_SPV P + -104) ->
  rw_cells bsegs m1 (l_SPV P + -104) (sql_saved P) ->
  munch (sql_Wb P) (l_m P) m1 -> wmono bsegs (l_m P) m1 -> mem_inv bsegs m1 ->
  rdbl bsegs m1 LP (LEND + 32) ->
  (LOCV = 2 -> rdbl bsegs m1 (l_DCTX P + 30372) (l_DCTX P + 95940)) ->
  l_DST P <= OP -> OP <= OEND -> OEND <= l_DST P + l_CAP P ->
  (OP <> 0 -> l_DST P <> 0) -> (LOCV = 2 -> l_DST P <> 0) -> 0 <= LOCV <= 2 ->
  ((l_LITP P <= LP /\ LP <= LEND /\ LEND = l_LBE P) \/ (LOCV <> 2 /\ l_DCTX P + 30372 <= LP /\ LP <= LEND /\ LEND = l_DCTX P + 95908)) ->
  (* [comment removed for export] *)
  sql_asan P m1 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 (l_DCTX P)) x24 (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 LEND) x27 x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x89e20) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Local Ltac lz_take240 FR H :=
  lazymatch type of FR with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn 7 cs) in
    let mid := eval cbn [firstn skipn] in (firstn 1 (skipn 7 cs)) in
    let post := eval cbn [skipn] in (skipn 8 cs) in
    pose proof FR as H; change (rw_cells sg mm A (pre ++ mid ++ post)) in H;
    apply rw_cells_app in H; destruct H as [_ H]; apply rw_cells_app in H; destruct H as [H _];
    cbn [cells_size csize Nat.add length] in H; replace (A + Z.of_nat 240) with (A + 240) in H by (clear; lia)
  end.
(* [comment removed for export] *)
Local Ltac last_fin FIN FR FRF SHS REP HH3 BUF STK GAP SAV H5V MU WM G5 :=
  let FRS := fresh "FRS" in
  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
  eapply FIN;
  [ split; [eexists; exact FRF|]; split; [eexists; exact SHS|]; split; [eexists; eexists; eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|]; split; [exact SAV|]; split; [eexists; exact H5V|]; split; [exact MU|]; split; [exact WM | assumption]
  | | ].

Lemma sql_lastx_ok : forall P, sql_ranges P -> sql_side P -> sql_sep P -> sql_astat P -> sql_pro P -> l_LBE P - l_LITP P < 2^32 ->
  zd_memmoveZ_stmtA -> sql_at_fin P -> sql_at_last2 P -> sql_at_lastx P.
Proof.
  intros P RG SD SEP AS PRO HLSZ MMV FIN LASTK. unfold sql_at_lastx.
  intros m1 OEND OP LP LEND LOCV ja jb jc jd je jff jsh x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x24 x27 x28 x29 x30
         FR FRF SHS REP HH3 H5V BUF STK GAP SAV MU WM MI LIT XLIT H1 H2 H3 HOPD HL2D HLV PH ASN.
  unfold sql_at_fin, sql_finv, sql_fe in FIN. unfold sql_at_last2, sql_fe in LASTK. unfold sql_fe in HH3. destruct REP as (r0' & r1' & r2' & REP).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_ranges sql_side sql_sep sql_astat sql_pro sql_Wb sql_saved sql_post sql_asan l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN, LASTK, REP, HH3, MU. destruct H5V as (H5R & H5L). unfold h5_vcells in H5R.
  destruct ASN as (AD & ADH & ARS & ATB & ACL & AB0 & ARL & AHL & AZS & ART).
  assert (AB : B0 < B1 -> aregU RNG m1 (B0) (B1 - B0) /\ ahull RNG m1 (B0) (B1 - B0))
    by (intros BB; destruct (AB0 BB) as (A1 & A2); split; [exact (A1 ltac:(clear - BB; lia)) | exact A2]). clear AB0.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  remember (fflag L 2 FF) as FLG eqn:EFLG. remember (LEND - LP) as ll eqn:Ell.
  assert (DST0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [rewrite E; apply Z.le_refl | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
  assert (RGF : 6443008 <= FF /\ FF + 256 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 4096 <= FRB /\ FRB + 672 <= SPV /\ lo + 4304 <= FRB /\
                0 <= OP < 2^47 /\ 0 <= OEND < 2^47 /\ 0 <= DST < 2^47 /\ 0 <= ll < 2^32 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296 /\ 4096 <= LP /\ LEND + 32 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47)
    by (rewrite ESHF, shad_div; unfold ASHOFF; clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 ES1 ATL H1 H2 H3 PH Ell HLSZ DST0 FRL; Z.div_mod_to_equations; lia).
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. clear - BL Hb1 Hb2. lia. }
  pose proof (ablk_lits _ _ FBK) as FBL.
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in AD, ADH, ARL, AHL.
  destruct (AD ltac:(clear; lia)) as (BD & UD & RD & RSD).      (* [comment removed for export] *)
  assert (MU1 : munch [(FF, FF + 256)] m1 m1) by apply munch_refl. assert (WM1 : wmono bsegs m1 m1) by apply wmono_refl.
  (* [comment removed for export] *)
  assert (KD1 : DCTX + 30096 + 276 <= FRB \/ FRB + 568 <= DCTX + 30096) by (clear - P1 G5 G6; lia).
  assert (KD2 : DCTX + 30096 + 276 <= FF \/ FF + 256 <= DCTX + 30096) by (clear - AFD; lia).
  hold REP. hold HH3. hold MU. hold WM. hold MU0. hold WM0. hold FFR0. hold AH. hold FIN. hold LASTK. hold LIT. hold XLIT. hold AD. hold ADH. hold AB. hold ARL. hold AHL. hold MMV. hold HOPD.
  hold Y1. hold Y2. hold Y3. hold Y4. hold Y5. hold Y6. hold Y7. hold Y8. hold Y9. hold Y10. hold Y11. hold Y12. hold Y13. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBA. hold LBH. hold INB_D. hold INB_O.
  hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold BDL. hold FFL. hold FRL. hold ESHF. hold FFc. hold ES1b.
  clear ARS ATB ACL AZS.
  assert (HL3 : LOCV = 0 \/ LOCV = 1 \/ LOCV = 2) by (clear - HLV; lia). clear HLV.
  destruct HL3 as [EL|[EL|EL]]; subst LOCV.
  1-2: clear HL2D XLIT.
  1-2: destruct PH as [(Q1 & Q2 & Q3)|(_ & Q1 & Q2 & Q3)].
  - (* [comment removed for export] *)
    kx_autoFLA (FR, FRF, H5R) [] [0x8a1fc; 0x8e5f8] 40%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange OEND 0 (2^47);
       KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 568;
       KZDisj FRB 568 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276]
      [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, AD, ADH, AB, ARL, AHL, MMV, HOPD.
    all: unfold held in P1. all: unfold held in P4.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a1fc) _ _ _ _) => assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia);
          eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3 | split; [exact H5R | exact H5L] | exact BUF | exact STK | exact GAP | exact SAV
                      | exact MU | exact WM | assumption | eapply rdbl_sub; [exact LIT | clear; lia | clear; lia] | clear - Ell; lia | exact H1 | exact H2 | exact H3
                      | clear - Q1 R10; lia | exact Q2 | clear - Q1 Q3 HLSZ; lia | clear - Q3 R12; lia | clear - P4 Q1 Q3 R10 R11; lia | exact HOPD | clear - HFIT Ell; lia | exact ART | eapply (aregU_sub RNG m1 LITP (LBE + 32 - LITP)); [exact ARL | clear - R10 R11; lia | exact Q1 | clear - Q2; lia | clear - Q3; lia] | eapply ahull_sub; [exact AHL | exact Q1 | clear - Q2 Q3; lia] | exact AB]
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRF;
          assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
          assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
          unfold held in AFD;
          assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply sql_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply sql_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 0)) by (split; [exact H5R | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after run A, pc =" UPC]
      end.
  - (* [comment removed for export] *)
    kx_autoFLA (FR, FRF, H5R) [] [0x8a1fc; 0x8e5f8] 40%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange OEND 0 (2^47);
       KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 568;
       KZDisj FRB 568 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276]
      [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, AD, ADH, AB, ARL, AHL, MMV, HOPD.
    all: unfold held in P1. all: unfold held in P4.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a1fc) _ _ _ _) => assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia);
          eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3 | split; [exact H5R | exact H5L] | exact BUF | exact STK | exact GAP | exact SAV
                      | exact MU | exact WM | assumption | eapply rdbl_sub; [exact LIT | clear; lia | clear; lia] | clear - Ell; lia | exact H1 | exact H2 | exact H3
                      | clear - Q1 R1; lia | exact Q2 | clear - Q1 Q3; lia | clear - Q3 R2; lia | clear - P1 Q1 Q3; lia | exact HOPD | clear - HFIT Ell; lia | exact ART | eapply (aregU_sub RNG m1 DCTX 95992); [exact AD | clear; lia | clear - Q1; lia | clear - Q2; lia | clear - Q3; lia] | eapply ahull_sub; [exact ADH | clear - Q1; lia | clear - Q2 Q3; lia] | exact AB]
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRF;
          assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
          assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
          unfold held in AFD;
          assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply sql_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply sql_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 0)) by (split; [exact H5R | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after run A, pc =" UPC]
      end.
  - (* [comment removed for export] *)
    kx_autoFLA (FR, FRF, H5R) [] [0x8a1fc; 0x8e5f8] 40%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange OEND 0 (2^47);
       KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 568;
       KZDisj FRB 568 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276]
      [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, AD, ADH, AB, ARL, AHL, MMV, HOPD.
    all: unfold held in P1. all: unfold held in P4.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a1fc) _ _ _ _) => assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia);
          eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3 | split; [exact H5R | exact H5L] | exact BUF | exact STK | exact GAP | exact SAV
                      | exact MU | exact WM | assumption | eapply rdbl_sub; [exact LIT | clear; lia | clear; lia] | clear - Ell; lia | exact H1 | exact H2 | exact H3
                      | clear - Q1 R10; lia | exact Q2 | clear - Q1 Q3 HLSZ; lia | clear - Q3 R12; lia | clear - P4 Q1 Q3 R10 R11; lia | exact HOPD | clear - HFIT Ell; lia | exact ART | eapply (aregU_sub RNG m1 LITP (LBE + 32 - LITP)); [exact ARL | clear - R10 R11; lia | exact Q1 | clear - Q2; lia | clear - Q3; lia] | eapply ahull_sub; [exact AHL | exact Q1 | clear - Q2 Q3; lia] | exact AB]
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRF;
          assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
          assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
          unfold held in AFD;
          assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply sql_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply sql_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 1)) by (split; [exact H5R | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after run A, pc =" UPC]
      end.
  - (* [comment removed for export] *)
    kx_autoFLA (FR, FRF, H5R) [] [0x8a1fc; 0x8e5f8] 40%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange OEND 0 (2^47);
       KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 568;
       KZDisj FRB 568 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276]
      [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, AD, ADH, AB, ARL, AHL, MMV, HOPD.
    all: unfold held in P1. all: unfold held in P4.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a1fc) _ _ _ _) => assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia);
          eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3 | split; [exact H5R | exact H5L] | exact BUF | exact STK | exact GAP | exact SAV
                      | exact MU | exact WM | assumption | eapply rdbl_sub; [exact LIT | clear; lia | clear; lia] | clear - Ell; lia | exact H1 | exact H2 | exact H3
                      | clear - Q1 R1; lia | exact Q2 | clear - Q1 Q3; lia | clear - Q3 R2; lia | clear - P1 Q1 Q3; lia | exact HOPD | clear - HFIT Ell; lia | exact ART | eapply (aregU_sub RNG m1 DCTX 95992); [exact AD | clear; lia | clear - Q1; lia | clear - Q2; lia | clear - Q3; lia] | eapply ahull_sub; [exact ADH | clear - Q1; lia | clear - Q2 Q3; lia] | exact AB]
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRF;
          assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
          assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
          unfold held in AFD;
          assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply sql_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply sql_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 1)) by (split; [exact H5R | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after run A, pc =" UPC]
      end.
  - (* [comment removed for export] *)
    destruct PH as [(Q1 & Q2 & Q3)|(NE2 & _)]; [| exfalso; exact (NE2 eq_refl)].
    pose proof (HL2D eq_refl) as HDST. clear HL2D. unfold held in Y13. pose proof (Y13 HDST) as BB. unfold held in Y4. pose proof (Y4 HDST) as B04.
    assert (HOP4 : 4096 <= OP) by (clear - B04 R6 H1; lia).
    (* [comment removed for export] *)
    kx_autoFLA (FR, FRF, H5R) [] [0x8e5f8; 0x53ee0; 0x8a1fc] 60%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange OEND 0 (2^47);
       KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 568;
       KZDisj FRB 568 (DCTX + 30096) 276; KZDisj FF 256 (DCTX + 30096) 276]
      [(FRB, 568); (FF, 256); (DCTX + 30096, 276)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LASTK, LIT, XLIT, AD, ADH, AB, ARL, AHL, MMV, HOPD.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRF;
          assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
          assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
          unfold held in AFD;
          assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply sql_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply sql_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
          assert (H5Vn : h5_viewed mx DCTX ws (Z_to_bv 64 2)) by (split; [exact H5R | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x53ee0) _ _ _ _) => idtac
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => first [exfalso; lia | fail 99 "unexpected LEAF after run B, pc =" UPC]
      end.
    (* [comment removed for export] *)
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (HFIT : ll <= OEND - OP) by (clear FIN LASTK MMV; lia).
    destruct (AB BB) as (ABU1 & ABH1). pose proof (ablk_lits _ _ (proj1 ABU1)) as BOL. replace (B0 + (B1 - B0)) with B1 in BOL by (clear; lia).
    unfold held in BDL.
    (* [comment removed for export] *)
    assert (ABU : aregU RNG mA B0 (B1 - B0)) by (eapply sql_aregU_trF; [exact ABU1 | exact MU1 | clear - BOL; lia | clear - BB; lia | clear - BOL ATR; lia | clear - FBL; lia | clear - G1; lia]).
    assert (ABH : ahull RNG mA B0 (B1 - B0)) by (eapply sql_ahull_tr; [exact ABH1 | exact WM1]).
    rename ART into ART1.
    assert (ART : art mA) by (eapply sql_art_trF; [exact ART1 | exact MU1 | exact WM1 | exact G1]).
    assert (ALU1 : aregU RNG mA LP ll) by (eapply (aregU_sub RNG mA LITP (LBE + 32 - LITP)); [exact ARL | clear - R10 R11; lia | exact Q1 | clear - G10; lia | clear - Q2 Q3 Ell; lia]).
    assert (ALU : aregU RNG mA LP ll) by (eapply sql_aregU_trF0; [exact ALU1 | exact MU1 | clear - G13; lia | clear - G10; lia | clear - G14 G10 Ell; lia | clear - FBL; lia | clear - G1; lia]).
    assert (ALH : ahull RNG mA LP ll) by (eapply ahull_sub; [eapply sql_ahull_tr; [exact AHL | exact WM1] | exact Q1 | clear - Q2 Q3 Ell; lia]).
    pose proof (ablk_lits _ _ (proj1 ALU1)) as BLL.
    unfold held in LIT. unfold held in XLIT. unfold held in P1. unfold held in P2. unfold held in P4. unfold held in P5. unfold held in AFD. unfold held in AFO. unfold held in AFL. unfold held in MMV.
    assert (OB : B0 <= OP /\ OP + ll <= B1 /\ OP + ll <= OEND) by (clear - H1 H2 H3 HFIT R6 R7 G10; lia). destruct OB as (OB1 & OB2 & OB3).
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?nn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      first [ constr_eq nn ll | assert (Enn : nn = ll) by (clear - Ell; lia); rewrite Enn ] end.
    eapply evtF_cut.
    { eapply (sql_mmove_spec MMV RNG OP LP ll FRB);
        [ eapply stk_sub; [exact BUF | exact OB1 | clear - G10; lia | exact OB2]
        | eapply rdbl_sub; [exact LIT | clear; lia | clear - Ell G10; lia]
        | clear - G10; lia
        | exact STK | clear - G6; lia | clear - G4 G5 G3; lia
        | clear - P4 Q1 Q2 Q3 Ell R10 R11 G5 G6 R13; lia
        | clear - P2 OB1 OB2 G6 G5 R13; lia
        | eapply aregU_app_blk; [exact ALU | clear - G10; lia]
        | apply aregU_aro; exact ALU
        | exact ALH
        | eapply aregU_app_blk; [eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact OB1 | clear - G10; lia | clear - OB2; lia] | clear - G10; lia]
        | apply aregU_aro; eapply (aregU_sub RNG mA B0 (B1 - B0)); [intros _; exact ABU | clear - BB; lia | exact OB1 | clear - G10; lia | clear - OB2; lia]
        | eapply ahull_sub; [exact ABH | exact OB1 | clear - OB2; lia]
        | exact ART
        | exact (astk_sub RNG lo SPV FRB (conj AST1 (conj RSTK RAI)) ltac:(clear - G5 G6 R13; lia))
        | assumption ]. }
    cbv beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mC & -> & MUC & WMC & MIC & STKC & DSTC).
    replace (ret_pc (Z_to_bv 64 0x89e50)) with (Z_to_bv 64 0x89e50) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (DJS : forall A k, 0 <= k -> (A + k <= FRB - MEMMOVE_STACK_A \/ FRB <= A) -> (A + k <= OP \/ OP + ll <= A) -> disjoint_from [(FRB - MEMMOVE_STACK_A, FRB); (OP, OP + ll)] A k).
    { intros A k Hk X1 X2. cbn [disjoint_from]. split; [clear - X1 Hk; lia|]. split; [clear - X2 Hk; lia| exact I]. }
    unfold KHIGH in AST1.
    assert (FRc : rw_cells bsegs mC FRB [CB 168 ja; C8 (Z_to_bv 64 OEND); CB 56 jb; C8 (Z_to_bv 64 DST); CB 8 jc; C8 (Z_to_bv 64 FF); CB 280 jd; C8 (Z_to_bv 64 LP); CB 24 je]).
    { eapply rw_cells_transport; [exact FR | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
    assert (FRFc : rw_cells bsegs mC FF [CB 248 jff; C8 (Z_to_bv 64 FLG)]).
    { eapply rw_cells_transport; [exact FRF | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - FFb ATL G6; lia | clear - AFO BB OB1 OB2; lia]]. }
    assert (SHSc : rw_cells bsegs mC SHF [CB 32 jsh]).
    { eapply rw_cells_transport; [exact SHS | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G12 AST1 G6; lia | clear - BOL OB1 OB2 G11 G12 ATR; lia]]. }
    assert (REPc : rw_cells bsegs mC (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2']).
    { eapply rw_cells_transport; [exact REP | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
    assert (HH3c : rw_cells bsegs mC (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)]).
    { eapply rw_cells_transport; [exact HH3 | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
    assert (H5Rc : rw_cells bsegs mC (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (Z_to_bv 64 2)]).
    { eapply rw_cells_transport; [exact H5R | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
    assert (GAPc : stk bsegs mC (FRB + 568) (SPV + -104)).
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
    assert (MUc : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mC).
    { eapply munch_trans; [exact MU | eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUC]]];
        unfold sub_fp; cbn [outside]; intros x Hx; [clear - Hx; lia | clear - Hx ES1 G6 R13 H1 OB3 H3; lia]. }
    assert (WMc : wmono bsegs m mC) by (eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WMC]]).
    assert (ARTc : art mC).
    { eapply sql_art_trW; [exact ART | exact MUC | exact WMC |]. intros A cs HA. apply DJS; [clear; lia | clear - HA G5 G6 ATL ATR; lia | clear - HA BOL OB1 OB2; lia]. }
    assert (ADa : areg RNG mA DCTX 95992).
    { eapply sql_areg_trW; [exact AD | exact MU1 |]. rewrite !shad_div; unfold ASHOFF. cbn [disjoint_from]. split; [clear - G15 G16 FBL ATR; Z.div_mod_to_equations; lia | exact I]. }
    assert (ADc : areg RNG mC DCTX 95992).
    { eapply sql_areg_trW; [exact ADa | exact MUC |]. rewrite !shad_div; unfold ASHOFF. apply DJS; [clear - G15; Z.div_mod_to_equations; lia | clear - G15 G16 G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - G15 G16 BOL OB1 OB2 ATR; Z.div_mod_to_equations; lia]. }
    assert (ADHc : ahull RNG mC DCTX 95992) by (eapply sql_ahull_tr; [eapply sql_ahull_tr; [exact ADH | exact WM1] | exact WMC]).
    assert (ABUc : aregU RNG mC B0 (B1 - B0)).
    { eapply sql_aregU_trW; [exact ABU | exact MUC |]. replace (B0 + (B1 - B0) - 1) with (B1 - 1) by (clear; lia). rewrite !shad_div; unfold ASHOFF.
      apply DJS; [clear - BB; Z.div_mod_to_equations; lia | clear - BOL BB G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - BOL BB OB1 OB2 ATR; Z.div_mod_to_equations; lia]. }
    assert (ABHc : ahull RNG mC B0 (B1 - B0)) by (eapply sql_ahull_tr; [exact ABH | exact WMC]).
    clear FR FRF SHS REP HH3 H5R GAP SAV BUF STK DSTC ART ADa ABU ABH AD ADH AB ABU1 ABH1 ART1 LIT XLIT ALU ALU1 ALH ARL AHL.
    assert (MU2 : munch [(FRB, FRB + 568); (FF, FF + 256)] mC mC) by apply munch_refl. assert (WM2 : wmono bsegs mC mC) by apply wmono_refl.
    (* [comment removed for export] *)
    assert (FFLO : FF + 256 <= lo) by (clear - FFb ATL; lia).
    assert (SHFF : SHF + 32 <= FF \/ FF + 256 <= SHF) by (clear - FBL G11 G12; lia).
    hold FIN. hold LASTK. hold MMV. hold XLITc. hold P1. hold P2. hold P5. hold AFD. hold AFO. hold AFL. hold BDL. hold BOL. hold BLL. hold REPc. hold HH3c. hold H5Rc. hold SHSc. hold GAPc. hold SAVc. hold BUFc. hold STKC.
    hold MUc. hold WMc. hold MUC. hold WMC. hold ARTc. hold ADc. hold ADHc. hold ABUc. hold ABHc. hold DJS. hold FFLO. hold SHFF.
    (* [comment removed for export] *)
    kx_autoFLA (FRc, FRFc) [] [0x8a1fc; 0x8e5f8] 60%nat
      [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange ll 0 (2^32); KZRange DCTX 4096 (2^47 - 95992);
       KZRange OEND 0 (2^47); KZRange DST 0 (2^47); KZRange SHF 2147450880 17594333495264; KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568]
      [(FRB, 568); (FF, 256)]
      [(FRB, 568); (FF, 256)].
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: unfold held in FIN, LASTK, MMV, XLITc, P1, P2, P5, AFD, AFO, AFL, BDL, BOL, BLL, REPc, HH3c, H5Rc, SHSc, GAPc, SAVc, BUFc, STKC.
    all: unfold held in MUc, WMc, MUC, WMC, ARTc, ADc, ADHc, ABUc, ABHc, DJS, FFLO, SHFF.
    (* [comment removed for export] *)
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (DJ2 : forall A k, 0 <= k -> (A + k <= FRB \/ FRB + 568 <= A) -> (A + k <= FF \/ FF + 256 <= A) -> disjoint_from [(FRB, FRB + 568); (FF, FF + 256)] A k)
            by (intros A k Hk X1 X2; cbn [disjoint_from]; split; [clear - X1 Hk; lia|]; split; [clear - X2 Hk; lia| exact I]);
          assert (REPf : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
            by (eapply rw_cells_transport; [exact REPc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - P1 G5 G6; lia | clear - AFD; lia]]);
          assert (HH3f : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
            by (eapply rw_cells_transport; [exact HH3c | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - P1 G5 G6; lia | clear - AFD; lia]]);
          assert (H5Rf : rw_cells bsegs mx (DCTX + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (Z_to_bv 64 2)])
            by (eapply rw_cells_transport; [exact H5Rc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - P1 G5 G6; lia | clear - AFD; lia]]);
          assert (SHSf : rw_cells bsegs mx SHF [CB 32 jsh])
            by (eapply rw_cells_transport; [exact SHSc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - G12 AST1 ATL G6; lia | clear - SHFF; lia]]);
          assert (GAPf : stk bsegs mx (FRB + 568) (SPV + -104))
            by (eapply stk_transport_disjoint; [exact GAPc | exact MU2 | exact WM2 | apply DJ2; [clear - G5; lia | clear; lia | clear - FFLO G5 G6; lia]]);
          assert (SAVf : rw_cells bsegs mx (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
            by (eapply rw_cells_transport; [exact SAVc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add]; apply DJ2; [clear; lia | clear - G5; lia | clear - FFLO G5 G6; lia]]);
          assert (BUFf : stk bsegs mx B0 B1)
            by (eapply stk_transport_disjoint; [exact BUFc | exact MU2 | exact WM2 | apply DJ2; [clear - BB; lia | clear - P2 G5 G6 R13; lia | clear - AFO BB; lia]]);
          assert (STKf : stk bsegs mx lo FRB)
            by (eapply stk_transport_disjoint; [exact STKC | exact MU2 | exact WM2 | apply DJ2; [clear - G6; lia | clear; lia | clear - FFLO; lia]]);
          assert (XLITf : rdbl bsegs mx (DCTX + 30372) (DCTX + 95940))
            by (eapply rdbl_transport; [exact XLITc | exact MU2 |]; intros x Hx; left; apply (disjoint_outside _ x 1 x); [| clear; lia]; apply DJ2; [clear; lia | clear - P1 G5 G6 Hx; lia | clear - AFD Hx; lia]);
          assert (MUf : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
            by (eapply munch_trans; [exact MUc | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx ES1 R13; lia]);
          assert (WMf : wmono bsegs m mx) by (eapply wmono_trans; [exact WMc | exact WM2]);
          assert (ARTf : art mx)
            by (eapply sql_art_trW; [exact ARTc | exact MU2 | exact WM2 |]; intros A cs HA; apply DJ2; [clear; lia | clear - HA G5 G6 ATL ATR; lia | clear - HA G1; lia])
      end.
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a1fc) _ _ ?mx _) =>
          assert (HFIT2 : 65536 <= OEND - (OP + ll)) by (clear FIN LASTK MMV DJS DJ2; lia);
          assert (ADf : areg RNG mx DCTX 95992)
            by (eapply sql_areg_trW; [exact ADc | exact MU2 |]; rewrite !shad_div; unfold ASHOFF; apply DJ2; [clear - G15; Z.div_mod_to_equations; lia | clear - G15 G16 G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - G15 G16 AFD FBL ATR BDL; Z.div_mod_to_equations; lia]);
          assert (ADHf : ahull RNG mx DCTX 95992) by (eapply sql_ahull_tr; [exact ADHc | exact WM2]);
          assert (ABUf : aregU RNG mx B0 (B1 - B0))
            by (eapply sql_aregU_trW; [exact ABUc | exact MU2 |]; replace (B0 + (B1 - B0) - 1) with (B1 - 1) by (clear; lia); rewrite !shad_div; unfold ASHOFF;
                apply DJ2; [clear - BB; Z.div_mod_to_equations; lia | clear - BOL BB G5 G6 ATL ATR; Z.div_mod_to_equations; lia | clear - BOL BB AFO FBL ATR; Z.div_mod_to_equations; lia]);
          assert (ABHf : ahull RNG mx B0 (B1 - B0)) by (eapply sql_ahull_tr; [exact ABHc | exact WM2]);
          eapply LASTK; [exact FRc | exact FRFc | exact SHSf | eexists; eexists; eexists; exact REPf | exact HH3f | split; [exact H5Rf | exact H5L] | exact BUFf | exact STKf | exact GAPf | exact SAVf
                        | exact MUf | exact WMf | assumption | eapply rdbl_sub; [exact XLITf | clear; lia | clear; lia] | clear; lia | clear - H1 HFIT G10; lia | clear - OB3; lia | exact H3
                        | clear - G15; lia | clear; lia | clear; lia | clear - G16; lia | clear - P1; lia | intros _; exact HDST | clear - HFIT2; lia
                        | exact ARTf
                        | eapply (aregU_sub RNG mx DCTX 95992); [exact ADf | clear; lia | clear; lia | clear; lia | clear; lia]
                        | eapply ahull_sub; [exact ADHf | clear; lia | clear; lia]
                        | intros _; split; [exact ABUf | exact ABHf]]
      | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x8e5f8) _ _ ?mx _) =>
          (* [comment removed for export] *)
          sql_blob_last FRFc;
          assert (H5Vf : h5_viewed mx DCTX ws (Z_to_bv 64 2)) by (split; [exact H5Rf | exact H5L]);
          replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
          last_fin FIN FRc FRFc SHSf REPf HH3f BUFf STKf GAPf SAVf H5Vf MUf WMf G5; [clear; lia | left; reflexivity]
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF after run C, pc =" UPC
      end.
  Unshelve. all: try exact 0%nat. all: try exact nil.
Qed.

End CANSEC1.
