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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2 AZ_seq_s_fin AZ_seq_s_xkit.
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
Definition sqs_at_lastb (P : ssq) : Prop :=
  forall (m1 : amem) (OEND OP LP LEND : Z) (loc : word) (ja jb jc jd je jf jsh : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word),
  rw_cells bsegs m1 (v_FRB P) [CB 72 ja; C8 (Z_to_bv 64 (v_DCTX P)); C8 (Z_to_bv 64 (v_DST P)); CB 48 jb; C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P)); CB 40 jc;
                               C8 (Z_to_bv 64 LEND); CB 48 jd; C8 (Z_to_bv 64 LP); CB 24 je] ->
  rw_cells bsegs m1 (v_FF P) [CB 248 jf; C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))] ->
  rw_cells bsegs m1 (v_SHF P) [CB 32 jsh] ->
  (exists r0' r1' r2', rw_cells bsegs m1 (v_DCTX P + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) ->
  dctx_h3 bsegs m1 (v_DCTX P) (v_pcs P) (v_dsz P) (v_bt P) (v_stg P) (v_le P) (sqs_fe P) ->
  h5_viewed m1 (v_DCTX P) (v_ws P) loc ->
  stk bsegs m1 (v_B0 P) (v_B1 P) -> stk bsegs m1 (v_lo P) (v_FRB P) -> stk bsegs m1 (v_FRB P + 280) (v_SPV P + -104) ->
  rw_cells bsegs m1 (v_SPV P + -104) (sqs_saved P) ->
  munch (sqs_Wb P) (v_m P) m1 -> wmono bsegs (v_m P) m1 -> mem_inv bsegs m1 ->
  rdbl bsegs m1 LP (LEND + 32) ->
  v_DST P <= OP -> OP <= OEND -> OEND <= v_DST P + v_CAP P -> v_DCTX P + 30372 <= LP -> LP <= LEND -> LEND + 32 <= v_DCTX P + 95940 ->
  (* [comment removed for export] *)
  art m1 -> areg (v_RNG P) m1 (v_DCTX P) DCTX_SIZEOF -> ahull (v_RNG P) m1 (v_DCTX P) DCTX_SIZEOF ->
  (v_B0 P < v_B1 P -> aregU (v_RNG P) m1 (v_B0 P) (v_B1 P - v_B0 P) /\ ahull (v_RNG P) m1 (v_B0 P) (v_B1 P - v_B0 P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10
             x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 OEND) x21 x22 (Z_to_bv 64 OP) x24 x25 x26 (Z_to_bv 64 (v_SHF P))
             x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x8f6d0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Local Ltac last_fin FIN FR FRF SHS REP HH3 BUF STK GAP SAV H5V MU WM G5 :=
  let FRS := fresh "FRS" in
  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
  eapply FIN;
  [ split; [eexists; exact FRF|]; split; [eexists; exact SHS|]; split; [eexists; eexists; eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|]; split; [exact SAV|]; split; [eexists; exact H5V|]; split; [exact MU|]; split; [exact WM | assumption]
  | | ].

Lemma sqs_lastb_ok : forall P, sqs_ranges P -> sqs_side P -> sqs_sep P -> sqs_astat P -> sqs_pro P -> zd_memcpyZ_stmtA -> sqs_at_fin P -> sqs_at_lastb P.
Proof.
  intros P RG SD SEP AS PRO MCP FIN. unfold sqs_at_lastb.
  intros m1 OEND OP LP LEND loc ja jb jc jd je jf jsh x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x24 x25 x26 x28 x29 x30 x31
         FR FRF SHS REP HH3 H5V BUF STK GAP SAV MU WM MI LIT H1 H2 H3 H4 H5 H6 ART AD ADH AB.
  unfold sqs_at_fin, sqs_finv, sqs_fe in FIN. unfold sqs_fe in HH3. destruct REP as (r0' & r1' & r2' & REP).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_ranges sqs_side sqs_sep sqs_astat sqs_pro sqs_Wb sqs_saved sqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in FIN, REP, HH3, MU. destruct H5V as (H5R & H5L). unfold h5_vcells in H5R.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  remember (fflag L 2 FF) as FLG eqn:EFLG. remember (LEND - LP) as ll eqn:Ell.
  assert (BB : B0 < B1) by (apply Y13; clear - Y15 R6; lia).
  assert (RGF : 6443008 <= FF /\ FF + 256 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 4096 <= FRB /\ FRB + 384 <= SPV /\ lo + 4304 <= FRB /\
                4096 <= OP < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= DST < 2^47 /\ 0 <= ll < 2^32 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296 /\ 4096 <= LP /\ LEND + 32 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47)
    by (rewrite ESHF, shad_div; unfold ASHOFF; clear - FFa FFb ATR R1 R2 R6 R7 R8 R9 R13 R14 R15 Y15 ES1 ATL H1 H2 H3 H4 H5 H6 Ell; Z.div_mod_to_equations; lia).
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. clear - BL Hb1 Hb2. lia. }
  pose proof (ablk_lits _ _ FBK) as FBL.
  assert (MU1 : munch [(FF, FF + 256)] m1 m1) by apply munch_refl. assert (WM1 : wmono bsegs m1 m1) by apply wmono_refl.
  hold REP. hold HH3. hold H5R. hold MU. hold WM. hold MU0. hold WM0. hold FFR0. hold AH. hold FIN. hold LIT. hold AD. hold ADH. hold AB. hold MCP.
  hold Y1. hold Y2. hold Y3. hold Y4. hold Y5. hold Y6. hold Y7. hold Y8. hold Y9. hold Y10. hold Y11. hold Y12. hold Y13. hold Y14. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBA. hold LBH. hold INB_D. hold INB_O.
  hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold BDL. hold FFL. hold FRL.
  (* [comment removed for export] *)
  kx_autoFLA (FR, FRF) [] [0x91ffc] 60%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange OEND 4096 (2^47);
     KZRange DST 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32);
     KZRange SHF 2147450880 17594333495264; KZWr FRB 280; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 280]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: kx_mem.
  all: unfold held in REP, HH3, H5R, MU, WM, MU0, WM0, FFR0, AH, FIN, LIT, AD, ADH, AB, MCP.
  all: lazymatch goal with
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
        assert (H5Vn : h5_viewed mx DCTX ws loc)
          by (split; [| exact H5L]; unfold h5_vcells; eapply sqd_dctx_cells_tr; [exact H5R | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
        replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
        last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV H5Vn MUn WMn G5; [clear; lia | left; reflexivity]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x53804) _ _ _ _) => idtac
    end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  assert (HFIT : ll <= OEND - OP) by (clear FIN MCP; lia).
  destruct (AB BB) as (ABU1 & ABH1). pose proof (ablk_lits _ _ (proj1 ABU1)) as BOL. replace (B0 + (B1 - B0)) with B1 in BOL by (clear; lia).
  (* [comment removed for export] *)
  assert (ABU : aregU RNG mA B0 (B1 - B0)) by (eapply sqd_aregU_trF; [exact ABU1 | exact MU1 | clear - BOL; lia | clear - BB; lia | clear - BOL ATR; lia | clear - FBL; lia | clear - G1; lia]).
  assert (ABH : ahull RNG mA B0 (B1 - B0)) by (eapply sqd_ahull_tr; [exact ABH1 | exact WM1]).
  rename ART into ART1.
  assert (ART : art mA) by (eapply sqd_art_trF; [exact ART1 | exact MU1 | exact WM1 | exact G1]).
  assert (ALH : ahull RNG mA LP ll) by (eapply ahull_sub; [eapply sqd_ahull_tr; [exact ADH | exact WM1] | clear - H4; lia | clear - H6 Ell; lia]).
  unfold held in BDL.
  assert (ALU : aregU RNG mA LP ll).
  { eapply sqd_aregU_trF0; [ | exact MU1 | clear - G13; lia | clear - G10; lia | clear - G14 G10 Ell; lia | clear - FBL; lia | clear - G1; lia].
    eapply (aregU_sub RNG _ DCTX 95992); [exact AD | clear; lia | clear - H4; lia | clear - G10; lia | clear - H6 Ell; lia]. }
  unfold held in LIT. unfold held in P1. unfold held in P2. unfold held in P5. unfold held in AFD. unfold held in AFO. unfold held in MCP.
  assert (OB : B0 <= OP /\ OP + ll <= B1 /\ OP + ll <= OEND) by (clear - H1 H2 H3 HFIT R6 R7 G10; lia). destruct OB as (OB1 & OB2 & OB3).
  assert (LPB : DCTX + 30372 <= LP /\ LP + ll + 32 <= DCTX + 95940) by (clear - H4 H6 Ell; lia). destruct LPB as (LB1 & LB2).
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?nn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    assert (Enn : nn = ll) by (clear - Ell; lia); rewrite Enn end.
  eapply evtF_cut.
  { eapply (sqd_mcpy_spec MCP RNG OP LP ll FRB);
      [ eapply stk_sub; [exact BUF | exact OB1 | clear - G10; lia | exact OB2]
      | eapply rdbl_sub; [exact LIT | clear; lia | clear - Ell G10; lia]
      | clear - P5 OB1 OB2 LB1 LB2 BB G10; lia
      | clear - G10; lia
      | exact STK | clear - G6; lia | clear - G4 G5 G3; lia
      | clear - P1 LB1 LB2 G5 G6 R13; lia
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
  replace (ret_pc (Z_to_bv 64 0x8fa74)) with (Z_to_bv 64 0x8fa74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (DJS : forall A k, 0 <= k -> (A + k <= FRB - MEMCPY_STACK_A \/ FRB <= A) -> (A + k <= OP \/ OP + ll <= A) -> disjoint_from [(FRB - MEMCPY_STACK_A, FRB); (OP, OP + ll)] A k).
  { intros A k Hk X1 X2. cbn [disjoint_from]. split; [clear - X1 Hk; lia|]. split; [clear - X2 Hk; lia| exact I]. }
  unfold KHIGH in AST1.
  assert (FRc : rw_cells bsegs mC FRB [CB 72 ja; C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST); CB 48 jb; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); CB 40 jc;
                                       C8 (Z_to_bv 64 LEND); CB 48 jd; C8 (Z_to_bv 64 LP); CB 24 je]).
  { eapply rw_cells_transport; [exact FR | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
  assert (FRFc : rw_cells bsegs mC FF [CB 248 jf; C8 (Z_to_bv 64 FLG)]).
  { eapply rw_cells_transport; [exact FRF | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - FFb ATL G6; lia | clear - AFO BB OB1 OB2; lia]]. }
  assert (SHSc : exists jsh', rw_cells bsegs mC SHF [CB 32 jsh']).
  { sqs_blob_all SHS. eexists. eapply rw_cells_transport; [exact SHS | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G12 AST1 G6; lia | clear - BOL OB1 OB2 G11 G12 ATR; lia]]. }
  destruct SHSc as (jsh' & SHSc).
  assert (REPc : rw_cells bsegs mC (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2']).
  { eapply rw_cells_transport; [exact REP | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
  assert (HH3c : rw_cells bsegs mC (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)]).
  { eapply rw_cells_transport; [exact HH3 | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
  assert (H5Vc : h5_viewed mC DCTX ws loc).
  { split; [| exact H5L]. unfold h5_vcells. eapply rw_cells_transport; [exact H5R | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2 BB; lia]]. }
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
  assert (MUc : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mC).
  { eapply munch_trans; [exact MU | eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUC]]];
      unfold sub_fp; cbn [outside]; intros x Hx; [clear - Hx; lia | clear - Hx ES1 G6 R13 H1 OB3 H3; lia]. }
  assert (WMc : wmono bsegs m mC) by (eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WMC]]).
  clear FR FRF SHS REP HH3 H5R GAP SAV BUF STK MU1 WM1 DSTC.
  assert (MU2 : munch [(FF, FF + 256)] mC mC) by apply munch_refl. assert (WM2 : wmono bsegs mC mC) by apply wmono_refl.
  hold FIN. hold MCP. hold LIT. hold P1. hold P2. hold P5. hold AFD. hold AFO. hold Y13. hold REPc. hold HH3c. hold H5Vc. hold MUc. hold WMc. hold MUC. hold WMC. hold ALU. hold ALH. hold AB. hold ABU. hold ABH. hold DJS. hold AD. hold ADH. hold BDL.
  (* [comment removed for export] *)
  kx_autoFLA (FRc, FRFc) [] [0x91ffc] 30%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange ll 0 (2^32);
     KZRange SHF 2147450880 17594333495264; KZWr FF 256; KZDisj FF 256 FRB 280; KZDisj SHF 32 FF 256]
    [(FRB, 280); (FF, 256)]
    [(FRB, 280); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: kx_mem.
  all: unfold held in FIN, MCP, LIT, P1, P2, P5, AFD, AFO, Y13, REPc, HH3c, H5Vc, MUc, WMc, MUC, WMC, ALU, ALH, AB, ABU, ABH, DJS, AD, ADH, BDL.
  all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x91ffc) _ _ ?mx _) =>
    sqs_blob_last FRFc;
    assert (REPf : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
      by (eapply sqd_dctx_cells_tr; [exact REPc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
    assert (HH3f : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
      by (eapply sqd_dctx_cells_tr; [exact HH3c | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
    assert (H5Vf : h5_viewed mx DCTX ws loc)
      by (destruct H5Vc as (H5Rc & _); split; [| exact H5L]; unfold h5_vcells in H5Rc |- *; eapply sqd_dctx_cells_tr; [exact H5Rc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
    assert (MUf : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
      by (eapply munch_trans; [exact MUc | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
    assert (WMf : wmono bsegs m mx) by (eapply wmono_trans; [exact WMc | exact WM2]);
    replace (Z_to_bv 64 v) with (Z_to_bv 64 (OP + ll - DST)) by (f_equal; clear - Ell; lia);
    last_fin FIN FRc FRFc SHSc REPf HH3f BUFc STKC GAPc SAVc H5Vf MUf WMf G5; [clear - OB1 OB2 H1 R6 R9 G10 G9; lia | right; clear - OB3 H1 H3; lia]
  end.
Qed.

End CANSEC1.
