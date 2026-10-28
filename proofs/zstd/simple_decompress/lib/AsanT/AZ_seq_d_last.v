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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2 AZ_seq_d_fin.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqd_mcpy_post (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz D n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMCPY_STACK_A, SPz); (D, D + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz /\ stk bsegs m' D (D + n).

Lemma sqd_mcpy_spec : zd_memcpyZ_stmtA ->
  forall (RNG : footprint) (D S n SPz : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem) lo,
  stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) -> (S + n <= D \/ D + n <= S) -> 0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMCPY_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMCPY_STACK_A \/ SPz <= S) -> (D + n <= lo \/ SPz <= D) ->
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk D (D + n) -> aro RNG m D n -> ahull RNG m D n ->
  art m -> astk RNG lo SPz -> mem_inv bsegs m ->
  evtF bsegs RNG (sqd_mcpy_post RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz D n lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMCPY) fc None m (seg_rom bsegs)).
Proof.
  intros MCP RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         STD RDS SEP Hn STK LO SPT SS SD ABS AOS AHS ABD AOD AHD ART AST MI.
  destruct (rdbl_bytes bsegs m S (S + n) RDS ltac:(lia)) as (src & LS & BS). replace (S + n - S) with n in LS by lia.
  destruct (stk_carve bsegs m D (D + n) (Z.to_nat n) STD ltac:(lia)) as [_ (junk & DJ)].
  replace (D + n - Z.of_nat (Z.to_nat n)) with D in DJ by lia.
  unfold zd_memcpyZ_stmtA in MCP.
  eapply evtF_mono.
  - eapply (MCP RNG D S n SPz ra gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo src junk);
      [ exact BS | exact LS | exact DJ | exact SEP | exact Hn | exact STK | exact LO | exact SPT | exact SS | exact SD
      | exact ABS | exact AOS | exact AHS | exact ABD | exact AOD | exact AHD | exact ART | exact AST | exact MI
      | reflexivity | reflexivity | reflexivity ].
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DST' & _).
    do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    pose proof (stk_of_rw_cells bsegs _ _ _ DST') as X. cbn [cells_size csize] in X.
    lazymatch type of X with stk _ _ _ ?h => replace h with (D + n) in X by (clear - Hn; lia) end. exact X.
Qed.


(* [comment removed for export] *)
Lemma sqd_aregU_trF : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 < n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n (B & U & R1 & R2) MU X0 Hn Xn FB F0. split; [exact B|]. split; [| split; [exact R1 | exact R2]].
  eapply unp_tr; [exact U | exact MU |]. pose proof (shspan_bounds X n X0 Hn Xn) as (S1 & S2 & S3).
  cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div in *. unfold ASHOFF in *. clear - S1 S2 S3 FB F0 Xn X0 Hn. Z.div_mod_to_equations. lia.
Qed.
Lemma sqd_aregU_trF0 : forall RNG (m m' : amem) FF X n,
  aregU RNG m X n -> munch [(FF, FF + 256)] m m' -> 0 <= X -> 0 <= n -> X + n <= 2^47 ->
  (FF + 256 <= 2147446784 \/ 17594333495296 <= FF) -> 0 <= FF -> aregU RNG m' X n.
Proof.
  intros RNG m m' FF X n A MU X0 Hn Xn FB F0. destruct (Z.eq_dec n 0) as [E|NZ].
  - subst n. destruct A as (B & U & R1 & R2). split; [exact B|]. split; [| split; [exact R1 | exact R2]].
    destruct U as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG. lia.
  - eapply sqd_aregU_trF; [exact A | exact MU | exact X0 | clear - Hn NZ; lia | exact Xn | exact FB | exact F0].
Qed.
Lemma sqd_ahull_tr : forall RNG (m m' : amem) X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R) WM. exists RLO, RHI.
  do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R].
Qed.
Lemma sqd_art_trF : forall (m m' : amem) FF, art m -> munch [(FF, FF + 256)] m m' -> wmono bsegs m m' -> 6443008 <= FF -> art m'.
Proof.
  intros m m' FF (G1 & G2 & G3 & G4 & G5 & G6) MU WM HF.
  assert (TC : forall A cs, rw_cells bsegs m A cs -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m' A cs).
  { intros A cs H HA. eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from]; split; [clear - HA HF; lia | exact I]]. }
  unfold art. split; [apply TC; [exact G1 | cbn; clear; lia]|]. split; [apply TC; [exact G2 | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | cbn; clear; lia]|]. split; [apply TC; [exact G4 | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | cbn; clear; lia]|]. apply TC; [exact G6 | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Definition sqd_at_last (P : sqp) : Prop :=
  forall (m1 : amem) (OEND OP LP LEND : Z) (ja jb jc jf jsh : list byte)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 : word),
  rw_cells bsegs m1 (w_FRB P) [CB 88 ja; C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 (w_DST P));
                            CB 80 jb; C8 (Z_to_bv 64 LP); CB 24 jc] ->
  rw_cells bsegs m1 (w_FF P) [CB 248 jf; C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))] ->
  rw_cells bsegs m1 (w_SHF P) [CB 32 jsh] ->
  (exists r0' r1' r2', rw_cells bsegs m1 (w_DCTX P + DCTX_entropy_rep) [C4 r0'; C4 r1'; C4 r2']) ->
  dctx_h3 bsegs m1 (w_DCTX P) (w_pcs P) (w_dsz P) (w_bt P) (w_stg P) (w_le P) (sqd_fe P) ->
  stk bsegs m1 (w_B0 P) (w_B1 P) -> stk bsegs m1 (w_lo P) (w_FRB P) -> stk bsegs m1 (w_FRB P + 216) (w_SPV P + -104) ->
  rw_cells bsegs m1 (w_SPV P + -104) (sqd_saved P) ->
  munch (sqd_Wb P) (w_m P) m1 -> wmono bsegs (w_m P) m1 -> mem_inv bsegs m1 ->
  rdbl bsegs m1 LP (LEND + 32) ->
  w_DST P <= OP -> OP <= OEND -> OEND <= w_DST P + w_CAP P -> w_LITP P <= LP -> LP <= LEND -> LEND <= w_LITP P + w_LITSZ P ->
  ((OEND <= LP /\ LEND + 32 <= w_B1 P) \/ LEND + 32 <= w_B0 P \/ w_B1 P <= LP) ->
  (OP <> 0 -> w_DST P <> 0) ->
  (* [comment removed for export] *)
  art m1 -> aregU (w_RNG P) m1 LP (LEND - LP) -> ahull (w_RNG P) m1 LP (LEND - LP) ->
  (w_B0 P < w_B1 P -> aregU (w_RNG P) m1 (w_B0 P) (w_B1 P - w_B0 P) /\ ahull (w_RNG P) m1 (w_B0 P) (w_B1 P - w_B0 P)) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10
             x11 x12 x13 x14 x15 x16 (Z_to_bv 64 OEND) (Z_to_bv 64 (w_SHF P)) x19 x20 x21 x22 (Z_to_bv 64 (w_FF P)) x24 (Z_to_bv 64 OP) x26 x27 x28 x29 x30 (Z_to_bv 64 LEND))
        (w_F P) (Z_to_bv 64 0x94840) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Local Ltac last_fin FIN FR FRF SHS REP HH3 BUF STK GAP SAV MU WM G5 :=
  let FRS := fresh "FRS" in
  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as FRS; cbn [cells_size csize Nat.add] in FRS;
  eapply FIN;
  [ split; [eexists; exact FRF|]; split; [eexists; exact SHS|]; split; [eexists; eexists; eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|];
    split; [eapply stk_merge; [exact FRS | exact GAP | clear - G5; lia]|]; split; [exact SAV|]; split; [exact MU|]; split; [exact WM | assumption]
  | | ].
(* [comment removed for export] *)
Lemma sqd_dctx_cells_tr : forall W (m1 m2 : amem) A cs,
  rw_cells bsegs m1 A cs -> munch W m1 m2 -> wmono bsegs m1 m2 -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m2 A cs.
Proof. intros W m1 m2 A cs H MU WM D. eapply rw_cells_transport; [exact H | exact MU | exact WM | exact D]. Qed.

Lemma sqd_last_ok : forall P, sqd_ranges P -> sqd_side P -> sqd_sep P -> sqd_astat P -> sqd_pro P -> zd_memcpyZ_stmtA -> sqd_at_fin P -> sqd_at_last P.
Proof.
  intros P RG SD SEP AS PRO MCP FIN. unfold sqd_at_last.
  intros m1 OEND OP LP LEND ja jb jc jf jsh x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30
         FR FRF SHS REP HH3 BUF STK GAP SAV MU WM MI LIT H1 H2 H3 H4 H5 H6 DJL HOPD ART ALU ALH AB.
  unfold sqd_at_fin, sqd_finv, sqd_fe in FIN. unfold sqd_fe in HH3. destruct REP as (r0' & r1' & r2' & REP).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_ranges sqd_side sqd_sep sqd_astat sqd_pro sqd_Wb sqd_saved sqd_post w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, dctx_h3 in FIN, REP, HH3, MU.
  destruct RG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  destruct SD as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct AS as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  destruct PRO as (AH & MU0 & WM0 & FFR0 & FFL & FRL & AF1 & AF2 & LBA & INB_D & INB_O & LBH & FBK).
  pose proof atop_range as ATR. unfold AIMG_HI in FFa. unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF, off_stack, apart in *. destruct AST as (AST1 & RSTK & RAI).
  remember (fflag L 2 FF) as FLG eqn:EFLG. remember (LEND - LP) as ll eqn:Ell.
  assert (DST0 : 0 <= DST) by (destruct (Z.eq_dec DST 0) as [E|E]; [rewrite E; apply Z.le_refl | pose proof (Y4 E) as B4; clear - B4 R6; lia]).
  assert (RGF : 6443008 <= FF /\ FF + 256 <= 2^47 /\ 17594333499936 <= SPV < 2^47 /\ 4096 <= FRB /\ FRB + 320 <= SPV /\ lo + 4304 <= FRB /\
                0 <= OP < 2^47 /\ 0 <= OEND < 2^47 /\ 0 <= DST < 2^47 /\ 0 <= ll < 2^32 /\ 2147450880 <= SHF /\ SHF + 32 <= 17594333495296 /\ 4096 <= LP /\ LEND + 32 < 2^47)
    by (rewrite ESHF, shad_div; unfold ASHOFF; clear - FFa FFb ATR R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 ES1 ATL H1 H2 H3 H4 H5 H6 DST0 Ell; Z.div_mod_to_equations; lia).
  destruct RGF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { destruct INB_D as (b & Hb & Hb1 & Hb2). pose proof (ablk_lits _ _ (LBH b Hb)) as BL. clear - BL Hb1 Hb2. lia. }
  pose proof (ablk_lits _ _ (proj1 ALU)) as BLL. replace (LP + ll) with LEND in BLL by (clear - Ell; lia). pose proof (ablk_lits _ _ FBK) as FBL.
  assert (MU1 : munch [(FF, FF + 256)] m1 m1) by apply munch_refl. assert (WM1 : wmono bsegs m1 m1) by apply wmono_refl.
  hold REP. hold HH3. hold MU. hold WM. hold MU0. hold WM0. hold FFR0. hold AH. hold FIN. hold LIT. hold DJL. hold ALU. hold ALH. hold AB. hold MCP. hold HOPD.
  hold Y1. hold Y2. hold Y3. hold Y4. hold Y5. hold Y6. hold Y7. hold Y8. hold Y9. hold Y10. hold Y11. hold AFD. hold AFO. hold AFS. hold AFL. hold AFT. hold LBA. hold LBH. hold INB_D. hold INB_O.
  hold P1. hold P2. hold P3. hold P4. hold P5. hold P6. hold P7. hold P8. hold BDL. hold BLL. hold FFL. hold FRL.
  (* [comment removed for export] *)
  kx_autoFLA (FR, FRF) [] [0x94908] 60%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange OEND 0 (2^47);
     KZRange DST 0 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange ll 0 (2^32);
     KZRange SHF 2147450880 17594333495264; KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj SHF 32 FF 256; KZDisj SHF 32 FRB 216]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: kx_mem.
  all: unfold held in REP, HH3, MU, WM, MU0, WM0, FFR0, AH, FIN, LIT, ALU, ALH, AB, MCP, HOPD.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x94908) _ _ ?mx _) =>
        (* [comment removed for export] *)
        sqd_blob_last FRF;
        assert (MUn : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
          by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
        assert (WMn : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WM1]);
        unfold held in AFD;
        assert (REPn : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
          by (eapply sqd_dctx_cells_tr; [exact REP | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
        assert (HH3n : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
          by (eapply sqd_dctx_cells_tr; [exact HH3 | exact MU1 | exact WM1 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
        first [ replace (Z_to_bv 64 v) with (Z_to_bv 64 18446744073709551546) by (apply Z_to_bv_eqm; reflexivity);
                last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV MUn WMn G5; [clear; lia | left; reflexivity]
              | (assert (DZ : DST = 0) by (clear FIN MCP; lia));
                replace (Z_to_bv 64 v) with (Z_to_bv 64 0) by (f_equal; clear FIN MCP; lia);
                last_fin FIN FR FRF SHS REPn HH3n BUF STK GAP SAV MUn WMn G5; [clear; lia | right; clear - R8; lia] ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x53804) _ _ _ _) => idtac
    end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  assert (HOP : OP <> 0) by (clear FIN MCP; lia).
  assert (HFIT : ll <= OEND - OP) by (clear FIN MCP; lia).
  pose proof (HOPD HOP) as HDST. unfold held in Y12. pose proof (Y12 HDST) as BB.
  destruct (AB BB) as (ABU1 & ABH1). pose proof (ablk_lits _ _ (proj1 ABU1)) as BOL. replace (B0 + (B1 - B0)) with B1 in BOL by (clear; lia).
  (* [comment removed for export] *)
  assert (ABU : aregU RNG mA B0 (B1 - B0)) by (eapply sqd_aregU_trF; [exact ABU1 | exact MU1 | clear - BOL; lia | clear - BB; lia | clear - BOL ATR; lia | clear - FBL; lia | clear - G1; lia]).
  assert (ABH : ahull RNG mA B0 (B1 - B0)) by (eapply sqd_ahull_tr; [exact ABH1 | exact WM1]).
  rename ALU into ALU1. rename ALH into ALH1. rename ART into ART1.
  assert (ART : art mA) by (eapply sqd_art_trF; [exact ART1 | exact MU1 | exact WM1 | exact G1]).
  assert (ALH : ahull RNG mA LP ll) by (eapply sqd_ahull_tr; [exact ALH1 | exact WM1]).
  unfold held in BLL. assert (ALU : aregU RNG mA LP ll) by (eapply sqd_aregU_trF0; [exact ALU1 | exact MU1 | clear - G13; lia | clear - G10; lia | clear - BLL G10 ATR Ell; lia | clear - FBL; lia | clear - G1; lia]).
  unfold held in LIT. unfold held in DJL. unfold held in P1. unfold held in P2. unfold held in P4. unfold held in P5. unfold held in AFD. unfold held in AFO. unfold held in MCP.
  assert (OB : B0 <= OP /\ OP + ll <= B1 /\ OP + ll <= OEND) by (clear - H1 H2 H3 HFIT R6 R7 G10; lia). destruct OB as (OB1 & OB2 & OB3).
  lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?nn) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    assert (Enn : nn = ll) by (clear - Ell; lia); rewrite Enn end.
  eapply evtF_cut.
  { eapply (sqd_mcpy_spec MCP RNG OP LP ll FRB);
      [ eapply stk_sub; [exact BUF | exact OB1 | clear - G10; lia | exact OB2]
      | eapply rdbl_sub; [exact LIT | clear; lia | clear - Ell G10; lia]
      | clear - DJL OB1 OB2 OB3 H1 R6 Ell G10; lia
      | clear - G10; lia
      | exact STK | clear - G6; lia | clear - G4 G5 G3; lia
      | clear - P4 H4 H5 H6 Ell G5 G6 R13; lia
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
  replace (ret_pc (Z_to_bv 64 0x948dc)) with (Z_to_bv 64 0x948dc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (DJS : forall A k, 0 <= k -> (A + k <= FRB - MEMCPY_STACK_A \/ FRB <= A) -> (A + k <= OP \/ OP + ll <= A) -> disjoint_from [(FRB - MEMCPY_STACK_A, FRB); (OP, OP + ll)] A k).
  { intros A k Hk X1 X2. cbn [disjoint_from]. split; [clear - X1 Hk; lia|]. split; [clear - X2 Hk; lia| exact I]. }
  unfold KHIGH in AST1.
  assert (FRc : rw_cells bsegs mC FRB [CB 88 ja; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DST); CB 80 jb; C8 (Z_to_bv 64 LP); CB 24 jc]).
  { eapply rw_cells_transport; [exact FR | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear; lia | clear - P2 OB1 OB2 G5 G6 R13; lia]]. }
  assert (FRFc : rw_cells bsegs mC FF [CB 248 jf; C8 (Z_to_bv 64 FLG)]).
  { eapply rw_cells_transport; [exact FRF | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - FFb ATL G6; lia | clear - AFO BB OB1 OB2; lia]]. }
  assert (SHSc : exists jsh', rw_cells bsegs mC SHF [CB 32 jsh']).
  { sqd_blob_all SHS. eexists. eapply rw_cells_transport; [exact SHS | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - G12 AST1 G6; lia | clear - BOL OB1 OB2 G11 G12 ATR; lia]]. }
  destruct SHSc as (jsh' & SHSc).
  assert (REPc : rw_cells bsegs mC (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2']).
  { eapply rw_cells_transport; [exact REP | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2; lia]]. }
  assert (HH3c : rw_cells bsegs mC (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)]).
  { eapply rw_cells_transport; [exact HH3 | exact MUC | exact WMC | cbn [cells_size csize Nat.add]; apply DJS; [clear; lia | clear - P1 G5 G6; lia | clear - P5 OB1 OB2; lia]]. }
  assert (GAPc : stk bsegs mC (FRB + 216) (SPV + -104)).
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
  assert (MUc : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mC).
  { eapply munch_trans; [exact MU | eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUC]]];
      unfold sub_fp; cbn [outside]; intros x Hx; [clear - Hx; lia | clear - Hx ES1 G6 R13 H1 OB3 H3; lia]. }
  assert (WMc : wmono bsegs m mC) by (eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WMC]]).
  clear FR FRF SHS REP HH3 GAP SAV BUF STK MU1 WM1 DSTC.
  assert (MU2 : munch [(FF, FF + 256)] mC mC) by apply munch_refl. assert (WM2 : wmono bsegs mC mC) by apply wmono_refl.
  hold FIN. hold MCP. hold LIT. hold DJL. hold P1. hold P2. hold P4. hold P5. hold AFD. hold AFO. hold Y12. hold REPc. hold HH3c. hold MUc. hold WMc. hold MUC. hold WMC. hold ALU. hold ALH. hold AB. hold ABU. hold ABH. hold HOPD. hold DJS.
  (* [comment removed for export] *)
  kx_autoFLA (FRc, FRFc) [] [0x94908] 30%nat
    [KZRange FF 6443008 (2^47); KZRange SPV 17594333499936 (2^47); KZRange FRB 4096 (2^47); KZRange OP 0 (2^47); KZRange DST 0 (2^47); KZRange ll 0 (2^32);
     KZRange SHF 2147450880 17594333495264; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj SHF 32 FF 256]
    [(FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => kx_z end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ /\ rng _ _ _ => split; [clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10; lia | eapply rng_sub; [exact RSTK | clear - R13 G4 G5 G6; lia | clear - R13 G4 G5 G6; lia]] end).
  all: kx_mem.
  all: unfold held in FIN, MCP, LIT, DJL, P1, P2, P4, P5, AFD, AFO, Y12, REPc, HH3c, MUc, WMc, MUC, WMC, ALU, ALH, AB, ABU, ABH, HOPD, DJS.
  all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x94908) _ _ ?mx _) =>
    sqd_blob_last FRFc;
    assert (REPf : rw_cells bsegs mx (DCTX + 26684) [C4 r0'; C4 r1'; C4 r2'])
      by (eapply sqd_dctx_cells_tr; [exact REPc | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
    assert (HH3f : rw_cells bsegs mx (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
      by (eapply sqd_dctx_cells_tr; [exact HH3c | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; clear - AFD; split; [lia| exact I]]);
    assert (MUf : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
      by (eapply munch_trans; [exact MUc | eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
    assert (WMf : wmono bsegs m mx) by (eapply wmono_trans; [exact WMc | exact WM2]);
    replace (Z_to_bv 64 v) with (Z_to_bv 64 (OP + ll - DST)) by (f_equal; clear - Ell; lia);
    last_fin FIN FRc FRFc SHSc REPf HH3f BUFc STKC GAPc SAVc MUf WMf G5; [clear - OB1 OB2 H1 R6 R9 G10 DST0; lia | right; clear - OB3 H1 H3; lia]
  end.
Qed.

End CANSEC1.
