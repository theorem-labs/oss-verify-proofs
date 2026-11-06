(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA D_libiface.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt B0_fs_L2f B0_sessK B0_hc_L2a B0_hc_L2b.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzArr BzCMem BzCStream BzCState BzCMtf BzCBlock BzCHuff BzArrD BzCLemmas1 CmpMem CmpCut CmpCutMS CmpCutMtf CmpCutSM CmpCutSmA BzCFactsSmA CmpCutSmB BzCFactsGm BzCSmF1 BzCFactsSmB BzCFactsSd CmpHmKit CmpSmKit CmpSmKit2 AsanKit AsanKit2 AsanCut AsanCutB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCNumZ CmpLaws CmpCutCB BzCFactsSmA2 BzCFactsSmB3 BzCFactsSd2 BzCLemmasMs6 BzCFactsBs6 BzCFactsCb BzCSortPost.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCDriver CmpSess CmpSessB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1 BzTables.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV B0_cmp_msV B0_b2c_cbV B0_b2c_hcV A0_b2c_hcR B0_b2c_hcG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Section HCT.
Context {BZP : BzParams} {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
Hypothesis CBC : compressBlock_contract RT CBFACTS.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_PRIM : af_live_primary RT.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis AF_CRC : forall Σ m, ART RT Σ m -> acc bsegs m 0xd13e0 1024.

Theorem handle_compress_cps : handle_compress_contract RT HCXB CBFACTS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx ob on dbza dbzfr g e z nin pl OB p1 p2 lo usp STRM W
    FDO MST A0E TP CEQ EM AM LIB SM SOKA OBM LOB OOK OLIV PLM ZIN PAY PAYLV OUTR AOUT ELIV A1LIV A2LIV FTLIV FRMAX CRED ART0 MI0 ST0 LOW LOR SPT SPA CX SEP IMG LAWS HX.
  intros T c Hc Hk. subst a0.
  pose proof alloc_ceiling_range as ACR. bz_params. unfold ESTATE_SIZE, FTAB_WORDS in ELIV, FTLIV. change (4 * 65537) with 262148 in FTLIV.
  set (P := usp - 288).
  set (Whc := [(c_E cx, c_E cx + 55768); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 262148); (ob, ob + on); (STRM, STRM + 80)]).
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & SSH).
  (* [comment removed for export] *)
  assert (WCL : forall x, ~ outside Whc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Whc in Hx. cbn [outside] in Hx.
    assert (C : (c_E cx <= x < c_E cx + 55768) \/ (c_A1 cx <= x < c_A1 cx + ARR1_SIZE) \/ (c_A2 cx <= x < c_A2 cx + ARR2_SIZE) \/
                (c_FT cx <= x < c_FT cx + 262148) \/ (ob <= x < ob + on) \/ (STRM <= x < STRM + 80)) by (clear - Hx; lia).
    destruct C as [C|[C|[C|[C|[C|C]]]]].
    - right; right; left. exists (c_E cx), 55768. split; [exact ELIV| exact C].
    - right; right; left. exists (c_A1 cx), ARR1_SIZE. split; [exact A1LIV| exact C].
    - right; right; left. exists (c_A2 cx), ARR2_SIZE. split; [exact A2LIV| exact C].
    - right; right; left. exists (c_FT cx), 262148. split; [exact FTLIV| exact C].
    - right; right; left. exists ob, on. split; [exact OLIV| exact C].
    - right; right; right; left. exists fS, kS. split; [exact FIN| clear - C FLO FHI; lia]. }
  unfold RT_STACK in LOR.
  destruct (act_setup_nf RT AF Σ m lo P usp Whc ART0 LOW ltac:(unfold P, RT_STACK; clear - LOR; lia) ltac:(unfold P; clear; lia) SPT
              ltac:(unfold P; clear - SPA; Z.div_mod_to_equations; lia) WCL) as (G & SOK).
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FR0 & FR1 & _ & FR3).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FHS.
  pose proof (AF_PRIM Σ m _ _ ART0 ELIV ltac:(clear; lia)) as IE. unfold SEGTOP_A in IE.
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 ELIV) as OFFE. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 A1LIV) as OFF1.
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 A2LIV) as OFF2. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 FTLIV) as OFFF.
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 OLIV) as OFFO.
  pose proof (FR3 _ _ ELIV) as XSE. pose proof (FR3 _ _ A1LIV) as XS1. pose proof (FR3 _ _ A2LIV) as XS2. pose proof (FR3 _ _ FTLIV) as XSF. pose proof (FR3 _ _ OLIV) as XSO.
  pose proof FHI as SFH0.
  revert FHI FR1 FHS XSE XS1 XS2 XSF XSO FR3. generalize (fs_size kS). intros fsz FHI FR1 FHS XSE XS1 XS2 XSF XSO FR3.
  assert (SLO : 0x62b000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= CmpFsKit0.CEILv) by (unfold CmpFsKit0.CEILv; rewrite CEQ; clear - FHI FR1; lia).
  assert (SES : CmpFsKit0.apartv (c_E cx) ESTATE_SIZE STRM 80) by (unfold CmpFsKit0.apartv, ESTATE_SIZE; clear - XSE FLO FHI; lia).
  assert (S1S : CmpFsKit0.apartv (c_A1 cx) ARR1_SIZE STRM 80) by (unfold CmpFsKit0.apartv; clear - XS1 FLO FHI; lia).
  assert (S2S : CmpFsKit0.apartv (c_A2 cx) ARR2_SIZE STRM 80) by (unfold CmpFsKit0.apartv; clear - XS2 FLO FHI; lia).
  assert (SFS : CmpFsKit0.apartv (c_FT cx) 262148 STRM 80) by (unfold CmpFsKit0.apartv; clear - XSF FLO FHI; lia).
  assert (SOS : CmpFsKit0.apartv ob on STRM 80) by (unfold CmpFsKit0.apartv; clear - XSO FLO FHI; lia).
  assert (OFFS : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM) by (clear - FHS FLO FHI; lia).
  set (SHE := c_E cx / 8 + 2147450880).
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
  assert (AE : sanchor (c_E cx) SHE) by (split; [clear - ME16; Z.div_mod_to_equations; lia| reflexivity]).
  set (SHS := STRM / 8 + 2147450880).
  assert (AS : sanchor STRM SHS) by (split; [exact S8| reflexivity]).
  assert (SHSR : 2147450880 <= SHS /\ SHS + 10 <= 17594333495296).
  { unfold SHS. unfold CmpFsKit0.CEILv in SHI. clear - SLO SHI ACR. Z.div_mod_to_equations. lia. }
  assert (SSH0 : bytes_at bsegs m SHS (repeat z8 10)) by exact SSH.
  clearbody SHE SHS.
  (* [comment removed for export] *)
  assert (PX : exists pP nP, (pl <> [] -> In (pP, nP) (rt_live RT Σ) /\ pP <= nin /\ nin + Z.of_nat (length pl) <= pP + nP)
                             /\ (pl <> [] -> CmpFsKit0.apartv nin (Z.of_nat (length pl)) STRM 80)).
  { destruct (Nat.eq_dec (length pl) 0) as [L0|LN].
    - exists 0, 0. split; intros NE; exfalso; apply NE; apply length_zero_iff_nil; exact L0.
    - assert (NE : pl <> []) by (intros EN; apply LN; rewrite EN; reflexivity).
      destruct (PAYLV NE) as (pP & nP & PIN & PL0 & PL1 & _). exists pP, nP. split; [intros _; split; [exact PIN| split; [exact PL0| exact PL1]]|].
      intros _. pose proof (FR3 _ _ PIN) as XSP. unfold CmpFsKit0.apartv. clear - XSP PL0 PL1 FLO FHI. lia. }
  destruct PX as (pP & nP & PAYL & PSS).
  (* [comment removed for export] *)
  assert (PR0 : L2Act.PRESI usp (rt_frames RT Σ) (rt_live RT Σ) Whc m m) by (intros a _; reflexivity).
  assert (ROOM : lo + RT_STACK + 304 + 2064 <= P) by (unfold P, RT_STACK; clear - LOR; lia).
  destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). destruct AM as (AR1 & AR2 & FTB). unfold FTAB_WORDS in FTB.
  pose proof (hc_shsep_ok RT cx ob on lo sp CX SEP IMG OOK (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) G CEQ ROOM SHI SES S1S S2S SFS SOS) as SHS'. unfold hc_shsep in SHS'. fold usp P in SHS'.
  destruct SHS' as (DEA1 & DEA2 & DEFT & DA1A2 & DA1FT & DA2FT & DOE & DOA1 & DOA2 & DOFT & DES & DA1S & DA2S & DFTS & DOS &
                    XL1 & XL2 & XL3 & XL4 & XL5 & XL6 & XL7 & XL8 & XL9 & XL10 & XL11 & XL12 & XL13 & XL14 & XL15 & XL16 & XL17).
  assert (SHP : shzW b0segs [(P, P + 288)] m STRM (STRM + 80)).
  { refine (proj1 (proj2 (proj2 (proj2 (proj2 (hc_views RT AF AF_DRV AF_CRC cx ob on nin pl lo sp CX SEP IMG OOK PAY SHS AS (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) G CEQ ROOM
              ELIV A1LIV A2LIV FTLIV OLIV fS kS FIN FLO SFH0 pP nP PAYL IE SLO SHI SES S1S S2S SFS SOS PSS OFFE OFF1 OFF2 OFFF OFFO OFFS SHSR m SSH0 PLM LIB
              Σ m [(P, P + 288)] SOK ART0 PR0 _ _ _ _ _ _ _ _)))))).
    - cbn [app_fp]. unfold SH_LO, SH_HI. split; [right; fold P in XL7; clear - XL7; lia| exact I].
    - cbn [disjoint_from aci_got_sh B0C]. split; [left; clear - XL7; lia| exact I].
    - cbn [disjoint_from aci_shvar B0C]. split; [left; clear - XL7; lia| exact I].
    - cbn [disjoint_from]. split; [left; clear - XL7; lia| exact I].
    - cbn [disjoint_from]. split; [left; clear - XL7; lia| exact I].
    - cbn [disjoint_from]. split; [left; clear - XL7; lia| exact I].
    - cbn [disjoint_from]. split; [left; clear - XL7; lia| exact I].
    - intros NE. pose proof (PAY NE) as PK. unfold pay_okB, CEIL in PK. cbn [disjoint_from]. split; [left; clear - PK XL14 LOW CEQ; unfold STACK_WIN in *; lia| exact I]. }
  destruct (B0_fs_L2f.fs_aconsts_of_art RT AF Σ m ART0) as [AC _].
  assert (CEP : CmpFsKit0.CEILv <= lo) by (unfold CmpFsKit0.CEILv; rewrite CEQ; exact LOW).
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_hc_P cx _ SHE SHS ob on dbza dbzfr p1 p2 P STRM lo gp tp F fc CX AE AS SLO SHI CEP ltac:(clear - XL14; lia) z nin m);
    [reflexivity| exact ST0| exact SM| exact (kmem_inv_N _ _ MI0)| exact AC| exact SHP|].
  clear Hc SM SHP. intros m1 v64 v80 v88 a0' a1' a4' a5' a6' a7' t6' SL SAVED ST1n SM NMI1 MU1 WM1. apply evt_done. intros k1 Hc1.
  destruct (after_l1_leaf AF G Σ [(P, P + 288)] 0 m m1 SOK ART0 MI0 PR0 NMI1 MU1 WM1 ltac:(clear; lia) ltac:(clear - ROOM; unfold RT_STACK in *; lia)
              ltac:(per_interval; left; match goal with HX : _ <= _ < _ |- _ => unfold P in HX |- *; clear - HX; lia end)) as (ART1 & MI1 & PR1 & _).
  assert (ST1 : stk bsegs m1 lo P) by exact ST1n. clear ST1n.
  pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro (c_E cx) (CLive (c_E cx) 55768)) as KE. pose proof (ck_intro (c_A1 cx) (CLive (c_A1 cx) ARR1_SIZE)) as KA1. pose proof (ck_intro (c_A2 cx) (CLive (c_A2 cx) ARR2_SIZE)) as KA2.
  pose proof (ck_intro (c_FT cx) (CLive (c_FT cx) 262148)) as KFT. pose proof (ck_intro ob (CLive ob on)) as KOB.
  assert (LOBn : Z.of_nat (length OB) = on) by exact LOB.
  apply (u8arr_transport b0segs [(P, P + 288)] m m1 ob _) in OBM; [| exact MU1| exact WM1| rewrite LOBn; cbn [disjoint_from]; split; [left; clear - XL5; lia| exact I]].
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
  (* [comment removed for export] *)
  destruct (handle_compress znew e z) as [[ef zf] prf] eqn:HRES.
  eapply (hc_l2_top RT AF HCXB CBFACTS CBC AF_DRV AF_CRC cx ob on dbza dbzfr z nin pl OB p1 p2 lo sp gp tp CX SEP IMG LAWS TP LOB OOK PAY SHE SHS AE AS PMc
            (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) FDO MST G CEQ ROOM ltac:(clear - FRMAX; lia) ELIV A1LIV A2LIV FTLIV OLIV fS kS FIN FLO SFH0 pP nP PAYL IE SLO SHI SES S1S S2S SFS SOS PSS
            OFFE OFF1 OFF2 OFFF OFFO OFFS SHSR m SSH0 PLM LIB (hc_fuel z) Σ g e z false false m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc T k1 ef zf prf
            (hlB_term _ _ LAWS cx on g e z HX) HRES);
    [| exact SOK| exact CRED| | | | | exact SL| exact SAVED| exact ART1| exact MI1| exact ST1| exact PR1| exact Hc1|].
  - unfold HPURE, hkin. rewrite Z.sub_diag. cbn [Z.to_nat skipn]. split; [exact HX| split; [exact ZIN| clear; lia]].
  - unfold emem. split; [exact EH1|]. split; [exact INU|]. split; [exact UNS|]. split; [exact EH2|]. split; [exact MTF|]. split; [exact SEL|]. split; [exact SELM|].
    split; [exact LEN|]. split; [exact CODE|]. split; [exact RFQ| exact LPK].
  - unfold CmpCut.amem, FTAB_WORDS. split; [exact AR1|]. split; [exact AR2| exact FTB].
  - unfold hkin. rewrite Z.sub_diag, Z.add_0_r. exact SM.
  - rewrite OUTR, outb_nil. exact OBM.
  - intros k5 Σ5 m5 g5 q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 F5 fc5 Hc5 LV5 FR5 SP5 CR5 PU5 EM5 AM5 SM5 OBM5 ART5 MI5 ST5 PR5.
    apply Hk. exists Σ5.
    split; [| split; [exact LV5| split; [exact FR5| split; [exact SP5| unfold HC_CREDIT; exact CR5]]]].
    eapply ASTA_conseq; [exact Hc5|]. intros ms <-. exists m5, q0, q1, q2, b1, b2, b3, b4, b5, b6, b7, q3, q4, q5, q6, F5, fc5, g5.
    destruct PU5 as (HX5 & ZI5 & KN5).
    split; [reflexivity|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact EM5|]. split; [exact AM5|].
    split; [exact (hc_lib RT cx ob on lo sp CX SEP IMG OOK (rt_frames RT Σ) (rt_live RT Σ) (rt_sp0 RT Σ) G CEQ ROOM IE SLO SHI SES S1S S2S SFS SOS m LIB m5 PR5)|].
    split; [exact SM5|]. split; [exact OBM5|].
    split; [rewrite ZI5, ZIN, skipn_map; reflexivity|]. split; [exact HX5|].
    exact (pres_final_nf RT AF Σ lo P usp Whc m m m5 ART0 LOW ltac:(unfold P; clear - XL14; lia) ltac:(unfold P; clear; lia) (munch_refl _ m) PR5).
Qed.
End HCT.
